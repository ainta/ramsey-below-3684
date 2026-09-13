"""Run one isolated experiment with sampled aggregate RSS and a hard time cap.

This is resource supervision, not mathematical verification. Child outputs and
measurement reports are generated artifacts. Only the spawned process group is
terminated on a limit; no pre-existing user process is signalled.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def group_rss_kib(group):
    total = 0
    members = 0
    for item in Path('/proc').iterdir():
        if not item.name.isdigit():
            continue
        try:
            fields = (item / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) != group:
                continue
            for line in (item / 'status').read_text().splitlines():
                if line.startswith('VmRSS:'):
                    total += int(line.split()[1])
                    members += 1
                    break
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return total, members


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rss-mib', type=int, default=8192)
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == '--':
        command = command[1:]
    if not command or args.rss_mib <= 0 or args.seconds <= 0:
        parser.error('positive limits and a command are required')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    logfile = args.output.with_suffix('.log')
    env = os.environ.copy()
    for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
                'NUMBA_NUM_THREADS'):
        env[key] = '1'
    started = time.monotonic()
    peak = peak_members = 0
    samples = []
    status = 'RUNNING'
    with logfile.open('w') as out:
        process = subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT,
                                   env=env, start_new_session=True)
        try:
            available = sorted(os.sched_getaffinity(0))
            os.sched_setaffinity(process.pid, available[:2])
            last_print = -15
            while process.poll() is None:
                elapsed = time.monotonic() - started
                rss, members = group_rss_kib(process.pid)
                peak = max(peak, rss)
                peak_members = max(peak_members, members)
                samples.append([round(elapsed, 3), rss, members])
                if elapsed - last_print >= 15:
                    print(f'RUN {elapsed:.1f}s RSS={rss / 1024:.1f}MiB '
                          f'peak={peak / 1024:.1f}MiB processes={members}', flush=True)
                    last_print = elapsed
                if rss > args.rss_mib * 1024:
                    status = 'RSS_LIMIT'
                    break
                if elapsed > args.seconds:
                    status = 'TIME_LIMIT'
                    break
                time.sleep(0.5)
            if status != 'RUNNING':
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
            if status == 'RUNNING':
                status = 'PASS_PROCESS' if code == 0 else 'PROCESS_FAILED'
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    report = dict(status=status, returncode=code, command=command,
                  elapsed_seconds=time.monotonic() - started,
                  peak_sampled_rss_kib=peak, peak_processes=peak_members,
                  rss_limit_mib=args.rss_mib, time_limit_seconds=args.seconds,
                  sample_period_seconds=0.5, samples=samples, log=str(logfile))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'samples'}, indent=2))
    return 0 if status == 'PASS_PROCESS' else 1


if __name__ == '__main__':
    raise SystemExit(main())

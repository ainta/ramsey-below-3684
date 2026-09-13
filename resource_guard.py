"""Monitor one process group, with optional RAM, time, and CPU limits.

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


def stop_group(process):
    """Stop the group even if its leader exits before a compiler child."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    return process.wait()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rss-mib', type=int, help='Stop above this sampled RSS (MiB)')
    parser.add_argument('--seconds', type=int, help='Stop after this many seconds')
    parser.add_argument('--cpus', type=int, help='Optionally restrict CPU affinity')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == '--':
        command = command[1:]
    if not command or any(v is not None and v <= 0 for v in
                          (args.rss_mib, args.seconds, args.cpus)):
        parser.error('a command and positive limits (when specified) are required')
    if not Path('/proc/self/status').is_file():
        parser.error('RSS monitoring requires Linux; use the Lean/Lake build directly elsewhere')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    logfile = args.output.with_suffix('.log')
    if args.output.exists() or logfile.exists():
        parser.error('Report or log already exists; choose a new --output')
    env = os.environ.copy()
    for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
                'NUMBA_NUM_THREADS'):
        env.setdefault(key, '1')
    started = time.monotonic()
    peak = peak_members = 0
    samples = []
    status = 'RUNNING'
    with logfile.open('w') as out:
        process = subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT,
                                   env=env, start_new_session=True)
        try:
            if args.cpus is not None:
                available = sorted(os.sched_getaffinity(0))
                try:
                    os.sched_setaffinity(process.pid, available[:args.cpus])
                except ProcessLookupError:
                    pass  # A short command may already have finished.
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
                if args.rss_mib is not None and rss > args.rss_mib * 1024:
                    status = 'RSS_LIMIT'
                    break
                if args.seconds is not None and elapsed > args.seconds:
                    status = 'TIME_LIMIT'
                    break
                time.sleep(0.5)
            if status != 'RUNNING':
                code = stop_group(process)
            else:
                code = process.wait()
            if status == 'RUNNING':
                status = 'PASS_PROCESS' if code == 0 else 'PROCESS_FAILED'
        except KeyboardInterrupt:
            status = 'INTERRUPTED'
            code = stop_group(process)
        finally:
            if process.poll() is None:
                stop_group(process)
    report = dict(status=status, returncode=code, command=command,
                  elapsed_seconds=time.monotonic() - started,
                  peak_sampled_rss_kib=peak, peak_processes=peak_members,
                  rss_limit_mib=args.rss_mib, time_limit_seconds=args.seconds,
                  cpu_affinity_limit=args.cpus,
                  sample_period_seconds=0.5, samples=samples, log=str(logfile))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'samples'}, indent=2))
    return 0 if status == 'PASS_PROCESS' else 1


if __name__ == '__main__':
    raise SystemExit(main())

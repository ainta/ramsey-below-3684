"""Recover resource supervision without restarting existing kernel checks.

The old parent is gone, so its wait status cannot be recovered. Success is
explicitly PASS_DURABLE_VERIFICATION, never an invented PASS_PROCESS/exit 0.
Every saved compiler success, the complete build plan, source digest, and
object timestamp are checked before that status is emitted.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import time

from resource_guard import group_rss_kib

ROOT = Path(__file__).resolve().parent


def identity(pid):
    try:
        fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        return dict(state=fields[0], group=int(fields[2]), start=int(fields[19]))
    except (FileNotFoundError, ProcessLookupError):
        return None


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def validate_complete(report_path, rounds, reuse_data):
    raw = report_path.read_bytes()
    report = json.loads(raw)
    assert report['status'] == 'PASS_ALL_REQUESTED_ROUND_CHECKS_NOT_HEADLINE_THEOREM'
    assert report['rounds'] == rounds
    plan = []
    for rnd in rounds:
        if not reuse_data:
            data = json.loads((ROOT / f'lean/Kernel/ChainData/R{rnd:02d}.json').read_text())
            plan.extend((m, 'chain_data') for m in data['modules'][2:])
        plan.append((f'Kernel/CheckedChainData/R{rnd:02d}', 'checked_chain_interface'))
        for label in ['ChainChecks', 'OuterChecks']:
            manifest = json.loads((ROOT / f'lean/Kernel/{label}/R{rnd:02d}.json').read_text())
            if label == 'OuterChecks':
                plan.extend((m, 'outer_data') for m in manifest['base_modules'][2:])
            plan.extend((c['module'], label) for c in manifest['chunks'])
            plan.extend((m, label + '_assembly') for m in manifest['assemblies'])
    assert [(r['module'], r['phase']) for r in report['modules']] == plan
    for row in report['modules']:
        source = ROOT / 'lean' / (row['module'] + '.lean')
        obj = source.with_suffix('.olean')
        assert hashlib.sha256(source.read_bytes()).hexdigest() == row['source_sha256'], row['module']
        assert obj.is_file() and obj.stat().st_mtime >= source.stat().st_mtime, row['module']
        if 'object_sha256' in row:
            assert hashlib.sha256(obj.read_bytes()).hexdigest() == row['object_sha256'], row['module']
    return hashlib.sha256(raw).hexdigest(), len(plan)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pid', type=int, required=True)
    parser.add_argument('--round', type=int, nargs='+', required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rss-mib', type=int, default=6144)
    parser.add_argument('--historical-peak-kib', type=int, required=True)
    parser.add_argument('--reuse-chain-data', action='store_true')
    args = parser.parse_args()
    before = identity(args.pid)
    assert before and before['group'] == args.pid
    assert Path(f'/proc/{args.pid}/cwd').resolve() == ROOT
    command = Path(f'/proc/{args.pid}/cmdline').read_bytes().split(b'\0')
    assert b'verify_rounds.py' in command and str(args.report).encode() in command
    assert not args.output.exists(), 'Preserve existing resource evidence'
    budget = json.loads((ROOT / 'verification_budget.json').read_text())
    deadline = datetime.fromisoformat(budget['verification_deadline_utc'].replace('Z', '+00:00'))
    started = time.monotonic()
    initial_elapsed = float(Path('/proc/uptime').read_text().split()[0]) - before['start'] / os.sysconf('SC_CLK_TCK')
    started_utc = datetime.now(timezone.utc).isoformat()
    peak = members_peak = count = 0
    status = 'MONITORING_RECOVERED_GROUP'
    live = args.output.with_suffix('.recovered_live.json')
    report = {}
    while True:
        current = identity(args.pid)
        same = current is not None and current['start'] == before['start']
        rss, members = group_rss_kib(args.pid) if same else (0, 0)
        peak = max(peak, rss)
        members_peak = max(members_peak, members)
        count += 1
        report = dict(status=status, original_pid=args.pid, original_start_ticks=before['start'],
            original_exit_code=None, elapsed_seconds=initial_elapsed + time.monotonic() - started,
            recovery_window_seconds=time.monotonic() - started, recovery_started_utc=started_utc,
            current_sampled_rss_kib=rss,
            peak_sampled_rss_kib=max(args.historical_peak_kib, peak),
            recovery_window_peak_sampled_rss_kib=peak,
            last_observed_historical_peak_kib=args.historical_peak_kib,
            peak_processes=members_peak, samples=count, sample_period_seconds=0.5,
            rss_limit_mib=args.rss_mib, verification_deadline_utc=deadline.isoformat(),
            continuous_memory_measurement=False,
            measurement_gap_note='Original tool-session supervisor disappeared; old wait status and samples are unavailable. Historical reported peak and this recovery window are retained, not a continuous peak.',
            completion_report=str(args.report),
            log=str(args.output.with_suffix('.log')))
        if not same or current['state'] == 'Z':
            try:
                digest, modules = validate_complete(args.report, args.round, args.reuse_chain_data)
                report.update(status='PASS_DURABLE_VERIFICATION',
                    complete_build_plan_and_sources_verified=True,
                    completion_report_sha256=digest, verified_modules=modules)
            except Exception as error:
                report.update(status='FAILED_OR_INCOMPLETE_RECOVERED_JOB', error=repr(error))
            break
        if rss > args.rss_mib * 1024 or datetime.now(timezone.utc) >= deadline:
            report['status'] = 'RSS_LIMIT' if rss > args.rss_mib * 1024 else 'TIME_LIMIT'
            # Signal only the validated process group belonging to this proof job.
            last = identity(args.pid)
            if last and last['start'] == before['start'] and last['group'] == args.pid:
                os.killpg(args.pid, signal.SIGTERM)
                until = time.monotonic() + 5
                while identity(args.pid) and time.monotonic() < until:
                    time.sleep(0.1)
                last = identity(args.pid)
                if last and last['start'] == before['start'] and last['state'] != 'Z':
                    os.killpg(args.pid, signal.SIGKILL)
            break
        if count % 10 == 1:
            atomic_json(live, report)
        time.sleep(0.5)
    atomic_json(live, report)
    atomic_json(args.output, report)
    print(json.dumps(report, indent=2), flush=True)
    return 0 if report['status'] == 'PASS_DURABLE_VERIFICATION' else 1


if __name__ == '__main__':
    raise SystemExit(main())

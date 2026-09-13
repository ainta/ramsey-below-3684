"""One-time recovery of orphaned verification jobs after a tool-session loss."""
from datetime import datetime, timezone
import json
from pathlib import Path
import signal
import subprocess
import time
import os
import shutil

from attach_resource_guard import identity

ROOT = Path(__file__).resolve().parent
PYTHON = str(ROOT / '.venv/bin/python')


def launch(command, log):
    with (ROOT / log).open('x') as output:
        child = subprocess.Popen(command, cwd=ROOT, start_new_session=True,
            stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT)
    return child.pid


def main():
    marker = ROOT / 'runs/tool_session_recovery.json'
    assert not marker.exists(), 'Recovery already launched; inspect before retrying'
    budget = json.loads((ROOT / 'verification_budget.json').read_text())
    deadline = datetime.fromisoformat(budget['verification_deadline_utc'].replace('Z', '+00:00'))
    remaining = int((deadline - datetime.now(timezone.utc)).total_seconds())
    assert remaining > 0
    old = {}
    for pid, name in [(1728610, 'verify_rounds.py'), (1729281, 'verify_rounds.py'),
                      (2174028, 'finish_verification.py'), (2315820, 'verify_pinned_final.py')]:
        old[pid] = identity(pid)
        assert old[pid] and old[pid]['group'] == pid
        assert Path(f'/proc/{pid}/cwd').resolve() == ROOT
        assert name.encode() in Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
    assert (ROOT / 'runs/final_assembly_second.resources.log').read_text().rstrip().endswith(
        'WAIT MODULE Kernel/OuterChecks/R05Boundary')
    assert not (ROOT / 'runs/final_assembly_second.resources.json').exists()
    assert not (ROOT / 'runs/pinned_final.resources.json').exists()
    record = dict(status='RECOVERY_STARTING', started_utc=datetime.now(timezone.utc).isoformat(),
        previous_group_identities=old,
        original_wait_statuses_unavailable=True,
        last_old_aggregate_sample_utc=datetime.fromtimestamp(
            (ROOT / 'runs/aggregate_complete_pipeline.json').stat().st_mtime, timezone.utc).isoformat(),
        numerical_workers_not_restarted=True, new_processes={})
    marker.write_text(json.dumps(record, indent=2) + '\n')
    for pid, rounds, prefix, peak in [
        (1728610, [1, 2, 3, 4, 5, 6], 'rounds_01_06_full', 4656333),
        (1729281, [7], 'round_07_full', 2973696)]:
        command = [PYTHON, '-u', 'attach_resource_guard.py', '--pid', str(pid),
            '--round', *map(str, rounds), '--report', f'runs/{prefix}.json',
            '--output', f'runs/{prefix}.resources.json', '--historical-peak-kib', str(peak)]
        if rounds == [7]:
            command.append('--reuse-chain-data')
        record['new_processes'][prefix + '_monitor'] = launch(command, f'runs/{prefix}.recovery_supervisor.log')
    # Only the two idle followers are replaced. Long-running Lean checks are untouched.
    for pid in [2174028, 2315820]:
        current = identity(pid)
        assert current and current['start'] == old[pid]['start']
        os.kill(pid, signal.SIGTERM)
    for pid in [2174028, 2315820]:
        until = time.monotonic() + 5
        while (current := identity(pid)) and current['state'] != 'Z' and time.monotonic() < until:
            time.sleep(0.1)
        assert not current or current['state'] == 'Z'
    for name in ['final_assembly_second.json', 'final_assembly_second.resources.log',
                 'pinned_final.resources.log']:
        source = ROOT / 'runs' / name
        if source.exists():
            shutil.copy2(source, source.with_name(name + '.before_session_recovery'))
    jobs = [
        ('final_assembly_second', [PYTHON, '-u', 'finish_verification.py',
            '--dependency-project', '/home/ainta/manuscripts/ramsey/claude_revision/lean',
            '--report', 'runs/final_assembly_second.json'], '10,11'),
        ('pinned_final', [PYTHON, '-u', 'verify_pinned_final.py',
            '--wait-for', 'runs/final_assembly_second.resources.json',
            '--report', 'runs/pinned_final.json'], '12,13')]
    for prefix, command, cpus in jobs:
        wrapper = ['taskset', '-c', cpus, PYTHON, '-u', 'resource_guard.py',
            '--rss-mib', '8192', '--seconds', str(remaining),
            '--output', f'runs/{prefix}.resources.json', '--', *command]
        record['new_processes'][prefix + '_supervisor'] = launch(wrapper, f'runs/{prefix}.recovered_supervisor.log')
    record['status'] = 'RECOVERY_LAUNCHED_NO_NUMERICAL_RESTART'
    marker.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()

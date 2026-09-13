"""Distinguish an observed process exit from recovered compiler evidence."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def resource_passed(report):
    if report.get('status') == 'PASS_PROCESS':
        return True
    if report.get('status') != 'PASS_DURABLE_VERIFICATION':
        return False
    if not report.get('complete_build_plan_and_sources_verified'):
        return False
    path = (ROOT / report['completion_report']).resolve()
    if not path.is_relative_to(ROOT / 'runs'):
        return False
    raw = path.read_bytes()
    return (hashlib.sha256(raw).hexdigest() == report['completion_report_sha256']
            and json.loads(raw)['status'] ==
            'PASS_ALL_REQUESTED_ROUND_CHECKS_NOT_HEADLINE_THEOREM')

"""Check release sources and rebuild with configurable parallelism and monitoring."""
import argparse
from datetime import datetime, timezone
import math
from pathlib import Path
import subprocess
import sys

from prepare_sources import DEFAULT_MANIFEST, check_sources, load_manifest

ROOT = Path(__file__).resolve().parent


def positive_float(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError('expected a positive finite number')
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1, help='Concurrent Lean processes (default: 1)')
    parser.add_argument('--ram-gib', type=positive_float, help='Optional total sampled RSS limit')
    parser.add_argument('--timeout-hours', type=positive_float, help='Optional rebuild time limit')
    parser.add_argument('--dependency-project', type=Path, default=ROOT / 'lean')
    parser.add_argument('--dependency-overlay', type=Path)
    parser.add_argument('--source-manifest', type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument('--module', default='RamseyBelow3684', help='Optional smaller smoke-check target')
    args = parser.parse_args()
    if args.jobs < 1:parser.error('--jobs must be positive')
    count = check_sources(ROOT, load_manifest(args.source_manifest))
    print(f'Source manifest checked: {count:,} modules', flush=True)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    prefix = ROOT / 'runs' / ('rebuild-' + stamp)
    guard = [sys.executable, '-u', str(ROOT / 'resource_guard.py'),
             '--output', str(prefix.with_suffix('.resources.json'))]
    if args.ram_gib is not None:
        guard += ['--rss-mib', str(max(1, math.ceil(args.ram_gib * 1024)))]
    if args.timeout_hours is not None:
        guard += ['--seconds', str(max(1, math.ceil(args.timeout_hours * 3600)))]
    build = [sys.executable, '-u', str(ROOT / 'reproduce_lean.py'),
             '--dependency-project', str(args.dependency_project.resolve()),
             '--module', args.module, '--jobs', str(args.jobs),
             '--output-root', str(prefix), '--report', str(prefix.with_suffix('.json'))]
    if args.dependency_overlay:
        build += ['--dependency-overlay', str(args.dependency_overlay.resolve())]
    print('Build output:', prefix, flush=True)
    return subprocess.call(guard + ['--'] + build, cwd=ROOT)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as error:
        raise SystemExit(str(error)) from error

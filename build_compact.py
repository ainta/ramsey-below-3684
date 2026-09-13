"""Use author-supplied extraction and outward repairs with an explicit U root.

No search profile is accepted as a Ramsey premise. Every seed support query
uses the exact profile reconstructed from the current candidate chain. The
independent verifier must subsequently accept the entire chain from U.
"""
import argparse
import json
from pathlib import Path
import shutil
import build_certificate as base
from exact_profile import Profile, decode
from build_fast import FastBuild


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--initial', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('tables', nargs='+', type=Path)
    args = p.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=False)
    raw = json.loads(args.initial.read_text())
    points = [(decode(t), decode(v)) for t, v in raw['points']]
    base.root_cached = lambda: Profile(points)
    shutil.copyfile(args.initial, args.output.parent/'initial_u.json')
    builder = FastBuild('explicit', args.output)
    builder.columns = True
    try:
        for rnd, table in enumerate(args.tables):
            print('TABLE', rnd, str(table), flush=True)
            builder.round(rnd, str(table.resolve()))
        builder.save(args.output)
    finally:
        builder.recordfile.close()
        builder.edgefile.close()


if __name__ == '__main__':
    main()

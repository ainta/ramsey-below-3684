"""Maintainer command: package the exact source closure of the verified theorem."""
import argparse
import gzip
import json
from pathlib import Path
import subprocess
import tarfile

from reproduce_lean import digest, import_closure

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verified-workspace', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, default=ROOT / 'release/source-manifest.json')
    args = parser.parse_args()
    verified = args.verified_workspace.resolve()
    evidence = json.loads((verified / 'STATUS.json').read_text())
    if evidence['status'] != 'PASS_COMPLETE_UNCONDITIONAL_RAMSEY_BASE_3_68395':
        raise SystemExit('A completed verification report is required')
    modules, external = import_closure('RamseyBelow3684', verified / 'lean')
    tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0'))
    rows = []
    for module in modules:
        name = 'lean/' + module.replace('.', '/') + '.lean'
        path = verified / name
        sha = digest(path)
        if sha != evidence['source_sha256'][name]:
            raise SystemExit('Verified source changed: ' + name)
        generated = name not in tracked
        if not generated and digest(ROOT / name) != sha:
            raise SystemExit('Tracked proof source differs: ' + name)
        if generated and not name.startswith('lean/Kernel/'):
            raise SystemExit('Untracked non-generated source: ' + name)
        rows.append(dict(path=name, size=path.stat().st_size, sha256=sha, generated=generated))
    rows.sort(key=lambda r: r['path'])
    if args.manifest.exists():
        raise SystemExit('Manifest already exists; preserve it or choose a new --manifest')
    args.output_dir.mkdir(parents=True, exist_ok=False)
    archive = args.output_dir / 'generated-lean-sources.tar.gz'
    print('PACK', sum(r['generated'] for r in rows), 'generated modules', flush=True)
    with archive.open('xb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0, compresslevel=6) as gz:
            with tarfile.open(fileobj=gz, mode='w|', format=tarfile.USTAR_FORMAT) as tar:
                for row in rows:
                    if not row['generated']:continue
                    info = tarfile.TarInfo(row['path'])
                    info.size = row['size']; info.mode = 0o644; info.mtime = 0
                    with (verified / row['path']).open('rb') as source:
                        tar.addfile(info, source)
    manifest = dict(schema=1, root_module='RamseyBelow3684', module_count=len(rows),
        source_bytes=sum(r['size'] for r in rows), lean_toolchain='v4.32.1',
        upstream_commit=evidence['final_theorem']['upstream_commit'],
        mathlib_commit=evidence['final_theorem']['mathlib_commit'],
        external_modules=external, files=rows,
        archive=dict(name=archive.name, sha256=digest(archive), size=archive.stat().st_size))
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(manifest, indent=2) + '\n'
    args.manifest.write_text(encoded)
    release_manifest = args.output_dir / 'source-manifest.json'
    release_manifest.write_text(encoded)
    (args.output_dir / 'SHA256SUMS').write_text(
        f'{digest(archive)}  {archive.name}\n'
        f'{digest(release_manifest)}  {release_manifest.name}\n')
    print('PACKAGED', archive, archive.stat().st_size, 'bytes', flush=True)


if __name__ == '__main__':
    main()

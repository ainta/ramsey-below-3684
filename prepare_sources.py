"""Install or check the generated Lean sources for this release."""
import argparse
import json
from pathlib import Path, PurePosixPath
import shutil
import re
import tarfile
import tempfile

from reproduce_lean import digest, import_closure

ROOT = Path(__file__).resolve().parent
DEFAULT_MANIFEST = ROOT / 'release/source-manifest.json'


def load_manifest(path):
    data = json.loads(Path(path).read_text())
    if data.get('schema') != 1:
        raise ValueError('Unsupported source manifest')
    seen = set()
    for row in data['files']:
        name = row['path']
        parts = PurePosixPath(name).parts
        if (PurePosixPath(name).is_absolute() or '..' in parts or
                not name.startswith('lean/') or not name.endswith('.lean') or
                str(PurePosixPath(name)) != name or name in seen):
            raise ValueError('Invalid or duplicate source path: ' + name)
        if (not isinstance(row['size'], int) or row['size'] < 0 or
                not re.fullmatch(r'[0-9a-f]{64}', row['sha256']) or
                not isinstance(row['generated'], bool)):
            raise ValueError('Invalid source metadata: ' + name)
        seen.add(name)
    if len(seen) != data['module_count']:
        raise ValueError('Incorrect module count in source manifest')
    return data


def checked_target(root, name):
    target = root / name
    current = root
    for part in PurePosixPath(name).parts:
        current = current / part
        if current.is_symlink():
            raise ValueError('Source path contains a symlink: ' + str(current))
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError('Source path escapes the checkout: ' + name)
    return target


def check_sources(root, manifest):
    missing = []
    for row in manifest['files']:
        path = checked_target(root, row['path'])
        if not path.is_file():
            missing.append(row['path'])
        elif path.stat().st_size != row['size'] or digest(path) != row['sha256']:
            raise ValueError('Source differs from this release: ' + row['path'])
    if missing:
        raise ValueError(f'{len(missing)} source files missing (first: {missing[0]}). '
                         'Run prepare_sources.py --archive generated-lean-sources.tar.gz')
    modules, external = import_closure(manifest['root_module'], root / 'lean')
    expected = {r['path'] for r in manifest['files']}
    actual = {'lean/' + m.replace('.', '/') + '.lean' for m in modules}
    if actual != expected or external != manifest['external_modules']:
        raise ValueError('The final theorem import closure differs from the release manifest')
    return len(modules)


def install_sources(root, manifest, archive):
    if archive.stat().st_size != manifest['archive']['size']:
        raise ValueError('Archive size does not match this release')
    if digest(archive) != manifest['archive']['sha256']:
        raise ValueError('Archive SHA-256 does not match this release')
    expected = {r['path']: r for r in manifest['files'] if r['generated']}
    # Check the checkout and all existing destinations before installing sources.
    for row in manifest['files']:
        name = row['path']
        target = checked_target(root, name)
        if not row['generated'] and not target.is_file():
            raise ValueError('Missing tracked source; use the matching Git revision: ' + name)
        if target.exists() and (not target.is_file() or digest(target) != row['sha256']):
            raise ValueError('Refusing to overwrite a different file: ' + name)
    with tempfile.TemporaryDirectory(prefix='.source-install-', dir=root) as temporary:
        staged = Path(temporary)
        seen = set()
        # Stream only named regular files; never extract archive paths or links directly.
        with tarfile.open(archive, 'r|gz') as tar:
            for member in tar:
                row = expected.get(member.name)
                if (row is None or member.name in seen or not member.isfile() or
                        member.size != row['size']):
                    raise ValueError('Unexpected archive entry: ' + member.name)
                target = staged / member.name
                target.parent.mkdir(parents=True, exist_ok=True)
                stream = tar.extractfile(member)
                with target.open('xb') as out:
                    shutil.copyfileobj(stream, out, length=1024 * 1024)
                if digest(target) != row['sha256']:
                    raise ValueError('Source hash mismatch: ' + member.name)
                seen.add(member.name)
        if seen != set(expected):
            raise ValueError('Archive is missing source files')
        for name in sorted(seen):
            target = checked_target(root, name)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                if digest(target) != expected[name]['sha256']:
                    raise ValueError('Source changed during installation: ' + name)
                continue
            # Exclusive creation also protects files created since the preflight.
            with (staged / name).open('rb') as source, target.open('xb') as out:
                shutil.copyfileobj(source, out, length=1024 * 1024)
    return check_sources(root, manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='Generated source archive to install')
    parser.add_argument('--manifest', type=Path,
                        help='Source manifest (default: beside archive, or release/source-manifest.json)')
    args = parser.parse_args()
    path = args.manifest or (args.archive.parent / 'source-manifest.json'
                            if args.archive else DEFAULT_MANIFEST)
    manifest = load_manifest(path)
    count = (install_sources(ROOT, manifest, args.archive) if args.archive else
             check_sources(ROOT, manifest))
    print(f'SOURCE CHECK PASSED: {count:,} modules; all source hashes and imports match.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, tarfile.TarError) as error:
        raise SystemExit(str(error)) from error

# Preparing a source-first release

The publication unit is a Git revision plus the generated-source archive.
It contains the source closure of the theorem, without local build caches.

## Package

From this checkout, point the packaging command at the completed verification
workspace and choose a new output directory:

```sh
python3 package_sources.py \
  --verified-workspace /path/to/completed-verification \
  --output-dir /path/to/new-release-assets
```

The command reads that workspace's completed `STATUS.json`, follows the
final theorem's imports, and checks every source hash. Tracked Lean files
must agree with this checkout. Only the missing generated sources are packed.

It produces:

- `generated-lean-sources.tar.gz`: regular `.lean` files with relative paths.
- `source-manifest.json`: the complete source inventory, hashes, and dependency pins.
- `SHA256SUMS`: checksums using the two release asset filenames, without local paths.

The manifest is also written to `release/source-manifest.json` for inclusion
in the Git revision. Existing output directories and manifests are preserved;
use a new destination and `--manifest` when preparing a different release.

## Check and publish

1. Review the source manifest and check the asset checksums.
2. In a separate clean checkout, install the archive with `prepare_sources.py`.
   Its complete source inventory should contain 16,024 modules, with only
   Mathlib, RamseyLean, and Std imports external to this theorem's closure.
3. Check the build entry points and, when running a new verification, record
   its report separately from the original evidence in `runs/`.
4. Commit the source manifest and documentation, tag that exact revision,
   and attach all three files to its release.

The new source-first artifacts belong to a new release, rather than silently
changing v1.0. Keep the original certificate available for research and replay.
Do not include `dependencies/pinned_check_lean` or its absolute symlinks in
the new source bundle. New users obtain external dependencies from the pins.

The original verification is documented in [VERIFICATION.md](VERIFICATION.md).
A change to packaging or build tools does not change that historical run's
measured settings or reports.

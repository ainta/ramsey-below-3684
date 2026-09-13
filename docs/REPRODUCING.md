# Rebuilding the proof

## 1. Install the sources

Maintainers produce the source bundle using [RELEASING.md](RELEASING.md);
the v1.0 assets are not this bundle.

Clone the repository and download these three files from the matching
[release](https://github.com/ainta/ramsey-below-3684/releases):

- `generated-lean-sources.tar.gz`
- `source-manifest.json`
- `SHA256SUMS`

Keep the three files in one directory. From that directory, check the download:

```sh
sha256sum -c SHA256SUMS
```

Then, from the repository root:

```sh
python3 prepare_sources.py --archive /path/to/generated-lean-sources.tar.gz
```

The installer checks the archive, each source file, and the complete import
closure. Existing identical files are kept; different files are not overwritten.
It reads `source-manifest.json` beside the archive. Keep that manifest for
the verification command below. You can select a different manifest location
with `--manifest`.

The full theorem uses **16,024 local Lean modules**, about **2.60 GB of source**.
The archive supplies generated `.lean` files, not compiled `.olean` files.
The numerical certificate and discovery scripts are not needed for this build.

## 2. Prepare the dependencies

Install [elan](https://github.com/leanprover/elan), Python 3.10 or newer, and Git.
The checkout pins Lean **4.32.1**, mathlib, and the original RamseyLean repository.

```sh
cd lean
lake update
lake exe cache get
lake build @RamseyLean
cd ..
```

This installs mathlib's build cache and builds the upstream RamseyLean library.
Dependency preparation is separate from checking this repository's proof.

## 3. Verify

On Linux, the convenience command builds into a fresh directory and records
elapsed time and sampled RAM usage:

```sh
python3 verify.py --source-manifest /path/to/source-manifest.json
```

One Lean process runs at a time by default. You can choose parallelism and
optionally set a total RAM or time limit:

```sh
python3 verify.py --source-manifest /path/to/source-manifest.json \
  --jobs 4 --ram-gib 16 --timeout-hours 168
```

| Option | Meaning | Default |
| --- | --- | --- |
| `--jobs N` | Concurrent Lean compiler processes | 1 |
| `--ram-gib G` | Stop when the group's sampled RSS exceeds G GiB | No limit |
| `--timeout-hours H` | Stop the rebuild after H hours | No limit |

The original run's settings are not required. More concurrent processes
generally use more RAM; the RAM limit stops a run rather than reducing its
memory consumption. Monitoring samples every 0.5 seconds. CPU affinity is
not restricted by default.

Outputs go to a new `runs/rebuild-<timestamp>` directory, with matching JSON
reports and a log beside it. Progress and resource reports are separate:
the build report records Lean verification, and the resource report records
the process outcome and measurements.

For an existing matching dependency checkout, pass `--dependency-project`.
Advanced audited overlays can be selected with `--dependency-overlay`; the
isolated builder rejects search paths containing this project's local proof objects.

### Standard Lake build

Once sources and dependencies are installed, a standard build is also available:

```sh
cd lean
lake build
```

The default target is `RamseyBelow3684`. This uses Lake's ordinary cache and
scheduler. The convenience command above instead uses a fresh output directory
and exposes an explicit process-count setting. RSS monitoring is Linux-specific;
ordinary Lean/Lake builds do not require that monitor.

### Source inspection and small checks

To check the source hashes without compiling:

```sh
python3 prepare_sources.py --manifest /path/to/source-manifest.json
```

To inspect the build plan:

```sh
python3 reproduce_lean.py --plan-only --report runs/import-plan.json
```

To smoke-check a small module after preparing the sources and dependencies:

```sh
python3 verify.py --source-manifest /path/to/source-manifest.json --module TerminalNumeric
```

A small-module check reports its own target, not completion of the full theorem.
See [VERIFICATION.md](VERIFICATION.md) for the completed original run.

# Ramsey below 3.684

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22737676.svg)](https://doi.org/10.5281/zenodo.22737676)

A Lean proof that, for all sufficiently large integers k,

```text
R(k,k) ≤ (73679/20000)^k = 3.68395^k,     3.68395 < 3.684.
```

The main theorem is [`Compact3684.ramsey_le_368395`](lean/RamseyBelow3684.lean).
It connects the initial Ramsey bound, eight certified bootstrap rounds,
and the terminal graph argument. The full proof has been checked by Lean,
using only `propext`, `Classical.choice`, and `Quot.sound`.

[Paper (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex)

## Build

The repository contains the reusable proofs and build tools. The source
release adds `generated-lean-sources.tar.gz`, `source-manifest.json`, and
`SHA256SUMS`; download them from the matching
[release](https://github.com/ainta/ramsey-below-3684/releases).

After downloading these files into one directory:

```sh
# In the download directory
sha256sum -c SHA256SUMS

# In this repository
python3 prepare_sources.py --archive /path/to/generated-lean-sources.tar.gz

# Prepare the pinned dependencies
cd lean
lake update
lake exe cache get
lake build @RamseyLean
cd ..

# Check the proof and record resource usage (Linux)
python3 verify.py --source-manifest /path/to/source-manifest.json
```

Use Python 3.10+ and [elan](https://github.com/leanprover/elan).
Lean 4.32.1 and the dependency revisions are pinned in `lean/`.
The complete local source closure has 16,024 modules, about 2.60 GB.

Choose settings for your machine:

```sh
python3 verify.py --source-manifest /path/to/source-manifest.json \
  --jobs 4 --ram-gib 16 --timeout-hours 168
```

By default, the convenience tool runs one Lean process at a time and records
RAM and elapsed time without imposing a RAM or time limit. All three settings
are configurable; our original execution settings are not required.
A standard `lake build` in `lean/` is also available after source preparation.

See [Rebuilding the proof](docs/REPRODUCING.md) for setup details, ordinary
Lake builds, and smaller checks.

## How the proof works

1. Start from the GNNW bound formalized in
   [RamseyLean-bootstrap](https://github.com/wamlat/RamseyLean-bootstrap).
2. Apply eight rounds using a uniform weighted graph theorem and certified
   finite continuation rules.
3. Obtain the affine bound with coefficients 0.544 and 0.7622, then use the
   all-spines graph argument to reach the diagonal base 3.68395.

For efficient checking, logarithm enclosures are shared, paths are compressed,
and arithmetic is checked in bounded chunks with `decide +kernel`. The
checker-soundness theorems connect these computations to the graph result.

[Mathematical details](PROOF_ROUTE.md) · [Weighted graph theorem](WEIGHTED_PROOF.md)

## Our verification

The complete verification took **56 h 43 min 40 s**, using existing matching
external dependency builds. The final pinned-source recheck had a **5.40 GiB**
sampled group peak; observed aggregate monitor windows reached **9.54 GiB**.

[Verification record](docs/VERIFICATION.md) describes the settings, measurements,
and monitoring history. [STATUS.json](STATUS.json) and
[the final axiom log](runs/pinned_final_theorem.log) contain the detailed evidence.
New runs write separate reports under `runs/`.

## Repository guide

| Location | Contents |
| --- | --- |
| `lean/RamseyBelow3684.lean` | Final unconditional theorem |
| `lean/Ramsey3683Bootstrap/` | Graph and checker-soundness proofs |
| `lean/Kernel/`, `lean/CertifiedRound/` | Arithmetic checkers and round assemblies |
| `docs/` | Reproduction instructions and verification history |
| `runs/`, `STATUS.json` | Original verification evidence |
| Source release archive | Generated Lean modules required for the full build |

The v1.0 numerical certificate remains available for discovery and replay work.
It is separate from the source-based Lean build above.
Maintainers: see [Preparing a release](docs/RELEASING.md).

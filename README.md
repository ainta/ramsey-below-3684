# Ramsey below 3.684: complete kernel-checked proof

**Complete:** Lean proves that, for all sufficiently large integers k,

    R(k,k) ≤ (73679/20000)^k = 3.68395^k,     3.68395 < 3.684.

The unconditional theorem is `Compact3684.ramsey_le_368395` in
[`lean/RamseyBelow3684.lean`](lean/RamseyBelow3684.lean). All eight concrete
rounds, the weighted graph theorem, full checker soundness, and terminal
graph transfer are connected. The final theorem was rechecked against the
pinned original-repository sources; its only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or
`native_decide` is a premise of the result.

The observed complete verification finished in **56 hours 43 minutes 40
seconds**, below the one-week budget. Matching external dependency caches
were reused; a separate clean rebuild is not being claimed. The final pinned
recheck had a **5.40 GiB** sampled process-group peak. Historical aggregate
monitor windows reached **9.54 GiB** and **8.29 GiB**; a roughly six-minute
supervision gap means these are not a continuous whole-run RAM measurement.
See [`STATUS.json`](STATUS.json), [`runs/pinned_final.json`](runs/pinned_final.json),
and the resource details below. Original archives/repositories were not modified.

## Repository layout and data

The git tree contains the reusable Lean modules, the checker-soundness
sources under `lean/Kernel/*.lean`, the round wrappers in
`lean/CertifiedRound/`, the Python/C++ tooling, and the verification
reports in `runs/`. Three large components are not tracked in git:

- `certificates/` (~1.7 GB of compressed record, edge, and run streams)
  is attached to the GitHub release as `certificates.tar` and is required
  for replay and for regenerating the kernel data modules.
- `dependencies/` (~0.4 GB) is a local build cache of the pinned upstream
  `wamlat/RamseyLean-bootstrap` (commit `e53b8cf1...`) and mathlib; it is
  attached to the release as `dependencies-cache.tar` for bit-exact audit,
  and can otherwise be rebuilt from the pinned commits in `lean/lakefile.toml`.
- the generated kernel data modules (~7.3 GB under `lean/Kernel/*/`) are
  regenerated from `certificates/` by the `generate_*.py` scripts or by
  `reproduce_lean.py`.

The main result is a direct GNNW-based eight-round chain, with no missing
predecessor. The resource-oriented version spends a little numerical slack
to share expensive logarithm checks:

| Artifact | What was actually established |
| --- | --- |
| `certificates/target_runs/verification.json` | Full exact replay; upper base 3.683687152314; expanded and run checkers agree byte-for-byte |
| `certificates/target_runs/verification18.json` | Full replay also passes with 18-digit directed intervals |
| `certificates/quantized/verification.json` | Shared-log version: upper base 3.683749312877; 351,607 log enclosures independently rechecked |
| `lean/TerminalNumeric.lean` | Lean proof of `2*exp(0.544)*sqrt(exp(0.7622)-1) < 3.684` |
| `lean/PrefixRange.lean` | Lean proofs of range/path-summary soundness and the affine-lift cancellation |
| `lean/ControlQuantization.lean` | Lean proofs of scalar support/density/budget facts for control rounding |
| `lean/Ramsey3683Bootstrap/WeightedUniform.lean` | Full uniform weighted book theorem on upstream graph predicates, including schedule existence and initialization |
| `lean/Ramsey3683Bootstrap/FiniteContinuation.lean` | Finite graph continuation with explicit integer thresholds and dense stopping hypotheses |
| `lean/Ramsey3683Bootstrap/GridClosure.lean` | Actual grid continuation, uniform profile closure, and passage to all integer targets |
| `lean/Kernel/LogInterval.lean` | Real soundness of the exact integer logarithm checker |
| `lean/InitialProfile.lean` | Unconditional initial profile, assembled from the original GNNW theorem and 20,000 kernel-checked tangent bounds |
| `lean/Ramsey3683Bootstrap/TerminalTransfer.lean` | Full finite and asymptotic all-spines graph transfer |
| `lean/TerminalTarget.lean` | Below-3.684 diagonal bound conditional only on the certificate's specific affine Ramsey profile |
| `lean/Ramsey3683Bootstrap/ChainSound.lean` | Full record/path interpretation by rank induction from explicit Boolean guards |
| `lean/Ramsey3683Bootstrap/RoundSound.lean` | Full round soundness, including outer paths and finite profile covers |
| `lean/ReflectedInitial.lean` | Checked link from the original theorem to the concrete reflected initial profile |
| `lean/TerminalStrict.lean` | The final reflected profile implies an eventual diagonal bound with base **3.68395 < 3.684** |
| `lean/ClosedFirstRoundNumeric.lean` | Closed, unconditional checkpoint: eventually `R(k,k) ≤ (93/25)^k`, checked against the pinned original sources |
| `lean/RamseyBelow3684.lean` | Complete unconditional eventual bound with base **3.68395 < 3.684**, all concrete kernel checks and pinned-source recheck passed |

Every numerical verification also checks that **0.544+0.7622t dominates the
whole reconstructed profile**. The numerical replay alone is not a Lean
Ramsey theorem. Here the graph rules, initial profile, checker soundness,
complete concrete kernel execution, and terminal transfer are all proved
and composed in the unconditional final module. All verification jobs have
finished successfully.
See [PROOF_ROUTE.md](PROOF_ROUTE.md) for the precise mathematical route and
completion evidence. [STATUS.json](STATUS.json) records the verified scope.
The completed weighted graph component is documented in [WEIGHTED_PROOF.md](WEIGHTED_PROOF.md).

The dependency source audit compared 585 shared modules against the pinned
original repository. Of these, 582 are byte-identical to the available cache;
the three descent/numerics differences were rebuilt into a private overlay.
The mathematical support and the closed 3.72 checkpoint were rechecked against
that overlay. The final theorem subsequently passed the same pinned-source
recheck. See `runs/dependency_provenance.json`, `runs/pinned_first_round.json`,
and `runs/pinned_final.json`.
An expression-dependency audit also checked all 6,856 external RamseyLean
declarations for uses of the changed interface. The two unchanged descent
exports used by `Numerics.Final` have exactly equal Lean types and values
in the cached and rebuilt environments; see
`runs/dependency_reference_boundary.resources.log` and
`runs/stable_dependency_exports.json`.

## Measured resources

Lean jobs were launched under resource supervision. Each job's monitor
samples process-group RSS every 0.5 seconds and terminates only its own group
on a configured limit. The workspace aggregate monitor samples every five
seconds; shared resident pages are counted per process, not as proportional
set size. Sampled peaks are not exact high-water marks or future guarantees.

The complete observed verification interval was **2026-09-11 02:50 UTC to
2026-09-13 11:33:40 UTC** (204,220.28 seconds). It includes overlapping
verification work, waiting, and development experiments, but excludes fresh
external dependency compilation. The original origin/deadline was preserved
through retries; see `verification_budget.json`.

At Sep 11 23:43 UTC, tool-session supervisors disappeared while the two
numerical workers continued. Detached group supervision was restored by
23:49 UTC without restarting either numerical worker. The old parent exit
statuses and missing RAM samples cannot be recovered. Consequently their
reports say `PASS_DURABLE_VERIFICATION`, not a fabricated exit code: the
complete compiler-success plan, source digests, and object metadata were
validated (10,101 main-worker modules and 4,645 R07 modules). The newly
supervised final assembly and pinned recheck both returned actual
`PASS_PROCESS`. See `runs/tool_session_recovery.json`.

The main numerical group's historically observed peak was **4.44 GiB**;
its recovery-window peak was **2.82 GiB**, and R07's was **2.85 GiB**. Final
assembly peaked at **5.36 GiB**, and the pinned recheck at **5.40 GiB**. The
two retained workspace aggregate windows peaked at **9.54 GiB** and
**8.29 GiB**. These scoped measurements explicitly retain the supervision gap.

- Exact shared-log replay: about **94 seconds, 888 MiB** sampled peak, one
  arithmetic worker. This is Python/C++ verification, not a Lean benchmark.
- All 351,607 log enclosures: **77.4 minutes, 2.56 GiB**, kernel-checked.
- All 20,000 initial tangent bounds: **13.1 minutes, 2.13 GiB**, kernel-checked.
- All 126,192 profile-shape/region checks: **6.2 minutes, 1.04 GiB**.
- Actual 512-record and 4,096-run batches together: **25.6 seconds,
  3.74 GiB** sampled peak, no axioms in the Boolean check theorems.
- Complete first-round record/run checks: **22.3 minutes, 3.86 GiB**.
- Complete first-round outer-path/cover checks: **5.7 minutes, 1.52 GiB**.
- All second- through fifth-round guards and their actual
  `CertifiedRound.R01.valid` through `R04.valid` theorems have also passed.
  The fifth round used 64.3 compiler minutes for its 292 data/check modules.
  All three large rounds have now also passed every concrete check and their
  actual round theorem.
- Complete largest-round data preparation: **2 hours 57 minutes, 1.67 GiB**.
  This compiles its packed tables, not all the checks on those tables.
- All 501,476 largest-round records and 1,097 blocks have passed their
  concrete kernel checks. The 980 record batches used **125.4 compiler
  minutes**. All **14,234,339** R07 runs subsequently passed in **21.80
  compiler hours**, followed by all 98 outer checks and the round assembly.
  R05's **11,888,962** runs passed in **18.13 compiler hours**, and R06's
  **13,807,699** runs in **22.15 compiler hours**. These overlap in wall time.
- An isolated 4,096-run sample using the largest round's complete node table:
  **25.1 seconds, 5.20 GiB** with a flat node selector, versus
  **20.0 seconds, 3.93 GiB** with named groups of 16 nodes. These samples use
  only the first run-data file and are not full-round measurements. Only
  future large-round headers were updated; certificate values were unchanged.
- With the full-size run selector, four 1,024-check kernel declarations
  joined by the proved `checkedRange_join` lemma took **22.3 seconds,
  2.24 GiB**, versus **22.8 seconds, 4.49 GiB** for one 4,096-check declaration.
  This preserves the exact predicate and checked range. It is now used in
  all three completed large rounds, without adding source files per
  batch. Each numerical part is checked by `decide +kernel`; the range
  assembly uses standard `propext` and `Quot.sound`, no new axioms.
  The full-size selector samples use real selected runs and dummy unselected
  leaves, so they do not measure the entire large-round data footprint.
- **Actual full-dataset samples:** 13,027 run checks from the beginning,
  middle, and end of R07 passed in **71.9 seconds, 2.64 GiB** sampled peak.
  This uses the complete real R07 tables and the new four-part checker;
  see `runs/r07_actual_run_samples.resources.json`. It is representative
  sampling; the subsequent complete round verification is reported above.
- Final generic-support recheck against the pinned original sources:
  **135.30 compiler seconds**; all closed assemblies rechecked in **39.02
  seconds**. The final module's initial assembly took **3.87 seconds**.
  Cached unchanged dependencies were reused.
- Unconditional initial-profile assembly: **6.3 seconds, 3.56 GiB** including imports.
- Complete finite/asymptotic terminal-transfer source compiles in about
  **5.2 seconds** using cached dependencies; see its monitored resource report.
- Lean terminal comparison: **3.5 seconds, 2.72 GiB** sampled peak, including
  imports. Standard `propext`, `Classical.choice`, `Quot.sound` only.
- A 256-check, 18-digit integer benchmark: **4.6 seconds, 1,012 MiB**.
- A 1,024-check, 18-digit `decide +kernel` benchmark: **13.7 seconds,
  1,795 MiB**, no axioms. This checks a sample of Boolean blue-cost guards;
  it does NOT establish real-log soundness or check the whole certificate.
- The earlier unoptimized 1,024-check test hit the 2 GiB cap and was
  stopped. Its source/report is retained as an unsuccessful experiment.
- The expanded supporting library, including the complete weighted graph
  theorem and finite continuation, built in about **41 seconds, 3.46 GiB**
  sampled peak. This reuses already-built upstream/mathlib dependencies;
  it is not a from-scratch dependency build or a complete Ramsey certificate build.

The numerical chain still contains 1,695,911 records. The solution is not to
pretend this data is small: prove each log enclosure once, share interval
path summaries, and check bounded opaque chunks. The complete development
verification has now been measured as stated above; the small tests alone
did not establish that result. A separate fresh isolated full rebuild has
not been measured.
The complete jobs use 6 GiB per verification process group, with two
round-verification groups run concurrently. The largest round's data
preparation and the first round's outer checks were also supervised.
These are resource caps, not measured whole-machine peak RAM figures.
Each of the two long-running round-verification groups was pinned to two
logical CPUs (four logical CPUs across those two groups).

## Reproduce the preferred exact replay

Requires Python 3.12, g++, and a little-endian POSIX environment. The exact
checker needs only Python's standard library; NumPy/Numba are for discovery
and extraction, not replay. Do not run Python with `-O`.

```sh
cd ramsey-below-3684
RAMSEY_INTERVAL_DIGITS=18 python3 resource_guard.py \
  --rss-mib 4096 --seconds 600 --output runs/replay.resources.json -- \
  python3 -u verify_stream.py certificates/quantized/bellman.json \
  --root . --workers 1 --report runs/replay.json
```

For the unquantized full differential replay, omit the environment setting,
select `certificates/target_runs/bellman.json`, and add `--compare-paths`.
The old `--root` option is retained for CLI compatibility; no predecessor is
loaded. The actual initial majorant is bundled inside each certificate.

The quantized generator and verifier are separate. The latter recomputes
every catalog enclosure, checks every record and dependency, reconstructs
every profile, and checks both affine support orientations and the terminal
line. Neither the generator nor a prior report is accepted as a premise.

## Build the Lean supporting library

Lean 4.32.1, mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The local build reuses the matching
existing mathlib environment **read-only** and writes only this directory:

```sh
python3 resource_guard.py --rss-mib 4096 --seconds 120 \
  --output runs/support-replay.resources.json -- \
  python3 -u build_support.py \
  --dependency-project /path/to/RamseyLean-bootstrap/checkout
```

For a separate machine, `lean/lakefile.toml` pins mathlib and the original
RamseyLean-bootstrap repository. Install its dependencies and build the
`Compact3684` supporting library there. This fresh dependency-install path
has not been benchmarked here.
`runs/support_build.json` deliberately reports `headline_proved: false`.
The large benchmark files are not imported by this library. The default
Lake target is now `RamseyBelow3684`, not just the supporting library.
For controlled memory usage, prefer the serial supervised command below
over an unrestricted parallel Lake build of the full certificate.

## Isolated full-proof rebuild

`reproduce_lean.py` follows the final theorem's local imports and builds them
serially into a **fresh** output directory. It does not put existing local
proof objects on the search path. Its planned closure contains 16,024 local
modules, mostly small bounded checks; packed integer data accounts for most
of the roughly 2.60 GB of source. No performance experiments are imported.
The single-module and four-module isolated smoke tests passed. The complete
isolated rebuild has not been run; the supervised development verification
and final pinned-source recheck described above are complete.

With matching, already-built external dependencies, the full command is:

```sh
python3 resource_guard.py --rss-mib 8192 --seconds 604800 \
  --output runs/isolated-full.resources.json -- \
  python3 -u reproduce_lean.py \
  --dependency-project /path/to/matching/upstream/project \
  --output-root runs/isolated-full \
  --report runs/isolated-full.json
```

For the audited local cache, also pass
`--dependency-overlay dependencies/upstream_overlay`. Existing output
directories are refused, not overwritten. External dependency compilation
is excluded from this command's measurement and must be reported separately.
The completed development verification retained its stricter fixed
deadline, `2026-09-18T02:50:00Z`; a retry does not receive a new one-week budget.

## Provenance and scope

Discovery/extraction utilities were adapted from
`ramsey_3_683139147865_style_source.zip` and the local
`ramsey_candidate_continuation_release`. The input U-majorant is extracted
from the latter's baseline, but **none of its bootstrap rounds is reused**;
all initial finite majorant checks are replayed. Author code is retained
where practical. New work includes resource supervision, mixed-resolution
search orchestration, direct-U extraction/replay, run compression and its
independent checker, differential tests, slack-paid control quantization,
the shared-log catalog, and the supporting Lean proofs.

The original reference repository is `wamlat/RamseyLean-bootstrap`, reviewed
at `e53b8cf11d064daae70372b3a93b2556a5fee926`. The final unconditional theorem
uses the same standard Lean axioms, with actual certificate computation
checked by the kernel and no external numerical oracle. It does not claim
the manuscript's stronger 3.683139147865 constant: the completed target here
is **3.68395 < 3.684**.

# How we verified the theorem

We started with the original GNNW bound, applied eight certified bootstrap
rounds, and transferred the resulting affine bound to the diagonal Ramsey
number. The final theorem is
[`Compact3684.ramsey_le_368395`](../lean/RamseyBelow3684.lean).

To keep the computation manageable, we shared **351,607 logarithm enclosures**,
compressed long paths into **41,793,102 runs** (checked as **41,794,061**
split batches), and checked bounded chunks in Lean. Large run batches use four 1,024-check declarations joined by a proved
range lemma. The graph and checker-soundness proofs are reused across all rounds.

The mathematical route is explained in [PROOF_ROUTE.md](../PROOF_ROUTE.md),
including the all-spines argument giving
`2 exp(0.544) sqrt(exp(0.7622) - 1) < 3.68395`.

## Completed run

| Measurement | Result |
| --- | --- |
| Verification interval | 11–13 September 2026 |
| Elapsed time | **56 h 43 min 40 s** |
| Final theorem assembly | **3.87 s** |
| Final pinned-source recheck | **174.32 s** of support and closed-assembly builds |
| Final pinned recheck's sampled group peak | **5.40 GiB** |
| Observed aggregate monitor-window peaks | **9.54 GiB**, **8.29 GiB** |

The run reused matching external dependency caches. Two long-running
verification groups ran concurrently, each with a 6 GiB sampled RSS limit
and two logical CPUs. Those are the settings used for these measurements,
not requirements for a new verification.

There was an approximately six-minute supervision gap after tool-session
supervisors disappeared. The numerical workers continued; their full output
plans and source hashes were subsequently validated. The two affected reports
record `PASS_DURABLE_VERIFICATION`, with the original exit codes unavailable.
The final assembly and pinned-source recheck both returned `PASS_PROCESS`.
The RAM figures above describe the recorded windows.

## Proof and provenance

Both final Ramsey theorems have exactly the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Numerical checks use
`decide +kernel`; the external discovery/replay programs are not proof premises.

The final recheck used the original repository at
`e53b8cf11d064daae70372b3a93b2556a5fee926` and mathlib at
`520045ab14e26149ee970e2e617ca04b09bde5d6`. A source audit and expression comparison
established the boundary between the available cache and the pinned sources.

The main records are:

- [STATUS.json](../STATUS.json): completed theorem, source hashes, and measurements.
- [pinned_final.json](../runs/pinned_final.json): final theorem and pinned commits.
- [pinned_final_theorem.log](../runs/pinned_final_theorem.log): final axiom
  inventory. Note: this historical log ends with a JSON footer from the
  support-build reporter (`"status": "PASS_SUPPORT_LIBRARY_NOT_RAMSEY_THEOREM"`,
  `"headline_proved": false`); those fields describe that reporter's own scope
  and predate the final assembly. The printed theorem and axiom list above the
  footer, and the authoritative status in `pinned_final.json`, are the record.
- [dependency_provenance.json](../runs/dependency_provenance.json): dependency audit.
- [tool_session_recovery.json](../runs/tool_session_recovery.json): supervision recovery.

These are records of the original verification. New executions write their
own reports and leave the historical evidence unchanged.

## Original numerical artifacts

The v1.0 release's `certificates.tar` contains the search and replay data.
It is useful for studying or regenerating the certificate, but is optional
when building the supplied Lean sources.

The v1.0 `dependencies-cache.tar` is a historical snapshot of the local audit
workspace. Its `pinned_check_lean` directory contains absolute symlinks, and
mathlib is not bundled. It is not an installation dependency for the
source-first release. New builds obtain dependencies from the pinned repositories.

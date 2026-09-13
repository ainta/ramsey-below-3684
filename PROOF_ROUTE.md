# A concrete route below 3.684

The below-3.684 target is now an **unconditional Lean theorem**:
`Compact3684.ramsey_le_368395` proves the eventual base **3.68395**. All
concrete kernel checks, round assemblies, terminal transfer, and the
pinned-original-source final recheck passed. The observed complete
verification took 56 hours 43 minutes 40 seconds with cached external
dependencies. The new finite certificates start at GNNW; they do not use
the unavailable predecessor of the 3.683139147865 manuscript certificate.

## The smaller mathematical target

It suffices to establish the uniform affine bound

    R(k,l) ≤ exp(0.544 k + 0.7622 l + o(k)),  1 ≤ l ≤ k.

The o(k) here must be uniform in l. A pointwise collection of bounds is not
enough. The final exact certificate verifier checks that this line dominates
its reconstructed entire polygon, including the small-ratio tail test. That
is finite arithmetic, not by itself a Lean proof that the polygon bounds R.
The completed kernel execution and proved graph soundness now establish
that implication in Lean and connect it to the final theorem.

Set A=exp(0.544), B=exp(0.7622). The terminal constant is

    2 A sqrt(B-1) = 3.68388932771268... < 3.684.

`lean/TerminalNumeric.lean` proves the strict real inequality in Lean using
two 12-term exponential bounds and rational arithmetic. It does not rely on
the decimal approximation above. There is no need to certify the original
long decimal, differentiate its optimizer, or formalize a large entropy
calculation just for this terminal comparison.

## A simpler terminal transfer: sum over all spines

This argument is now compiled in `AllSpines`, `TerminalCore`, and
`TerminalTransfer`. It replaces the single-spine entropy/binomial asymptotics.
The implementation uses deliberately loose polynomial constants, recorded
below; they do not affect the final exponential base.

Suppose, for each eta>0, uniformly for 1≤r≤k,

    R(r,k) ≤ C_eta exp(eta k) A^k B^r,

where A>1 and B>2. Fix s>1 and put z=s²-1 and D=(B+s²-1)/s. Assume D≥1.
Consider a coloring of N vertices with no monochromatic k-clique, k≥2 and
N≥32k³. Relabel colors so that red has at least half the edges. Set
p=1/2-1/(2k). Choose W maximizing

    e_red(W) - p |W|²/2.

Deleting one vertex gives the minimum-degree estimate needed in W.
Comparing excesses and using |W|²≤N|W| yields the weaker but sufficient
linear estimate |W|≥N/(4k), avoiding an extra square-root argument.

Let S be a maximum red clique in W, M=|S|<k, and X=W\S. Then
|X|≥N/(8k)≥4k². Double-counting edges between S and X gives

    average_{v in X} deg_S(v) ≥ M/2 - 1.

For every T⊆S, its page P_T of common red neighbors in X has no red
(M-|T|+1)-clique, by maximal cardinality of S, and no blue k-clique.
Consequently

    |P_T| < R(M-|T|+1,k)
          ≤ C_eta exp(eta k) A^k B^(M-|T|+1).

Now sum over **all** subsets T, weighting each by z^|T|. The finite binomial
identity and Jensen's inequality for u↦s^(2u) give

    |X| s^(M-2)
      ≤ sum_{v in X} (1+z)^deg_S(v)
       = sum_{T⊆S} z^|T| |P_T|
      ≤ C_eta exp(eta k) A^k B (B+z)^M.

It follows that

    N ≤ 8k B s² C_eta exp(eta k) (A D)^k.

The finite prefactor and exp(eta k) are absorbed by any fixed exponential
slack. Choose s=sqrt(B-1), which makes D=2sqrt(B-1)>1. Thus every base
strictly above 2A sqrt(B-1) is eventually a diagonal Ramsey bound.
This argument handles small and large M simultaneously. It needs neither a
Stirling estimate nor a separate limiting argument for bounded M.

## The numerical chain constructed here

Five uniform-grid Bellman rounds at N=2000, M=160, followed by three at
N=6000, M=500. M here denotes the search control-grid size, not the clique
size in the preceding argument. The initial U-majorant is independently
rechecked; none of the old baseline's bootstrap rounds is assumed.

The extracted chain has 1,695,911 records, 1,691,788 weighted records,
and 813,922,863 expanded path references. Constant-column runs encode the
paths with 41,793,102 runs. This is still substantial data, not a tiny proof.

The unquantized exact replay gives an upper terminal base 3.683687152314.
It also verifies the deliberately simpler global line 0.544+0.7622t.
Full run-based and expanded C++ path replays give byte-identical results;
all support, density, budget, initial-majorant, and profile checks are then
replayed with exact rational / directed-integer arithmetic in Python.

## Spend the slack to share expensive checks

The expensive repeated calculation need not be attached to every record.
Let eps=18/10^6 and h=16/10^6. Make the following candidate transformation:

    E(t) -> E(t)+eps*t        v(t) -> v(t)+eps*t
    b -> b+eps               cost -> cost+eps.

Round mu and q=1-p downward on a rational relative grid with consecutive
ratios at most 1+h. The regenerated upper density is p'=1-q'; take the
strict lower density pi'=p'-10^-12. Since the original p-pi was larger
than 10^-12, pi' is no smaller than the original pi.

Both support orientations remain valid after b increases by eps. Decreasing
mu increases (1-mu)(a+theta log(1-mu)) in the positive regime. The budget
gain pays for log(mu)-log(mu')≤log(1+h)≤h<eps. The blue-cost gain similarly
pays for log(q)-log(q'). These scalar facts are proved in
`lean/ControlQuantization.lean`, with their hypotheses explicit.

There is an important finite-grid correction: every path and outer size
margin decreases by exactly eps/N. It does **not** decrease by path length
times eps/N. The original minimum path and outer margins exceed 10^-8,
whereas eps/2000=9*10^-9 and eps/6000=3*10^-9. The cancellation behind this
claim is proved in `linearLift_compose` and `linearLift_accepts`.

The independent verifier does not trust these transformation arguments: it
rechecks the transformed certificate from its transformed U-majorant.
That complete replay passed, with an upper terminal base 3.683749312877;
the simple global line 0.544+0.7622t still dominates the entire profile.
The transformed controls use 351,607 distinct logarithm arguments, versus
4*1,691,788 plus the unconditional blue checks if recomputed per record.
Each catalog enclosure is independently recomputed before it is shared.

At 18 decimal places, 20 atanh-series terms suffice after dyadic reduction:
for u in [0,1/3], the tail is at most

    9 / (4 (2m+1) 3^(2m+1)) < 10^-18,  m=20.

This reduces both operand size and series length. It does not weaken exact
verification: a wider enclosure must still pass every strict inequality.

## Completed Lean proof and assurance

Completed, compiled supporting results:

- The uniform weighted graph theorem, including selection of scalar slack,
  logarithmic schedules, all finite recursive graph cases, and initialization.
  Its statement has no assumed schedule, weighted-rule oracle, or certificate
  validity premise. See `WEIGHTED_PROOF.md` for its exact scope.
- The finite candidate continuation and one-shot row-floor preparation from
  the development archive, repaired and compiled against the pinned API.
- The strict real terminal inequality for a=0.544, d=0.7622.
- Range-summary soundness, composition, and the finite-grid affine-lift
  identities, using only Std for the path module.
- Scalar support, weighted-density, weighted-budget, and blue-cost facts
  used by control quantization.
- The real soundness of the shared-log checker, all 351,607 concrete log
  enclosures, all 20,000 initial tangents, and all 126,192 profile/region checks.
- Full grid semantics and record/path soundness (`ChainSound.guards_sound`),
  including row/column identities, prefix recurrences, range maxima, and
  well-founded rank induction. No expanded path-reference proof is generated.
- Full outer-path and finite-cover soundness (`Outer.guards_sound`), including
  monotone lifting from a red-size grid to all integer targets.
- The finite and asymptotic all-spines graph transfer, and the strictly
  below-3.684 target base 3.68395 conditional on the final reflected profile.

All of the following completion requirements have now passed:

1. Every concrete kernel check for the 1,695,911 records, 41,794,061 split
   compressed runs, outer paths, and profile covers passed. All eight round
   theorems were compiled, not merely generated.
2. `RamseyBelow3684.lean` compiled and passed the pinned original-source
   recheck. Its final axioms are exactly `propext`, `Classical.choice`, and
   `Quot.sound`; no external numerical verifier is a premise. See
   `runs/pinned_final.json` and `runs/pinned_final_theorem.log`.
3. The complete observed verification took 204,220.28 seconds, below the
   fixed 604,800-second budget. The pinned recheck peaked at 5.40 GiB
   sampled group RSS. Historical aggregate windows reached 9.54 and
   8.29 GiB. The roughly six-minute supervision gap and reused dependency
   caches are explicitly recorded; a separate clean rebuild and continuous
   whole-run memory measurement are not claimed. See README and STATUS.

For resource control, prove each catalog enclosure once, expose only its
checked interval, and use bounded opaque chunks for the remaining exact
guards and path summaries. Do not put the whole certificate into one
`decide`. `decide +kernel` is kernel checking, not `native_decide`.
The completed verification supplies the actual time and scoped RAM evidence;
the earlier experiments alone did not establish it. The certificate remains
substantial data (roughly 2.60 GB of local Lean source), but no monolithic
certificate-sized reduction or proof term is required. This proves the
below-3.684 target, not the stronger manuscript base 3.683139147865.

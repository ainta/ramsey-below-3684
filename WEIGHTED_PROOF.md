# Completed uniform weighted graph theorem

`lean/Ramsey3683Bootstrap/WeightedUniform.lean` proves
`Ramsey3683Bootstrap.isGood_of_density_weighted_card_product`.

For positive x, y, theta, mu and p in (0,1), assume (x,y) is in the
upstream asymptotic Ramsey-region interior and

    x < p^(1/(1-mu)) * (1-mu)^theta.

There is one L, independent of the finite graph and of k and t, such that
for every positive k,l,t with l >= L, an upstream Candidate (X,Y) with
density at least p and

    x^(-k) y^(-l) (mu^theta)^(-t) <= |X|^theta |Y|

is (k,l,t)-good in the upstream graph/clique predicates. In particular,
this is not a theorem conditional on the existence of weighted schedules.

## Proof components

- `WeightedParameters`: weighted limit and capped power profile, reduced to
  upstream analytic lemmas.
- `WeightedLocal`: red/blue scalar branch alternative, including empty
  children and signed child density excess.
- `WeightedMoment`: excess-monotone regularization and branch transport.
- `WeightedEngine`: finite strong induction on k+t, using actual graph cores,
  blue books, density averaging, and clique extensions.
- `WeightedSchedules`: weighted blue gain and left-cardinality growth.
- `WeightedSlack`: existence of strict scalar slack from the theorem's
  original hypotheses, followed by selection of a smaller growth parameter.
- `WeightedConcrete`: explicit schedules realizing every engine field.
- `WeightedUniform`: one uniform cutoff and the initial potential estimate.

The new schedule simplification separates the natural moment exponent r
from a larger fixed integer R with r <= R and r <= R*theta. Raising the
upstream logarithmic-spine gain to theta then pays for the weighted blue
step. The existing polynomial/subexponential loss estimates still apply.
No numerical enumeration of possible graphs or clique sizes is involved.

## Verification and provenance

The supplied development archive's first four modules were copied without
changing the archive, repaired against Lean 4.32.1, and compiled. Unchanged
copies are retained in `vendor_development`. The four schedule/uniform
modules were added in this workspace. FiniteContinuation and Preparation
were also copied, repaired, and compiled.

The final theorem's printed axioms are exactly:

    propext, Classical.choice, Quot.sound

No sorry, extra axiom, native_decide, external verifier acceptance, or
assumed certificate validity occurs in that theorem.

The dependency environment reuses read-only build products from
`/home/ainta/manuscripts/ramsey/claude_revision/lean`. Its BookInduction source
matches the original bootstrap repository at
`e53b8cf11d064daae70372b3a93b2556a5fee926` byte for byte:

    59af07cd79b2f11c657725c8f24bdfbd9e1d06eefbd1987b51b76a5a3574c7c2

Mathlib is pinned at `520045ab14e26149ee970e2e617ca04b09bde5d6`.
`runs/support_weighted_complete.resources.json` measures the expanded build
with existing dependencies. Peak RSS is sampled, not an exact high-water
measurement or a future guarantee.

## Not a proof of the numerical headline

This establishes the manuscript's weighted graph ingredient. It does not
prove that the 1,695,911-record numerical chain is a Ramsey bound. Uniform
continuation/profile closure, checker soundness with complete kernel
execution, and terminal graph transfer remain unconnected. The full
below-3.684 Lean theorem and its end-to-end runtime/RAM remain unestablished.

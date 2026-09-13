import RamseyLean.Numerics

/-! Reuse the original repository's proved GNNW bound without a new axiom.
The pinned upstream uses legacy modules, so its transitive imports remain
part of this module's measured resource footprint. -/
theorem Compact3684.initial_uniform :
    RamseyLean.UniformRamseyExpBound (RamseyLean.F RamseyLean.finalB) :=
  RamseyLean.uniformRamseyExpBound_final

#print axioms Compact3684.initial_uniform

import RamseyLean.Numerics
import Lean.Util.FoldConsts

/-! Read-only environment inspection, not a theorem or a proof premise.
Check which cached declarations actually reference any Descent declaration.
This checks the boundary of the three-file pinned-source overlay. -/
open Lean in
run_cmd do
  let env ← getEnv
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => Name.anonymous
  let mut count : Nat := 0
  let mut references : Nat := 0
  for (name, info) in env.constants do
    let moduleName := owner name
    if !(`RamseyLean).isPrefixOf moduleName || moduleName == `RamseyLean.Descent then
      continue
    count := count+1
    for used in info.getUsedConstantsAsSet do
      if owner used == `RamseyLean.Descent then
        references := references+1
        logInfo m!"DIRECT_DESCENT_REFERENCE {moduleName} {name} {used}"
        -- These two exports precede the source change and are byte-identical.
        -- All consumers of the modified interface must be recompiled.
        unless used == `RamseyLean.denseCaseExponent ||
            used == `RamseyLean.denseCaseExponent._proof_1 ||
            moduleName == `RamseyLean.Numerics.Preliminary || moduleName == `RamseyLean.Numerics do
          throwError m!"Additional changed-interface consumer needs recompilation: {moduleName} {used}"
  logInfo m!"PASS_REFERENCE_AUDIT declarations={count} direct_references={references}"

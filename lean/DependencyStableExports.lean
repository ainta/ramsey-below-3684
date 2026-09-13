import RamseyLean.Numerics

/-! Read-only exact expression inventory for the unchanged exports used by
cached modules outside the rebuilt dependency boundary. -/
open Lean in
run_cmd do
  let env ← getEnv
  for name in #[`RamseyLean.denseCaseExponent, `RamseyLean.denseCaseExponent._proof_1] do
    let some info := env.find? name | throwError m!"Missing export {name}"
    let row := Json.mkObj [
      ("name",toJson name.toString),
      ("type",toJson (reprStr info.type)),
      ("value",toJson (reprStr (info.value? (allowOpaque := true))))]
    logInfo m!"STABLE_EXPORT {row.compress}"

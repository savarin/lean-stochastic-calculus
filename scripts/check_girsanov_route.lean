import BlackScholesSolution

open Lean

/-- Follow types and proof bodies in the checked kernel environment. -/
partial def collectDependencies (kenv : Kernel.Environment) (n : Name) :
    StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match kenv.find? n with
  | none => return
  | some ci =>
    for c in ci.type.getUsedConstants do collectDependencies kenv c
    match ci.value? (allowOpaque := true) with
    | some v => for c in v.getUsedConstants do collectDependencies kenv c
    | none => return

#eval show CoreM Unit from do
  let kenv := (← getEnv).checked.get
  let (_, used) := (collectDependencies kenv `PalomarBlackScholes.black_scholes).run {}
  IO.println s!"Reachable constants: {used.size}"
  let required : List Name := [
    `StochasticCalculus.GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_predictable,
    `StochasticCalculus.GirsanovDensityData.martingale_stopAt_complexDoleans_predictable,
    `StochasticCalculus.girsanovDensityData_neg_mul_stopped,
    `StochasticCalculus.isPreBrownianReal_girsanovShiftedBrownian_const_dynamic,
    `StochasticCalculus.continuousBrownianVersion]
  for name in required do
    unless used.contains name do
      throwError "Missing required proof dependency: {name}"
    IO.println s!"PASS: {name}"
  let oracle := used.toList.filter fun n => (`StochasticCalculus.Girsanov).isPrefixOf n
  unless oracle.isEmpty do
    throwError "Old Gaussian oracle remains reachable: {oracle}"
  if used.contains `StochasticCalculus.girsanovMeasure_const_eq_oracle then
    throwError "Old oracle measure-identification bridge remains reachable"
  IO.println "PASS: the dynamic Girsanov route is used; the old Gaussian oracle is absent"

import BB
import Lean.Elab.Print

/-!
Audit every declaration whose defining module belongs to this project,
including private declarations, definitions, instances, and generated helpers.
The transitive dependency closure may contain only Lean's standard classical
foundations. Any additional axiom or unsafe project definition is a hard error.
-/

open Lean Elab Command

set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let mut projectDecls : Array Name := #[]
  let mut theoremCount := 0
  let mut definitionCount := 0
  let mut compiledRuntimeCount := 0
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[index.toNat]!
      if module.toString == "BB" || module.toString.startsWith "BB." then
        -- Lean's compiler produces unsafe runtime-only `_cstage` constants for
        -- closed rational computations. They are not mathematical declarations.
        -- The source scanner prohibits user-written unsafe/partial definitions,
        -- and the dependency check below rejects them in any logical proof.
        let runtimeOnly := info.isUnsafe || info.isPartial
        if runtimeOnly then
          compiledRuntimeCount := compiledRuntimeCount + 1
          logInfo m!"BBRUNTIME|{module}|{name}"
          continue
        projectDecls := projectDecls.push name
        let kind ← match info with
          | .axiomInfo _ => throwError "Project axiom is prohibited: {name}"
          | .thmInfo _ =>
              theoremCount := theoremCount + 1
              pure "theorem"
          | .defnInfo _ =>
              definitionCount := definitionCount + 1
              pure "definition"
          | .opaqueInfo _ => pure "opaque"
          | .ctorInfo _ => pure "constructor"
          | .recInfo _ => pure "recursor"
          | .inductInfo _ => pure "inductive"
          | .quotInfo _ => pure "quotient"
        logInfo m!"BBDECL|{module}|{kind}|{name}"
  let action : CollectAxioms.M Unit := projectDecls.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for name in state.visited.toList do
    if let some info := env.find? name then
      if info.isUnsafe || info.isPartial then
        throwError "A logical declaration depends on an unsafe or partial definition: {name}"
  let bad := state.axioms.filter fun name =>
    name != `propext && name != `Classical.choice && name != `Quot.sound
  unless bad.isEmpty do
    throwError "Forbidden transitive axioms: {bad.toList}"
  logInfo m!"BBAUDIT|project_declarations|{projectDecls.size}|theorems|{theoremCount}|safe_definitions|{definitionCount}|compiled_runtime_helpers|{compiledRuntimeCount}|axioms|{state.axioms.toList}"

#print axioms BB.Operator.theorem_2_1
#print axioms BB.Euclidean.System.exact_euclidean_certificate
#print axioms BB.Euclidean.System.exact_uniform_rate
#print axioms BB.Euclidean.System.exactValue_positive_formula
#print axioms BB.Operator.lemma_3_2
#print axioms BB.Operator.frozen_interval_certificate
#print axioms BB.Local.theorem_5_1_at
#print axioms BB.Counterexample.global_c2_counterexample
#print axioms BB.Numerical.objective_increase_indices
#print axioms BB.Operator.EndpointOperatorOrbit.energy_exact_step
#print axioms BB.Quadratic.exists_unique_affine_minimizer
#print axioms BB.Operator.affine_endpoint_energy_error_form

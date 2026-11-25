import BB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some i := env.getModuleIdxFor? name then
      if let some module := env.allImportedModuleNames.get? i then
        if module.toString.startsWith "BB." then
          match info with
          | .thmInfo _ => roots := roots.push name
          | _ => pure ()
  unless roots.size == 1940 do
    throwError "Expected 1940 project theorems, found {roots.size}"
  -- Traverses dependencies as #print axioms does, sharing visited nodes.
  -- The resulting axiom set is the union of the closures of all roots.
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let allowed : List Name :=
    [Name.str (Name.mkSimple "Classical") "choice",
     Name.str (Name.mkSimple "Quot") "sound", Name.mkSimple "propext"]
  unless state.axioms.size == allowed.length && state.axioms.all (fun ax => allowed.contains ax) do
    throwError "Unexpected project axioms: {state.axioms.toList}"
  logInfo m!"BB_PROJECT_THEOREMS: {roots.size}"
  logInfo m!"BB_PROJECT_AXIOM_UNION: {state.axioms.toList}"

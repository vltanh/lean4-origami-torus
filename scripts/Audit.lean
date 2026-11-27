module

public import Lean

/-! Audit the compiled project and Palomar Solutions for nonstandard axioms. -/

open Lean

private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private def audit (modules : List Name) : CoreM UInt32 := do
  let env ← getEnv
  let mut checked := 0
  let mut failed := false
  for name in env.header.moduleNames, data in env.header.moduleData do
    if modules.contains name then
      for decl in data.constNames do
        checked := checked + 1
        let forbidden := (← collectAxioms decl).filter (fun ax => !allowedAxioms.contains ax)
        unless forbidden.isEmpty do
          IO.eprintln s!"{decl} depends on disallowed axioms: {forbidden.toList}"
          failed := true
  IO.println s!"Audited {checked} declarations in {modules.length} modules."
  return if failed || checked == 0 then 1 else 0

public unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    throw <| IO.userError "Pass the module names to audit."
  Lean.initSearchPath (← Lean.findSysroot)
  let modules := args.map String.toName
  let imports := modules.toArray.map fun name => { module := name, importAll := true : Import }
  -- Load Lean's precomputed axiom dependencies for imported declarations.
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports {} (loadExts := true)
  let (status, _) ← (audit modules).toIO { fileName := "scripts/Audit.lean", fileMap := default } { env }
  return status

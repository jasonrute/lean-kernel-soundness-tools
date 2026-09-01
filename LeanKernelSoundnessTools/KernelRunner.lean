/-
# Kernel Runner

This file provides a way to run a kernel on a lean export file. It uses
`Lean4Lean.Replay` to replay the export file's declarations into a kernel
`Environment`, and then uses the kernel's `check` method to verify proofs.

The runner also handles the lean-inductive-model preprocessing step: before
replaying, it calls lean-inductive-model to expand inductive type definitions
into the fragment-compatible form.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/-! ## Running a kernel on an export file -/

/--
Run the lean-inductive-model preprocessing on an export file.

This step expands inductive type definitions so that the export file
contains only the fragment that lean4lean can verify: axioms, definitions,
theorems, opaque constants, quotient types, and mutual definitions.

Returns the preprocessed export data.
-/
def preprocess (exportFile : String) : IO ParsedExport :=
  -- TODO: call lean-inductive-model to preprocess
  -- For now, just parse the export file directly
  parseExport exportFile

/--
Parse an export file into `ParsedExport`.
-/
def parseExport (exportFile : String) : IO ParsedExport :=
  -- TODO: use TestPrinter.NdjsonParser or write a new parser
  -- For now, stub
  return { declarations := [] }

/--
Run a kernel on an export file.

This is the main entry point for the end-to-end pipeline:
1. Preprocess the export file (lean-inductive-model)
2. Replay declarations into a kernel Environment
3. Check each declaration using the kernel

Returns the final environment and a list of check results.
-/
def runKernel (k : Kernel) (exportFile : String) : IO (Option (Environment × List (Name × KernelResult))) :=
  do
  let parsed ← preprocess exportFile
  let env ← replayExport parsed
  match env with
  | none => return none
  | some env =>
    let mut results := []
    for decl in parsed.declarations do
      match decl with
      | .axiomInfo v =>
        let r := k.check env v.name v.type
        results := (v.name, r) :: results
      | .defnInfo v =>
        let r := k.check env v.name v.type
        results := (v.name, r) :: results
      | .thmInfo v =>
        let r := k.check env v.name v.type
        results := (v.name, r) :: results
      | .opaqueInfo v =>
        let r := k.check env v.name v.type
        results := (v.name, r) :: results
      | _ => pure ()
    return some (env, results.reverse)

/--
Replay an export file's declarations into a kernel Environment.

Uses `Lean4Lean.Replay.replayFromFresh` or the lower-level `Replay.replay`.
-/
def replayExport (p : ParsedExport) : IO (Option Environment) :=
  -- TODO: use Lean4Lean.Replay.replayFromFresh
  return none

end LeanKernelSoundnessTools

/-
# Main entry point for the kernel checker CLI

Usage:
  lean-kernel-check <export-file> [<kernel>]

Kernels:
  error     ErrorKernel (always rejects)
  accept    AcceptKernel (always accepts)
  lean4lean  Lean4LeanKernel (uses the actual type checker)

Default: lean4lean
-/

import LeanKernelSoundnessTools.Kernel
import LeanKernelSoundnessTools.KernelRunner

open LeanKernelSoundnessTools

open Lean
open Kernel

def printUsage : IO Unit := IO.eprintln "Usage: lean-kernel-check <export-file> [<kernel>]"

def printKernels : IO Unit :=
  IO.eprintln "Kernels: error, accept, lean4lean (default)"

def printError (msg : String) : IO Unit :=
  IO.eprintln s!"Error: {msg}"

def resolveKernel (kernelName : String) : IO Kernel :=
  if kernelName == "error" then
    pure instKernelInvalid
  else if kernelName == "accept" then
    pure instKernelValid
  else if kernelName == "lean4lean" then
    pure Lean4LeanKernel
  else do
    printError s!"Unknown kernel: {kernelName}"
    printKernels
    throw (IO.userError s!"Unknown kernel: {kernelName}")

unsafe def runWithKernel (kernelName : String) (exportFile : String) : IO Unit := do
  let kernel ← resolveKernel kernelName
  let r ← runKernel kernel exportFile
  match r with
  | none =>
    printError "Failed to run kernel: could not replay export file"
  | some (_env, results) =>
    for (name, result) in results do
      IO.println s!"{name}: {result.toString}"

/-- Parse command-line arguments and run the kernel checker.

Usage: lean-kernel-check <export-file> [<kernel>]
-/
unsafe def main (args : List String) : IO Unit := do
  match args with
  | [] => do
    printUsage
    printKernels
  | [exportFile] =>
    runWithKernel "lean4lean" exportFile
  | [exportFile, kernel] =>
    runWithKernel kernel exportFile
  | _ => do
    printUsage
    printKernels

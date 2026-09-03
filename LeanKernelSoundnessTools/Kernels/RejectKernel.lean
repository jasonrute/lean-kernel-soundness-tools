/-
# RejectKernel

A kernel that always rejects every input (returns `.invalid`).
It is unsound but consistent.
-/

import LeanKernelSoundnessTools.Tools.Kernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## RejectKernel -/

/--
A kernel that always rejects every input.
-/
structure RejectKernel where
  /-- Check if `p` is a valid proof of `T` in `env`. Always returns `.invalid`. -/
  check : Environment → Expr → Expr → KernelResult

end LeanKernelSoundnessTools

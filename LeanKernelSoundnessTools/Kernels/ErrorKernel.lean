/-
# ErrorKernel

A kernel that returns `.error` for every input. It is sound and consistent.
-/

import LeanKernelSoundnessTools.Tools.Kernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## ErrorKernel -/

/--
A kernel that returns an error for every input.
-/
structure ErrorKernel where
  /-- Check if `p` is a valid proof of `T` in `env`. Always returns `.error`. -/
  check : Environment → Expr → Expr → KernelResult

end LeanKernelSoundnessTools

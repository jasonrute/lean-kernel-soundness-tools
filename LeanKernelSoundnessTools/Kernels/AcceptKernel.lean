/-
# AcceptKernel

A kernel that always accepts every input. It is both unsound and inconsistent.
-/

import LeanKernelSoundnessTools.Tools.Kernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## AcceptKernel -/

/--
A kernel that always accepts every input.
-/
structure AcceptKernel where
  /-- Check if `p` is a valid proof of `T` in `env`. Always returns `.valid`. -/
  check : Environment → Expr → Expr → KernelResult

/--
Provide a `Kernel` instance for `AcceptKernel`.
-/
instance : Kernel where
  check := fun _ _ _ => .valid

end LeanKernelSoundnessTools

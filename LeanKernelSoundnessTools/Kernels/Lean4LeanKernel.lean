/-
# Lean4LeanKernel

A kernel that wraps the actual Lean4Lean kernel for proof checking.
This is the real kernel implementation.
-/

import LeanKernelSoundnessTools.Tools.Kernel
import Lean4Lean.Replay
import Lean4Lean.Verify.Environment

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## Lean4LeanKernel -/

/--
A kernel that wraps the actual Lean4Lean kernel.
It replays declarations into an environment and checks proofs using
the Lean4Lean type checker.
-/
structure Lean4LeanKernel where
  /-- Replay declarations and check proofs using Lean4Lean. -/
  check : Environment → Expr → Expr → KernelResult

end LeanKernelSoundnessTools

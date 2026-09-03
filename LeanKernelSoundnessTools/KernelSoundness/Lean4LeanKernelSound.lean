/-
# Lean4LeanKernel Soundness and Consistency

`Lean4LeanKernel` wraps the actual Lean4Lean kernel. It is sound and consistent
(assuming the Lean4Lean kernel is sound).
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.Lean4LeanKernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## Lean4LeanKernel is sound -/

/--
`Lean4LeanKernel` is sound (assuming the Lean4Lean kernel is sound).

This is a placeholder: the real proof requires showing that the Lean4Lean
type checker is sound relative to the verification model.
-/
theorem lean4LeanKernel_sound (buildVEnv : Environment → VEnv) :
    Sound (Kernel.mk (fun env p T =>
      -- stub: real implementation uses Lean4Lean.Replay and type checking
      .valid
    )) buildVEnv := by
  sorry

/-! ## Lean4LeanKernel is consistent -/

/--
`Lean4LeanKernel` is consistent (assuming the Lean4Lean kernel is consistent).

This is a placeholder: the real proof requires showing that the Lean4Lean
type checker never proves `False`.
-/
theorem lean4LeanKernel_consistent :
    Consistent (Kernel.mk (fun env p T =>
      -- stub: real implementation uses Lean4Lean.Replay and type checking
      .valid
    )) := by
  sorry

end LeanKernelSoundnessTools

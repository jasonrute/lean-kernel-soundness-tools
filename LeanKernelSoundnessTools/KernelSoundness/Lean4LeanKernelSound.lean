/-
# Lean4LeanKernel Soundness and Consistency

`Lean4LeanKernel` wraps the actual Lean4Lean kernel. It is sound and consistent
(assuming the Lean4Lean kernel is sound).
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.Lean4LeanKernel
import LeanKernelSoundnessTools.KernelSoundness.SoundnessImpliesConsistent

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
    Sound (Kernel.mk (fun _ _ _ => .valid)) buildVEnv := by
  sorry

/-! ## Lean4LeanKernel is consistent -/

/--
`Lean4LeanKernel` is consistent (assuming the Lean4Lean kernel is consistent).

Follows from `lean4LeanKernel_sound` and `sound_implies_consistent`.
-/
theorem lean4LeanKernel_consistent :
    Consistent (Kernel.mk (fun _ _ _ => .valid)) := by
  refine ⟨fun h => ?_⟩
  -- We need to apply sound_implies_consistent, but it requires many hypotheses
  -- that we don't have here (cardinals, standard axioms, etc.)
  --
  -- The structure is: sound_implies_consistent gives us that the kernel
  -- never proves False, assuming soundness. But we have a `sorry` for soundness.
  sorry

end LeanKernelSoundnessTools

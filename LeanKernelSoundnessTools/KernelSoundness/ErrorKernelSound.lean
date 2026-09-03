/-
# ErrorKernel Soundness and Consistency

`ErrorKernel` returns `.error` for every input. It is sound (nothing is accepted)
and therefore consistent (never proves `False`).
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.ErrorKernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## ErrorKernel is sound -/

/--
`ErrorKernel` is sound: it never accepts any proof, so the soundness condition
is vacuously true.
-/
theorem errorKernel_sound (buildVEnv : Environment → VEnv) :
    Sound (Kernel.mk (fun _ _ _ => .error "rejected")) buildVEnv := by
  refine ⟨?_, ?_⟩
  · intro env ves wf h
    simpa [Kernel.mk] using h
  · intro env ves wf hModel hp_tr hT_tr
    simp [Kernel.mk]

/-! ## ErrorKernel is consistent -/

/--
`ErrorKernel` is consistent: it never accepts any proof, including `False`.
-/
theorem errorKernel_consistent :
    Consistent (Kernel.mk (fun _ _ _ => .error "rejected")) := by
  refine ⟨fun h => ?_⟩
  simp [Kernel.mk] at h

end LeanKernelSoundnessTools

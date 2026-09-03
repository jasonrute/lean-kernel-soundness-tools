/-
# RejectKernel Unsoundness

`RejectKernel` always returns `.invalid`, so it is unsound.
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.RejectKernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## RejectKernel is unsound -/

/--
`RejectKernel` is not sound: it rejects every input, but the verification
model accepts some inputs (e.g., `.sort .zero`).

Counterexample: `p = .sort .zero`, `T = .sort (.succ .zero)`.
The model accepts via `HasType.sort`, but `RejectKernel.check` returns `.invalid`.
-/
theorem rejectKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (Kernel.mk (fun _ _ _ => .invalid)) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hModel : (ves.venv .safe).HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial : VLevel.zero.WF 0)
  have hp_tr : TrExprS (ves.venv .safe) [] [] (.sort .zero) (.sort .zero) :=
    TrExprS.sort rfl
  have hT_tr : TrExprS (ves.venv .safe) [] [] (.sort (.succ .zero)) (.sort (.succ .zero)) :=
    TrExprS.sort rfl
  have hcheck := hbackward wf hModel hp_tr hT_tr
  simp [Kernel.mk] at hcheck

end LeanKernelSoundnessTools

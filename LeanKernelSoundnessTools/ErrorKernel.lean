/-
# Error Kernel

Two dummy kernels for testing: `FailKernel` (returns `.invalid`) and
`ErrorKernel` (returns `.error`).
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
`FailKernel` always returns `.invalid`. It is NOT sound because there exist
proofs that the verification model accepts but that `FailKernel` rejects.

Counterexample: `p = .sort .zero`, `T = .sort (.succ .zero)`.
The model accepts via `HasType.sort`, but `FailKernel.check` returns `.invalid`.
-/
theorem failKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (FailKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hModel : (ves.venv .safe).HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial)
  have hp_tr : TrExprS (ves.venv .safe) [] [] (.sort .zero) (.sort .zero) :=
    TrExprS.sort (by simp)
  have hT_tr : TrExprS (ves.venv .safe) [] [] (.sort (.succ .zero)) (.sort (.succ .zero)) :=
    TrExprS.sort (by simp)
  have hcheck := hbackward hModel hp_tr hT_tr
  simp [FailKernel.mk] at hcheck

/--
`ErrorKernel` always returns `.error "rejected"`. It IS sound because
it never returns `.valid`, so the forward direction is vacuously true,
and it never returns `.invalid`, so the backward direction also holds.
-/
theorem errorKernel_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    Sound (ErrorKernel.mk : Kernel) buildVEnv := by
  refine ⟨?_, ?_⟩
  · intro env ves wf h
    simp [ErrorKernel.mk] at h
  · intro env ves wf hModel hp_tr hT_tr
    simp [ErrorKernel.mk]

end LeanKernelSoundnessTools

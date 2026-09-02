/-
# Error Kernel

`ErrorKernel` always returns `.invalid`. It is not sound because it rejects
proofs that the verification model accepts.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
`ErrorKernel` always returns `.invalid`. It is NOT sound because there exist
proofs that the verification model accepts but that `ErrorKernel` rejects.

Counterexample: `p = .sort .zero`, `T = .sort (.succ .zero)`.
The model accepts via `HasType.sort`, but `ErrorKernel.check` returns `.invalid`.
-/
theorem errorKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (instKernelInvalid : Kernel) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hModel : (ves.venv .safe).HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial)
  have hp_tr : TrExprS (ves.venv .safe) [] [] (.sort .zero) (.sort .zero) :=
    TrExprS.sort (by simp)
  have hT_tr : TrExprS (ves.venv .safe) [] [] (.sort (.succ .zero)) (.sort (.succ .zero)) :=
    TrExprS.sort (by simp)
  have hcheck := hbackward hModel hp_tr hT_tr
  simp [instKernelInvalid] at hcheck

/--
`ErrorKernel` always returns `.invalid`. It IS sound because
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

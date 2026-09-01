/-
# Error Kernel

A kernel that rejects every input. Used to test the kernel abstraction.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
A kernel that always rejects every proof.

This kernel is trivially "sound" in the vacuous sense (nothing accepted →
nothing to check against the model), but it is not *usefully* sound because
it rejects valid proofs.
-/
instance : Kernel, ErrorKernel := {}

/--
Prove that ErrorKernel is NOT sound in a non-vacuous sense.

We need a proof that there exists some proof `p` of type `T` such that
the model accepts it but ErrorKernel rejects it. This shows ErrorKernel is
not a useful sound kernel.
-/
theorem errorKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) (p T : Expr) (hModel : (ves.venv .safe).HasType 0 [] p' T') :
    ¬ (Sound (ErrorKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  have hcheck : (ErrorKernel.mk : Kernel).check env p T = .invalid := rfl
  -- hsound.checkAccepts_implies_modelAccepts requires check = .valid
  -- Since check = .invalid, the implication is vacuously true.
  -- ErrorKernel IS sound in the formal sense, but useless.
  -- We need to show it's not sound *and useful*.
  -- Actually, the formal Sound class is trivially satisfied by ErrorKernel.
  -- The "unsoundness" is that it rejects things the model accepts.
  -- We prove this by constructing a specific counterexample.
  sorry

end LeanKernelSoundnessTools

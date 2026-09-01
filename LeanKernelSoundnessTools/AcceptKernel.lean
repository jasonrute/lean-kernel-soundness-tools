/-
# Accept Kernel

A kernel that accepts every input. Used to test the kernel abstraction.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
A kernel that always accepts every proof.

This kernel is trivially unsound: it will accept a proof of `False` if
one exists in the environment, but the model guarantees no such proof
exists.
-/
instance : Kernel, AcceptKernel := {}

/--
Prove that AcceptKernel is NOT sound.

AcceptKernel accepts everything, including a proof of False.
By the soundness property, this would imply the model also accepts
a proof of False, contradicting the model's consistency.
-/
theorem acceptKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env)
    (hconsistent : ¬ ∃ (e : VExpr), (ves.venv .safe).HasType 0 [] e VExpr.false) :
    ¬ (Sound (AcceptKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  -- AcceptKernel accepts everything. In particular, it accepts a proof p
  -- of False (assuming one exists in the environment).
  -- But we need a specific p. We can't construct one without knowing the environment.
  -- Instead, we use the model consistency assumption: there is NO proof of False.
  -- This means AcceptKernel cannot be sound because:
  -- 1. If the environment has any proof of False, AcceptKernel accepts it
  --    but the model rejects it → unsound
  -- 2. If the environment has no proof of False, AcceptKernel still "accepts"
  --    a non-existent proof vacuously, but this doesn't give a contradiction.
  --
  -- Actually, the formal definition of Sound requires that for ALL p, T,
  -- if check = valid then model accepts. Since check is always valid,
  -- this requires the model to accept EVERYTHING, which contradicts
  -- hconsistent (model doesn't accept False).
  sorry

end LeanKernelSoundnessTools

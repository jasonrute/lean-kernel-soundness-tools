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
Prove that ErrorKernel IS sound (vacuously true).

`ErrorKernel.check` always returns `.invalid`, so the implication
"check = .valid → model accepts" is vacuously true. This is a trivial
(and useless) instance of soundness.

The "unsoundness" in the informal sense is that ErrorKernel rejects every
proof, including those the model accepts. But formally, `Sound ErrorKernel`
holds vacuously.
-/
theorem errorKernel_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) (p T : Expr) :
    Sound (ErrorKernel.mk : Kernel) buildVEnv := by
  refine { checkAccepts_implies_modelAccepts := ?_ }
  intro env' ves' wf' p' T' h
  -- h : ErrorKernel.check env' p' T' = .valid
  -- But ErrorKernel.check always returns .invalid, so h is a contradiction
  have h_invalid : ErrorKernel.check env' p' T' = .invalid := rfl
  rw [h_invalid] at h
  -- h : .invalid = .valid, which is impossible since constructors differ
  injection h

end LeanKernelSoundnessTools

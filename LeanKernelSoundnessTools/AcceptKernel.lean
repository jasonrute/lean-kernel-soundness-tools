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

With the bidirectional Sound class:
- Forward: `check = .valid → model accepts` — fails because model can't translate `.mvar`
- Backward: `model accepts → check ≠ .invalid` — holds trivially
-/
theorem acceptKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (AcceptKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hcheck : (AcceptKernel.mk : Kernel).check env (Lean.Expr.mvar (MVarId.mk ``test)) (Expr.const ``False []) = .valid := rfl
  have hmodel := hforward wf hcheck
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  cases hp_tr

end LeanKernelSoundnessTools

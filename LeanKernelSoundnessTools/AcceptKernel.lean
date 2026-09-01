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

`Sound AcceptKernel` would require that for every `(p, T)`, the translation
`TrExprS` holds. But `TrExprS` fails for bound variables in an empty context
(e.g., `.bvar 0`). We use this as a counterexample.
-/
theorem acceptKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (AcceptKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  -- Pick p = .bvar 0 and T = .sort .zero as a counterexample
  -- AcceptKernel.check always returns .valid, so soundness applies
  have hcheck : (AcceptKernel.mk : Kernel).check env (.bvar 0) (.sort .zero) = .valid := rfl
  have hmodel := hsound.checkAccepts_implies_modelAccepts wf hcheck
  rcases hmodel with ⟨ves', wf', p', T', hp_tr, hT_tr⟩
  -- hp_tr : TrExprS (ves.venv .safe) [] [] (.bvar 0) p'
  -- By the TrExprS.bvar rule, this requires [].find? (.inl 0) = some (e, A)
  -- But [].find? (.inl 0) = none, contradiction
  cases hp_tr
  -- hp_tr is TrExprS.bvar hfind where hfind : [].find? (.inl 0) = some (e, A)
  -- [].find? (.inl 0) reduces to none, giving none = some (e, A) which is false
  simp at hfind
  exact hfind

end LeanKernelSoundnessTools

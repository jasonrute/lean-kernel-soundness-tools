/-
# Accept Kernel

`AcceptKernel` always returns `.valid`. It is not sound because it accepts
proofs that the verification model cannot translate.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
`AcceptKernel` always returns `.valid`. It is NOT sound because there exist
expressions (e.g., `.mvar`) that cannot be translated by `Lean4Lean.TrExprS`,
but `AcceptKernel` accepts everything. Thus soundness would require translations
that don't exist.
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

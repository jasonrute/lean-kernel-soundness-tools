/-
# AcceptKernel Unsoundness and Inconsistency

`AcceptKernel` always accepts every input, so it is not sound and not consistent.
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.AcceptKernel

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean hiding Environment Exception
open Kernel

/-! ## AcceptKernel is unsound -/

/--
`AcceptKernel` is not sound: there exist proofs that the verification model
accepts but that `AcceptKernel` "rejects" (well, it accepts them too, but
the forward direction of soundness requires the model to translate `.bvar`,
which it cannot).

Specifically: `p = .bvar 0`, `T = .sort .zero`. The model cannot translate
`.bvar` because it has no variable context, so `TrExprS` fails.
-/
theorem acceptKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (Kernel.mk (fun _ _ _ => .valid)) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hcheck : (Kernel.mk (fun _ _ _ => .valid)).check env (.bvar 0) (.sort .zero) = .valid := rfl
  have hmodel := hforward wf hcheck
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  cases hp_tr
  all_goals
    simp [VLCtx.find?] at *

/-! ## AcceptKernel is inconsistent -/

/--
`AcceptKernel` is not consistent: it accepts a proof of `False`.
-/
theorem acceptKernel_not_consistent (env : Environment) :
    ¬ (Consistent (Kernel.mk (fun _ _ _ => .valid))) := by
  intro hconsistent
  have hcheck : (Kernel.mk (fun _ _ _ => .valid)).check env
    (Expr.const ``False []) (Expr.const ``False []) = .valid := rfl
  exact hconsistent.not_proves_false hcheck

end LeanKernelSoundnessTools

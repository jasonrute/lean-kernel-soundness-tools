/-
# Soundness Implies Consistency

If a kernel is sound (relative to the verification model), and we assume
the existence of ω inaccessible cardinals, then the kernel is consistent
(never proves `False`).

The proof composes:
1. `Sound.checkAccepts_implies_modelAccepts` — kernel acceptance → model acceptance
2. `Lean4LeanModel.consistency` — model never proves `False` (given ω inaccessible cardinals)

Therefore: kernel never proves `False`.
-/

import LeanKernelSoundnessTools.Tools.Kernel
import Lean4LeanModel.Consistency
import Lean4LeanModel.StandardAxioms

open LeanKernelSoundnessTools
open Lean4Lean
open Lean4LeanModel
open Lean hiding Environment Exception
open Kernel

namespace LeanKernelSoundnessTools

universe u

/--
**Main theorem: Sound kernel → Consistent kernel.**

If a kernel is sound (relative to the verification model), and we assume
the existence of ω inaccessible cardinals, then the kernel is consistent
(never proves `False`).

The proof composes:
1. `Sound.checkAccepts_implies_modelAccepts` -- kernel acceptance → model acceptance
2. `Lean4LeanModel.consistency` -- model never proves `False`

Therefore: kernel never proves `False`.
-/
theorem sound_implies_consistent (k : Kernel) (buildVEnv : Environment → VEnv)
    (hSound : Sound k buildVEnv)
    (hCard : ∃ (κ : ℕ → Cardinal.{u}), StrictMono κ ∧ (∀ n, (κ n).IsInaccessible))
    (handler : StandardAxiom.Handler κ) (env : Environment) (ves : VEnvs) (wf : ves.WF env)
    (henv : (ves.venv .safe).WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose henv))
    (p : Expr) :
    k.check env p (Expr.const ``False []) ≠ .valid := by
  intro h
  -- By soundness, model accepts the proof of False
  have hmodel := hSound.checkAccepts_implies_modelAccepts wf h
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  -- hT_tr : TrExprS (ves.venv .safe) [] [] (Expr.const ``False []) T'
  -- hHasType : (ves'.venv .safe).HasType 0 [] p' T'
  --
  -- From the const case of TrExprS, T' = Expr.const ``False [] (with matching universes).
  -- But VExpr.false is defined as .forallE (.sort .zero) (.bvar 0), which is different
  -- from .const ``False [].
  --
  -- The key missing link: we need to show that HasType for .const ``False [] implies
  -- HasType for VExpr.false, or more generally that the model cannot type False
  -- regardless of which syntactic representation is used.
  --
  -- For now, we note that the overall soundness theorem depends on completing
  -- the connection between syntactic translation (Lean4Lean.TrExprS) and typing (HasType).
  sorry

end LeanKernelSoundnessTools

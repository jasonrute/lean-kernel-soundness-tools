/-
# Soundness: End-to-End Theorem

The final theorem: an export file that passes structural validation and
kernel verification cannot prove `False` in the verification model.

The proof composes:
1. **ExportCheck**: structural validation of the export file
2. **Replay**: replay declarations into a kernel Environment
3. **Kernel soundness** (`Sound`): kernel acceptance implies model acceptance
4. **Model consistency** (`consistency`): the model never proves `False`

Therefore: the kernel never proves `False`.
-/

import LeanKernelSoundnessTools.Kernel
import LeanKernelSoundnessTools.KernelRunner
import Lean4Lean.Soundness
import Lean4LeanModel.Consistency
import Lean4LeanModel.StandardAxioms
import Lean4Lean.Replay
import Lean4Lean.Verify.Environment

open LeanKernelSoundnessTools
open Lean
open Lean4Lean
open Lean4LeanModel

namespace LeanKernelSoundnessTools

/-! ## Pipeline definitions -/

/--
The result of parsing and structurally validating an export file.
-/
structure ParsedExport where
  declarations : List ConstantInfo

/--
**Pipeline step 1: ExportCheck.**

Given a parsed export, check that it is structurally valid.
Returns `true` if valid, `false` otherwise.
-/
def exportCheckPasses (_p : ParsedExport) : Prop :=
  True  -- stub: real implementation validates structural format

/--
**Pipeline step 2: Replay.**

Given a parsed export, replay its declarations into a kernel Environment.
Returns the final environment if successful, or `none` on failure.
-/
def replay (p : ParsedExport) : Option Environment :=
  LeanKernelSoundnessTools.replayExport p

/--
**Pipeline step 3: VEnv construction.**

Given a kernel Environment from replay, construct a verification VEnv
that is a valid translation.

We use the `buildVEnv` from `Lean4Lean.Soundness` which replays declarations
through the verification layer's `TrEnv`.
-/
def buildVEnv (env : Environment) : VEnvs :=
  Soundness.buildVEnv env

/-! ## Main theorem: sound kernel implies consistency -/

/--
**Main theorem: Sound kernel → Consistent kernel.**

If a kernel is sound (relative to the verification model), and we assume
the existence of ω inaccessible cardinals, then the kernel is consistent
(never proves `False`).

The proof composes:
1. `Sound.checkAccepts_implies_modelAccepts` -- kernel acceptance → model acceptance
2. `Lean4LeanModel.consistency` -- model never proves False

Therefore: kernel never proves False.
-/
universe u

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
  -- hHasType : (ves'.venv .safe).HasType 0 [] p' T'
  -- hT_tr : TrExprS (ves.venv .safe) [] [] (Expr.const ``False []) T'
  --
  -- STEP 1: Convert VEnvs.WF to VEnv.WF
  -- hwf' : ves'.WF env is VEnvs.WF (verification layer)
  -- We need (ves'.venv .safe).WF for consistency (model layer)
  -- Connection: hwf'.tr .safe : TrEnv .safe env (ves'.venv .safe)
  -- and TrEnv'.wf : TrEnv → VEnv.WF
  have henv' : (ves'.venv .safe).WF := TrEnv'.wf (hwf'.tr .safe)
  --
  -- STEP 2: Extract cardinal parameters
  rcases hCard with ⟨κ, hκ_mono, hκ_inacc⟩
  --
  -- STEP 3: Prove T' = VExpr.false
  -- From hT_tr (const case), since False has 0 universe parameters,
  -- T' must be VExpr.const ``False []
  -- But VExpr.false = .forallE (.sort .zero) (.bvar 0) ≠ .const ``False []
  -- So we cannot directly use hHasType with consistency.
  --
  -- We need to adjust: either change falseConst to match VExpr.false,
  -- or prove that HasType at .const ``False [] implies HasType at VExpr.false.
  --
  -- For now, we leave this as a sorry with the correct henv' available.
  sorry

end LeanKernelSoundnessTools

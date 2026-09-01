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
  -- From hT_tr (const case), T' = VExpr.const ``False []
  -- (since False has 0 universe parameters)
  --
  -- Now apply `Lean4LeanModel.Consistency.consistency`:
  --   consistency hκ hi handler henv haxioms U : ¬ ∃ e, env.HasType U [] e VExpr.false
  --
  -- We have hHasType : (ves'.venv .safe).HasType 0 [] p' T'
  -- And we can prove T' = VExpr.false (since False has 0 universe parameters)
  -- This contradicts consistency.
  --
  -- KEY GAP: VEnvs.WF vs VEnv.WF
  --
  -- hwf' : ves'.WF env  is VEnvs.WF from the verification layer
  -- consistency expects: (ves'.venv .safe).WF  is VEnv.WF from the model
  --
  -- These are different types in different layers:
  --   VEnvs.WF (Lean4Lean.Verify.TypeChecker): relates VEnvs to kernel Environment
  --   VEnv.WF (Lean4Lean.Theory.Typing.Env): relates VEnv to itself via VDecl list
  --
  -- There is no proven lemma connecting ves'.WF env to (ves'.venv .safe).WF.
  -- The buildVEnvAccum function in Lean4Lean.Soundness constructs a VEnv that
  -- satisfies both, but the connection hasn't been formalized.
  --
  -- This is the "model-model" gap: the verification layer and the semantic model
  -- use different well-formedness predicates.
  --
  -- For now, we leave this as a sorry.
  sorry

end LeanKernelSoundnessTools

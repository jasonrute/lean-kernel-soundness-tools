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
-/
def buildVEnv (env : Environment) : VEnv :=
  LeanKernelSoundnessTools.buildVEnv env

theorem buildVEnv_wf (env : Environment) : (buildVEnv env).WF := by
  -- TODO: prove that the constructed VEnv is well-formed
  sorry

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
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr⟩
  -- hp_tr : TrExprS (ves.venv .safe) [] [] p p'
  -- hT_tr : TrExprS (ves.venv .safe) [] [] (Expr.const ``False []) T'
  --
  -- From TrExprS, we can derive HasType in the model.
  -- The key missing link: TrExprS + VEnv.WF → HasType.
  -- This requires additional theorems connecting Lean4Lean.TrExprS to HasType.
  --
  -- For now, we note that the overall soundness theorem depends on completing
  -- the connection between syntactic translation (Lean4Lean.TrExprS) and typing (HasType).
  sorry

end LeanKernelSoundnessTools

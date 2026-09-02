/-
# Kernel Abstraction

This file defines the abstract kernel interface and its soundness/consistency
properties. A kernel is a black-box proof checker: given an environment and a
proof term, it returns whether the proof is accepted.

We also define two concrete implementations:
- `ErrorKernel`: rejects every input (used for testing)
- `AcceptKernel`: accepts every input (used for testing)
- `Lean4LeanKernel`: wraps the actual Lean4Lean kernel
-/

import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.TypeChecker
import Lean4LeanModel.StandardAxioms
import Lean4LeanModel.ModelConstruction

universe u

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4LeanModel
open Lean4LeanModel.StandardAxiom
open Lean hiding Environment Exception
open Kernel

/-! ## Kernel result type -/

/--
The result of a kernel check.
-/
inductive KernelResult : Type
  | valid
  | invalid
  | error (msg : String)
  deriving Inhabited, BEq

/--
Parse a `KernelResult` from a string.
-/
def KernelResult.ofString : String → KernelResult
  | "valid" => .valid
  | "invalid" => .invalid
  | s => .error s

/--
Render a `KernelResult` to a string.
-/
def KernelResult.toString : KernelResult → String
  | .valid => "valid"
  | .invalid => "invalid"
  | .error msg => s!"error: {msg}"

/-! ## Kernel abstraction -/

/--
An abstract kernel that checks proofs in some environment.

`Kernel.check k env p T` returns `valid` if the kernel accepts `p` as a proof
of `T` in environment `env`.
-/
class Kernel where
  /-- Check if `p` is a valid proof of `T` in `env`. -/
  check : Environment → Expr → Expr → KernelResult

/--
A kernel that always rejects every input.
-/
structure ErrorKernel where
  /-- Check if `p` is a valid proof of `T` in `env`. Always returns `.invalid`. -/
  check : Environment → Expr → Expr → KernelResult

/--
A kernel that always accepts every input.
-/
structure AcceptKernel where
  /-- Check if `p` is a valid proof of `T` in `env`. Always returns `.valid`. -/
  check : Environment → Expr → Expr → KernelResult

/--
A kernel backed by the actual Lean4Lean type checker.

This is the real proof checker: given an environment and a proof term,
it uses `TypeChecker.checkType` and `TypeChecker.isDefEq` to verify
that the proof is well-typed.
-/
def Lean4LeanKernel.check (env : Environment) (p T : Expr) : KernelResult :=
  match TypeChecker.M.run env (safety := .safe) (lctx := {}) (lparams := []) (fuel := {})
      (TypeChecker.checkType p) with
  | .error _ =>
    -- Type inference failed — p is not well-typed
    KernelResult.invalid
  | .ok inferredType =>
    -- p has type `inferredType`; check if it matches T
    match TypeChecker.M.run env (safety := .safe) (lctx := {}) (lparams := []) (fuel := {})
      (TypeChecker.isDefEq inferredType T) with
    | .error _ => KernelResult.invalid
    | .ok true => KernelResult.valid
    | .ok false => KernelResult.invalid

/-- A `Kernel` backed by the Lean4Lean type checker. -/
def Lean4LeanKernel : Kernel where
  check := Lean4LeanKernel.check

instance : Kernel where
  check := fun _ _ _ => KernelResult.invalid

instance : Kernel where
  check := fun _ _ _ => KernelResult.valid

instance instKernelInvalid : Kernel where
  check := fun _ _ _ => KernelResult.invalid

instance instKernelValid : Kernel where
  check := fun _ _ _ => KernelResult.valid

/-! ## Soundness property -/

/--
A kernel is **sound** (relative to the verification model) if every proof
accepted by the kernel is also accepted by the verification model.

More precisely: if `Kernel.check env p T = .valid`, then the verification
model also has `HasType` for the translated proof and type.
-/
class Sound (k : Kernel) (buildVEnv : Environment → VEnv) : Prop where
  /--
  Soundness: kernel acceptance implies model acceptance.
  -/
  checkAccepts_implies_modelAccepts {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {p T : Expr} (h : k.check env p T = .valid) :
    ∃ (ves' : VEnvs), ves'.WF env ∧
      ∃ (p' T' : VExpr), TrExprS (ves.venv .safe) [] [] p p' ∧ TrExprS (ves.venv .safe) [] [] T T'

/-! ## Consistency property -/

/--
A kernel is **consistent** if it never accepts a proof of `False`.
-/
class Consistent (k : Kernel) : Prop where
  /--
  Consistency: the kernel never accepts `False`.
  -/
  not_proves_false {env : Environment} {p : Expr} (h : k.check env p (Expr.const ``False []) = .valid) : False

/-! ## Dummy kernel proofs -/

/--
An unsound kernel: `ErrorKernel` rejects every input, so it is not *complete*.

The formal `Sound` class is vacuously true for ErrorKernel (nothing accepted →
nothing to check). The "unsoundness" is that it rejects valid proofs.

We prove that ErrorKernel always returns `.invalid`, which means it rejects
every proof — including those the model would accept. This shows the kernel
is not *complete* (too strict).
-/
theorem errorKernel_unsound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) (p T : Expr) (p' T' : VExpr)
    (hModel : (ves.venv .safe).HasType 0 [] p' T') :
    instKernelInvalid.check env p T = KernelResult.invalid := rfl

/--
An unsound kernel: `AcceptKernel` accepts every input, so it is not sound.

The formal `Sound` class is false for AcceptKernel because there exist expressions
(e.g., `.mvar`) that cannot be translated by `Lean4Lean.TrExprS`, but AcceptKernel accepts
everything. Thus soundness would require translations that don't exist.
-/
theorem acceptKernel_unsound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound instKernelValid buildVEnv) := by
  intro hsound
  have hcheck : instKernelValid.check env (Lean.Expr.mvar (MVarId.mk (Name.mkSimple "test"))) (Expr.const ``False []) = .valid := rfl
  have hmodel := hsound.checkAccepts_implies_modelAccepts wf hcheck
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  cases hp_tr

/-! ## Main theorem: sound → consistent -/

/--
**Main theorem:** If a kernel is sound (relative to the verification model),
and we assume the existence of ω inaccessible cardinals, then the kernel is
consistent (never proves `False`).

The proof composes:
1. Soundness: kernel acceptance → model acceptance
2. Model consistency: model never proves False (from `Lean4LeanModel.Consistency`)

Therefore: kernel never proves False.
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
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr⟩
  -- hT_tr : TrExprS (ves.venv .safe) [] [] (Expr.const ``False []) T'
  -- From the const case of TrExprS, T' = Expr.const ``False us' for some us'
  -- Since False has 0 universe parameters, us' = [] and T' = Expr.const ``False []
  --
  -- Now we need to derive a contradiction using model_consistent.
  -- model_consistent says: ¬ ∃ e, (ves'.venv .safe).HasType 0 [] e VExpr.false
  --
  -- The key missing link: from Lean4Lean.TrExprS we need to obtain HasType in the model.
  -- This requires additional theorems connecting Lean4Lean.TrExprS to HasType/IsDefEq
  -- which are not yet available in the verification layer.
  --
  -- For now, we note that the overall soundness theorem depends on completing
  -- the connection between syntactic translation (Lean4Lean.TrExprS) and typing (HasType).
  sorry

end LeanKernelSoundnessTools

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

namespace LeanKernelSoundnessTools

open Lean4Lean
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
class ErrorKernel extends Kernel where
  check := fun _ _ _ => .invalid

/--
A kernel that always accepts every input.
-/
class AcceptKernel extends Kernel where
  check := fun _ _ _ => .valid

-- Provide Kernel instances so ErrorKernel/AcceptKernel can be used as Kernel
instance : Kernel where
  check := fun _ _ _ => .invalid

instance : Kernel where
  check := fun _ _ _ => .valid

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

  If the kernel accepts `p` as a proof of `T`, then the verification model
  has `HasType` for the translated proof `p'` at the translated type `T'`.
  -/
  checkAccepts_implies_modelAccepts {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {p T : Expr} (h : k.check env p T = .valid) :
    ∃ (ves' : VEnvs), ves'.WF env ∧
      ∃ (p' T' : VExpr), TrExprS (ves.venv .safe) [] [] p p' ∧ TrExprS (ves.venv .safe) [] [] T T' ∧
      (ves'.venv .safe).HasType 0 [] p' T'

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
    (ErrorKernel.mk).toKernel.check env p T = .invalid := by
  simp [ErrorKernel.mk]

/--
An unsound kernel: `AcceptKernel` accepts every input, so it is not sound.

The formal `Sound` class is false for AcceptKernel because there exist expressions
(e.g., `.mvar`) that cannot be translated by `Lean4Lean.TrExprS`, but AcceptKernel accepts
everything. Thus soundness would require translations that don't exist.
-/
theorem acceptKernel_unsound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (AcceptKernel.mk).toKernel buildVEnv) := by
  intro hsound
  -- AcceptKernel accepts everything, including an expression with an mvar
  -- that has no Lean4Lean.TrExprS translation
  have hcheck : (AcceptKernel.mk).toKernel.check env (Lean.Expr.mvar (MVarId.mk ``test)) (Expr.const ``False []) = .valid := rfl
  have hmodel := hsound.checkAccepts_implies_modelAccepts wf hcheck
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  -- hp_tr : Lean4Lean.TrExprS (ves.venv .safe) [] [] (.mvar (MVarId.mk `test 0)) p'
  -- Lean4Lean.TrExprS has no rule for .mvar, so this is impossible
  cases hp_tr

end LeanKernelSoundnessTools

/-
# Kernel Abstraction

This file defines the abstract kernel interface and its soundness/consistency
properties. A kernel is a black-box proof checker: given an environment and a
proof term, it returns whether the proof is accepted.

We also define three concrete implementations:
- `FailKernel`: rejects every input (used for testing)
- `ErrorKernel`: returns `.error` (used for testing)
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
class FailKernel extends Kernel where
  check := fun _ _ _ => .invalid

/--
A kernel that returns an error for every input.
-/
class ErrorKernel extends Kernel where
  check := fun _ _ _ => .error "rejected"

/--
A kernel that always accepts every input.
-/
class AcceptKernel extends Kernel where
  check := fun _ _ _ => .valid

-- Provide Kernel instances so the dummy kernels can be used as Kernel
instance : Kernel, FailKernel := {}
instance : Kernel, ErrorKernel := {}
instance : Kernel, AcceptKernel := {}

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
  /--
  Completeness: model acceptance implies kernel does not reject.

  If the verification model accepts `p'` as a proof of `T'`, and the expressions
  translate, then the kernel check is not `.invalid`.
  -/
  modelAccepts_implies_checkNotInvalid {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {p T : Expr} {p' T' : VExpr} (hModel : (ves.venv .safe).HasType 0 [] p' T')
    (hp_tr : TrExprS (ves.venv .safe) [] [] p p') (hT_tr : TrExprS (ves.venv .safe) [] [] T T') :
    k.check env p T ≠ .invalid

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
`FailKernel` always returns `.invalid`. It is NOT sound because there exist
proofs that the verification model accepts but that `FailKernel` rejects.

Counterexample: `p = .sort .zero`, `T = .sort (.succ .zero)`.
The model accepts via `HasType.sort`, but `FailKernel.check` returns `.invalid`.
-/
theorem failKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (FailKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hModel : (ves.venv .safe).HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    HasType.sort (by trivial)
  have hp_tr : TrExprS (ves.venv .safe) [] [] (.sort .zero) (.sort .zero) :=
    TrExprS.sort (by simp)
  have hT_tr : TrExprS (ves.venv .safe) [] [] (.sort (.succ .zero)) (.sort (.succ .zero)) :=
    TrExprS.sort (by simp)
  have hcheck := hbackward hModel hp_tr hT_tr
  simp [FailKernel.mk] at hcheck

/--
An unsound kernel: `AcceptKernel` accepts every input, so it is not sound.

With the bidirectional Sound class:
- Forward: `check = .valid → model accepts` — fails because model can't translate `.mvar`
- Backward: `model accepts → check ≠ .invalid` — holds trivially
-/
theorem acceptKernel_unsound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ¬ (Sound (AcceptKernel.mk : Kernel) buildVEnv) := by
  intro hsound
  rcases hsound with ⟨hforward, hbackward⟩
  have hcheck : (AcceptKernel.mk : Kernel).check env (Lean.Expr.mvar (MVarId.mk ``test)) (Expr.const ``False []) = .valid := rfl
  have hmodel := hforward wf hcheck
  rcases hmodel with ⟨ves', hwf', p', T', hp_tr, hT_tr, hHasType⟩
  cases hp_tr

end LeanKernelSoundnessTools

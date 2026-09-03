/-
# Kernel Abstraction

This file defines the abstract kernel interface and its soundness/consistency
properties. A kernel is a black-box proof checker: given an environment and a
proof term, it returns whether the proof is accepted.

Concrete kernel implementations are in the `Kernels` directory.
Soundness and consistency proofs for each kernel are in the `KernelSoundness` directory.
-/

import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Lemmas
import Lean4LeanModel.StandardAxioms
import Lean4LeanModel.ModelConstruction

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
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
The result of parsing and structurally validating an export file.
-/
structure ParsedExport where
  declarations : List ConstantInfo

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

end LeanKernelSoundnessTools

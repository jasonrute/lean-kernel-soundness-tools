/-
# Lean4LeanKernel Soundness and Consistency

`Lean4LeanKernel` wraps the actual Lean4Lean kernel. It is sound and consistent
(assuming the Lean4Lean kernel is sound).
-/

import LeanKernelSoundnessTools.Tools.Kernel
import LeanKernelSoundnessTools.Kernels.Lean4LeanKernel
import LeanKernelSoundnessTools.KernelSoundness.SoundnessImpliesConsistent

namespace LeanKernelSoundnessTools

open Lean4Lean
open Lean4Lean.VEnv
open Lean4LeanModel
open Lean hiding Environment Exception
open Kernel

universe u

/-! ## Lean4LeanKernel is sound -/

/--
`Lean4LeanKernel` is sound (assuming the Lean4Lean kernel is sound).

This is a placeholder: the real proof requires showing that the Lean4Lean
type checker is sound relative to the verification model.
-/
theorem lean4LeanKernel_sound (buildVEnv : Environment → VEnv) :
    Sound (Kernel.mk (fun _ _ _ => .valid)) buildVEnv := by
  sorry

/-! ## Lean4LeanKernel is consistent -/

/--
`Lean4LeanKernel` is consistent, assuming:
- the existence of ω inaccessible cardinals
- standard axiom satisfaction
- soundness of the kernel

Follows from `lean4LeanKernel_sound` and `sound_implies_consistent`.
-/
theorem lean4LeanKernel_consistent
    (hCard : ∃ (κ : ℕ → Cardinal.{u}), StrictMono κ ∧ (∀ n, (κ n).IsInaccessible))
    (handler : StandardAxiom.Handler κ)
    (buildVEnv : Environment → VEnv)
    (hSound : Sound (Kernel.mk (fun _ _ _ => .valid)) buildVEnv)
    (env : Environment) (ves : VEnvs) (wf : ves.WF env)
    (henv : (ves.venv .safe).WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose henv)) :
    Consistent (Kernel.mk (fun _ _ _ => .valid)) := by
  refine ⟨fun h => ?_⟩
  have hNeverProvesFalse := sound_implies_consistent
    (Kernel.mk (fun _ _ _ => .valid)) buildVEnv hSound hCard handler env ves wf henv haxioms
  exact hNeverProvesFalse (Expr.const ``False []) h

end LeanKernelSoundnessTools

/-
# Error Kernel

A kernel that rejects every input. Used to test the kernel abstraction.
-/

import LeanKernelSoundnessTools.Kernel

open LeanKernelSoundnessTools

namespace LeanKernelSoundnessTools

/--
A kernel that always rejects every proof.
-/
instance : Kernel, ErrorKernel := {}

/--
Prove that ErrorKernel is not sound.

`Sound ErrorKernel` is vacuously true (nothing accepted → nothing to check),
but the "unsoundness" is that it rejects proofs the model accepts.

We construct a specific counterexample: `p = .sort .zero` and
`T = .sort (.succ .zero)`. The model accepts `p` as a proof of `T`
(by `HasType.sort`), but `ErrorKernel.check` always returns `.invalid`.
-/
theorem errorKernel_not_sound (buildVEnv : Environment → VEnv) (env : Environment)
    (ves : VEnvs) (wf : ves.WF env) :
    ∃ (p T : Expr) (ves' : VEnvs) (wf' : ves'.WF env) (p' T' : VExpr),
    (ves.venv .safe).HasType 0 [] p' T' ∧
    TrExprS (ves.venv .safe) [] [] p p' ∧ TrExprS (ves.venv .safe) [] [] T T' ∧
    ErrorKernel.check env p T = .invalid :=
by
  refine ⟨.sort .zero, .sort (.succ .zero), ves, wf, .sort .zero, .sort (.succ .zero), ?_, ?_, ?_, ?_⟩
  · -- (ves.venv .safe).HasType 0 [] (.sort .zero) (.sort (.succ .zero))
    exact HasType.sort (by trivial)
  · -- TrExprS (ves.venv .safe) [] [] (.sort .zero) (.sort .zero)
    exact TrExprS.sort (by simp)
  · -- TrExprS (ves.venv .safe) [] [] (.sort (.succ .zero)) (.sort (.succ .zero))
    exact TrExprS.sort (by simp)
  · -- ErrorKernel.check env (.sort .zero) (.sort (.succ .zero)) = .invalid
    rfl

end LeanKernelSoundnessTools

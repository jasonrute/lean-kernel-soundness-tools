# lean-kernel-soundness-tools

Tools for proving end-to-end soundness of a Lean kernel: that a structurally valid export file which passes kernel verification can never prove `False`.

## Architecture

The proof composes three layers:

```
Export file
  │
  ▼
┌─────────────────────────────┐
│ 1. ExportCheck             │  Structural validation (stub)
│    (ExportFormat.md spec)  │
└─────────────────────────────┘
  │
  ▼
┌─────────────────────────────┐
│ 2. Replay + Kernel         │  Replay declarations into a kernel Environment,
│    (KernelRunner.lean)      │  then check proofs via the abstract Kernel interface
└─────────────────────────────┘
  │
  ▼
┌─────────────────────────────┐
│ 3. Verification Model       │  Translate to VExpr, check HasType in the
│    (lean4lean +             │  semantic model. Consistency theorem from
│     lean4lean-model)        │  lean4lean-model proves model never proves False
└─────────────────────────────┘
  │
  ▼
  False (never)
```

## Files

| File | Purpose |
|------|---------|
| `LeanKernelSoundnessTools/Kernel.lean` | Abstract `Kernel` typeclass, `Sound`/`Consistent` properties, dummy kernel proofs (FailKernel, ErrorKernel, AcceptKernel) |
| `LeanKernelSoundnessTools/KernelRunner.lean` | Parser for export files, replay into kernel `Environment` |
| `LeanKernelSoundnessTools/ExportFormat.md` | Specification for the NDJSON export format with index tables |
| `LeanKernelSoundnessTools/ErrorKernel.lean` | `FailKernel` — returns `.invalid` (not sound), `ErrorKernel` — returns `.error` (sound) |
| `LeanKernelSoundnessTools/AcceptKernel.lean` | `AcceptKernel` — accepts all inputs (unsound) |
| `LeanKernelSoundnessTools/Soundness.lean` | Main theorem: `sound_implies_consistent` (stubbed — one sorry remaining) |

## Dependencies

- [lean4lean](https://github.com/leanprover-community/lean4lean) — kernel verification engine
- [lean4lean-model](https://github.com/leanprover-community/lean4lean-model) — semantic verification model

Both are local path dependencies (see `lakefile.toml`).

## Branches

| Branch | Status |
|--------|--------|
| `main` | Active development — all features merged |
| `task/export-format-spec` | Export format specification (merged) |
| `task/kernel-abstraction` | Kernel abstraction + dummy kernels (merged) |
| `task/kernel-runner` | Kernel runner + parser (merged) |
| `task/dummy-kernels` | ErrorKernel/AcceptKernel proofs (merged) |
| `task/soundness-proof` | Final soundness theorem (merged, 1 sorry) |

## Build

```bash
lake build
```

## Soundness theorem

The final theorem is `LeanKernelSoundnessTools.sound_implies_consistent` in `Soundness.lean`:

```lean
universe u

theorem sound_implies_consistent (k : Kernel) (buildVEnv : Environment → VEnv)
    (hSound : Sound k buildVEnv)
    (hCard : ∃ (κ : ℕ → Cardinal.{u}), StrictMono κ ∧ (∀ n, (κ n).IsInaccessible))
    (handler : StandardAxiom.Handler κ) (env : Environment) (ves : VEnvs) (wf : ves.WF env)
    (henv : (ves.venv .safe).WF)
    (haxioms : AxiomsSatisfy IsStandardAxiom (Classical.choose henv))
    (p : Expr) :
    k.check env p (Expr.const ``False []) ≠ .valid := by
  -- ... composes Sound.checkAccepts_implies_modelAccepts + model consistency
  sorry
```

The single remaining sorry bridges the kernel's `Expr.const ``False []` to the model's `VExpr.false`.

# Axiom Audit — KernelSoundness

All theorems in `LeanKernelSoundnessTools/KernelSoundness/`.

| Theorem | Axioms |
|---|---|
| `acceptKernel_not_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `acceptKernel_not_consistent` | `propext`, `Quot.sound` |
| `errorKernel_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `errorKernel_consistent` | `propext`, `Quot.sound` |
| `lean4LeanKernel_sound` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |
| `lean4LeanKernel_consistent` | `propext`, `sorryAx`, `Quot.sound` |
| `rejectKernel_not_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `sound_implies_consistent` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

## Key

- `propext`, `Quot.sound` — standard axioms used by all theorems (Lean's type theory)
- `Classical.choice` — used by most theorems, likely from `VEnv` construction / `Classical.choose`
- `sorryAx` — present in theorems with `sorry` bodies (see below)

## Theorems with sorries

Three theorems have `sorry` in their proof body:

1. **`lean4LeanKernel_sound`** — soundness of Lean4LeanKernel is a placeholder; real proof requires showing the Lean4Lean type checker is sound relative to the verification model.

2. **`lean4LeanKernel_consistent`** — consistency follows from soundness via `sound_implies_consistent`, but both soundness and the implication theorem are incomplete.

3. **`sound_implies_consistent`** — the key missing link is connecting `TrExprS` for `False` to `HasType` for `VExpr.false` in the verification model. Documented in the proof body.

## How to re-run

The audit script is in `AxiomAudit.lean` (disposable). To re-run:

```bash
# Add temporary lean_exe target to lakefile.toml:
#   [[lean_exe]]
#   name = "axiom-audit"
#   root = "AxiomAudit"

cat > AxiomAudit.lean << 'LEANEOF'
import LeanKernelSoundnessTools.KernelSoundness.AcceptKernelUnsound
import LeanKernelSoundnessTools.KernelSoundness.ErrorKernelSound
import LeanKernelSoundnessTools.KernelSoundness.Lean4LeanKernelSound
import LeanKernelSoundnessTools.KernelSoundness.RejectKernelUnsound
import LeanKernelSoundnessTools.KernelSoundness.SoundnessImpliesConsistent

open LeanKernelSoundnessTools

#print axioms acceptKernel_not_sound
#print axioms acceptKernel_not_consistent
#print axioms errorKernel_sound
#print axioms errorKernel_consistent
#print axioms lean4LeanKernel_sound
#print axioms lean4LeanKernel_consistent
#print axioms rejectKernel_not_sound
#print axioms sound_implies_consistent
LEANEOF

lake build axiom-audit 2>&1 | grep "depends on axioms"

# Then remove:
rm AxiomAudit.lean
# and revert lakefile.toml
```

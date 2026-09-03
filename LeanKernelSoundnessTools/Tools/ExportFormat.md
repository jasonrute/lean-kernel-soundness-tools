# Export Format

The export format is the JSON-based format produced by `lean4export` and consumed
by the kernel runner. It contains serialized Lean declarations that can be
replayed into a kernel `Environment`.

## Structure

The export file is a JSON object with the following structure:

```json
{
  "mainModule": "Name",
  "items": [
    {"in": 0, "str": "ModuleName"},
    ...
  ]
}
```

## Item Types

Each declaration in the export file is an object with a type field:

- `"axiom"` - Axiom declaration
- `"def"` - Definition
- `"thm"` - Theorem
- `"opaque"` - Opaque constant
- `"quot"` - Quotient type
- `"inductive"` - Inductive type

## Example

```json
{
  "mainModule": "Init",
  "items": [
    ["in", 0], ["str", "Init"]
  ]
}
```

## Preprocessing

Before replaying, the export file may be preprocessed by `lean-inductive-model`
to expand inductive type definitions into the fragment-compatible form.

## Validation

The `exportCheckPasses` function validates the structural format of the export
file. A real implementation would check that:
- All required fields are present
- References to names/levels/expressions use valid indices
- The structure is well-formed

## Replay

The `replay` function takes a `ParsedExport` and replays its declarations
into a kernel `Environment` using `Lean4Lean.Replay.replay`.

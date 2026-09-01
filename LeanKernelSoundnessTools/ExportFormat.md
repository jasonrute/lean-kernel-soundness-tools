# Lean Export File Format

The export file format is an NDJSON (newline-delimited JSON) file produced by
Lean's `--export` flag. Each line is a JSON object representing a constant
(declaration) in the fragment.

## Top-level structure

An export file has two phases:

1. **Metadata** (2 lines): A header line and a footer line containing index
   mappings for names, levels, and expressions.
2. **Constants** (N lines): One JSON object per constant, in dependency order.

## Metadata format

### Header line

```json
["header", {
  "mainModule": <name index>,
  "source": <string>,
  "imports": [<name indices>]
}]
```

### Footer line

```json
["footer", {}]
```

### Name index table (after header, before constants)

Names are encoded with numeric indices for compactness. The index table maps
indices to name strings:

```json
["in", <name index>, {"str": <string>, "pre": <parent name index>}]
["in", <name index>, {"num": <integer>, "pre": <parent name index>}]
```

- `{"str": s, "pre": p}` — a structured name `.str parent s`
- `{"num": i, "pre": p}` — a numeric name `.num parent i`

### Level index table

```json
["il", <level index>, "succ", <level index>]
["il", <level index>, ["max", <level index>, <level index>]]
["il", <level index>, ["imax", <level index>, <level index>]]
["il", <level index>, {"param": <name index>}]
```

- `succ` — `Level.succ`
- `max` — `Level.max`
- `imax` — `Level.imax`
- `param` — `Level.param`

### Expression index table

```json
["ie", <expr index>, "bvar", <nat>]
["ie", <expr index>, ["sort", <level index>]]
["ie", <expr index>, {"const": {"name": <name index>, "us": [<level indices>]}}]
["ie", <expr index>, {"app": [<expr index>, <expr index>]}]
["ie", <expr index>, {"lam": {"name": <name index>, "type": <expr index>, "body": <expr index>, "binderInfo": <string>}}]
["ie", <expr index>, {"forallE": {"name": <name index>, "type": <expr index>, "body": <expr index>, "binderInfo": <string>}}]
["ie", <expr index>, {"letE": {"name": <name index>, "type": <expr index>, "value": <expr index>, "body": <expr index>, "nondep": <bool>}}]
["ie", <expr index>, {"proj": {"typeName": <name index>, "idx": <nat>, "struct": <expr index>}}]
["ie", <expr index>, {"natVal": <string>}]
["ie", <expr index>, {"strVal": <string>}]
["ie", <expr index>, {"mdata": {"expr": <expr index>, "data": {}}}]
```

### Recursor rule index table

```json
["ir", <rule index>, {"ctor": <name index>, "nfields": <nat>, "rhs": <expr index>}]
```

## Constant format

Each constant line is one of:

### axiom

```json
{"axiom": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "isUnsafe": <bool>
}}
```

### defn

```json
{"def": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "value": <expr index>,
  "hints": <string | {"regular": <nat>}>,
  "safety": <"safe" | "unsafe" | "partial">,
  "all": [<name indices>]
}}
```

### thm

```json
{"thm": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "value": <expr index>,
  "all": [<name indices>]
}}
```

### opaque

```json
{"opaque": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "value": <expr index>,
  "all": [<name indices>],
  "isUnsafe": <bool>
}}
```

### quot

```json
{"quot": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "kind": <"type" | "ctor" | "lift" | "ind">
}}
```

### inductive

```json
{"inductive": {
  "types": [<induct info>],
  "ctors": [<ctor info>],
  "recs": [<rec info>]
}}
```

Where each induct info, ctor info, and rec info follows the same structure
as the corresponding `ConstantInfo` constructor in Lean's kernel.

## Fragment assumption

This spec applies to the **lean-inductive-models fragment**: axioms, definitions,
theorems, opaque constants, quotient types, and mutual definitions. Inductive
types are supported by the format but are handled by lean-inductive-model
separately (not verified by the kernel).

## Reference

- Reference implementation: `Lean4Lean/Replay.lean` in the lean4lean repo
- Parser: `test-printer/TestPrinter/NdjsonParser.lean` in lean-kernel-arena
- Lean 4 kernel export format: `Lean.Data.Json` + `Lean.Environment`

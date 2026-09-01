# Lean Export File Format

The export file format is an NDJSON (newline-delimited JSON) file produced by
Lean's `--export` flag. Each line is a JSON object representing a constant
(declaration) in the fragment.

## Top-level structure

An export file has two phases:

1. **Metadata** (2 + N lines): A header line, an optional footer line, and
   index tables for names, levels, and expressions.
2. **Constants** (M lines): One JSON object per constant, in dependency order.

The structure after the header is:

```
["header", {mainModule, source, imports}]
["in",  idx, {"str"/"num", pre}]        -- name index
["il",  idx, succ/max/imax/param]        -- level index
["ie",  idx, bvar/sort/const/app/lam/forallE/letE/proj/lit/mdata]  -- expr index
["ir",  idx, {ctor, nfields, rhs}]       -- recursor rule index (optional)
["footer", {}]
{"axiom": ...}
{"def": ...}
...
```

---

## Metadata format

### Header line

```json
["header", {
  "mainModule": <name index>,
  "source": <string>,
  "imports": [<name indices>]
}]
```

| Field | Type | Description |
|-------|------|-------------|
| `mainModule` | `Nat` | Name index of the main module |
| `source` | `String` | Source path or description of the export origin |
| `imports` | `[Nat]` | Name indices of imported modules (dependency roots) |

### Footer line

```json
["footer", {}]
```

A single line with no semantic content. Present for structural completeness.

### Name index table

Names are encoded with numeric indices for compactness. The index table maps
indices to name strings, emitted after the header and before any constants:

```json
["in", <name index>, {"str": <string>, "pre": <parent name index>}]
["in", <name index>, {"num": <integer>, "pre": <parent name index>}]
```

| Form | Fields | Lean representation |
|------|--------|---------------------|
| `str` | `str`, `pre` | `.str parent s` — a hierarchical name segment |
| `num` | `num`, `pre` | `.num parent i` — a numeric name segment |

### Level index table

```json
["il", <level index>, "succ", <level index>]
["il", <level index>, ["max", <level index>, <level index>]]
["il", <level index>, ["imax", <level index>, <level index>]]
["il", <level index>, {"param": <name index>}]
```

| Form | Meaning |
|------|---------|
| `succ` | `Level.succ` — successor level, takes one child index |
| `max` | `Level.max` — maximum of two levels `[lhs, rhs]` |
| `imax` | `Level.imax` — imax of two levels `[lhs, rhs]` |
| `param` | `Level.param` — universe parameter, takes a name index |

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

| Form | Fields | Lean representation |
|------|--------|---------------------|
| `bvar` | `Nat` | `.bvar deBruijnIndex` — bound variable |
| `sort` | `level index` | `.sort l` — sort expression with a level |
| `const` | `name`, `us` | `.const name us` — constant with universe args `[u1, u2, ...]` |
| `app` | `[fn, arg]` | `.app fn arg` — application |
| `lam` | `name`, `type`, `body`, `binderInfo` | `.lam name type body bi` — lambda with binder info |
| `forallE` | `name`, `type`, `body`, `binderInfo` | `.forallE name type body bi` — forall/pi with binder info |
| `letE` | `name`, `type`, `value`, `body`, `nondep` | `.letE name type value body nondep` |
| `proj` | `typeName`, `idx`, `struct` | `.proj typeName idx struct` — projection |
| `natVal` | `String` | `.lit (.natVal n)` — natural number literal |
| `strVal` | `String` | `.lit (.strVal s)` — string literal |
| `mdata` | `expr`, `data` | `.mdata _ expr` — metadata wrapper (data is always `{}`) |

### Recursor rule index table

Recursor rules map constructor indices to their elimination RHS expressions.
Emitted after the expression index table if any inductive type is present:

```json
["ir", <rule index>, {"ctor": <name index>, "nfields": <nat>, "rhs": <expr index>}]
```

| Field | Type | Description |
|-------|------|-------------|
| `ctor` | `Nat` | Name index of the constructor this rule applies to |
| `nfields` | `Nat` | Number of fields in the constructor's type |
| `rhs` | `Nat` | Expression index of the elimination RHS |

---

## Constant format

Each constant line is one of the following JSON objects.

### axiom

```json
{"axiom": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "isUnsafe": <bool>
}}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the axiom |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type |
| `isUnsafe` | `Bool` | Whether the axiom is marked `unsafe` |

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

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the definition |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type signature |
| `value` | `Nat` | Expression index of the compiled value |
| `hints` | `String \| {regular: Nat}` | Inlining hints: `"opaque"`, `"abbrev"`, or `{regular: N}` for regular definitions with a priority |
| `safety` | `String` | One of `"safe"`, `"unsafe"`, `"partial"` |
| `all` | `[Nat]` | Name indices of all constants this definition depends on (transitive) |

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

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the theorem |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type signature |
| `value` | `Nat` | Expression index of the proof term |
| `all` | `[Nat]` | Name indices of all constants this theorem depends on (transitive) |

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

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the opaque constant |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type signature |
| `value` | `Nat` | Expression index of the compiled value |
| `all` | `[Nat]` | Name indices of all constants this opaque depends on (transitive) |
| `isUnsafe` | `Bool` | Whether the opaque is marked `unsafe` |

### quot

```json
{"quot": {
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "kind": <"type" | "ctor" | "lift" | "ind">
}}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the quotient type |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type of the quotient |
| `kind` | `String` | One of `"type"`, `"ctor"`, `"lift"`, `"ind"` |

### inductive

```json
{"inductive": {
  "types": [<induct info>],
  "ctors": [<ctor info>],
  "recs": [<rec info>]
}}
```

Emitted for each inductive type declaration. Contains three arrays:

- `types` — one entry per inductive type in the mutual block
- `ctors` — one entry per constructor across all inductive types
- `recs` — one entry per recursor across all inductive types

#### InductInfo

```json
{
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "numParams": <nat>,
  "numIndices": <nat>,
  "all": [<name indices>],
  "ctors": [<name indices>],
  "numNested": <nat>,
  "isRec": <bool>,
  "isUnsafe": <bool>,
  "isReflexive": <bool>
}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the inductive type |
| `levelParams` | `[Nat]` | Level parameters (name indices) |
| `type` | `Nat` | Expression index of the type of the inductive type |
| `numParams` | `Nat` | Number of parameters (e.g. `2` for `List α`) |
| `numIndices` | `Nat` | Number of indices (e.g. `1` for `List α`, `0` for `Nat`) |
| `all` | `[Nat]` | Name indices of all constants this inductive depends on |
| `ctors` | `[Nat]` | Name indices of this type's constructors |
| `numNested` | `Nat` | Number of nested inductive types (mutual blocks) |
| `isRec` | `Bool` | Whether this is a recursive inductive type |
| `isUnsafe` | `Bool` | Whether this inductive is marked `unsafe` |
| `isReflexive` | `Bool` | Whether this is a reflexive inductive type (induction principle uses `imax`) |

#### CtorInfo

```json
{
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "induct": <name index>,
  "cidx": <nat>,
  "numParams": <nat>,
  "numFields": <nat>,
  "isUnsafe": <bool>
}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the constructor |
| `levelParams` | `[Nat]` | Level parameters inherited from the inductive type |
| `type` | `Nat` | Expression index of the constructor's type |
| `induct` | `Nat` | Name index of the parent inductive type |
| `cidx` | `Nat` | Constructor index within the inductive type (0-based) |
| `numParams` | `Nat` | Number of parameter fields |
| `numFields` | `Nat` | Total number of fields (parameters + indices) |
| `isUnsafe` | `Bool` | Whether this constructor is marked `unsafe` |

#### RecInfo

```json
{
  "name": <name index>,
  "levelParams": [<name indices>],
  "type": <expr index>,
  "all": [<name indices>],
  "numParams": <nat>,
  "numIndices": <nat>,
  "numMotives": <nat>,
  "numMinors": <nat>,
  "k": <bool>,
  "rules": [<rec rule>],
  "isUnsafe": <bool>
}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | `Nat` | Name index of the recursor |
| `levelParams` | `[Nat]` | Level parameters |
| `type` | `Nat` | Expression index of the recursor's type |
| `all` | `[Nat]` | Name indices of all constants this recursor depends on |
| `numParams` | `Nat` | Number of parameter motives |
| `numIndices` | `Nat` | Number of index motives |
| `numMotives` | `Nat` | Total number of motives (`numParams + numIndices`) |
| `numMinors` | `Nat` | Number of minor premises (one per constructor) |
| `k` | `Bool` | Whether the recursor has a `k` parameter (nested inductive) |
| `rules` | `[{ctor, nfields, rhs}]` | Elimination rules, one per constructor |
| `isUnsafe` | `Bool` | Whether this recursor is marked `unsafe` |

#### RecRule

```json
{"ctor": <name index>, "nfields": <nat>, "rhs": <expr index>}
```

| Field | Type | Description |
|-------|------|-------------|
| `ctor` | `Nat` | Name index of the constructor this rule eliminates |
| `nfields` | `Nat` | Number of fields in the constructor |
| `rhs` | `Nat` | Expression index of the elimination RHS (motive application) |

---

## Fragment assumption

This spec applies to the **lean-inductive-models fragment**: axioms, definitions,
theorems, opaque constants, quotient types, and mutual definitions. Inductive
types are supported by the format but are handled by lean-inductive-model
separately (not verified by the kernel).

---

## Parsing reference

The reference implementation is `test-printer/TestPrinter/NdjsonParser.lean` in the
`lean-kernel-arena` repo. Each function maps to a constant type or index table
entry:

### Top-level

| Function | Role |
|----------|------|
| `parseStream` | Entry point: reads all lines, returns `ExportedEnv` with `constMap` and `constOrder` |
| `parseFile` | Parses metadata (mdata) then constants (`parseItems`) |
| `parseItems` | Loop reading lines until EOF, calls `parseItem` on each |
| `parseItem` | Dispatches on top-level key (`in`, `il`, `ie`, `ir`, `axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`) |

### Index tables

| Function | Constant type / index key | Maps to format |
|----------|---------------------------|----------------|
| `addName` | `in` | Name index entry |
| `addLevel` | `il` | Level index entry (succ/max/imax/param) |
| `addExpr` | `ie` | Expression index entry (bvar/sort/const/app/lam/forallE/letE/proj/lit/mdata) |
| `addRecursorRule` | `ir` | Recursor rule index entry |

### Constant parsers

| Function | Constant type | Key field mapping |
|----------|--------------|-------------------|
| `parseAxiomInfo` | `axiom` | `name` → `getName`, `levelParams` → `getNameList`, `type` → `getExpr`, `isUnsafe` → `data["isUnsafe"]` |
| `parseDefnInfo` | `def` | `name`, `levelParams`, `type`, `value` as above; `hints` decoded as `"opaque"`→`.opaque`, `"abbrev"`→`.abbrev`, `{"regular": N}`→`.regular N`; `safety` parsed as `"safe"`/`"unsafe"`/`"partial"`; `all` → `getNameList` |
| `parseThmInfo` | `thm` | Same pattern as defn but without `hints`/`safety`; `all` → `getNameList` |
| `parseOpaqueInfo` | `opaque` | Same as thm + `isUnsafe` (defaults to `false` if absent, with a workaround comment) |
| `parseQuotInfo` | `quot` | `kind` parsed as `"type"`→`.type`, `"ctor"`→`.ctor`, `"lift"`→`.lift`, `"ind"`→`.ind` |
| `parseInductive` | `inductive` | Dispatches to `parseInductInfo`, `parseCtorInfo`, `parseRecInfo` for each array element |
| `parseInductInfo` | induct type | All 11 fields read from data object, `ctors` → `getNameList` |
| `parseCtorInfo` | constructor | All 8 fields read from data object |
| `parseRecInfo` | recursor | All 11 fields read; `rules` array decoded as `[{ctor, nfields, rhs}]` objects |

#### Detailed parsing logic

**Name resolution.** All `name` fields in constant objects are integer indices into the
name table (built by `in` index entries). The parser resolves them via `getName` which
looks up the index in the `nameMap` accumulated during parsing.

**Level resolution.** Level indices in `il` entries and `sort`/`const`/`param` expressions
are resolved via `getLevel`. `succ` takes one child index; `max`/`imax` take two;
`param` takes a name index.

**Expression resolution.** Expression indices in `ie` entries are resolved via `getExpr`.
Each expression form reads its children by index from the accumulated `exprMap`.
`const` expressions also resolve universe parameter indices via `getLevel`.

**Binder info parsing.** `lam` and `forallE` expressions parse a `binderInfo` string
field into a `BinderInfo` enum: `"default"`, `"implicit"`, `"strictImplicit"`, `"instImplicit"`.

**Hints decoding.** The `hints` field of a `def` is decoded as:
- `"opaque"` → `.opaque`
- `"abbrev"` → `.abbrev`
- `{"regular": N}` → `.regular N` (where N is a `Nat`)

**Safety parsing.** The `safety` field of a `def` is parsed as:
- `"safe"` → `.safe`
- `"unsafe"` → `.unsafe`
- `"partial"` → `.partial`

**Quot kind parsing.** The `kind` field of a `quot` is parsed as:
- `"type"` → `.type`
- `"ctor"` → `.ctor`
- `"lift"` → `.lift`
- `"ind"` → `.ind`

**Recursor rules.** Each entry in the `rules` array of a `rec` is decoded as:
`{"ctor": <name index>, "nfields": <nat>, "rhs": <expr index>}`

---

## Examples

### Minimal theorem

```json
["header", {"mainModule": 0, "source": "example.lean", "imports": []}]
["in", 0, {"str": "MyThm", "pre": 0}]
["il", 0, {"param": 0}]
["ie", 0, {"const": {"name": 0, "us": []}}]
["ie", 1, {"sort": 0}]
["ie", 2, {"forallE": {"name": 0, "type": 1, "body": 3, "binderInfo": "default"}}]
["ie", 3, {"app": [2, 0]}]
["footer", {}]
{"thm": {"name": 0, "levelParams": [], "type": 1, "value": 3, "all": []}}
```

### Minimal axiom

```json
["header", {"mainModule": 0, "source": "example.lean", "imports": [1]}]
["in", 0, {"str": "MyAxiom", "pre": 0}]
["in", 1, {"str": "Init", "pre": 0}]
["il", 0, {"param": 1}]
["ie", 0, {"const": {"name": 0, "us": []}}]
["footer", {}]
{"axiom": {"name": 0, "levelParams": [], "type": 0, "isUnsafe": false}}
```

### Definition with hints and safety

```json
["header", {"mainModule": 0, "source": "example.lean", "imports": []}]
["in", 0, {"str": "MyDef", "pre": 0}]
["il", 0, {"param": 0}]
["ie", 0, {"const": {"name": 0, "us": []}}]
["ie", 1, {"sort": 0}]
["ie", 2, {"lam": {"name": 0, "type": 1, "body": 0, "binderInfo": "default"}}]
["footer", {}]
{"def": {"name": 0, "levelParams": [], "type": 1, "value": 2, "hints": "abbrev", "safety": "safe", "all": []}}
```

### Opaque constant

```json
{"opaque": {"name": 0, "levelParams": [], "type": 0, "value": 1, "all": [], "isUnsafe": true}}
```

### Quotient type

```json
{"quot": {"name": 0, "levelParams": [], "type": 1, "kind": "type"}}
```

### Inductive type with constructor and recursor

```json
{"inductive": {
  "types": [{
    "name": 0,
    "levelParams": [],
    "type": 1,
    "numParams": 1,
    "numIndices": 0,
    "all": [],
    "ctors": [1],
    "numNested": 0,
    "isRec": true,
    "isUnsafe": false,
    "isReflexive": false
  }],
  "ctors": [{
    "name": 1,
    "levelParams": [],
    "type": 2,
    "induct": 0,
    "cidx": 0,
    "numParams": 1,
    "numFields": 1,
    "isUnsafe": false
  }],
  "recs": [{
    "name": 2,
    "levelParams": [],
    "type": 3,
    "all": [],
    "numParams": 1,
    "numIndices": 0,
    "numMotives": 1,
    "numMinors": 1,
    "k": false,
    "rules": [{"ctor": 1, "nfields": 1, "rhs": 4}],
    "isUnsafe": false
  }]
}}
```

---

## Reference

- Reference implementation: `Lean4Lean/Replay.lean` in the lean4lean repo
- Parser: `test-printer/TestPrinter/NdjsonParser.lean` in lean-kernel-arena
- Lean 4 kernel export format: `Lean.Data.Json` + `Lean.Environment`
- Lean 4 kernel types: `Lean.Declaration`, `Lean.ConstantInfo`, `Lean.Expr`, `Lean.Level`

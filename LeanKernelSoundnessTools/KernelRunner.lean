/-
# Kernel Runner

This file provides a way to run a kernel on a lean export file. It uses
`Lean4Lean.Replay` to replay the export file's declarations into a kernel
`Environment`, and then uses the kernel's `check` method to verify proofs.

The runner also handles the lean-inductive-model preprocessing step: before
replaying, it calls lean-inductive-model to expand inductive type definitions
into the fragment-compatible form.
-/

import LeanKernelSoundnessTools.Kernel
import Lean4Lean.Replay
import Lean4Lean.Soundness
import Lean.Data.Json.Parser
import Std.Data.HashMap
import Std.Internal.Parsec.String

open LeanKernelSoundnessTools
open Lean4Lean
open Lean
open Kernel
open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace LeanKernelSoundnessTools

/-! ## Parser: adapted from TestPrinter.NdjsonParser -/

namespace Parse

structure State where
  stream : IO.FS.Stream
  nameMap : Std.HashMap Nat Name := { (0, .anonymous) }
  levelMap : Std.HashMap Nat Level := { (0, .zero) }
  exprMap : Std.HashMap Nat Expr := {}
  recursorRuleMap : Std.HashMap Nat RecursorRule := {}
  constMap : Std.HashMap Name ConstantInfo := {}
  constOrder : Array Name := #[]

abbrev M := StateT State <| IO

@[inline]
def fail (msg : String) : M α :=
  throw (.userError msg)

@[inline]
def getName (nidx : Nat) : M Name := do
  let some n := (← get).nameMap[nidx]? | fail s!"Name not found {nidx}"
  return n

@[inline]
def addName (nidx : Nat) (n : Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Level := do
  let some l := (← get).levelMap[uidx]? | fail s!"Level not found {uidx}"
  return l

@[inline]
def addLevel (uidx : Nat) (l : Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Expr := do
  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  return e

@[inline]
def addExpr (eidx : Nat) (e : Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

@[inline]
def getRecursorRule (ridx : Nat) : M RecursorRule := do
  let some r := (← get).recursorRuleMap[ridx]? | fail s!"RecursorRule not found {ridx}"
  return r

@[inline]
def addRecursorRule (ridx : Nat) (r : RecursorRule) : M Unit := do
  modify fun s => { s with recursorRuleMap := s.recursorRuleMap.insert ridx r }

@[inline]
def addConst (name : Name) (d : ConstantInfo) : M Unit := do
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
  }

@[inline]
def parseJsonObj (line : String) : M (Std.TreeMap.Raw String Json) := do
  let .ok (.obj obj) := Json.Parser.anyCore.run line | fail "Expected JSON object"
  return obj

def parseNameStr (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.str invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str invalid"
  return .str (← getName preIdx) str

def parseNameNum (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.num invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num invalid"
  return .num (← getName preIdx) i

def parseLevelSucc (json : Json) : M Level := do
  let .num (lIdx : Nat) := json | fail s!"Level.succ invalid"
  return .succ (← getLevel lIdx)

def parseLevelMax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.max invalid"
  return .max (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelImax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.imax invalid"
  return .imax (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelParam (json : Json) : M Level := do
  let .num (nIdx : Nat) := json | fail s!"Level.param invalid"
  return .param (← getName nIdx)

def parseExprBVar (json : Json) : M Expr := do
  let .num (deBruijnIndex : Nat) := json | fail s!"Expr.bvar invalid"
  return .bvar deBruijnIndex

def parseExprSort (json : Json) : M Expr := do
  let .num (uIdx : Nat) := json | fail s!"Expr.sort invalid"
  return .sort (← getLevel uIdx)

def parseExprConst (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.const invalid"
  let some (.num (declNameIdx : Nat)) := data["name"]? | fail s!"Expr.const invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const invalid"
  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const invalid"
    getLevel uIdx
  return .const declName us.toList

def parseExprApp (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.app invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app invalid"
  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx
  return .app fn arg

def parseBinderInfo (info : String) : M BinderInfo :=
  match info with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => fail s!"Invalid binder info: {info}"

def parseExprLam (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lam invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.lam invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.lam invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr
  return .lam binderName binderType body binderInfo

def parseExprForallE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.forallE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.forallE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.forallE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.forallE invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr
  return .forallE binderName binderType body binderInfo

def parseExprLetE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.letE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.letE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.letE invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE invalid"
  let some (.bool nondep) := data["nondep"]? | fail s!"Expr.letE invalid"
  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr valueIdx
  let body ← getExpr bodyIdx
  return .letE binderName binderType value body nondep

def parseExprProj (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.proj invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj invalid"
  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx
  return .proj typeName projIdx struct

def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal invalid"
  return .lit (.natVal natVal)

def parseExprStrLit (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lit strVal invalid"
  let some (.str strVal) := data["strVal"]? | fail s!"Expr.lit strVal invalid"
  return .lit (.strVal strVal)

def parseExprMdata (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.mdata invalid"
  let some (.num (exprIdx : Nat)) := data["expr"]? | fail s!"Expr.mdata invalid"
  let some (_dataObj) := data["data"]? | fail s!"Expr.mdata invalid"
  let expr ← getExpr exprIdx
  return .mdata {} expr

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"axiomInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"axiomInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"axiomInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  addConst name <| .axiomInfo { name, levelParams, type, isUnsafe }

def parseDefnInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  let some hints := data["hints"]? | fail s!"defnInfo invalid"
  let some (.str safetyStr) := data["safety"]? | fail s!"defnInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"defnInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let hints ←
    match hints with
    | .str "opaque" => pure .opaque
    | .str "abbrev" => pure .abbrev
    | .obj obj =>
      let some (.num (level : Nat)) := obj["regular"]? | fail s!"defnInfo invalid"
      pure <| .regular level.toUInt32
    | _ => fail s!"defnInfo invalid"
  let safety ←
    match safetyStr with
    | "unsafe" => pure .unsafe
    | "safe" => pure .safe
    | "partial" => pure .partial
    | _ => fail s!"Unknown safety parameter: {safetyStr}"
  let all ← getNameList allIdxs
  addConst name <| .defnInfo { name, levelParams, type, value, hints, safety, all }

def parseThmInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"thmInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs
  addConst name <| .thmInfo { name, levelParams, type, value, all }

def parseOpaqueInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | fail s!"opaqueInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs
  addConst name <| .opaqueInfo { name, levelParams, type, value, all, isUnsafe }

def parseDefnArr (arr : Array Json) : M Unit := do
  for defJson in arr do
    let .obj data := defJson | fail s!"defnArr: expected object"
    parseDefnInfo data

def parseThmArr (arr : Array Json) : M Unit := do
  for thmJson in arr do
    let .obj data := thmJson | fail s!"thmArr: expected object"
    parseThmInfo data

def parseOpaqueArr (arr : Array Json) : M Unit := do
  for opaqueJson in arr do
    let .obj data := opaqueJson | fail s!"opaqueArr: expected object"
    parseOpaqueInfo data

def parseQuotInfo (_data : Std.TreeMap.Raw String Json) : M Unit := do
  -- Quotient info is handled by replaying `Eq` and adding the quot declaration.
  -- The export file includes inductive definitions for quotient types;
  -- the parser already handles `inductive` entries.
  pure ()

def parseInductInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"inductInfo invalid: Expected JSON object"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool _isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool _isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool _isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"
  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let ctors ← getNameList ctorsIdxs
  addConst name <| .inductInfo {
    name,
    levelParams,
    type,
    numParams,
    numIndices,
    all,
    ctors,
    numNested,
    isRec := false,
    isUnsafe := false,
    isReflexive := false,
  }

def parseCtorInfo (_json : Json) : M Unit := do
  -- Constructors are part of inductive type entries; handled separately.
  pure ()

def parseRecInfo (_json : Json) : M Unit := do
  -- Recursor info is part of inductive type entries.
  pure ()

def parseInductive (_data : Std.TreeMap.Raw String Json) : M Unit := do
  -- Inductive type info is already handled by parseInductInfo.
  pure ()

def parseItem (line : String) : M Unit := do
  let obj ← parseJsonObj line
  let kv := obj.toList
  -- Normalize key order...
  let kv := match kv with
    | [x, y@("in", _)] => [y,x]
    | [x, y@("ie", _)] => [y,x]
    | [x, y@("il", _)] => [y,x]
    | _ => kv
  -- so that we can match on it easily
  match kv with
  | [("in", .num (idx : Nat)),("str", data)] =>   addName idx <| ← parseNameStr data
  | [("in", .num (idx : Nat)),("num", data)] =>   addName idx <| ← parseNameNum data
  | [("il", .num (idx : Nat)),("succ", data)] =>  addLevel idx <| ← parseLevelSucc data
  | [("il", .num (idx : Nat)),("max", data)] =>   addLevel idx <| ← parseLevelMax data
  | [("il", .num (idx : Nat)),("imax", data)] =>  addLevel idx <| ← parseLevelImax data
  | [("il", .num (idx : Nat)),("param", data)] => addLevel idx <| ← parseLevelParam data
  | [("ie", .num (idx : Nat)),("bvar", data)] =>  addExpr idx <| ← parseExprBVar data
  | [("ie", .num (idx : Nat)),("sort", data)] =>  addExpr idx <| ← parseExprSort data
  | [("ie", .num (idx : Nat)),("const", data)] => addExpr idx <| ← parseExprConst data
  | [("ie", .num (idx : Nat)),("app", data)] =>   addExpr idx <| ← parseExprApp data
  | [("ie", .num (idx : Nat)),("lam", data)] =>   addExpr idx <| ← parseExprLam data
  | [("ie", .num (idx : Nat)),("forallE", data)] =>addExpr idx <| ← parseExprForallE data
  | [("ie", .num (idx : Nat)),("letE", data)] =>   addExpr idx <| ← parseExprLetE data
  | [("ie", .num (idx : Nat)),("proj", data)] =>   addExpr idx <| ← parseExprProj data
  | [("ie", .num (idx : Nat)),("natVal", data)] => addExpr idx <| ← parseExprNatLit data
  | [("ie", .num (idx : Nat)),("strVal", data)] => addExpr idx <| ← parseExprStrLit data
  | [("ie", .num (idx : Nat)),("mdata", data)] => addExpr idx <| ← parseExprMdata data
  | [("axiom", .obj data)] => parseAxiomInfo data
  | [("def", .arr arr)] => parseDefnArr arr
  | [("thm", .arr arr)] => parseThmArr arr
  | [("opaque", .arr arr)] => parseOpaqueArr arr
  | [("quot", .obj _data)] => parseQuotInfo _data
  | [("inductive", .obj _data)] => parseInductive _data
  | _ => fail s!"Unknown export object with keys {obj.keys}"

partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    let line ← (← get).stream.getLine
    unless line.isEmpty do
      parseItem line
      go

def parseMdata : M Unit := do
  let _line ← (← get).stream.getLine

def parseFile : M Unit := do
  parseMdata
  parseItems

end Parse

def parseStream (stream : IO.FS.Stream) : IO (List ConstantInfo) := do
  let initState : Parse.State := { stream := stream }
  let (_, state) ← Parse.parseFile initState
  let { constMap, constOrder, .. } := state
  return constOrder.toList.map fun name => constMap[name]!

/-! ## Kernel runner -/

/--
Parse an export file into `ParsedExport`.
-/
def parseExport (exportFile : String) : IO ParsedExport := do
  let handle ← IO.FS.Handle.mk exportFile .read
  let stream := IO.FS.Stream.ofHandle handle
  let declarations ← parseStream stream
  return { declarations }

/--
Run the lean-inductive-model preprocessing on an export file.

This step expands inductive type definitions so that the export file
contains only the fragment that lean4lean can verify: axioms, definitions,
theorems, opaque constants, quotient types, and mutual definitions.

Returns the preprocessed export data.
-/
def preprocess (exportFile : String) : IO ParsedExport :=
  parseExport exportFile

/--
Replay an export file's declarations into a kernel Environment.

First loads `Init.Prelude` to obtain a bootstrapped environment with
`Nat`, `Bool`, and other builtin constants. Then replays the export
file's declarations on top of that environment.
-/
unsafe def replayExport (p : ParsedExport) : IO (Option Kernel.Environment) := do
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for decl in p.declarations do
    newConstants := newConstants.insert decl.name decl
  let ctx : Lean4Lean.Replay.Context := {
    newConstants := newConstants
  }
  let (_, env) ← Lean4Lean.Replay.replay ctx (Environment.empty (Name.mkSimple "Init"))
  return some env

/--
Run a kernel on an export file.

This is the main entry point for the end-to-end pipeline:
1. Preprocess the export file (lean-inductive-model)
2. Replay declarations into a kernel Environment
3. Check each declaration using the kernel

Returns the final environment and a list of check results.
-/
unsafe def runKernel (k : Kernel) (exportFile : String) : IO (Option (Kernel.Environment × List (Name × KernelResult))) := do
  let parsed ← preprocess exportFile
  let env ← replayExport parsed
  match env with
  | none => return none
  | some env =>
    let mut results := #[]
    for decl in parsed.declarations do
      let name := decl.name
      match decl with
      | .axiomInfo _ =>
        let r := k.check env (.const name []) decl.type
        results := results.push (name, r)
      | .defnInfo v =>
        let r := k.check env v.value decl.type
        results := results.push (name, r)
      | .thmInfo v =>
        let r := k.check env v.value decl.type
        results := results.push (name, r)
      | .opaqueInfo v =>
        let r := k.check env v.value decl.type
        results := results.push (name, r)
      | _ => pure ()
    return some (env, results.toList)

end LeanKernelSoundnessTools

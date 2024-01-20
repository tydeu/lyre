/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lyre.Grammar
import Lean.Compiler.IR.Basic
import Lean.Elab.Eval

/-! # IR Builder

Defines the `BuilderM` monad, which is used to convert IR syntax
parsed from Lyre's IR Grammar into Lean IR objects.
-/

open Lean IR Elab

namespace Lyre

abbrev Ty := TSyntax `irType
abbrev Expr := TSyntax `irExpr
abbrev Stmt := TSyntax `irStmt
abbrev Decl := TSyntax `irDecl

abbrev Arg := TSyntax ``arg
abbrev Param := TSyntax ``param
abbrev CtorInfo := TSyntax ``ctorInfo
abbrev CtorInfoIdx := TSyntax ``ctorInfoIdx
abbrev Alt := TSyntax ``alt
abbrev StmtSeq := TSyntax ``stmtSeq
abbrev ExternEntry := TSyntax ``Parser.Attr.externEntry
abbrev MDataVal := TSyntax ``mdataVal

inductive Var
| vdecl (id : VarId) (ty : IRType) (val : IR.Expr)
| param (id : VarId) (ty : IRType)

@[inline] def Var.mk (id : VarId) (ty : IRType) (val? : Option IR.Expr := none) : Var :=
  match val? with
  | some val => .vdecl id ty val
  | none => .param id ty

@[inline] def Var.id : Var → VarId
| .vdecl id .. | .param id .. => id

@[inline] def Var.ty : Var → IRType
| .vdecl _ ty .. | .param _ ty .. => ty

structure JoinPoint where
  id : JoinPointId
  params : Array IR.Param
  body : FnBody
  ty? : Option IRType := none

structure BuilderScope where
  joinPoints : NameMap JoinPoint := {}
  vars : NameMap Var := {}

structure BuilderContext where
  parentScopes : Array BuilderScope := #[]

structure BuilderState where
  nextVarId : VarId := ⟨1⟩
  nextJoinPointId : JoinPointId := ⟨1⟩
  currScope : BuilderScope := {}

abbrev BuilderM :=
   ReaderT BuilderContext <| StateT BuilderState <| TermElabM

@[inline] nonrec def BuilderM.run (x : BuilderM α) : TermElabM α :=
  x.run {} |>.run' {}

def withNewScope (x : BuilderM α) : BuilderM α := do
  let oldScope ← modifyGet fun s => (s.currScope, {s with currScope := {}})
  try
    withReader (fun c => {c with parentScopes := c.parentScopes.push oldScope}) x
  finally
    modify ({· with currScope := oldScope})

@[inline] def newJoinPoint (name : Name) (ps : Array IR.Param) (b : FnBody) (ty? : Option IRType := none) : BuilderM JoinPointId := modifyGet fun s =>
  let jp := JoinPoint.mk s.nextJoinPointId ps b ty?
  let scope := {s.currScope with joinPoints := s.currScope.joinPoints.insert name jp}
  (jp.id, {s with nextJoinPointId := ⟨jp.id.idx + 1⟩, currScope := scope})

@[inline] def getJoinPoint? (name : Name) : BuilderM (Option JoinPoint) := do
  return (← get).currScope.joinPoints.find? name <|> (← read).parentScopes.findSome? (·.joinPoints.find? name)

@[inline] def getJoinPoint (id : Ident) : BuilderM JoinPoint := do
  match (← getJoinPoint? id.getId) with
  | some j => return j
  | none => throw <| .error id s!"unknown IR join point '{id.getId}'"

@[inline] def getJoinPointId (id : Ident) : BuilderM JoinPointId := do
  return (← getJoinPoint id).id

@[inline] def newVar (name : Name) (ty : IRType) (val? : Option IR.Expr := none) : BuilderM VarId := modifyGet fun s =>
  let v := Var.mk s.nextVarId ty val?
  let scope := {s.currScope with vars := s.currScope.vars.insert name v}
  (v.id, {s with nextVarId := ⟨v.id.idx + 1⟩, currScope := scope})

@[inline] def getVar? (name : Name) : BuilderM (Option Var) := do
  return (← get).currScope.vars.find? name <|> (← read).parentScopes.findSome? (·.vars.find? name)

@[inline]  def getVar (id : Ident) : BuilderM Var := do
  match (← getVar? id.getId) with
  | some v => return v
  | none => throw <| .error id s!"unknown IR variable '{id.getId}'"

@[inline] def getVarId (id : Ident) : BuilderM VarId := do
  return (← getVar id).id

partial def mkType (ty : Ty) : BuilderM IRType :=
  match ty with
  | `(irType|float) => return .float
  | `(irType|u8)    => return .uint8
  | `(irType|u16)   => return .uint16
  | `(irType|u32)   => return .uint32
  | `(irType|u64)   => return .uint64
  | `(irType|usize) => return .usize
  | `(irType|◾)     => return .irrelevant
  | `(irType|obj)   => return .object
  | `(irType|tobj)  => return .tobject
  | `(irType|struct $(id?)? {$tys,*}) =>
    return .struct (id?.map (·.getId)) (← tys.getElems.mapM mkType)
  | `(irType|union $(id?)? {$tys,*})  =>
    return .union (id?.map (·.getId) |>.getD .anonymous) (← tys.getElems.mapM mkType)
  | ty => throwIllFormedSyntax ty "IR type"

def mkParam (stx : Lyre.Param) : BuilderM IR.Param := do
  match stx with
  | `(param|($id : $[@&%$b?]? $ty)) =>
    let ty ← mkType ty
    return {x := ← newVar id.getId ty, borrow := b?.isSome, ty}
  | _ => throwIllFormedSyntax stx "IR parameter"

def mkArg (stx : Lyre.Arg) : BuilderM IR.Arg := do
  match stx with
  | `(arg|◾) => return .irrelevant
  | `(arg|$id:ident) => .var <$> getVarId id
  | _ => throwIllFormedSyntax stx "IR argument"

def mkArgAndType (stx : Lyre.Arg) : BuilderM (IR.Arg × IRType) := do
  match stx with
  | `(arg|◾) => return (.irrelevant, .irrelevant)
  | `(arg|$id:ident) => let var ← getVar id; return (.var var.id, var.ty)
  | _ => throwIllFormedSyntax stx "IR argument"

def extractCIdx? (ctor : Ident) : Option Nat := do
  let .str .anonymous c := ctor.getId | failure
  unless c.startsWith "ctor_" do failure
  c.drop 5 |>.toNat?

def mkCtor (stx : Lyre.CtorInfo) (argStxs : Array Lyre.Arg) : BuilderM (IR.CtorInfo × Array IR.Arg) := do
  let `(ctorInfo|$ctor$[.$usize?.$ssize?]?$[[$id?]]?) := stx
    | throwIllFormedSyntax stx "IR constructor"
  let name := id?.map (·.getId) |>.getD .anonymous
  let some cidx := extractCIdx? ctor
    | throw <| .error ctor s!"ill-formed IR constructor name '{ctor.getId}'"
  if let some id := id? then
    let name ← resolveGlobalConstNoOverloadWithInfo id
    let some (.ctorInfo {cidx := ecidx, ..}) := (← getEnv).find? name
      | throwWithSyntax (ref := id) stx m!"'{name}' is not a constructor"
    if cidx != ecidx then
      throwWithSyntax stx m!"constructor tag mismatch: constructor '{id.getId}' is expected to be 'ctor_{ecidx}'"
  let args : Array IR.Arg := Array.mkEmpty argStxs.size
  let info : IR.CtorInfo := {name, cidx, size := 0, usize := 0, ssize := 0}
  let (args, info) ← argStxs.foldlM (init := (args, info)) fun (args, info) stx => do
    match stx with
    | `(arg|◾) => return (args.push .irrelevant, info)
    | `(arg|$id:ident) =>
      let var ← getVar id
      let info :=
        match var.ty with
        | .uint8 => {info with usize := info.ssize+1}
        | .uint16 => {info with usize := info.ssize+2}
        | .uint32 => {info with usize := info.ssize+4}
        | .float | .uint64 => {info with usize := info.ssize+8}
        | .usize => {info with usize := info.usize+1}
        | .object | .tobject => {info with size:= info.size+1}
        | _ => info
      return (args.push (.var var.id), info)
    | _ => throwIllFormedSyntax stx "IR argument"
  if let some usizeStx := usize? then
    let usize := usizeStx.raw[0].isFieldIdx?.getD 0
    if usize != info.usize then
      let stx := Unhygienic.run `(ctor|$stx $argStxs*)
      throwWithSyntax (ref := usizeStx) stx m!"constructor info mismatch: constructor has {info.usize} usize argument(s), but is expected to have {usize}"
  if let some ssizeStx := ssize? then
    let ssize := ssizeStx.raw[0].isFieldIdx?.getD 0
    if ssize != info.ssize then
      let stx := Unhygienic.run `(ctor|$stx $argStxs*)
      throwWithSyntax (ref := ssizeStx) stx m!"constructor info mismatch: constructor has {info.ssize} bytes of scalar argument(s), but is expected to have {ssize}"
  return (info, args)

def mkExpr (stx : Lyre.Expr) : BuilderM (IR.Expr × Option IRType) := do
  match stx with
  | `(ctor|$i:ctorInfo $ys*) =>
    let (info, args) ← mkCtor i ys
    let ty := if info.size > 0 then .object else .uint8
    return (.ctor info args, some ty)
  | `(irExpr|reset[$n] $x) =>
    return (.reset n.getNat (← getVarId x), some .object)
  | `(irExpr|reuse $x in $i $ys*) =>
    let (info, args) ← mkCtor i ys
    return (.reuse (← getVarId x) info false args, some .object)
  | `(irExpr|reuse! $x in $i $ys*) =>
    let (info, args) ← mkCtor i ys
    return (.reuse (← getVarId x) info true args, some .object)
  | `(irExpr|proj[$i] $x) =>
    return (.proj i.getNat (← getVarId x), some .object)
  | `(irExpr|uproj[$i] $x) =>
    return (.uproj i.getNat (← getVarId x), some .usize)
  | `(irExpr|sproj[$n,$o] $x $[: $ty?]?) =>
    return (.sproj n.getNat o.getNat (← getVarId x), ← ty?.mapM mkType)
  | `(fap|$c:ident $ys*) =>
    let some decl := IR.findEnvDecl (← getEnv) c.getId
      | throw <| .error c s!"unknown IR constant '{c.getId}'"
    try discard <| resolveGlobalConstNoOverloadWithInfo c catch _ => pure ()
    let ty := match decl with
      | .fdecl (type := ty) .. | .extern (type := ty) .. => ty
    return (.fap c.getId (← ys.mapM mkArg), some ty)
  | `(irExpr|pap $c $ys*) =>
    return (.pap c.getId (← ys.mapM mkArg), some .object)
  | `(irExpr|app $x $ys*) =>
    return (.ap (← getVarId x) (← ys.mapM mkArg), none)
  | `(irExpr|box $x) =>
    let var ← getVar x
    return (.box var.ty var.id, some .object)
  | `(irExpr|unbox $x $[: $ty?]?) =>
    return (.unbox (← getVarId x), ← ty?.mapM mkType)
  | `(irExpr|$n:num $[: $ty?]?) =>
    return (.lit <| .num n.getNat, ← ty?.mapM mkType)
  | `(irExpr|$s:str) =>
    return (.lit <| .str s.getString, some .object)
  | `(irExpr|isShared $x) =>
    return (.isShared (← getVarId x), some .uint8)
  | _ =>
    throwIllFormedSyntax stx "IR expression"

def expectType? (name : Name) (inferred? : Option IRType) (expected? : Option Ty) : BuilderM (Option IRType) := do
  let some ty := expected? | return inferred?
  let ety ← mkType ty
  let some ity := inferred? | return some ety
  unless ity == ety do
    throw <| .error ty m!"type mismatch: '{name}' has type '{ity}' but is expected to have type '{ty}'"
  return some ety

@[implemented_by Term.evalTerm]
opaque evalTerm (α) (type : Lean.Expr) (value : Syntax) (safety := DefinitionSafety.safe) : TermElabM α

def elabMDataVal (stx: MDataVal) : BuilderM IR.MData := do
  match stx with
  | `(mdataVal|$ $val) => evalTerm KVMap (mkConst ``KVMap) val
  | `(mdataVal|[$kvps,*]) => kvps.getElems.foldlM (init := KVMap.empty) fun m kv => do
    let `(kvpair|$key := $val) := kv
      | throwIllFormedSyntax stx "metadata key-value pair"
    return m.insert key.getId (← evalTerm DataValue (mkConst ``DataValue) val)
  | _ => throwIllFormedSyntax stx "metadata value"

section end

mutual

partial def initStmtIds (stx : Stmt) : BuilderM Unit := do
  match stx with
  | `(irStmt|let $x $[: $ty?]? := $e) =>
    let (val, ity?) ← mkExpr e
    let some ty ← expectType? x.getId ity? ty?
      | throw <| .error x s!"cannot infer type for '{x.getId}'"
    discard <| newVar x.getId ty val
  | `(irStmt|$j:ident $ps* $[: $ty?]? := $stmts*) =>
    let (ps, body, ty?) ← withNewScope do
      let ps ← ps.mapM mkParam
      let (body, bty?) ← mkFnBody stmts
      let ty? ← expectType? j.getId bty? ty?
      return (ps, body, ty?)
    discard <| newJoinPoint j.getId ps body ty?
  | _ => pure ()


partial def mkAlt (stx : Lyre.Alt) : BuilderM (IR.Alt × Option IRType) := do
  match stx with
  | `(alt|$id:ident → $stmts*) =>
    -- NOTE: We dummy out the sizes in the ctor here
    -- because they are not used by the core emitters
    -- and we do not have the relevant information.
    let some (.ctorInfo {cidx, ..}) := (← getEnv).find? id.getId
      | throw <| .error id s!"unknown constructor '{id.getId}'"
    let info := {name := id.getId, cidx, size := 0, usize := 0, ssize := 0}
    let (body, ty?) ← mkFnBody stmts
    return (.ctor info body, ty?)
  | `(alt|default → $stmts*) =>
    let (body, ty?) ← mkFnBody stmts
    return (.default body, ty?)
  | _ => throwIllFormedSyntax stx "IR case alternative"

partial def mkAlts (stxs : Array Lyre.Alt) : BuilderM (Array IR.Alt × Option IRType) := do
  stxs.foldlM (init := (Array.mkEmpty stxs.size, none)) fun (alts, ty?) stx => do
    let (alt, aty?) ← mkAlt stx
    let ty? ← id do
      let some ty := ty? | return aty?
      let some aty := aty? | return ty?
      unless aty == ty do
        throw <| .error stx m!"type mismatch:{indentD stx}\nhas type '{aty}' but is expected to have type '{ty}'"
      return some ty
    return (alts.push alt, ty?)

-- Precondition: top-level Var/JoinPoint ids are already declared
partial def mkControlStmt (stx : Stmt) : BuilderM (FnBody × Option IRType) := do
  match stx with
  | `(irStmt|case $[[$tid?]]? $x $[: $ty?]? of $cs*) =>
    let var ← getVar x
    if let some ty := ty? then
      let ety ← mkType ty
      unless ety == var.ty do
        throw <| .error ty m!"type mismatch: '{x.getId}' has type '{var.ty}' but is expected to have type '{ety}'"
    let tid := tid?.map (·.getId) |>.getD .anonymous
    let (alts, ty?) ← mkAlts cs
    return (.case tid var.id var.ty alts, ty?)
  | `(irStmt|jmp%$tk $j $ys*) =>
    let jp ← getJoinPoint j
    if ys.size != jp.params.size then
      throwWithSyntax (ref := tk) stx m!"incorrect number of arguments: '{j.getId}' has {jp.params.size} parameter(s), but {ys.size} argument(s) were provided"
    let args ← (jp.params.zip ys).mapM fun (param, argStx) => do
      let (arg, ty) ← mkArgAndType argStx
      unless ty == param.ty do
        throwWithSyntax (ref := argStx) stx m!"type mismatch: '{argStx}' has type '{ty}' but is expected to have type '{param.ty}'"
      return arg
    return (.jmp jp.id args, jp.ty?)
  | `(irStmt|ret $x) =>
    let (id, ty) ← mkArgAndType x
    return (.ret id, some ty)
  | `(irStmt|⊥) =>
    return (.unreachable, none)
  | _ => throwWithSyntax stx m!"invalid terminal statement"

-- Precondition: top-level Var/JoinPoint ids are already declared
partial def prependStmt (stx : Stmt) (b : FnBody) : BuilderM FnBody := do
  match stx with
  | `(irStmt|let $x $[: $_]? := $_) =>
    let some (.vdecl x ty e) ← getVar? x.getId
      | throw <| .error x s!"(internal) variable '{x.getId}' not pre-declared"
    return .vdecl x ty e b
  | `(irStmt|$j:ident $_* $[: $_]? := $_*) =>
    let some j ← getJoinPoint? j.getId
      | throw <| .error j s!"(internal) join point '{j.getId}' not pre-declared"
    return .jdecl j.id j.params j.body b
  | `(irStmt|set $x[$i] := $y) =>
    return .set (← getVarId x) i.getNat (← mkArg y) b
  | `(irStmt|uset $x[$i] := $y) =>
    return .uset (← getVarId x) i.getNat (← getVarId y) b
  | `(irStmt|sset $x[$i,$o] : $ty := $y) =>
    return .sset (← getVarId x) i.getNat o.getNat (← getVarId y) (← mkType ty) b
  | `(irStmt|setTag $x:ident := $cidx) =>
    return .setTag (← getVarId x) cidx.getNat b
  | `(irStmt|inc $[persistent%$p?]? $[ref%$r?]? $[[$n?]]? $x) =>
    let n := n?.map (·.getNat) |>.getD 1
    return .inc (← getVarId x) n r?.isNone p?.isSome b
  | `(irStmt|dec $[persistent%$p?]? $[ref%$r?]? $[[$n?]]? $x) =>
    let n := n?.map (·.getNat) |>.getD 1
    return .dec (← getVarId x) n r?.isNone p?.isSome b
  | `(irStmt|del $x) =>
    return .del (← getVarId x) b
  | `(irStmt|mdata $d) =>
    return .mdata (← elabMDataVal d) b
  | `(irStmt|case $[[$_]]? $_ $[: $_]? of $_*) | `(irStmt|jmp $_ $_*) | `(irStmt|ret $_) | `(irStmt|⊥) =>
    throwWithSyntax stx m!"control statement must be the last statement in a function body"
  | _ => throwIllFormedSyntax stx "IR statement"

partial def mkFnBody (stmts : Array Stmt) : BuilderM (FnBody × Option IRType) := do
  stmts.forM initStmtIds
  let (stmt, ty?) ← mkControlStmt stmts.back
  let body ← stmts.foldrM prependStmt stmt (start := stmts.size - 1)
  return (body, ty?)

end

open Lean.Parser.Attr in
def mkExternEntries (entriesStx : Array Lyre.ExternEntry) : BuilderM (List Lean.ExternEntry) := do
  if entriesStx.size == 0 then
    return [ .adhoc `all ]
  let entries ← entriesStx.foldrM (init := []) fun stx entries => do
    match stx with
    | `(externEntry|$[$backend?]? $[inline%$inline?]? $str) =>
      let backend := backend?.map (·.getId) |>.getD `all
      let entry :=
        if inline?.isSome then
          .inline backend str.getString
        else
          .standard backend str.getString
      return entry :: entries
    | _ => throwIllFormedSyntax stx "extern entry"
  return entries

def mkDecl (stx : Lyre.Decl) : BuilderM IR.Decl := do
  match stx with
  | `(irDecl|$[@$sorryDep?]? def $did $ps* $[: $ty?]? := $stmts*) =>
    let ps ← ps.mapM mkParam
    let (body, bty?) ← mkFnBody stmts
    let some ty ← expectType? did.getId bty? ty?
      | throw <| .error did s!"cannot infer type for '{did.getId}'"
    let sorryDep? := sorryDep?.map (·.getId)
    return .fdecl did.getId ps ty body {sorryDep?}
  | `(irDecl|extern $did $ps* : $ty $[:= $entries?*]?) =>
    let data ← id do
      if let some entries := entries? then
        return {entries := ← mkExternEntries entries}
      else
        return getExternAttrData? (← getEnv) did.getId |>.getD {entries := []}
    return .extern did.getId (← ps.mapM mkParam) (← mkType ty) data
  | _ => throwIllFormedSyntax stx "IR declaration"

/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Attr
import Lyre.Util.Grammar

/-! # IR Grammar

Syntax definitions which encode Lyre's IR Grammar.
The goal is to closely mirror the syntax printed by `toString`
on an Lean IR object (e.g., `Lean.IR.Decl`).
-/

namespace Lyre

/-! ## Constructors -/

section
open Lean Parser
def checkCtor :=
  checkStackTop (msg := "expected 'ctor_{n}'") fun stx =>
    match stx with
    | .ident _ rawVal _ _ => rawVal.toString.startsWith "ctor_"
    | _ => stx.isAntiquot

def ctorInfoIdx := leading_parser
  fieldIdx <|> rawCh '0'

syntax ctorInfo :=
  ident checkCtor
  (noWs "." noWs ctorInfoIdx noWs "." noWs ctorInfoIdx)?
  ("[" ident "]")?
end

/-! ## Types -/

declare_syntax_cat irType (behavior := symbol)

syntax float : irType := &"float"
syntax uint8 : irType := &"u8"
syntax uint16 : irType := &"u16"
syntax uint32 : irType := &"u32"
syntax uint64 : irType := &"u64"
syntax usize : irType := &"usize"
syntax irrelevant : irType := "◾"
syntax object : irType := &"obj"
syntax tobject : irType := &"tobj"
syntax struct : irType := &"struct " (ident)? "{" ppGroup(ppIndent((irType,*))) "}"
syntax union : irType := &"union " (ident)? "{" ppGroup(ppIndent((irType,*))) "}"

/-! ## Expressions -/

declare_syntax_cat irExpr (behavior := symbol)

syntax param := "(" ident  " : " "@& "? irType ")"
syntax arg := ident <|> "◾"

syntax ctor : irExpr := ctorInfo (colGt ppSpace arg)*
syntax reset : irExpr := &"reset" "[" num "] " ident
syntax reuse : irExpr :=
  (&"reuse" <|> &"reuse!"?) ppSpace ident " in " ctorInfo (colGt ppSpace arg)*
syntax proj : irExpr := &"proj" "[" num "] " ident
syntax uproj : irExpr := &"uproj" "[" num "] " ident
syntax sproj : irExpr := &"sproj" "[" num ", " num "] " ident (" : " irType)?
syntax fap : irExpr := ident (colGt arg)*
syntax pap : irExpr := &"pap " ident (colGt ppSpace arg)*
syntax ap : irExpr := &"app " ident (colGt ppSpace arg)*
syntax box : irExpr := &"box " ident
syntax unbox : irExpr := &"unbox " ident (" : " irType)?
syntax isShared : irExpr := &"isShared " ident

syntax strLit : irExpr := str
syntax numLit : irExpr := num (":" irType)?

/-! ## Statements -/

declare_syntax_cat irStmt (behavior := symbol)
syntax stmtSeq := sepBy1IndentSemicolon(irStmt)

syntax endSemi := ";"?
syntax ctorAlt := ident " →" ppIndent(stmtSeq)
syntax defaultAlt := &"default" " →" ppIndent(stmtSeq)
syntax alt := ctorAlt <|> defaultAlt

syntax kvpair := ident " := " term
syntax mdataVal := ("$" term:max) <|> ("[" kvpair,* "]")

syntax vdecl : irStmt := "let " ident (" : " irType)? " := " irExpr
syntax jdecl : irStmt := ident param* (" : " irType)? " :=" ppIndent(stmtSeq)
syntax set : irStmt := &"set " ident "[" num "] := " arg
syntax uset : irStmt := &"uset " ident "[" num "] := " ident
syntax sset : irStmt :=
  &"sset " ident "[" num ", " num "]" " : " irType " := " ident
syntax setTag : irStmt := &"setTag " ident " := " num
syntax inc : irStmt := &"inc" &"persistent"? &"ref"? ("[" num "]")? ident
syntax dec : irStmt := &"dec" &"persistent"? &"ref"? ("[" num "]")? ident
syntax del : irStmt := &"del " ident
syntax mdata : irStmt := &"mdata " mdataVal
syntax case : irStmt :=
  &"case " ("[" ident "]")? ident (" : " irType)?  &" of" many1Indent(ppLine alt)
syntax jmp : irStmt := &"jmp " ident (colGt ppSpace arg)*
syntax ret : irStmt := &"ret " arg
syntax unreachable : irStmt := "⊥"

/-! ## Declarations -/

declare_syntax_cat irDecl (behavior := symbol)

syntax funDecl : irDecl := ("@" ident ppLine)?
  "def " ident param* (" : " irType)? " :=" ppIndent(stmtSeq)

open Lean.Parser.Attr in
syntax externDecl : irDecl :=
  &"extern " ident param* " : " irType
  (" := " (ppSpace externEntry)+)?

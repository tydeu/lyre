/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lyre.Builder
import Lean.Compiler.IR

open Lean IR Elab Command

namespace Lyre

/--
Directly set the Lean IR for a the definition `name`.
The definition most not already have IR. This can be accomplish, e.g.,
by marked the definition `noncumptable` when declared.
-/
def setAdhoc [Monad m] [MonadEnv m] [MonadError m]
  (name : Name) (ps : Array IR.Param) (ty : IRType) (body : FnBody) (info : DeclInfo)
: m Unit := do
  let env ← getEnv
  if env.getModuleIdxFor? name |>.isSome then
    throwError "declaration is in an imported module"
  if IR.findEnvDecl env name |>.isSome then
    throwError "declaration already has an implementation"
  /-
  The `extern` attribute only supports `afterSet` on constructors
  and projections, so we manually extend this to normal definitions
  lacking an implementation (i.e., `noncomputable` definitions)
  -/
  let env := externAttr.ext.modifyState env fun s =>
    s.insert name {entries := [.adhoc `all]}
  let decl := .fdecl name ps ty body info
  let env := IR.declMapExt.addEntry env decl
  match IR.addBoxedVersion env decl with
  | .ok env => setEnv env
  | .error e => throwError s!"(compiler) {e}"

/--
Implement a definition directly with raw Lean IR.
The definition most not already have IR. This can be accomplish, e.g.,
by marked the definition `noncumptable` when declared.

**Example**

```
noncomputable def myAdd (m n : Nat) : Nat :=
  m + n

ir_impl myAdd (m : @& obj) (n : @& obj) :=
  let x := Nat.add m n
  ret x

#eval myAdd 1 2 -- 3
```
-/
scoped syntax "ir_impl " ident param* (" : " irType)? " := " stmtSeq : command

elab_rules : command | `(ir_impl $id $ps* $[: $ty?]? := $stmts*) => do
  let name ← resolveGlobalConstNoOverloadWithInfo id
  let (ps, ty, body) ← liftTermElabM <| BuilderM.run do
    let ps ← ps.mapM mkParam
    let (body, bty?) ← mkFnBody stmts
    let some ty ← expectType? id.getId bty? ty?
      | throw <| .error id s!"cannot infer type for '{id.getId}'"
    return (ps, ty, body)
  setAdhoc name ps ty body {}

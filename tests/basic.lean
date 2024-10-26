import Lyre
open scoped Lyre Lyre.Test

noncomputable def myAdd (m n : Nat) : Nat :=
  m + n

ir_impl myAdd (m : @& obj) (n : @& obj) :=
  let x := Nat.add m n
  ret x

/-- info: 3 -/
#guard_msgs in
#eval myAdd 1 2

noncomputable opaque getNum (_ : Unit) : Nat

ir_impl getNum (_ : obj) :=
  let n := 2 : obj
  ret n

/-- info: 2 -/
#guard_msgs in
#eval getNum ()

noncomputable opaque throwMyError : IO Unit

ir_impl throwMyError (w : obj) :=
  let msg := "myError"
  let err := IO.Error.userError msg
  let res := ctor_1[EStateM.Result.error] err w
  ret res

/-- info: error: myError -/
#guard_msgs in
#eval throwMyError.toBaseIO

noncomputable opaque getNil (α : Type u) : List α

ir_impl getNil (_ : ◾) :=
  let l : obj := List.nil
  ret l

/-- info: [] -/
#guard_msgs in
#eval getNil Nat

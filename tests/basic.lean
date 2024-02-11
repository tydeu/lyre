import Lyre
open scoped Lyre Lyre.Test

noncomputable def myAdd (m n : Nat) : Nat :=
  m + n

ir_impl myAdd (m : @& obj) (n : @& obj) :=
  let x := Nat.add m n
  ret x

#eval myAdd 1 2

noncomputable opaque getNum (_ : Unit) : Nat

ir_impl getNum (_ : obj) :=
  let n := 2 : obj
  ret n

#eval getNum ()

noncomputable opaque throwMyError : IO Unit

ir_impl throwMyError (w : obj) :=
  let msg := "myError"
  let err := IO.Error.userError msg
  let res := ctor_1[EStateM.Result.error] err w
  ret res

#eval throwMyError.toBaseIO

noncomputable opaque getNil (α : Type u) : List α

ir_impl getNil (_ : ◾) :=
  let l : obj := List.nil
  ret l

#eval getNil Nat

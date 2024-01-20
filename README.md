# Lyre

A library for writing Lean IR as Lean syntax.

**Example**

```lean
noncomputable def myAdd (m n : Nat) : Nat :=
  m + n

ir_impl myAdd (m : @& obj) (n : @& obj) :=
  let x := Nat.add m n
  ret x

#eval myAdd 1 2 -- 3
```

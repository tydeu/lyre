import Lake
open Lake DSL

package lyre

@[default_target]
lean_lib Lyre

def runLean (file : FilePath) : ScriptM PUnit := do
  let exitCode ← IO.Process.spawn {
    cmd := (← getLean).toString,
    args := #[file.toString],
    env := ← getAugmentedEnv
  } >>= (·.wait)
  if exitCode ≠ 0 then
    IO.Process.exit exitCode.toUInt8

@[test_driver]
script test do
  runLean <| "tests" / "basic.lean"
  return 0

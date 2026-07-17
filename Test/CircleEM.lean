import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def runCheck (name : String) (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDef d.tm d.ty with
    | .ok _ => "OK"
    | .error e => s!"FAIL: {e.toList.take 250 |> String.ofList}"
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {r}  ({(t1 - t0)} ms)"
  (← IO.getStdout).flush
def main : IO Unit := do
  defnCacheEnable
  IO.println "=== S¹ ≃ K(ℤ,1) checks ==="
  (← IO.getStdout).flush
  runCheck "toEM" toEMD
  runCheck "fromEM" fromEMD
  runCheck "invUnique" invUniqueD
  runCheck "emNegOne" emNegOneD
  runCheck "toIntLoop" toIntLoopD
  runCheck "toFrom" toFromD
  runCheck "s1EquivEM" s1EquivEMD
  runCheck "s1IsEM" s1IsEMD
  runCheck "fromTo" fromToD

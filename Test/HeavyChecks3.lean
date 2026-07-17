import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def runCheck (name : String) (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDef d.tm d.ty with
    | .ok _ => "OK"
    | .error e => s!"FAIL: {e.toList.take 200 |> String.ofList}"
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {r}  ({(t1 - t0)} ms)"
  (← IO.getStdout).flush
def main : IO Unit := do
  defnCacheEnable
  IO.println "=== heavy checks 3 (post junk-fix) ==="
  (← IO.getStdout).flush
  runCheck "codes" codesD
  runCheck "encodeEM" encodeEMD
  runCheck "encodeLoop" encodeLoopD
  runCheck "decodeEM" decodeEMD
  runCheck "decodeEncodeEM" decodeEncodeEMD
  runCheck "pi1EM1" pi1EM1D
  runCheck "isGroupoidS1" isGroupoidS1D
  runCheck "lGComp" lGCompD

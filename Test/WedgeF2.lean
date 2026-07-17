import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def chk (name : String) (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDef d.tm d.ty with
    | .ok _ => "OK" | .error e => s!"FAIL {(e.take 300).toString}"
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {r}  ({t1-t0} ms)"
  (← IO.getStdout).flush
def main : IO Unit := do
  defnCacheEnable
  IO.println "=== pi1(S1∨S1)=F2 checks ==="
  (← IO.getStdout).flush
  chk "windAll" windAllD
  chk "decodeAll" decodeAllD
  chk "decodeEncodeF2" decodeEncodeF2D
  chk "windGen" windGenD
  chk "transpCompW8" transpCompW8D
  chk "consGNoCancel" consGNoCancelD
  chk "encodeDecodeF2" encodeDecodeF2D
  chk "omegaW8F2Equiv" omegaW8F2EquivD
  chk "w8LoopIsF2" w8LoopIsF2D

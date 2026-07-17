import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def chk (name : String) (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDef d.tm d.ty with
    | .ok _ => "OK" | .error e => s!"FAIL {(e.take 200).toString}"
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {r}  ({t1-t0} ms)"
  (← IO.getStdout).flush
def main : IO Unit := do
  defnCacheEnable
  IO.println "=== dim-1 homotopy hypothesis checks ==="
  (← IO.getStdout).flush
  chk "loopRecCongEnc" loopRecCongEncD
  chk "loopRecRetr" loopRecRetrD
  chk "loopRecOmegaEquiv" loopRecOmegaEquivD
  chk "loopRecCongAll" loopRecCongAllD
  chk "loopRecFibBase" loopRecFibBaseD
  chk "loopRecEquiv" loopRecEquivD
  chk "homotopyHyp1" homotopyHyp1D

import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def chkCtx (u : List String × Ctx × List Val) (name : String)
    (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDefCtx u.1 u.2.1 u.2.2 d.tm d.ty with
    | .ok _ => "OK" | .error e => s!"FAIL {(e.take 120).toString}"
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {r} ({t1-t0} ms)"
  (← IO.getStdout).flush
def main (_args : List String) : IO Unit := do
  defnCacheEnable
  profEnable
  let _ ← IO.asTask (do
    for _ in [0:200] do
      IO.sleep 20000
      let c ← profRead
      IO.println s!"cutHit={c[6]!} cutMiss={c[7]!} transp={c[5]!}"
      (← IO.getStdout).flush)
  let t0 ← IO.monoMsNow
  let u := buildDefCtx allDefs
  let t1 ← IO.monoMsNow
  IO.println s!"ctx built: {u.1.length} defs ({t1-t0} ms)"
  (← IO.getStdout).flush
  chkCtx u "windAll" windAllD
  chkCtx u "decodeAll" decodeAllD
  chkCtx u "decodeEncodeF2" decodeEncodeF2D
  chkCtx u "windGen" windGenD
  chkCtx u "transpCompW8" transpCompW8D
  chkCtx u "consGNoCancel" consGNoCancelD
  chkCtx u "encodeDecodeF2" encodeDecodeF2D
  chkCtx u "omegaW8F2Equiv" omegaW8F2EquivD
  chkCtx u "w8LoopIsF2" w8LoopIsF2D

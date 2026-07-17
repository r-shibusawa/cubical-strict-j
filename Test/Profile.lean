import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library
def main : IO Unit := do
  IO.println "=== profile: uaCompMul ==="
  profEnable
  defnCacheEnable
  profReset
  let t0 ← IO.monoMsNow
  let r := match checkDef uaCompMulD.tm uaCompMulD.ty with
    | .ok _ => "OK" | .error _ => "FAIL"
  let t1 ← IO.monoMsNow
  let c ← profRead
  IO.println s!"{r} in {t1-t0} ms"
  IO.println s!"conv:   {c[0]!}"
  IO.println s!"capp:   {c[1]!}"
  IO.println s!"force:  {c[3]!}"
  IO.println s!"hcomp:  {c[4]!}"
  IO.println s!"transp: {c[5]!}"
  IO.println s!"cacheHit:  {c[6]!}"
  IO.println s!"cacheMiss: {c[7]!}"
  IO.println s!"cappHit:   {c[2]!}"

import FormalizedMathematics.Cubical.Library

/-! Native computation runner: the F₂-winding of composite loops on the
figure eight — including the non-abelian `LR ≠ RL` demonstration
(`lake exe windf2`). -/

open Cubical Cubical.Raw Cubical.Library

def w8T' : Raw := wedge .s1 .s1 .sbase .sbase
def w8b : Raw := .pinl .sbase
def w8r' : Raw := .pinr .sbase
def loopL' : Raw := .plam "i" (.pinl (.sloop (.var "i")))
def loopLinv' : Raw := .plam "i" (.pinl (.sloop (.ineg (.var "i"))))
def pushT' : Raw := .plam "i" (.ppush (.lam "u0" .sbase) (.lam "u0" .sbase) .tt (.var "i"))
def cW (a b c p q : Raw) : Raw := apps transD.ref [w8T', a, b, c, p, q]
def loopRc : Raw :=
  cW w8b w8r' w8b pushT'
    (cW w8r' w8r' w8b (.plam "i" (.pinr (.sloop (.var "i"))))
      (apps symmD.ref [w8T', w8b, w8r', pushT']))
def loopRcInv : Raw := apps symmD.ref [w8T', w8b, w8b, loopRc]

def runNf (name : String) (p : Raw) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match normalize (.app windF2D.ref p) f2Ty with
    | .ok t => s!"{repr t}".take 300
    | .error e => s!"ERR: {e.toList.take 150 |> String.ofList}"
  let t1 ← IO.monoMsNow
  IO.println s!"windF2({name}) [{t1-t0} ms]:"
  IO.println s!"  {r}"
  (← IO.getStdout).flush

def main : IO Unit := do
  defnCacheEnable
  IO.println "=== windF2, native ==="
  runNf "L" loopL'
  runNf "L⬝L" (cW w8b w8b w8b loopL' loopL')
  runNf "L⬝L⁻¹" (cW w8b w8b w8b loopL' loopLinv')
  runNf "Rc" loopRc
  runNf "L⬝Rc" (cW w8b w8b w8b loopL' loopRc)
  runNf "Rc⬝L" (cW w8b w8b w8b loopRc loopL')
  -- the commutator: nontrivial in F₂ (unlike the abelianized wind8!)
  runNf "[L,Rc]" (cW w8b w8b w8b loopL'
    (cW w8b w8b w8b loopRc
      (cW w8b w8b w8b
        (apps symmD.ref [w8T', w8b, w8b, loopL'])
        loopRcInv)))

import FormalizedMathematics.Cubical.Library

/-! Native computation runner: the Sanov (`SL₂(ℤ)`) winding of loops
on the figure eight — the proof-free-carrier replacement for `windF2`
(`lake exe sanov`; add argument `deep` for the direct composite-loop
transports).

Fast part (milliseconds): the type checks, the generator windings,
and the *iterated* per-generator transport — the practical decision
procedure, linear in word length; its agreement with the direct
composite-loop winding is the library's `congTrans` + `transpTrans`.
Includes the commutator `L·R·L⁻¹·R⁻¹ ↦ [[21,-8],[8,-3]] ≠ I`, which
every abelian invariant maps to the identity.

Deep part (`deep`): direct transport along `trans`-composite loops —
one nested `hcomp`-in-`U` layer computes in ~1 min (`L⬝L⁻¹`, the
conjugated `R`); at three layers (`L⬝R`) the nested-Glue evaluation
blows up superlinearly (measured > 40 min; the identified kernel fix
is value-sharing across Kan steps). -/

open Cubical Cubical.Raw Cubical.Library

def chk (name : String) (d : LibDef) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := match checkDef d.tm d.ty with
    | .ok _ => "OK" | .error e => s!"FAIL {(e.take 200).toString}"
  let t1 ← IO.monoMsNow
  IO.println s!"check {name}: {r}  ({t1-t0} ms)"
  (← IO.getStdout).flush

def zLit (n : Int) : Raw := if n ≥ 0 then posZ n.toNat else negZ (-n).toNat

/-- Decode a normalized `ℤ⁴` value back into four integers. -/
partial def dNat : Term → Option Nat
  | .zero => some 0
  | .succ t => (dNat t).map (· + 1)
  | _ => none

def dZ : Term → Option Int
  | .ipos t => (dNat t).map Int.ofNat
  | .inegsuc t => (dNat t).map (fun n => -(Int.ofNat n) - 1)
  | _ => none

def dM : Term → Option (Int × Int × Int × Int)
  | .pair (.pair a b) (.pair c d) => do
    pure (← dZ a, ← dZ b, ← dZ c, ← dZ d)
  | _ => none

/-- Direct winding of a loop at the basepoint, checked against an
expected matrix. -/
def runNf (name : String) (p : Raw) (a b c d : Int) : IO Unit := do
  let expected := resolveClosed (sanovMk (zLit a) (zLit b) (zLit c) (zLit d))
  let t0 ← IO.monoMsNow
  let r := match normalize (.app windSLD.ref p) sanovTy with
    | .ok t =>
      if t == expected then s!"PASS  = (({a},{b}),({c},{d}))"
      else s!"MISMATCH: got {(s!"{repr t}").take 300}"
    | .error e => s!"ERR: {e.toList.take 150 |> String.ofList}"
  let t1 ← IO.monoMsNow
  IO.println s!"windSL({name}) [{t1-t0} ms]: {r}"
  (← IO.getStdout).flush

/-- The four generators, as monodromy lines of the Sanov cover. -/
inductive Gen | L | Linv | R | Rinv
def Gen.line : Gen → Raw
  | .L    => .app helixSLD.ref (.pinl (.sloop (.var "i")))
  | .Linv => .app helixSLD.ref (.pinl (.sloop (.ineg (.var "i"))))
  | .R    => .app helixSLD.ref (.pinr (.sloop (.var "i")))
  | .Rinv => .app helixSLD.ref (.pinr (.sloop (.ineg (.var "i"))))
def Gen.name : Gen → String
  | .L => "L" | .Linv => "L⁻¹" | .R => "R" | .Rinv => "R⁻¹"

/-- One step of the iterated procedure: transport a concrete matrix
along one generator's monodromy. -/
def step (g : Gen) (m : Int × Int × Int × Int) :
    Option (Int × Int × Int × Int) :=
  let (a, b, c, d) := m
  let base := sanovMk (zLit a) (zLit b) (zLit c) (zLit d)
  match normalize (.transp "i" g.line base) sanovTy with
  | .ok t => dM t
  | .error _ => none

/-- Fold a word through `step`, timing the whole run. -/
def runWord (w : List Gen) (a b c d : Int) : IO Unit := do
  let name := String.intercalate "·" (w.map Gen.name)
  let t0 ← IO.monoMsNow
  let r := w.foldlM (fun m g => step g m) ((1, 0, 0, 1) : Int × Int × Int × Int)
  let t1 ← IO.monoMsNow
  let verdict := match r with
    | some m => if m == (a, b, c, d) then s!"PASS  = {m}" else s!"MISMATCH: {m}"
    | none => "ERR"
  IO.println s!"iter({name}) [{t1-t0} ms]: {verdict}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  defnCacheEnable
  IO.println "=== windSL (Sanov matrices), native ==="
  chk "addCancel" addCancelD
  chk "addCancelN" addCancelND
  chk "sanovL" sanovLD
  chk "sanovR" sanovRD
  chk "helixSL" helixSLD
  chk "windSL" windSLD
  runNf "L" w8LoopL 1 2 0 1
  runNf "L⁻¹" w8LoopLinv 1 (-2) 0 1
  IO.println "--- iterated per-generator transport (the linear-time procedure) ---"
  runWord [.L] 1 2 0 1
  runWord [.R] 1 0 2 1
  runWord [.L, .Linv] 1 0 0 1
  runWord [.L, .R] 5 2 2 1
  runWord [.R, .L] 1 2 2 5
  -- the commutator: ≠ I in SL₂(ℤ) — invisible to every abelian invariant
  runWord [.L, .R, .Linv, .Rinv] 21 (-8) 8 (-3)
  -- a longer word: (L·R)³ = [[5,2],[2,1]]³
  runWord [.L, .R, .L, .R, .L, .R] 169 70 70 29
  if args.contains "deep" then
    IO.println "--- direct composite-loop transports (nested hcomp-in-U) ---"
    runNf "L⬝L⁻¹" (w8Comp w8LoopL w8LoopLinv) 1 0 0 1
    runNf "R" w8LoopR 1 0 2 1
    runNf "L⬝R" (w8Comp w8LoopL w8LoopR) 5 2 2 1
    runNf "R⬝L" (w8Comp w8LoopR w8LoopL) 1 2 2 5

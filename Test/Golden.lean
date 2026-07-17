import FormalizedMathematics.Cubical.Library
open Cubical Cubical.Library

/-- Differential-test fingerprint of one definition: whether it checks,
and a hash of the quoted normal form of its (closed) type.  Sensitive to
any eval/quote/conv/force regression while cheap (types are small). -/
def fingerprint (d : LibDef) : String :=
  match d.ty.resolve [] with
  | .error e => s!"{d.name}: TYRESOLVE_ERR {(e.take 40).toString}"
  | .ok tyT =>
    let ok := match checkDef d.tm d.ty with | .ok _ => "ok" | .error _ => "FAIL"
    let nfTy := nf tyT
    s!"{d.name}: {ok} ty#{(toString (repr nfTy)).hash}"

def main (args : List String) : IO Unit := do
  defnCacheEnable  -- O(1) witness cuts for the native lb computation
  let lines := allDefs.map fingerprint
  match args with
  | ["gen", path] =>
    IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")
    IO.println s!"golden written: {lines.length} defs → {path}"
  | ["check", path] => do
    let golden ← IO.FS.readFile path
    let goldenLines := (golden.splitOn "\n").filter (· ≠ "")
    -- name-keyed join: newly registered definitions are reported as
    -- additions, not spurious positional mismatches
    let key (l : String) : String := ((l.splitOn ": ").headD l)
    let mut mismatches := 0
    let mut adds := 0
    for g in goldenLines do
      match lines.find? (fun c => key c == key g) with
      | some c =>
        if g ≠ c then
          IO.println s!"MISMATCH:\n  golden: {g}\n  now:    {c}"
          mismatches := mismatches + 1
      | none =>
        IO.println s!"REMOVED: {g}"
        mismatches := mismatches + 1
    for c in lines do
      if goldenLines.all (fun g => key g ≠ key c) then adds := adds + 1
    if mismatches == 0 then
      IO.println s!"GOLDEN OK: {goldenLines.length} defs match ({adds} new)"
    else IO.println s!"GOLDEN FAIL: {mismatches} mismatch(es)"
  | _ => IO.println "usage: golden (gen|check) <path>"

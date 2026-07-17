import FormalizedMathematics.Cubical.LibEM

/-! # Coherence, chapter 1: Mac Lane's pentagon and triangle in 1-types

The pentagon and triangle laws for path composition, **in any 1-type**:
parallel 2-cells in a groupoid are equal, so every diagram of associators
and unitors commutes — Mac Lane's coherence, groupoid form.

The *untruncated* versions (as genuine 3-cells in an arbitrary type) are
harder than they look: `trans refl refl` computes to `refl` only at
concrete types (ℕ, ℤ, …); at an abstract type the composite is a stuck
`hcomp`, so path-induction base cases do not close definitionally and the
coherence cells must be bootstrapped by hand (`assocRefl`,
`transReflRRefl`, …) — recorded in HANDOFF as the next stage of the
coherence programme. -/

namespace Cubical.Library

open Raw

private def cmp (A x y z p q : Raw) : Raw :=
  apps transD.ref [A, x, y, z, p, q]

/-- The five objects/edges of the pentagon, its two composite routes. -/
private def pentParts (A : Raw) :
    Raw × Raw × Raw × Raw × Raw :=
  let a : Raw := .var "a"
  let b : Raw := .var "b"
  let c : Raw := .var "c"
  let d : Raw := .var "d"
  let e : Raw := .var "e"
  let p : Raw := .var "p"
  let q : Raw := .var "q"
  let r : Raw := .var "r"
  let s : Raw := .var "s"
  let pq : Raw := cmp A a b c p q
  let qr : Raw := cmp A b c d q r
  let rs : Raw := cmp A c d e r s
  let PT : Raw := .path A a e
  let lhs : Raw := cmp A a d e (cmp A a c d pq r) s
  let rhs : Raw := cmp A a b e p (cmp A b c e q rs)
  let mid1 : Raw := cmp A a c e pq rs
  let midA : Raw := cmp A a d e (cmp A a b d p qr) s
  let midB : Raw := cmp A a b e p (cmp A b d e qr s)
  let P1 : Raw := apps transD.ref [PT, lhs, mid1, rhs,
    apps transAssocD.ref [A, a, c, d, e, pq, r, s],
    apps transAssocD.ref [A, a, b, c, e, p, q, rs]]
  let P2 : Raw := apps transD.ref [PT, lhs, midB, rhs,
    apps transD.ref [PT, lhs, midA, midB,
      apps congD.ref [.path A a d, PT,
        .lam "h" (cmp A a d e (.var "h") s),
        cmp A a c d pq r, cmp A a b d p qr,
        apps transAssocD.ref [A, a, b, c, d, p, q, r]],
      apps transAssocD.ref [A, a, b, d, e, p, qr, s]],
    apps congD.ref [.path A b e, PT,
      .lam "h" (cmp A a b e p (.var "h")),
      cmp A b d e qr s, cmp A b c e q rs,
      apps transAssocD.ref [A, b, c, d, e, q, r, s]]]
  (PT, lhs, rhs, P1, P2)

/-- **The pentagon, in a 1-type**: the two reassociation routes agree. -/
def pentagonD : LibDef where
  name := "pentagon"
  ty :=
    let A : Raw := .var "A"
    let (PT, lhs, rhs, P1, P2) := pentParts A
    .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
      (.pi "a" A (.pi "b" A (.pi "c" A (.pi "d" A (.pi "e" A
      (.pi "p" (.path A (.var "a") (.var "b"))
      (.pi "q" (.path A (.var "b") (.var "c"))
      (.pi "r" (.path A (.var "c") (.var "d"))
      (.pi "s" (.path A (.var "d") (.var "e"))
        (.path (.path PT lhs rhs) P1 P2)))))))))))
  tm :=
    let A : Raw := .var "A"
    let (_, lhs, rhs, P1, P2) := pentParts A
    lams ["A", "gA", "a", "b", "c", "d", "e", "p", "q", "r", "s"]
      (apps (.var "gA") [.var "a", .var "e", lhs, rhs, P1, P2])

#guard pentagonD.ok

/-- The triangle's two routes. -/
private def triParts (A : Raw) : Raw × Raw × Raw × Raw × Raw :=
  let a : Raw := .var "a"
  let b : Raw := .var "b"
  let c : Raw := .var "c"
  let p : Raw := .var "p"
  let q : Raw := .var "q"
  let rb : Raw := .plam "i9" b
  let PT : Raw := .path A a c
  let lhs : Raw := cmp A a b c (cmp A a b b p rb) q
  let pq : Raw := cmp A a b c p q
  let T1 : Raw := apps transD.ref [PT, lhs,
    cmp A a b c p (cmp A b b c rb q), pq,
    apps transAssocD.ref [A, a, b, b, c, p, rb, q],
    apps congD.ref [.path A b c, PT,
      .lam "h" (cmp A a b c p (.var "h")),
      cmp A b b c rb q, q,
      apps transReflLD.ref [A, b, c, q]]]
  let T2 : Raw := apps congD.ref [.path A a b, PT,
    .lam "h" (cmp A a b c (.var "h") q),
    cmp A a b b p rb, p,
    apps transReflRD.ref [A, a, b, p]]
  (PT, lhs, pq, T1, T2)

/-- **The triangle, in a 1-type**: the associator at a middle `refl` is
the exchange of the two unitors. -/
def triangleD : LibDef where
  name := "triangle"
  ty :=
    let A : Raw := .var "A"
    let (PT, lhs, pq, T1, T2) := triParts A
    .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
      (.pi "a" A (.pi "b" A (.pi "c" A
      (.pi "p" (.path A (.var "a") (.var "b"))
      (.pi "q" (.path A (.var "b") (.var "c"))
        (.path (.path PT lhs pq) T1 T2)))))))
  tm :=
    let A : Raw := .var "A"
    let (_, lhs, pq, T1, T2) := triParts A
    lams ["A", "gA", "a", "b", "c", "p", "q"]
      (apps (.var "gA") [.var "a", .var "c", lhs, pq, T1, T2])

#guard triangleD.ok

/-- Instances: the pentagon holds in `Ω S¹`-style path spaces of sets, in
particular in ℤ. -/
def pentagonZD : LibDef where
  name := "pentagonZ"
  ty :=
    let A : Raw := .int
    .pi "a" A (.pi "b" A (.pi "c" A (.pi "d" A (.pi "e" A
      (.pi "p" (.path A (.var "a") (.var "b"))
      (.pi "q" (.path A (.var "b") (.var "c"))
      (.pi "r" (.path A (.var "c") (.var "d"))
      (.pi "s" (.path A (.var "d") (.var "e"))
        (let (PT, lhs, rhs, P1, P2) := pentParts A
         .path (.path PT lhs rhs) P1 P2)))))))))
  tm := apps pentagonD.ref [.int,
    apps isSetToGpdD.ref [.int, isSetZD.ref]]

#guard pentagonZD.ok

/-! ## Chapter 2: connection-style fillers and the cube associator

Untruncated (no 1-type assumption) tools.  The key idea: state the
fillers as `PathP` whose *endpoint faces collapse definitionally* — a
`(k=0)`/`(k=1)` tube branch that becomes identically true makes the
`hcomp` reduce to its tube at `1`, so the `PathP` endpoints are `p`,
`trans p q`, `trans q r`, `r` on the nose.  The associator then assembles
from the two fillers by `trans` at the *moving* middle point `q k`, and
its own endpoints are handled entirely by the `papp` endpoint-annotation
rule — no cube reasoning leaks out of the fillers. -/

/-- Right filler: `PathP (λ k. Path A w (q k)) p (p ⬝ q)`. -/
def transFillD : LibDef where
  name := "transFill"
  ty := .pi "A" .univ (.pi "w" (.var "A") (.pi "x" (.var "A")
    (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "w") (.var "x"))
    (.pi "q" (.path (.var "A") (.var "x") (.var "y"))
      (.pathP "k"
        (.path (.var "A") (.var "w")
          (.papp (.var "q") (.var "x") (.var "y") (.var "k")))
        (.var "p")
        (apps transD.ref [.var "A", .var "w", .var "x", .var "y",
          .var "p", .var "q"])))))))
  tm := lams ["A", "w", "x", "y", "p", "q"]
    (.plam "k" (.plam "i" (.hcomp "j" (.var "A")
      [([(.var "i", false)], .var "w"),
       ([(.var "i", true)],
         .papp (.var "q") (.var "x") (.var "y")
           (.imin (.var "j") (.var "k"))),
       ([(.var "k", false)],
         .papp (.var "p") (.var "w") (.var "x") (.var "i"))]
      (.papp (.var "p") (.var "w") (.var "x") (.var "i")))))

#guard transFillD.ok

/-- Left filler: `PathP (λ k. Path A (q k) z) (q ⬝ r) r`. -/
def transFillLD : LibDef where
  name := "transFillL"
  ty := .pi "A" .univ (.pi "x" (.var "A") (.pi "y" (.var "A")
    (.pi "z" (.var "A")
    (.pi "q" (.path (.var "A") (.var "x") (.var "y"))
    (.pi "r" (.path (.var "A") (.var "y") (.var "z"))
      (.pathP "k"
        (.path (.var "A")
          (.papp (.var "q") (.var "x") (.var "y") (.var "k"))
          (.var "z"))
        (apps transD.ref [.var "A", .var "x", .var "y", .var "z",
          .var "q", .var "r"])
        (.var "r")))))))
  tm := lams ["A", "x", "y", "z", "q", "r"]
    (.plam "k" (.plam "i" (.hcomp "j" (.var "A")
      [([(.var "i", false)],
         .papp (.var "q") (.var "x") (.var "y") (.var "k")),
       ([(.var "i", true)],
         .papp (.var "r") (.var "y") (.var "z") (.var "j")),
       ([(.var "k", true)],
         .papp (.var "r") (.var "y") (.var "z")
           (.imin (.var "j") (.var "i")))]
      (.papp (.var "q") (.var "x") (.var "y")
        (.imax (.var "k") (.var "i"))))))

#guard transFillLD.ok

/-- **The cube associator, in any type**: `p ⬝ (q ⬝ r) ≡ (p ⬝ q) ⬝ r`,
with no groupoid assumption.  `assocConn k := transFill p q k ⬝ transFillL
q r k`, a composite across the moving middle point `q k`. -/
def assocConnD : LibDef where
  name := "assocConn"
  ty := .pi "A" .univ (.pi "w" (.var "A") (.pi "x" (.var "A")
    (.pi "y" (.var "A") (.pi "z" (.var "A")
    (.pi "p" (.path (.var "A") (.var "w") (.var "x"))
    (.pi "q" (.path (.var "A") (.var "x") (.var "y"))
    (.pi "r" (.path (.var "A") (.var "y") (.var "z"))
      (.path (.path (.var "A") (.var "w") (.var "z"))
        (apps transD.ref [.var "A", .var "w", .var "x", .var "z", .var "p",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z",
            .var "q", .var "r"]])
        (apps transD.ref [.var "A", .var "w", .var "y", .var "z",
          apps transD.ref [.var "A", .var "w", .var "x", .var "y",
            .var "p", .var "q"],
          .var "r"])))))))))
  tm :=
    let pq := apps transD.ref [.var "A", .var "w", .var "x", .var "y",
      .var "p", .var "q"]
    let qr := apps transD.ref [.var "A", .var "x", .var "y", .var "z",
      .var "q", .var "r"]
    let fillR := apps transFillD.ref [.var "A", .var "w", .var "x",
      .var "y", .var "p", .var "q"]
    let fillL := apps transFillLD.ref [.var "A", .var "x", .var "y",
      .var "z", .var "q", .var "r"]
    lams ["A", "w", "x", "y", "z", "p", "q", "r"]
      (.plam "k" (apps transD.ref
        [.var "A", .var "w",
         .papp (.var "q") (.var "x") (.var "y") (.var "k"), .var "z",
         .papp fillR (.var "p") pq (.var "k"),
         .papp fillL qr (.var "r") (.var "k")]))

#guard assocConnD.ok

/-- **Bootstrap 3-cell (experiment): the two unit laws agree at `refl`,
definitionally.**  With `p = refl` both unit squares evaluate to `hcomp`s
whose tubes are all the constant `a`, so they should be convertible and
the 3-cell is `refl`. -/
def transReflRReflD : LibDef where
  name := "transReflRRefl"
  ty := .pi "A" .univ (.pi "a" (.var "A")
    (.path
      (.path (.path (.var "A") (.var "a") (.var "a"))
        (apps transD.ref [.var "A", .var "a", .var "a", .var "a",
          apps reflD.ref [.var "A", .var "a"],
          apps reflD.ref [.var "A", .var "a"]])
        (apps reflD.ref [.var "A", .var "a"]))
      (apps transReflRD.ref [.var "A", .var "a", .var "a",
        apps reflD.ref [.var "A", .var "a"]])
      (apps transReflLD.ref [.var "A", .var "a", .var "a",
        apps reflD.ref [.var "A", .var "a"]])))
  tm := lams ["A", "a"]
    (.plam "m" (apps transReflRD.ref [.var "A", .var "a", .var "a",
      apps reflD.ref [.var "A", .var "a"]]))

#guard transReflRReflD.ok

/-! ## Chapter 3: the square-exchange principle

For any *syntactic* square `S k m` the two boundary routes agree:
`(bottom ⬝ right) ≡ (left ⬝ top)`.  Proof by the moving-middle idiom
alone: the middle point slides along the anti-diagonal `S (~m) m`, and
the two half-edges are connection squares — no `hcomp` beyond the two
`trans` themselves, no `J`.  Instances below: the `cong₂` exchange law
and naturality of the unit 2-cells — the toolkit for Eckmann–Hilton and
the untruncated pentagon. -/

/-- Meta-helper (Lean level): the exchange cell for the square `S k m`
over `P` with corners `s00 s10 s01 s11`:
`Path (Path P s00 s11) (bottom ⬝ right) (left ⬝ top)`. -/
private def squareExchange (P s00 s11 : Raw) (S : Raw → Raw → Raw) : Raw :=
  let m : Raw := .var "m9"
  let k : Raw := .var "k9"
  let mid : Raw := S (.ineg m) m
  let f1 : Raw := .plam "k9" (S (.imin k (.ineg m)) (.imin k m))
  let f2 : Raw := .plam "k9" (S (.imax k (.ineg m)) (.imax k m))
  .plam "m9" (apps transD.ref [P, s00, mid, s11, f1, f2])

/-- **`cong₂` exchange**: for `f : X → Y → Z`, `p : x ≡ x'`,
`q : y ≡ y'`:
`cong (f · y) p ⬝ cong (f x') q  ≡  cong (f x ·) q ⬝ cong (f · y') p`. -/
def congSlideD : LibDef where
  name := "congSlide"
  ty :=
    let f (u v : Raw) : Raw := .app (.app (.var "f") u) v
    let X : Raw := .var "X"
    let Y : Raw := .var "Y"
    let Z : Raw := .var "Z"
    let x : Raw := .var "x"
    let x2 : Raw := .var "x2"
    let y : Raw := .var "y"
    let y2 : Raw := .var "y2"
    let cBottom : Raw := apps congD.ref [X, Z,
      .lam "h" (f (.var "h") y), x, x2, .var "p"]
    let cRight : Raw := apps congD.ref [Y, Z,
      .lam "h" (f x2 (.var "h")), y, y2, .var "q"]
    let cLeft : Raw := apps congD.ref [Y, Z,
      .lam "h" (f x (.var "h")), y, y2, .var "q"]
    let cTop : Raw := apps congD.ref [X, Z,
      .lam "h" (f (.var "h") y2), x, x2, .var "p"]
    .pi "X" .univ (.pi "Y" .univ (.pi "Z" .univ
      (.pi "f" (.arr X (.arr Y Z))
      (.pi "x" X (.pi "x2" X (.pi "y" Y (.pi "y2" Y
      (.pi "p" (.path X x x2)
      (.pi "q" (.path Y y y2)
        (.path (.path Z (f x y) (f x2 y2))
          (apps transD.ref [Z, f x y, f x2 y, f x2 y2, cBottom, cRight])
          (apps transD.ref [Z, f x y, f x y2, f x2 y2, cLeft, cTop])))))))))))
  tm :=
    let f (u v : Raw) : Raw := .app (.app (.var "f") u) v
    let S (kk mm : Raw) : Raw :=
      f (.papp (.var "p") (.var "x") (.var "x2") kk)
        (.papp (.var "q") (.var "y") (.var "y2") mm)
    lams ["X", "Y", "Z", "f", "x", "x2", "y", "y2", "p", "q"]
      (squareExchange (.var "Z")
        (f (.var "x") (.var "y")) (f (.var "x2") (.var "y2")) S)

#guard congSlideD.ok

/-- **Naturality of the right unitor**: for `α : p ≡ p'` in `Path A a b`:
`cong (· ⬝ refl) α ⬝ transReflR p'  ≡  transReflR p ⬝ α`. -/
def natReflRD : LibDef where
  name := "natReflR"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let pp : Raw := .var "p"
    let pp2 : Raw := .var "p2"
    let P : Raw := .path A a b
    let rb : Raw := apps reflD.ref [A, b]
    let cmpR (h : Raw) : Raw := apps transD.ref [A, a, b, b, h, rb]
    let cBottom : Raw := apps congD.ref [P, P,
      .lam "h" (cmpR (.var "h")), pp, pp2, .var "al"]
    .pi "A" .univ (.pi "a" A (.pi "b" A
      (.pi "p" P (.pi "p2" P
      (.pi "al" (.path P pp pp2)
        (.path (.path P (cmpR pp) pp2)
          (apps transD.ref [P, cmpR pp, cmpR pp2, pp2, cBottom,
            apps transReflRD.ref [A, a, b, pp2]])
          (apps transD.ref [P, cmpR pp, pp, pp2,
            apps transReflRD.ref [A, a, b, pp],
            .var "al"])))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let P : Raw := .path A a b
    let rb : Raw := apps reflD.ref [A, b]
    let alk (kk : Raw) : Raw := .papp (.var "al") (.var "p") (.var "p2") kk
    let S (kk mm : Raw) : Raw :=
      .papp (apps transReflRD.ref [A, a, b, alk kk])
        (apps transD.ref [A, a, b, b, alk kk, rb]) (alk kk) mm
    lams ["A", "a", "b", "p", "p2", "al"]
      (squareExchange P
        (apps transD.ref [A, a, b, b, .var "p", rb]) (.var "p2") S)

#guard natReflRD.ok

/-- **Naturality of the left unitor**: for `α : p ≡ p'` in `Path A a b`:
`cong (refl ⬝ ·) α ⬝ transReflL p'  ≡  transReflL p ⬝ α`. -/
def natReflLD : LibDef where
  name := "natReflL"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let pp : Raw := .var "p"
    let pp2 : Raw := .var "p2"
    let P : Raw := .path A a b
    let ra : Raw := apps reflD.ref [A, a]
    let cmpL (h : Raw) : Raw := apps transD.ref [A, a, a, b, ra, h]
    let cBottom : Raw := apps congD.ref [P, P,
      .lam "h" (cmpL (.var "h")), pp, pp2, .var "al"]
    .pi "A" .univ (.pi "a" A (.pi "b" A
      (.pi "p" P (.pi "p2" P
      (.pi "al" (.path P pp pp2)
        (.path (.path P (cmpL pp) pp2)
          (apps transD.ref [P, cmpL pp, cmpL pp2, pp2, cBottom,
            apps transReflLD.ref [A, a, b, pp2]])
          (apps transD.ref [P, cmpL pp, pp, pp2,
            apps transReflLD.ref [A, a, b, pp],
            .var "al"])))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let P : Raw := .path A a b
    let ra : Raw := apps reflD.ref [A, a]
    let alk (kk : Raw) : Raw := .papp (.var "al") (.var "p") (.var "p2") kk
    let S (kk mm : Raw) : Raw :=
      .papp (apps transReflLD.ref [A, a, b, alk kk])
        (apps transD.ref [A, a, a, b, ra, alk kk]) (alk kk) mm
    lams ["A", "a", "b", "p", "p2", "al"]
      (squareExchange P
        (apps transD.ref [A, a, a, b, ra, .var "p"]) (.var "p2") S)

#guard natReflLD.ok

/-- Generic right-cancellation: `(P ⬝ q⁻¹) ⬝ q ≡ P`. -/
def cancelRD : LibDef where
  name := "cancelR"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "c" (.var "A")
    (.pi "P" (.path (.var "A") (.var "a") (.var "b"))
    (.pi "q" (.path (.var "A") (.var "c") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps transD.ref [.var "A", .var "a", .var "c", .var "b",
          apps transD.ref [.var "A", .var "a", .var "b", .var "c",
            .var "P",
            apps symmD.ref [.var "A", .var "c", .var "b", .var "q"]],
          .var "q"])
        (.var "P")))))))
  tm :=
    let A : Raw := .var "A"
    let PT : Raw := .path A (.var "a") (.var "b")
    let qi : Raw := apps symmD.ref [A, .var "c", .var "b", .var "q"]
    let Pqi : Raw := apps transD.ref [A, .var "a", .var "b", .var "c",
      .var "P", qi]
    lams ["A", "a", "b", "c", "P", "q"]
      (apps transD.ref [PT,
        apps transD.ref [A, .var "a", .var "c", .var "b", Pqi, .var "q"],
        apps transD.ref [A, .var "a", .var "b", .var "b", .var "P",
          apps transD.ref [A, .var "b", .var "c", .var "b", qi, .var "q"]],
        .var "P",
        apps transAssocD.ref [A, .var "a", .var "b", .var "c", .var "b",
          .var "P", qi, .var "q"],
        apps transD.ref [PT,
          apps transD.ref [A, .var "a", .var "b", .var "b", .var "P",
            apps transD.ref [A, .var "b", .var "c", .var "b", qi, .var "q"]],
          apps transD.ref [A, .var "a", .var "b", .var "b", .var "P",
            apps reflD.ref [A, .var "b"]],
          .var "P",
          apps congD.ref [.path A (.var "b") (.var "b"), PT,
            .lam "h" (apps transD.ref [A, .var "a", .var "b", .var "b",
              .var "P", .var "h"]),
            apps transD.ref [A, .var "b", .var "c", .var "b", qi, .var "q"],
            apps reflD.ref [A, .var "b"],
            apps transInvLD.ref [A, .var "c", .var "b", .var "q"]],
          apps transReflRD.ref [A, .var "a", .var "b", .var "P"]]])

#guard cancelRD.ok

/-- **Left cancellation**: `q⁻¹ ⬝ q ≡ refl`, from `cancelR` at `P = refl`
plus the left unitor. -/
def cancelLD : LibDef where
  name := "cancelL"
  ty := .pi "A" .univ (.pi "b" (.var "A") (.pi "c" (.var "A")
    (.pi "q" (.path (.var "A") (.var "c") (.var "b"))
      (.path (.path (.var "A") (.var "b") (.var "b"))
        (apps transD.ref [.var "A", .var "b", .var "c", .var "b",
          apps symmD.ref [.var "A", .var "c", .var "b", .var "q"],
          .var "q"])
        (apps reflD.ref [.var "A", .var "b"])))))
  tm :=
    let A : Raw := .var "A"
    let b : Raw := .var "b"
    let c : Raw := .var "c"
    let q : Raw := .var "q"
    let rb : Raw := apps reflD.ref [A, b]
    let qi : Raw := apps symmD.ref [A, c, b, q]
    let rqi : Raw := apps transD.ref [A, b, b, c, rb, qi]
    let qiq : Raw := apps transD.ref [A, b, c, b, qi, q]
    let rqiq : Raw := apps transD.ref [A, b, c, b, rqi, q]
    let VT : Raw := .path A b b
    -- whiskerR (symm (transReflL qi)) q : qi⬝q ≡ (refl⬝qi)⬝q
    let w : Raw := apps congD.ref [.path A b c, VT,
      .lam "h" (apps transD.ref [A, b, c, b, .var "h", q]),
      qi, rqi,
      apps symmD.ref [.path A b c, rqi, qi,
        apps transReflLD.ref [A, b, c, qi]]]
    lams ["A", "b", "c", "q"]
      (apps transD.ref [VT, qiq, rqiq, rb, w,
        apps cancelRD.ref [A, b, b, c, rb, q]])

#guard cancelLD.ok

/-! ## Chapter 4: Eckmann–Hilton

`α ⬝ β ≡ β ⬝ α` for 2-loops, **in any type** — no truncation, no `J`.
The proof is an 18-step composite of 3-cells: slide the two loops past
each other with the `cong₂` exchange (`congSlide`), convert whiskered
forms back with the two unitor naturalities, and cancel the shared unitor
`U := transReflR refl` — which by `transReflRRefl` coincides
*definitionally* with `transReflL refl`, so the left/right bookkeeping
never leaves conversion. -/

/-- Right-nested composite of a chain of cells: `steps` are
`(source vertex, cell)` pairs, `z` the final vertex, `sp` the space. -/
private def chain3 (sp z : Raw) : List (Raw × Raw) → Raw
  | [] => z
  | [(_, m)] => m
  | (v, m) :: rest =>
    let v' := match rest with
      | (w, _) :: _ => w
      | [] => z
    apps transD.ref [sp, v, v', z, m, chain3 sp z rest]

def eckmannHiltonD : LibDef where
  name := "eckmannHilton"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let P : Raw := .path A a a
    let rfa : Raw := apps reflD.ref [A, a]
    let O2 : Raw := .path P rfa rfa
    let c2 (X Y Z e1 e2 : Raw) : Raw := apps transD.ref [P, X, Y, Z, e1, e2]
    .pi "A" .univ (.pi "a" A (.pi "al" O2 (.pi "be" O2
      (.path O2
        (c2 rfa rfa rfa (.var "al") (.var "be"))
        (c2 rfa rfa rfa (.var "be") (.var "al"))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let al : Raw := .var "al"
    let be : Raw := .var "be"
    let P : Raw := .path A a a
    let rfa : Raw := apps reflD.ref [A, a]
    let cL (p q : Raw) : Raw := apps transD.ref [A, a, a, a, p, q]
    let rr : Raw := cL rfa rfa
    let O2 : Raw := .path P rfa rfa
    let Vsp : Raw := .path P rr rfa
    let Wsp : Raw := .path P rr rr
    let c2 (X Y Z e1 e2 : Raw) : Raw := apps transD.ref [P, X, Y, Z, e1, e2]
    let U : Raw := apps transReflRD.ref [A, a, a, rfa]
    let sU : Raw := apps symmD.ref [P, rr, rfa, U]
    let cA : Raw := apps congD.ref [P, P,
      .lam "h" (cL (.var "h") rfa), rfa, rfa, al]
    let cB : Raw := apps congD.ref [P, P,
      .lam "h" (cL rfa (.var "h")), rfa, rfa, be]
    let ab : Raw := c2 rfa rfa rfa al be
    let ba : Raw := c2 rfa rfa rfa be al
    let Ua : Raw := c2 rr rfa rfa U al
    let Ub : Raw := c2 rr rfa rfa U be
    let cAU : Raw := c2 rr rr rfa cA U
    let cBU : Raw := c2 rr rr rfa cB U
    let cAcB : Raw := c2 rr rr rr cA cB
    let cBcA : Raw := c2 rr rr rr cB cA
    -- main-chain vertices, in Vsp
    let A1 : Raw := c2 rr rfa rfa U ab
    let A2 : Raw := c2 rr rfa rfa Ua be
    let A3 : Raw := c2 rr rfa rfa cAU be
    let A4 : Raw := c2 rr rr rfa cA Ub
    let A5 : Raw := c2 rr rr rfa cA cBU
    let A6 : Raw := c2 rr rr rfa cAcB U
    let A7 : Raw := c2 rr rr rfa cBcA U
    let A8 : Raw := c2 rr rr rfa cB cAU
    let A9 : Raw := c2 rr rr rfa cB Ua
    let A10 : Raw := c2 rr rfa rfa cBU al
    let A11 : Raw := c2 rr rfa rfa Ub al
    let A12 : Raw := c2 rr rfa rfa U ba
    -- ingredient 3-cells
    let natRa : Raw := apps natReflRD.ref [A, a, a, rfa, rfa, al]
    let natLb : Raw := apps natReflLD.ref [A, a, a, rfa, rfa, be]
    let ftrans : Raw := .lam "h1" (.lam "h2" (cL (.var "h1") (.var "h2")))
    let slide : Raw := apps congSlideD.ref
      [P, P, P, ftrans, rfa, rfa, rfa, rfa, al, be]
    let m1 : Raw := apps assocConnD.ref [P, rr, rfa, rfa, rfa, U, al, be]
    let m2 : Raw := apps congD.ref [Vsp, Vsp,
      .lam "h" (c2 rr rfa rfa (.var "h") be), Ua, cAU,
      apps symmD.ref [Vsp, cAU, Ua, natRa]]
    let m3 : Raw := apps symmD.ref [Vsp, A4, A3,
      apps assocConnD.ref [P, rr, rr, rfa, rfa, cA, U, be]]
    let m4 : Raw := apps congD.ref [Vsp, Vsp,
      .lam "h" (c2 rr rr rfa cA (.var "h")), Ub, cBU,
      apps symmD.ref [Vsp, cBU, Ub, natLb]]
    let m5 : Raw := apps assocConnD.ref [P, rr, rr, rr, rfa, cA, cB, U]
    let m6 : Raw := apps congD.ref [Wsp, Vsp,
      .lam "h" (c2 rr rr rfa (.var "h") U), cAcB, cBcA, slide]
    let m7 : Raw := apps symmD.ref [Vsp, A8, A7,
      apps assocConnD.ref [P, rr, rr, rr, rfa, cB, cA, U]]
    let m8 : Raw := apps congD.ref [Vsp, Vsp,
      .lam "h" (c2 rr rr rfa cB (.var "h")), cAU, Ua, natRa]
    let m9 : Raw := apps assocConnD.ref [P, rr, rr, rfa, rfa, cB, U, al]
    let m10 : Raw := apps congD.ref [Vsp, Vsp,
      .lam "h" (c2 rr rfa rfa (.var "h") al), cBU, Ub, natLb]
    let m11 : Raw := apps symmD.ref [Vsp, A12, A11,
      apps assocConnD.ref [P, rr, rfa, rfa, rfa, U, be, al]]
    let bigM : Raw := chain3 (.path P rr rfa) A12
      [(A1, m1), (A2, m2), (A3, m3), (A4, m4), (A5, m5), (A6, m6),
       (A7, m7), (A8, m8), (A9, m9), (A10, m10), (A11, m11)]
    -- final cancellation, in O2
    let r2 : Raw := apps reflD.ref [P, rfa]
    let sUU : Raw := c2 rfa rr rfa sU U
    let E1 : Raw := ab
    let E2 : Raw := c2 rfa rfa rfa r2 ab
    let E3 : Raw := c2 rfa rfa rfa sUU ab
    let E4 : Raw := c2 rfa rr rfa sU A1
    let E5 : Raw := c2 rfa rr rfa sU A12
    let E6 : Raw := c2 rfa rfa rfa sUU ba
    let E7 : Raw := c2 rfa rfa rfa r2 ba
    let E8 : Raw := ba
    let cLU : Raw := apps cancelLD.ref [P, rfa, rr, U]
    let e1 : Raw := apps symmD.ref [O2, E2, E1,
      apps transReflLD.ref [P, rfa, rfa, ab]]
    let e2 : Raw := apps congD.ref [O2, O2,
      .lam "h" (c2 rfa rfa rfa (.var "h") ab), r2, sUU,
      apps symmD.ref [O2, sUU, r2, cLU]]
    let e3 : Raw := apps symmD.ref [O2, E4, E3,
      apps assocConnD.ref [P, rfa, rr, rfa, rfa, sU, U, ab]]
    let e4 : Raw := apps congD.ref [Vsp, O2,
      .lam "h" (c2 rfa rr rfa sU (.var "h")), A1, A12, bigM]
    let e5 : Raw := apps assocConnD.ref [P, rfa, rr, rfa, rfa, sU, U, ba]
    let e6 : Raw := apps congD.ref [O2, O2,
      .lam "h" (c2 rfa rfa rfa (.var "h") ba), sUU, r2, cLU]
    let e7 : Raw := apps transReflLD.ref [P, rfa, rfa, ba]
    lams ["A", "a", "al", "be"]
      (chain3 O2 E8
        [(E1, e1), (E2, e2), (E3, e3), (E4, e4), (E5, e5), (E6, e6),
         (E7, e7)])

#guard eckmannHiltonD.ok

/-! ## Chapter 5: the untruncated triangle

`normCof`'s canonical face literals (kernel, 2026-07-13) make the two
fillers of `assocConn p refl q` *convertible* with the unitor squares:
the `F`-side is `symm (transReflR p)` and the `G`-side is
`transReflL q`, on the nose.  So the associator at a middle `refl` IS
the diagonal of the unitor square `S k m := (symm (transReflR p) @ k) ⬝
(transReflL q @ m)`, and Mac Lane's triangle reduces to the
diagonal-vs-edges lemma for syntactic squares — moving middle again. -/

/-- Meta-helper: `trans (diagonal S) refl ≡ trans (left S) (top S)`,
by sliding the middle along `S (~u) 1`. -/
private def squareDiagL (P s00 s11 : Raw) (S : Raw → Raw → Raw) : Raw :=
  let u : Raw := .var "m9"
  let k : Raw := .var "k9"
  let mid : Raw := S (.ineg u) .i1
  let first : Raw := .plam "k9" (S (.imin k (.ineg u)) k)
  let second : Raw := .plam "k9" (S (.imax (.ineg u) k) .i1)
  .plam "m9" (apps transD.ref [P, s00, mid, s11, first, second])

/-- **Mac Lane's triangle, in any type**:
`assocConn p refl q ⬝ cong (· ⬝ q) (transReflR p) ≡
 cong (p ⬝ ·) (transReflL q)`. -/
def triangleConnD : LibDef where
  name := "triangleConn"
  ty :=
    let A : Raw := .var "A"
    let w : Raw := .var "w"
    let x : Raw := .var "x"
    let z : Raw := .var "z"
    let p : Raw := .var "p"
    let q : Raw := .var "q"
    let rx : Raw := apps reflD.ref [A, x]
    let PT : Raw := .path A w z
    let s00 : Raw := apps transD.ref [A, w, x, z, p,
      apps transD.ref [A, x, x, z, rx, q]]
    let s11 : Raw := apps transD.ref [A, w, x, z,
      apps transD.ref [A, w, x, x, p, rx], q]
    let s01 : Raw := apps transD.ref [A, w, x, z, p, q]
    let whisk : Raw := apps congD.ref [.path A w x, PT,
      .lam "h" (apps transD.ref [A, w, x, z, .var "h", q]),
      apps transD.ref [A, w, x, x, p, rx], p,
      apps transReflRD.ref [A, w, x, p]]
    let lhs : Raw := apps transD.ref [PT, s00, s11, s01,
      apps assocConnD.ref [A, w, x, x, z, p, rx, q], whisk]
    let rhs : Raw := apps congD.ref [.path A x z, PT,
      .lam "h" (apps transD.ref [A, w, x, z, p, .var "h"]),
      apps transD.ref [A, x, x, z, rx, q], q,
      apps transReflLD.ref [A, x, z, q]]
    .pi "A" .univ (.pi "w" A (.pi "x" A (.pi "z" A
      (.pi "p" (.path A w x) (.pi "q" (.path A x z)
        (.path (.path PT s00 s01) lhs rhs))))))
  tm :=
    let A : Raw := .var "A"
    let w : Raw := .var "w"
    let x : Raw := .var "x"
    let z : Raw := .var "z"
    let p : Raw := .var "p"
    let q : Raw := .var "q"
    let rx : Raw := apps reflD.ref [A, x]
    let PT : Raw := .path A w z
    let prx : Raw := apps transD.ref [A, w, x, x, p, rx]
    let rxq : Raw := apps transD.ref [A, x, x, z, rx, q]
    let s00 : Raw := apps transD.ref [A, w, x, z, p, rxq]
    let s11 : Raw := apps transD.ref [A, w, x, z, prx, q]
    let s01 : Raw := apps transD.ref [A, w, x, z, p, q]
    let sUp : Raw := apps symmD.ref [.path A w x, prx, p,
      apps transReflRD.ref [A, w, x, p]]
    let Lq : Raw := apps transReflLD.ref [A, x, z, q]
    let S (kk mm : Raw) : Raw := apps transD.ref [A, w, x, z,
      .papp sUp p prx kk, .papp Lq rxq q mm]
    let dg : Raw := apps assocConnD.ref [A, w, x, x, z, p, rx, q]
    let left : Raw := .plam "k" (S .i0 (.var "k"))
    let top : Raw := .plam "k" (S (.var "k") .i1)
    let sT : Raw := apps symmD.ref [PT, s01, s11, top]
    let r1 : Raw := apps reflD.ref [PT, s11]
    let c2 (X Y Z e1 e2 : Raw) : Raw := apps transD.ref [PT, X, Y, Z, e1, e2]
    let X1 : Raw := c2 s00 s11 s01 dg sT
    let X2 : Raw := c2 s00 s11 s01 (c2 s00 s11 s11 dg r1) sT
    let X3 : Raw := c2 s00 s11 s01
      (c2 s00 s01 s11 left top) sT
    let X5 : Raw := left
    let VT : Raw := .path PT s00 s01
    let t1 : Raw := apps congD.ref [.path PT s00 s11, VT,
      .lam "h" (c2 s00 s11 s01 (.var "h") sT),
      dg, c2 s00 s11 s11 dg r1,
      apps symmD.ref [.path PT s00 s11, c2 s00 s11 s11 dg r1, dg,
        apps transReflRD.ref [PT, s00, s11, dg]]]
    let t2 : Raw := apps congD.ref [.path PT s00 s11, VT,
      .lam "h" (c2 s00 s11 s01 (.var "h") sT),
      c2 s00 s11 s11 dg r1, c2 s00 s01 s11 left top,
      squareDiagL PT s00 s11 S]
    let t4 : Raw := apps cancelRD.ref [PT, s00, s01, s11, left, sT]
    lams ["A", "w", "x", "z", "p", "q"]
      (apps transD.ref [VT, X1, X2, X5,
        t1,
        apps transD.ref [VT, X2, X3, X5, t2, t4]])

#guard triangleConnD.ok

/-! ## Chapter 6: towards the untruncated pentagon

Move the associator along the fillers: the family
`Λ l := assocConn p (transFill q r @ l) (transFillL r s @ l)` is a
syntactic square of 2-cells whose four edges are pentagon cells, so
`squareExchange` yields the pentagon's left commuting half; a second
family `Ψ l := assocConn (transFill p q @ l) (transFillL q r @ l) s`
yields the right half.  The two new diagonal 2-cells `pentDiag`
(`(p⬝q)⬝(r⬝s) ≡ (p⬝(q⬝r))⬝s`) and `pentDiagL`
(`p⬝((q⬝r)⬝s) ≡ (p⬝q)⬝(r⬝s)`) appear as the tops/bottoms. -/

private structure PentCtx where
  A : Raw := .var "A"
  w : Raw := .var "w"
  x : Raw := .var "x"
  y : Raw := .var "y"
  z : Raw := .var "z"
  v : Raw := .var "v"
  p : Raw := .var "p"
  q : Raw := .var "q"
  r : Raw := .var "r"
  s : Raw := .var "s"

private def pentPis (body : Raw) : Raw :=
  let c : PentCtx := {}
  .pi "A" .univ (.pi "w" c.A (.pi "x" c.A (.pi "y" c.A (.pi "z" c.A
    (.pi "v" c.A
    (.pi "p" (.path c.A c.w c.x)
    (.pi "q" (.path c.A c.x c.y)
    (.pi "r" (.path c.A c.y c.z)
    (.pi "s" (.path c.A c.z c.v) body)))))))))

private def pentLams (body : Raw) : Raw :=
  lams ["A", "w", "x", "y", "z", "v", "p", "q", "r", "s"] body

namespace PentCtx

/-- composite `a⬝b` at points `u1→u2→u3`. -/
private def t3 (c : PentCtx) (u1 u2 u3 a b : Raw) : Raw :=
  apps transD.ref [c.A, u1, u2, u3, a, b]

private def pq (c : PentCtx) : Raw := c.t3 c.w c.x c.y c.p c.q
private def qr (c : PentCtx) : Raw := c.t3 c.x c.y c.z c.q c.r
private def rs (c : PentCtx) : Raw := c.t3 c.y c.z c.v c.r c.s
private def V1 (c : PentCtx) : Raw :=
  c.t3 c.w c.x c.v c.p (c.t3 c.x c.y c.v c.q c.rs)
private def V2 (c : PentCtx) : Raw := c.t3 c.w c.y c.v c.pq c.rs
private def V3 (c : PentCtx) : Raw :=
  c.t3 c.w c.z c.v (c.t3 c.w c.y c.z c.pq c.r) c.s
private def V4 (c : PentCtx) : Raw :=
  c.t3 c.w c.z c.v (c.t3 c.w c.x c.z c.p c.qr) c.s
private def V5 (c : PentCtx) : Raw :=
  c.t3 c.w c.x c.v c.p (c.t3 c.x c.z c.v c.qr c.s)
private def PT (c : PentCtx) : Raw := .path c.A c.w c.v

/-- `transFill q r @ l` with annotations. -/
private def qrHat (c : PentCtx) (l : Raw) : Raw :=
  .papp (apps transFillD.ref [c.A, c.x, c.y, c.z, c.q, c.r]) c.q c.qr l
/-- `transFillL r s @ l`. -/
private def sHat (c : PentCtx) (l : Raw) : Raw :=
  .papp (apps transFillLD.ref [c.A, c.y, c.z, c.v, c.r, c.s]) c.rs c.s l
/-- `transFill p q @ l`. -/
private def pqHat (c : PentCtx) (l : Raw) : Raw :=
  .papp (apps transFillD.ref [c.A, c.w, c.x, c.y, c.p, c.q]) c.p c.pq l
/-- `transFillL q r @ l`. -/
private def qrCheck (c : PentCtx) (l : Raw) : Raw :=
  .papp (apps transFillLD.ref [c.A, c.x, c.y, c.z, c.q, c.r]) c.qr c.r l

/-- point `r l`. -/
private def rl (c : PentCtx) (l : Raw) : Raw := .papp c.r c.y c.z l
/-- point `q l`. -/
private def ql (c : PentCtx) (l : Raw) : Raw := .papp c.q c.x c.y l

/-- the Λ-family square: `S1 l m := assocConn p (qrHat l) (sHat l) @ m`. -/
private def S1 (c : PentCtx) (l m : Raw) : Raw :=
  let lhs := c.t3 c.w c.x c.v c.p (c.t3 c.x (c.rl l) c.v (c.qrHat l) (c.sHat l))
  let rhs := c.t3 c.w (c.rl l) c.v (c.t3 c.w c.x (c.rl l) c.p (c.qrHat l)) (c.sHat l)
  .papp (apps assocConnD.ref [c.A, c.w, c.x, c.rl l, c.v,
    c.p, c.qrHat l, c.sHat l]) lhs rhs m

/-- the Ψ-family square: `S2 l m := assocConn (pqHat l) (qrCheck l) s @ m`. -/
private def S2 (c : PentCtx) (l m : Raw) : Raw :=
  let lhs := c.t3 c.w (c.ql l) c.v (c.pqHat l)
    (c.t3 (c.ql l) c.z c.v (c.qrCheck l) c.s)
  let rhs := c.t3 c.w c.z c.v (c.t3 c.w (c.ql l) c.z (c.pqHat l) (c.qrCheck l)) c.s
  .papp (apps assocConnD.ref [c.A, c.w, c.ql l, c.z, c.v,
    c.pqHat l, c.qrCheck l, c.s]) lhs rhs m

end PentCtx

/-- The pentagon diagonal `(p⬝q)⬝(r⬝s) ≡ (p⬝(q⬝r))⬝s`: the top edge of
the Λ-family square. -/
def pentDiagD : LibDef where
  name := "pentDiag"
  ty :=
    let c : PentCtx := {}
    pentPis (.path c.PT c.V2 c.V4)
  tm :=
    let c : PentCtx := {}
    pentLams (.plam "l" (c.S1 (.var "l") .i1))

#guard pentDiagD.ok

/-- The other diagonal `p⬝((q⬝r)⬝s) ≡ (p⬝q)⬝(r⬝s)`: the bottom edge of
the Ψ-family square. -/
def pentDiagLD : LibDef where
  name := "pentDiagL"
  ty :=
    let c : PentCtx := {}
    pentPis (.path c.PT c.V5 c.V2)
  tm :=
    let c : PentCtx := {}
    pentLams (.plam "l" (c.S2 (.var "l") .i0))

#guard pentDiagLD.ok

/-- **Pentagon, left commuting half** (naturality of the associator along
the `q,r`/`r,s` fillers):
`cong (p⬝·) (assocConn q r s) ⬝ assocConn p (q⬝r) s ≡
 assocConn p q (r⬝s) ⬝ pentDiag`. -/
def pentNatLD : LibDef where
  name := "pentNatL"
  ty :=
    let c : PentCtx := {}
    let congB1 : Raw := apps congD.ref [.path c.A c.x c.v, c.PT,
      .lam "h" (c.t3 c.w c.x c.v c.p (.var "h")),
      c.t3 c.x c.y c.v c.q c.rs, c.t3 c.x c.z c.v c.qr c.s,
      apps assocConnD.ref [c.A, c.x, c.y, c.z, c.v, c.q, c.r, c.s]]
    let lhs : Raw := apps transD.ref [c.PT, c.V1, c.V5, c.V4, congB1,
      apps assocConnD.ref [c.A, c.w, c.x, c.z, c.v, c.p, c.qr, c.s]]
    let rhs : Raw := apps transD.ref [c.PT, c.V1, c.V2, c.V4,
      apps assocConnD.ref [c.A, c.w, c.x, c.y, c.v, c.p, c.q, c.rs],
      apps pentDiagD.ref [c.A, c.w, c.x, c.y, c.z, c.v, c.p, c.q, c.r, c.s]]
    pentPis (.path (.path c.PT c.V1 c.V4) lhs rhs)
  tm :=
    let c : PentCtx := {}
    pentLams (squareExchange c.PT c.V1 c.V4 (fun l m => c.S1 l m))

#guard pentNatLD.ok

/-- **Pentagon, right commuting half**:
`pentDiagL ⬝ assocConn (p⬝q) r s ≡
 assocConn p (q⬝r) s ⬝ cong (·⬝s) (assocConn p q r)`. -/
def pentNatRD : LibDef where
  name := "pentNatR"
  ty :=
    let c : PentCtx := {}
    let congB3 : Raw := apps congD.ref [.path c.A c.w c.z, c.PT,
      .lam "h" (c.t3 c.w c.z c.v (.var "h") c.s),
      c.t3 c.w c.x c.z c.p c.qr, c.t3 c.w c.y c.z c.pq c.r,
      apps assocConnD.ref [c.A, c.w, c.x, c.y, c.z, c.p, c.q, c.r]]
    let lhs : Raw := apps transD.ref [c.PT, c.V5, c.V2, c.V3,
      apps pentDiagLD.ref [c.A, c.w, c.x, c.y, c.z, c.v, c.p, c.q, c.r, c.s],
      apps assocConnD.ref [c.A, c.w, c.y, c.z, c.v, c.pq, c.r, c.s]]
    let rhs : Raw := apps transD.ref [c.PT, c.V5, c.V4, c.V3,
      apps assocConnD.ref [c.A, c.w, c.x, c.z, c.v, c.p, c.qr, c.s],
      congB3]
    pentPis (.path (.path c.PT c.V5 c.V3) lhs rhs)
  tm :=
    let c : PentCtx := {}
    pentLams (squareExchange c.PT c.V5 c.V3 (fun l m => c.S2 l m))

#guard pentNatRD.ok

namespace PentCtx

/-- The double filler `Q m l : q m → r l` ("rest of `q`, then `r` up to
`l`"), with conjunction-free faces making all four specializations
definitional: `Q 0 l ≐ transFill q r @ l`, `Q m 1 ≐ transFillL q r @ m`,
`Q m 0 ≐ (i ↦ q (m∨i))`, `Q 1 l ≐ (i ↦ r (l∧i))`. -/
private def Qd (c : PentCtx) (m l j : Raw) : Raw :=
  .hcomp "j2" c.A
    [([(j, false)], .papp c.q c.x c.y m),
     ([(j, true)], .papp c.r c.y c.z (.imin (.var "j2") l)),
     ([(l, false)], .papp c.q c.x c.y (.imax m j)),
     ([(m, true)], .papp c.r c.y c.z (.imin (.imin (.var "j2") l) j))]
    (.papp c.q c.x c.y (.imax m j))

/-- The fusion cell `γ l m : Path A w (r l)`, one hcomp thanks to the
conjunction face `(l=0)∧(m=1)`: at `m=0` the face is identically false
(dropped), giving `trans p (transFill q r @ l)` on the nose; at `m=1` it
normalizes to `(l=0)`, giving `transFill (p⬝q) r @ l` on the nose; at
`l=1` it is dropped again, giving `assocConn p q r @ m`. -/
private def gammaD (c : PentCtx) (l m : Raw) : Raw :=
  .plam "i"
    (.hcomp "j" c.A
      [([(.var "i", false)], c.w),
       ([(.var "i", true)], c.Qd m l (.var "j")),
       ([(l, false), (m, true)],
         .papp c.pq c.w c.y (.var "i"))]
      (.papp (c.pqHat m) c.w (.papp c.q c.x c.y m) (.var "i")))

/-- The third pentagon square: `W l m := γ l m ⬝ transFillL r s @ l`. -/
private def W (c : PentCtx) (l m : Raw) : Raw :=
  c.t3 c.w (c.rl l) c.v (c.gammaD l m) (c.sHat l)

end PentCtx

/-- The refill cell: re-filling the already-complete filler of `p⬝q`,
whiskered by `r⬝s` — semantically `refl` at `(p⬝q)⬝(r⬝s)`; proving it
`refl` is the one remaining step of the pentagon. -/
def pentRefillD : LibDef where
  name := "pentRefill"
  ty :=
    let c : PentCtx := {}
    pentPis (.path c.PT c.V2 c.V2)
  tm :=
    let c : PentCtx := {}
    pentLams (.plam "m" (c.W .i0 (.var "m")))

#guard pentRefillD.ok

/-- **Pentagon, third square** (fusion of the two `p,q`-side fillers):
`pentDiag ⬝ cong (·⬝s) (assocConn p q r) ≡
 pentRefill ⬝ assocConn (p⬝q) r s`. -/
def pentNatWD : LibDef where
  name := "pentNatW"
  ty :=
    let c : PentCtx := {}
    let congB3 : Raw := apps congD.ref [.path c.A c.w c.z, c.PT,
      .lam "h" (c.t3 c.w c.z c.v (.var "h") c.s),
      c.t3 c.w c.x c.z c.p c.qr, c.t3 c.w c.y c.z c.pq c.r,
      apps assocConnD.ref [c.A, c.w, c.x, c.y, c.z, c.p, c.q, c.r]]
    let lhs : Raw := apps transD.ref [c.PT, c.V2, c.V4, c.V3,
      apps pentDiagD.ref [c.A, c.w, c.x, c.y, c.z, c.v, c.p, c.q, c.r, c.s],
      congB3]
    let rhs : Raw := apps transD.ref [c.PT, c.V2, c.V2, c.V3,
      apps pentRefillD.ref [c.A, c.w, c.x, c.y, c.z, c.v, c.p, c.q, c.r, c.s],
      apps assocConnD.ref [c.A, c.w, c.y, c.z, c.v, c.pq, c.r, c.s]]
    pentPis (.path (.path c.PT c.V2 c.V3) lhs rhs)
  tm :=
    let c : PentCtx := {}
    pentLams (squareExchange c.PT c.V2 c.V3 (fun l m => c.W l m))

#guard pentNatWD.ok

namespace PentCtx

/-- `transFill p q @ t @ i` (a point of `A`). -/
private def pqAt (c : PentCtx) (t i : Raw) : Raw :=
  .papp (c.pqHat t) c.w (c.ql t) i

/-- The hfill of `γ0`'s composition: `γ0fill m j` at `j=1` is `γ0 m`, at
`j=0` it is `transFill p q @ m`. -/
private def g0fill (c : PentCtx) (m j i : Raw) : Raw :=
  .hcomp "j2" c.A
    [([(i, false)], c.w),
     ([(i, true)], .papp c.q c.x c.y (.imax m (.imin (.var "j2") j))),
     ([(m, true)], .papp c.pq c.w c.y i),
     ([(j, false)], c.pqAt m i)]
    (c.pqAt m i)

/-- The box-with-lid cell: `ε u m i` connects `γ0` (at `u=0`) to
`refl (p⬝q)` (at `u=1`), with *every* edge collapsed by an
identically-true face — the walls are the fillers themselves. -/
private def epsCell (c : PentCtx) (u m i : Raw) : Raw :=
  .hcomp "j" c.A
    [([(i, false)], c.w),
     ([(i, true)],
       .papp c.q c.x c.y (.imax (.imin m (.ineg u)) (.var "j"))),
     ([(u, false)], c.g0fill m (.var "j") i),
     ([(u, true)], c.pqAt (.var "j") i),
     ([(m, false)], c.pqAt (.var "j") i),
     ([(m, true)], c.pqAt (.imax (.ineg u) (.var "j")) i)]
    (c.pqAt (.imin m (.ineg u)) i)

end PentCtx

/-- **The refill cell is `refl`**: `pentRefill ≡ refl` at
`(p⬝q)⬝(r⬝s)`, by the box-with-lid argument. -/
def pentRefillReflD : LibDef where
  name := "pentRefillRefl"
  ty :=
    let c : PentCtx := {}
    pentPis (.path (.path c.PT c.V2 c.V2)
      (apps pentRefillD.ref [c.A, c.w, c.x, c.y, c.z, c.v,
        c.p, c.q, c.r, c.s])
      (apps reflD.ref [c.PT, c.V2]))
  tm :=
    let c : PentCtx := {}
    pentLams (.plam "u" (.plam "m"
      (apps transD.ref [c.A, c.w, c.y, c.v,
        .plam "i" (c.epsCell (.var "u") (.var "m") (.var "i")),
        c.rs])))

#guard pentRefillReflD.ok

/-- **Mac Lane's pentagon, in any type** (no truncation, no `J`):
`assocConn p q (r⬝s) ⬝ assocConn (p⬝q) r s ≡
 cong (p⬝·) (assocConn q r s) ⬝ (assocConn p (q⬝r) s ⬝
   cong (·⬝s) (assocConn p q r))`. -/
def pentagonConnD : LibDef where
  name := "pentagonConn"
  ty :=
    let c : PentCtx := {}
    let congB1 : Raw := apps congD.ref [.path c.A c.x c.v, c.PT,
      .lam "h" (c.t3 c.w c.x c.v c.p (.var "h")),
      c.t3 c.x c.y c.v c.q c.rs, c.t3 c.x c.z c.v c.qr c.s,
      apps assocConnD.ref [c.A, c.x, c.y, c.z, c.v, c.q, c.r, c.s]]
    let congB3 : Raw := apps congD.ref [.path c.A c.w c.z, c.PT,
      .lam "h" (c.t3 c.w c.z c.v (.var "h") c.s),
      c.t3 c.w c.x c.z c.p c.qr, c.t3 c.w c.y c.z c.pq c.r,
      apps assocConnD.ref [c.A, c.w, c.x, c.y, c.z, c.p, c.q, c.r]]
    let lam0 : Raw := apps assocConnD.ref [c.A, c.w, c.x, c.y, c.v,
      c.p, c.q, c.rs]
    let psi1 : Raw := apps assocConnD.ref [c.A, c.w, c.y, c.z, c.v,
      c.pq, c.r, c.s]
    let psi0 : Raw := apps assocConnD.ref [c.A, c.w, c.x, c.z, c.v,
      c.p, c.qr, c.s]
    let routeA : Raw := apps transD.ref [c.PT, c.V1, c.V2, c.V3, lam0, psi1]
    let routeB : Raw := apps transD.ref [c.PT, c.V1, c.V5, c.V3, congB1,
      apps transD.ref [c.PT, c.V5, c.V4, c.V3, psi0, congB3]]
    pentPis (.path (.path c.PT c.V1 c.V3) routeA routeB)
  tm :=
    let c : PentCtx := {}
    let args : List Raw :=
      [c.A, c.w, c.x, c.y, c.z, c.v, c.p, c.q, c.r, c.s]
    let congB1 : Raw := apps congD.ref [.path c.A c.x c.v, c.PT,
      .lam "h" (c.t3 c.w c.x c.v c.p (.var "h")),
      c.t3 c.x c.y c.v c.q c.rs, c.t3 c.x c.z c.v c.qr c.s,
      apps assocConnD.ref [c.A, c.x, c.y, c.z, c.v, c.q, c.r, c.s]]
    let congB3 : Raw := apps congD.ref [.path c.A c.w c.z, c.PT,
      .lam "h" (c.t3 c.w c.z c.v (.var "h") c.s),
      c.t3 c.w c.x c.z c.p c.qr, c.t3 c.w c.y c.z c.pq c.r,
      apps assocConnD.ref [c.A, c.w, c.x, c.y, c.z, c.p, c.q, c.r]]
    let lam0 : Raw := apps assocConnD.ref [c.A, c.w, c.x, c.y, c.v,
      c.p, c.q, c.rs]
    let psi1 : Raw := apps assocConnD.ref [c.A, c.w, c.y, c.z, c.v,
      c.pq, c.r, c.s]
    let psi0 : Raw := apps assocConnD.ref [c.A, c.w, c.x, c.z, c.v,
      c.p, c.qr, c.s]
    let pDiag : Raw := apps pentDiagD.ref args
    let pRefill : Raw := apps pentRefillD.ref args
    let rV2 : Raw := apps reflD.ref [c.PT, c.V2]
    let c2 (X Y Z e1 e2 : Raw) : Raw :=
      apps transD.ref [c.PT, X, Y, Z, e1, e2]
    let V23 : Raw := .path c.PT c.V2 c.V3
    let V13 : Raw := .path c.PT c.V1 c.V3
    let V14 : Raw := .path c.PT c.V1 c.V4
    let V22 : Raw := .path c.PT c.V2 c.V2
    let E1 : Raw := c2 c.V1 c.V2 c.V3 lam0 psi1
    let E2 : Raw := c2 c.V1 c.V2 c.V3 lam0 (c2 c.V2 c.V2 c.V3 rV2 psi1)
    let E3 : Raw := c2 c.V1 c.V2 c.V3 lam0 (c2 c.V2 c.V2 c.V3 pRefill psi1)
    let E4 : Raw := c2 c.V1 c.V2 c.V3 lam0 (c2 c.V2 c.V4 c.V3 pDiag congB3)
    let E5 : Raw := c2 c.V1 c.V4 c.V3 (c2 c.V1 c.V2 c.V4 lam0 pDiag) congB3
    let E6 : Raw := c2 c.V1 c.V4 c.V3 (c2 c.V1 c.V5 c.V4 congB1 psi0) congB3
    let E7 : Raw := c2 c.V1 c.V5 c.V3 congB1 (c2 c.V5 c.V4 c.V3 psi0 congB3)
    let whiskL0 (X Y e : Raw) : Raw := apps congD.ref [V23, V13,
      .lam "h" (c2 c.V1 c.V2 c.V3 lam0 (.var "h")), X, Y, e]
    let a1 : Raw := whiskL0 psi1 (c2 c.V2 c.V2 c.V3 rV2 psi1)
      (apps symmD.ref [V23, c2 c.V2 c.V2 c.V3 rV2 psi1, psi1,
        apps transReflLD.ref [c.PT, c.V2, c.V3, psi1]])
    let a2 : Raw := whiskL0 (c2 c.V2 c.V2 c.V3 rV2 psi1)
      (c2 c.V2 c.V2 c.V3 pRefill psi1)
      (apps congD.ref [V22, V23,
        .lam "h" (c2 c.V2 c.V2 c.V3 (.var "h") psi1), rV2, pRefill,
        apps symmD.ref [V22, pRefill, rV2,
          apps pentRefillReflD.ref args]])
    let a3 : Raw := whiskL0 (c2 c.V2 c.V2 c.V3 pRefill psi1)
      (c2 c.V2 c.V4 c.V3 pDiag congB3)
      (apps symmD.ref [V23, c2 c.V2 c.V4 c.V3 pDiag congB3,
        c2 c.V2 c.V2 c.V3 pRefill psi1,
        apps pentNatWD.ref args])
    let a4 : Raw := apps assocConnD.ref [c.PT, c.V1, c.V2, c.V4, c.V3,
      lam0, pDiag, congB3]
    let a5 : Raw := apps congD.ref [V14, V13,
      .lam "h" (c2 c.V1 c.V4 c.V3 (.var "h") congB3),
      c2 c.V1 c.V2 c.V4 lam0 pDiag, c2 c.V1 c.V5 c.V4 congB1 psi0,
      apps symmD.ref [V14, c2 c.V1 c.V5 c.V4 congB1 psi0,
        c2 c.V1 c.V2 c.V4 lam0 pDiag,
        apps pentNatLD.ref args]]
    let a6 : Raw := apps symmD.ref [V13, E7, E6,
      apps assocConnD.ref [c.PT, c.V1, c.V5, c.V4, c.V3,
        congB1, psi0, congB3]]
    pentLams (chain3 V13 E7
      [(E1, a1), (E2, a2), (E3, a3), (E4, a4), (E5, a5), (E6, a6)])

#guard pentagonConnD.ok

end Cubical.Library

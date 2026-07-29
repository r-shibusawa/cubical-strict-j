import FormalizedMathematics.Cubical.LibWord

/-! # Word problems over cellular contexts, II: a faithful matrix invariant

The `F₂` cover of the figure eight (`helixF2`/`windF2`) is complete
but hits a normalization wall on composite loops: its fiber is the
type of *reduced words*, a Σ whose values carry `IsTrue` proofs, and
whose cover equivalence embeds the `isSetF2` proof — every Kan step
walks that proof.

This file replaces the carrier, not the kernel: the **Sanov
representation** `F₂ ↪ SL₂(ℤ)`, `L ↦ [[1,2],[0,1]]`,
`R ↦ [[1,0],[2,1]]`, is *faithful*, and its carrier is the flat
proof-free type `ℤ⁴` (a matrix, as a pair of row pairs).  Each circle
of the wedge winds by right-multiplication with its generator matrix —
an equivalence with an elementary integer-arithmetic inverse.  The
winding of a loop is then the matrix of its word.  Measured outcomes
(`lake exe sanov`, machine-checked against expected matrices):

* the generators wind to their Sanov matrices in *milliseconds*
  (`windF2`: seconds), inverses to the inverse matrices;
* **iterated per-generator transport** — one Glue-transport per
  letter, feeding the concrete matrix forward — runs at < 1 ms per
  letter: `L·R ↦ [[5,2],[2,1]]` and `R·L ↦ [[1,2],[2,5]]` are
  **distinct** (separating a pair every abelian invariant conflates),
  and the commutator `L·R·L⁻¹·R⁻¹ ↦ [[21,-8],[8,-3]] ≠ I`.  This is
  the practical word-problem procedure, linear in word length; its
  agreement with the direct composite-loop winding is the library's
  `congTrans` (push `cong helixSL` through `trans`) + `transpTrans`
  (transport along a `trans` of type paths = composed transports).
* direct transport along `trans`-composite loops marks the remaining
  kernel frontier: one nested `hcomp`-in-`U` layer completes in ~1 min
  (`L⬝L⁻¹ ↦ I`, and the wedge-conjugated `R ↦ [[1,0],[2,1]]`); three
  layers (`L⬝R`) blow up superlinearly (aborted past 50 CPU-min) —
  the identified fix is kernel value-sharing across Kan steps.

Faithfulness of the Sanov representation means this single flat
invariant decides the full word problem of `F₂`. -/

namespace Cubical.Library

open Raw

/-! ## Integer cancellation lemmas -/

private def vx : Raw := .var "x"
private def vy : Raw := .var "y"
private def addZ (a b : Raw) : Raw := apps addD.ref [a, b]
private def negA (a : Raw) : Raw := .app negZD.ref a
private def dbl (a : Raw) : Raw := addZ a a
private def zeroZ : Raw := posZ 0

/-- `x + (−x + y) ≡ y` — associate, cancel, unit. -/
def addCancelD : LibDef where
  name := "addCancel"
  ty := .pi "x" .int (.pi "y" .int
    (.path .int (addZ vx (addZ (negA vx) vy)) vy))
  tm :=
    let A : Raw := addZ vx (addZ (negA vx) vy)
    let B1 : Raw := addZ (addZ vx (negA vx)) vy
    let B2 : Raw := addZ zeroZ vy
    let s1 : Raw := apps symmD.ref [.int, B1, A,
      apps addAssocD.ref [vx, negA vx, vy]]
    let s2 : Raw := apps congD.ref [.int, .int,
      .lam "w" (addZ (.var "w") vy),
      addZ vx (negA vx), zeroZ,
      .app addInvRD.ref vx]
    let s3 : Raw := .app addZeroLD.ref vy
    lams ["x", "y"] (apps transD.ref [.int, A, B2, vy,
      apps transD.ref [.int, A, B1, B2, s1, s2], s3])

#guard addCancelD.ok

/-- `(−x) + (x + y) ≡ y` — the mirror cancellation. -/
def addCancelND : LibDef where
  name := "addCancelN"
  ty := .pi "x" .int (.pi "y" .int
    (.path .int (addZ (negA vx) (addZ vx vy)) vy))
  tm :=
    let A : Raw := addZ (negA vx) (addZ vx vy)
    let B1 : Raw := addZ (addZ (negA vx) vx) vy
    let B2 : Raw := addZ zeroZ vy
    let s1 : Raw := apps symmD.ref [.int, B1, A,
      apps addAssocD.ref [negA vx, vx, vy]]
    let s2 : Raw := apps congD.ref [.int, .int,
      .lam "w" (addZ (.var "w") vy),
      addZ (negA vx) vx, zeroZ,
      .app addInvLD.ref vx]
    let s3 : Raw := .app addZeroLD.ref vy
    lams ["x", "y"] (apps transD.ref [.int, A, B2, vy,
      apps transD.ref [.int, A, B1, B2, s1, s2], s3])

#guard addCancelND.ok

/-! ## The Sanov generator matrices as equivalences of `ℤ⁴`

Row-major matrices `((a,b),(c,d))`; the generators act by
right-multiplication on each row: `(a,b)·L = (a, 2a+b)`,
`(a,b)·R = (a+2b, b)`.  Inverses prepend the negated double; the
round trips are exactly the two cancellation lemmas, componentwise. -/

private def P2 : Raw := .sigma "u" .int .int
/-- `ℤ⁴` — a 2×2 integer matrix as a pair of row pairs. -/
def sanovTy : Raw := .sigma "v" P2 P2
private def M4 : Raw := sanovTy
/-- A matrix value `((a,b),(c,d))`, row-major. -/
def sanovMk (a b c d : Raw) : Raw := .pair (.pair a b) (.pair c d)
private def mkM (a b c d : Raw) : Raw := sanovMk a b c d
private def vv : Raw := .var "v"
private def ra : Raw := .fst (.fst vv)
private def rb : Raw := .snd (.fst vv)
private def rc : Raw := .fst (.snd vv)
private def rd : Raw := .snd (.snd vv)

/-- `addCancel` at `(x, y)`, applied at `i`. -/
private def cAt (x y : Raw) : Raw :=
  .papp (apps addCancelD.ref [x, y])
    (addZ x (addZ (negA x) y)) y (.var "i")

/-- `addCancelN` at `(x, y)`, applied at `i`. -/
private def cNAt (x y : Raw) : Raw :=
  .papp (apps addCancelND.ref [x, y])
    (addZ (negA x) (addZ x y)) y (.var "i")

/-- Right-multiplication by `L = [[1,2],[0,1]]` is an equivalence. -/
def sanovLD : LibDef where
  name := "sanovL"
  ty := equivR M4 M4
  tm :=
    let f : Raw := .lam "v" (mkM ra (addZ (dbl ra) rb) rc (addZ (dbl rc) rd))
    let g : Raw := .lam "v"
      (mkM ra (addZ (negA (dbl ra)) rb) rc (addZ (negA (dbl rc)) rd))
    let s : Raw := .lam "v"
      (.plam "i" (mkM ra (cAt (dbl ra) rb) rc (cAt (dbl rc) rd)))
    let t : Raw := .lam "v"
      (.plam "i" (mkM ra (cNAt (dbl ra) rb) rc (cNAt (dbl rc) rd)))
    apps isoToEquivD.ref [M4, M4, f, g, s, t]

#guard sanovLD.ok

/-- Right-multiplication by `R = [[1,0],[2,1]]` is an equivalence. -/
def sanovRD : LibDef where
  name := "sanovR"
  ty := equivR M4 M4
  tm :=
    let f : Raw := .lam "v" (mkM (addZ (dbl rb) ra) rb (addZ (dbl rd) rc) rd)
    let g : Raw := .lam "v"
      (mkM (addZ (negA (dbl rb)) ra) rb (addZ (negA (dbl rd)) rc) rd)
    let s : Raw := .lam "v"
      (.plam "i" (mkM (cAt (dbl rb) ra) rb (cAt (dbl rd) rc) rd))
    let t : Raw := .lam "v"
      (.plam "i" (mkM (cNAt (dbl rb) ra) rb (cNAt (dbl rd) rc) rd))
    apps isoToEquivD.ref [M4, M4, f, g, s, t]

#guard sanovRD.ok

/-! ## The `SL₂(ℤ)` cover of the figure eight -/

private def w8T : Raw := wedge .s1 .s1 .sbase .sbase
private def w8base : Raw := .pinl .sbase

/-- **The Sanov cover**: each circle winds `ℤ⁴` by right-multiplication
with its generator matrix. -/
def helixSLD : LibDef where
  name := "helixSL"
  ty := .arr w8T .univ
  tm := .lam "p" (.pushrec "k" .univ
    (.lam "x" (.s1elim "x2" .univ M4
      (apps uaD.ref [M4, M4, sanovLD.ref]) (.var "x")))
    (.lam "x" (.s1elim "x2" .univ M4
      (apps uaD.ref [M4, M4, sanovRD.ref]) (.var "x")))
    (.lam "u" (.plam "i" M4))
    (.var "p"))

#guard helixSLD.ok

/-- **The matrix winding**: transport the identity matrix along the
Sanov cover — a loop computes to the Sanov matrix of its word. -/
def windSLD : LibDef where
  name := "windSL"
  ty := .arr (.path w8T w8base w8base) M4
  tm := .lam "p" (.transp "i"
    (.app helixSLD.ref (.papp (.var "p") w8base w8base (.var "i")))
    (mkM (posZ 1) zeroZ zeroZ (posZ 1)))

#guard windSLD.ok

/-! ## The loops

The winding *computations* (generators to their Sanov matrices, the
non-abelian separation `L·R ≠ R·L`, cancellation back to the
identity) run in the compiled harness `Test/Sanov.lean`; results are
recorded there and in docs/WordProblem.md. -/

def w8LoopL : Raw := .plam "i" (.pinl (.sloop (.var "i")))
def w8LoopLinv : Raw := .plam "i" (.pinl (.sloop (.ineg (.var "i"))))
private def pushPT : Raw := .plam "i"
  (.ppush (.lam "u0" .sbase) (.lam "u0" .sbase) .tt (.var "i"))
private def pinrBase : Raw := .pinr .sbase
/-- The right generator, conjugated through the wedge path. -/
def w8LoopR : Raw :=
  apps transD.ref [w8T, w8base, pinrBase, w8base,
    apps transD.ref [w8T, w8base, pinrBase, pinrBase, pushPT,
      .plam "i" (.pinr (.sloop (.var "i")))],
    apps symmD.ref [w8T, w8base, pinrBase, pushPT]]
/-- Loop composition at the wedge basepoint. -/
def w8Comp (p q : Raw) : Raw :=
  apps transD.ref [w8T, w8base, w8base, w8base, p, q]

end Cubical.Library

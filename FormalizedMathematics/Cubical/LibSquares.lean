import FormalizedMathematics.Cubical.LibSwitchover

/-! # Dimension-2 strictness probes

The dimension-1 reparametrization coherence theorem (docs/ReparamCoherence.md) says the
connection algebra acts on a generic *path* faithfully as the free
De Morgan algebra.  This file opens dimension 2: a generic 2-loop
`q : Path (Path A a a) refl refl` carries an action of *pairs* of
De Morgan formulas, `q(φ)(ψ) := (q @ φ) @ ψ`, and the probes below map
which identifications of reparametrized squares are definitional.

Theorem C₂ (paper proof: docs/ReparamCoherence2.md): call (φ,ψ)
*degenerate* if φ ∈ {0,1} or ψ ∈ {0,1} **in the free De Morgan
algebra** (the kernel's papp collapse is DNF-based, so this is exact).
Then `⟨i⟩⟨j⟩ q(φ)(ψ) ≡ ⟨i⟩⟨j⟩ q(φ')(ψ')` iff either both pairs are
degenerate (all degenerate squares collapse to the constant square),
or neither is and (φ,ψ) = (φ',ψ') in DM(i,j)².  The probes below are
the machine evidence for every clause: the strict identifications,
the degenerate collapse, and the separations.

Notable expected *negative*: transposition `⟨i⟩⟨j⟩ q(j)(i)` is NOT
convertible with `⟨i⟩⟨j⟩ q(i)(j)` — the definitional shadow of
Eckmann–Hilton being weak (the swap needs hcomp-generating structure).
-/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

private def A : Raw := .var "A"
private def a : Raw := .var "a"
private def q : Raw := .var "q"
private def rfla : Raw := apps reflD.ref [A, a]
/-- `Path A a a` — the type of 1-loops. -/
private def LoopT : Raw := .path A a a
/-- `Path (Path A a a) refl refl` — the type of generic 2-loops. -/
private def SqT : Raw := .path LoopT rfla rfla

private def ctxQ (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "q" SqT body))

/-- `q(φ)(ψ) := (q @ φ) @ ψ : A`. -/
private def qat (f s : Raw) : Raw :=
  .papp (.papp q rfla rfla f) a a s

/-- `⟨i⟩⟨j⟩ q(φ)(ψ)` — a reparametrized square. -/
private def sq (f s : Raw) : Raw := .plam "i" (.plam "j" (qat f s))

private def vi : Raw := .var "i"
private def vj : Raw := .var "j"

/-! ## Positive probes: the DM² action is strict -/

/-- Idempotence in the second coordinate:
`⟨i⟩⟨j⟩ q(i)(j∧j) ≐ ⟨i⟩⟨j⟩ q(i)(j)`. -/
def sq2IdemD : LibDef where
  name := "sq2Idem"
  ty := ctxQ (.path SqT (sq vi (.imin vj vj)) (sq vi vj))
  tm := lams ["A", "a", "q"] (.plam "k" (sq vi vj))

#guard sq2IdemD.ok

/-- Involution in the first coordinate:
`⟨i⟩⟨j⟩ q(¬¬i)(j) ≐ ⟨i⟩⟨j⟩ q(i)(j)`. -/
def sq2InvolD : LibDef where
  name := "sq2Invol"
  ty := ctxQ (.path SqT (sq (.ineg (.ineg vi)) vj) (sq vi vj))
  tm := lams ["A", "a", "q"] (.plam "k" (sq vi vj))

#guard sq2InvolD.ok

/-- Cross-coordinate absorption:
`⟨i⟩⟨j⟩ q(i)(j∧(j∨i)) ≐ ⟨i⟩⟨j⟩ q(i)(j)`. -/
def sq2AbsorbD : LibDef where
  name := "sq2Absorb"
  ty := ctxQ (.path SqT (sq vi (.imin vj (.imax vj vi))) (sq vi vj))
  tm := lams ["A", "a", "q"] (.plam "k" (sq vi vj))

#guard sq2AbsorbD.ok

/-- De Morgan duality with both coordinates in play, stated at the
dependent square type matching the actual `i = 1` edge
`⟨j⟩ q(¬j)(j)` (cf. the dimension-1 `strictDeMorgan` probe):
`⟨i⟩⟨j⟩ q(¬(i∧j))(j) ≐ ⟨i⟩⟨j⟩ q(¬i∨¬j)(j)`. -/
def sq2DeMorganD : LibDef where
  name := "sq2DeMorgan"
  ty :=
    let edge1 : Raw := .plam "j" (qat (.ineg vj) vj)
    let SqDM : Raw := .pathP "i" LoopT rfla edge1
    ctxQ (.path SqDM
      (sq (.ineg (.imin vi vj)) vj)
      (sq (.imax (.ineg vi) (.ineg vj)) vj))
  tm := lams ["A", "a", "q"]
    (.plam "k" (sq (.ineg (.imin vi vj)) vj))

#guard sq2DeMorganD.ok

/-! ## Negative probes: what dimension 2 does NOT identify -/

-- Controls: both negative-probe left-hand squares ARE well-typed at
-- `SqT` (their boundaries collapse to `refl`), so the failures below
-- are conversion failures, not typing artifacts.
def sq2TransposeCtrlD : LibDef where
  name := "sq2TransposeCtrl"
  ty := ctxQ SqT
  tm := lams ["A", "a", "q"] (sq vj vi)

#guard sq2TransposeCtrlD.ok

def sq2DiagCtrlD : LibDef where
  name := "sq2DiagCtrl"
  ty := ctxQ SqT
  tm := lams ["A", "a", "q"] (sq (.imin vi vj) (.imax vi vj))

#guard sq2DiagCtrlD.ok

-- Transposition FAILS: `⟨i⟩⟨j⟩ q(j)(i) ≢ ⟨i⟩⟨j⟩ q(i)(j)`.
-- (The two-level neutral spines carry the generic dimensions in
-- swapped positions; no DM identity relates them.  This is the
-- definitional shadow of Eckmann–Hilton being weak.)
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" (sq vi vj)))
  (ctxQ (.path SqT (sq vj vi) (sq vi vj))))

-- Distinct diagonal pair FAILS:
-- `⟨i⟩⟨j⟩ q(i∧j)(i∨j) ≢ ⟨i⟩⟨j⟩ q(i)(j)` (corners agree, formulas differ).
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" (sq vi vj)))
  (ctxQ (.path SqT (sq (.imin vi vj) (.imax vi vj)) (sq vi vj))))

/-! ## Degenerate collapse: one endpoint coordinate kills the square -/

private def sqConst : Raw := .plam "i" (.plam "j" a)

/-- First coordinate an endpoint: `⟨i⟩⟨j⟩ q(0)(j) ≐ ⟨i⟩⟨j⟩ a`
(inner papp collapses to `refl`, which absorbs the second papp). -/
def sq2DegFstD : LibDef where
  name := "sq2DegFst"
  ty := ctxQ (.path SqT (sq .i0 vj) sqConst)
  tm := lams ["A", "a", "q"] (.plam "k" sqConst)

#guard sq2DegFstD.ok

/-- Second coordinate an endpoint: `⟨i⟩⟨j⟩ q(i)(0) ≐ ⟨i⟩⟨j⟩ a`
(the outer papp of the *neutral* `q(i)` collapses to the stored
endpoint). -/
def sq2DegSndD : LibDef where
  name := "sq2DegSnd"
  ty := ctxQ (.path SqT (sq vi .i0) sqConst)
  tm := lams ["A", "a", "q"] (.plam "k" sqConst)

#guard sq2DegSndD.ok

/-- Two different-looking degenerate squares are equal:
`⟨i⟩⟨j⟩ q(0)(j) ≐ ⟨i⟩⟨j⟩ q(1)(i∨j)` — the degenerate class is a
single point. -/
def sq2DegCrossD : LibDef where
  name := "sq2DegCross"
  ty := ctxQ (.path SqT (sq .i0 vj) (sq .i1 (.imax vi vj)))
  tm := lams ["A", "a", "q"] (.plam "k" (sq .i1 (.imax vi vj)))

#guard sq2DegCrossD.ok

/-! ## No excluded middle at dimension 2

`i∧¬i` is NOT an endpoint of the free De Morgan algebra, so
`(i∧¬i, j)` is non-degenerate: the square stays a neutral spine and
is separated from the constant square — even though every *corner*
of `i∧¬i` is `0`. -/

-- Control: the square is well-typed at `SqT` (all its edges collapse).
def sq2LEMCtrlD : LibDef where
  name := "sq2LEMCtrl"
  ty := ctxQ SqT
  tm := lams ["A", "a", "q"] (sq (.imin vi (.ineg vi)) vj)

#guard sq2LEMCtrlD.ok

-- `⟨i⟩⟨j⟩ q(i∧¬i)(j) ≢ ⟨i⟩⟨j⟩ a`.
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" sqConst))
  (ctxQ (.path SqT (sq (.imin vi (.ineg vi)) vj) sqConst)))

/-! ## Multi-cell layer (C-3): distinct cells never interact strictly

Context with a generic 1-loop `p` and two generic 2-loops `q, r`.
The pure reparametrization layer over several cells is the **wedge**
of the single-cell layers: the degenerate class is one shared point,
and non-degenerate cubes are separated by cell identity (head) and
spine depth in addition to their formula tuples. -/

private def pv : Raw := .var "p"
private def rv : Raw := .var "r"

private def ctxM (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A")
    (.pi "p" LoopT (.pi "q" SqT (.pi "r" SqT body))))

/-- `c(φ)(ψ)` for a generic 2-loop variable `c`. -/
private def cat (c f s : Raw) : Raw :=
  .papp (.papp c rfla rfla f) a a s

private def sqc (c f s : Raw) : Raw := .plam "i" (.plam "j" (cat c f s))

/-- Cross-cell degenerate collapse: the wedge point is shared —
`⟨i⟩⟨j⟩ q(0)(j) ≐ ⟨i⟩⟨j⟩ r(i)(1)` (both collapse to the constant
square, though built from different cells). -/
def sqxDegD : LibDef where
  name := "sqxDeg"
  ty := ctxM (.path SqT (sqc q .i0 vj) (sqc rv vi .i1))
  tm := lams ["A", "a", "p", "q", "r"] (.plam "k" (sqc rv vi .i1))

#guard sqxDegD.ok

-- Distinct cells, same formulas: SEPARATED —
-- `⟨i⟩⟨j⟩ q(i)(j) ≢ ⟨i⟩⟨j⟩ r(i)(j)` (heads are different variables).
#guard !(okD
  (lams ["A", "a", "p", "q", "r"] (.plam "k" (sqc rv vi vj)))
  (ctxM (.path SqT (sqc q vi vj) (sqc rv vi vj))))

/-- Control: the 1-cell square `⟨i⟩⟨j⟩ p((i∧¬i)∧(j∧¬j))` is well-typed
at `SqT` (all four edges hit `0`), and non-degenerate in the interior
(the formula is nonzero in the free De Morgan algebra). -/
def sqxDepthCtrlD : LibDef where
  name := "sqxDepthCtrl"
  ty := ctxM SqT
  tm := lams ["A", "a", "p", "q", "r"]
    (.plam "i" (.plam "j" (.papp pv a a
      (.imin (.imin vi (.ineg vi)) (.imin vj (.ineg vj))))))

#guard sqxDepthCtrlD.ok

-- Spine-depth separation: a 1-cell square is never convertible with a
-- 2-cell square — `⟨i⟩⟨j⟩ p((i∧¬i)∧(j∧¬j)) ≢ ⟨i⟩⟨j⟩ q(i∧¬i)(j∧¬j)`
-- (both well-typed at SqT, both non-degenerate; the spines have
-- different depths).
#guard !(okD
  (lams ["A", "a", "p", "q", "r"]
    (.plam "k" (sqc q (.imin vi (.ineg vi)) (.imin vj (.ineg vj)))))
  (ctxM (.path SqT
    (.plam "i" (.plam "j" (.papp pv a a
      (.imin (.imin vi (.ineg vi)) (.imin vj (.ineg vj))))))
    (sqc q (.imin vi (.ineg vi)) (.imin vj (.ineg vj))))))

/-! ## C-4 ingredients: the free De Morgan cube-category action

The assignment `φ⃗ ↦ ⟨i⃗⟩ q(φ⃗)` is an *action* of the hom-sets of the
De Morgan cube category (morphisms `[m] → [n]` = n-tuples over
DM(i₁..i_m), composition = substitution).  The probes below check that
the action is **strict**: the identity morphism acts as the identity
(path η, twice) and composition of reparametrizations is definitional
(β for path abstraction = formula substitution).  Together with C₂'s
faithfulness and the degeneracy collapse (= factoring through a face),
this gives the characterization: the strict layer of a generic n-cell
is the boundary-collapsed representable 𝔻(−,[n])/∂ — a "De Morgan
n-sphere" — and multi-cell contexts give wedges of these. -/

/-- Unit law of the action: the identity tuple `(i, j)` acts as the
identity — `⟨i⟩⟨j⟩ q(i)(j) ≐ q` (nested path η). -/
def sqEtaD : LibDef where
  name := "sqEta"
  ty := ctxQ (.path SqT (sq vi vj) q)
  tm := lams ["A", "a", "q"] (.plam "k" q)

#guard sqEtaD.ok

/-- Composition law of the action: reparametrizing a reparametrized
square substitutes the formulas —
`⟨i⟩⟨j⟩ (⟨u⟩⟨v⟩ q(u)(v))(i∨j)(i∧j) ≐ ⟨i⟩⟨j⟩ q(i∨j)(i∧j)`. -/
def sqCloneCompD : LibDef where
  name := "sqCloneComp"
  ty :=
    let Ssq : Raw := .plam "u" (.plam "v" (qat (.var "u") (.var "v")))
    let lhs : Raw := .plam "i" (.plam "j"
      (.papp (.papp (.ann Ssq SqT) rfla rfla (.imax vi vj))
        a a (.imin vi vj)))
    ctxQ (.path SqT lhs (sq (.imax vi vj) (.imin vi vj)))
  tm := lams ["A", "a", "q"]
    (.plam "k" (sq (.imax vi vj) (.imin vi vj)))

#guard sqCloneCompD.ok

/-- Control: the diagonal `[1] → [2]`, `i ↦ (i, i)`, gives a
well-typed 1-cube `⟨i⟩ q(i)(i) : Path A a a` from the 2-cell `q` —
the partial/lower-dimensional layer of the action. -/
def sqDiagCtrlD : LibDef where
  name := "sqDiagCtrl"
  ty := ctxQ LoopT
  tm := lams ["A", "a", "q"] (.plam "i" (qat vi vi))

#guard sqDiagCtrlD.ok

-- Distinct non-degenerate `[1] → [2]` morphisms are separated:
-- `⟨i⟩ q(i)(i) ≢ ⟨i⟩ q(i)(¬i)` (the diagonal vs the anti-diagonal).
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" (.plam "i" (qat vi (.ineg vi)))))
  (ctxQ (.path LoopT
    (.plam "i" (qat vi vi))
    (.plam "i" (qat vi (.ineg vi))))))

/-! ## Fiberwise sharpness probes (algebraic boundaries)

Level 0: a generic loop's two orientations `⟨i⟩p(i)` and `⟨i⟩p(¬i)`
share their term-level boundary `(a, a)` but lie over distinct
algebraic boundaries `(0,1)` vs `(1,0)`, and are definitionally
separated.  Level 1: over a generic 2-loop, with `t = k∧¬k`,
`dᵢ = i∧¬i`, `dⱼ = j∧¬j`, the 3-cubes
`H = ⟨k⟩⟨i⟩⟨j⟩ q(t∧dᵢ)(t∧dⱼ)` and `H′ = ⟨k⟩⟨i⟩⟨j⟩ q(t∧dⱼ)(t∧dᵢ)`
are term-level homotopies between constant squares, every face
constant, yet definitionally distinct — their formula tuples
restrict differently on faces (`(0, t∧dⱼ)` vs `(t∧dⱼ, 0)` at
`i = 0`).  The *impossibility* of a strict homotopy inside each
pair is the universally quantified pen-and-paper half; the probes
record the well-typedness controls and the separations. -/

private def ctxP (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "p" LoopT body))

private def pat (f : Raw) : Raw := .papp pv a a f

/-- Orientation control: `⟨i⟩ p(¬i) : Path A a a` is well typed. -/
def sqOrientCtrlD : LibDef where
  name := "sqOrientCtrl"
  ty := ctxP LoopT
  tm := lams ["A", "a", "p"] (.plam "i" (pat (.ineg vi)))

#guard sqOrientCtrlD.ok

-- Orientation separation: `⟨i⟩ p(i) ≢ ⟨i⟩ p(¬i)`.
#guard !(okD
  (lams ["A", "a", "p"] (.plam "k" (.plam "i" (pat (.ineg vi)))))
  (ctxP (.path LoopT
    (.plam "i" (pat vi))
    (.plam "i" (pat (.ineg vi))))))

private def vk : Raw := .var "k"
private def tK : Raw := .imin vk (.ineg vk)
private def dI : Raw := .imin vi (.ineg vi)
private def dJ : Raw := .imin vj (.ineg vj)

/-- `⟨k⟩⟨i⟩⟨j⟩ q(f)(s)` — a reparametrized 3-cube. -/
private def cube3 (f s : Raw) : Raw :=
  .plam "k" (.plam "i" (.plam "j" (qat f s)))

private def T3 : Raw := .path SqT sqConst sqConst

/-- Tower control `H = ⟨k⟩⟨i⟩⟨j⟩ q(t∧dᵢ)(t∧dⱼ)`: a well-typed
homotopy between constant squares, all faces constant. -/
def sqTowerHD : LibDef where
  name := "sqTowerH"
  ty := ctxQ T3
  tm := lams ["A", "a", "q"] (cube3 (.imin tK dI) (.imin tK dJ))

#guard sqTowerHD.ok

/-- Tower control `H′` (coordinates swapped). -/
def sqTowerH2D : LibDef where
  name := "sqTowerH2"
  ty := ctxQ T3
  tm := lams ["A", "a", "q"] (cube3 (.imin tK dJ) (.imin tK dI))

#guard sqTowerH2D.ok

-- Tower separation: `H ≢ H′` (K2: distinct non-degenerate tuples).
#guard !(okD
  (lams ["A", "a", "q"] (.plam "l" (cube3 (.imin tK dI) (.imin tK dJ))))
  (ctxQ (.path T3
    (cube3 (.imin tK dJ) (.imin tK dI))
    (cube3 (.imin tK dI) (.imin tK dJ)))))

end Cubical.Library

import FormalizedMathematics.Cubical.LibSquares

/-! # Generic-boundary cells: the uncollapsed representable

The strict-layer paper (docs/paperC) proves that a generic *loop*
spans a boundary-collapsed representable — a De Morgan sphere — the
collapse being forced by the degenerate (refl) boundary.  This file
opens the sequel question flagged there: a generic square `Q` with
**generic boundary** (four generic vertices, four generic edges).

Expected picture (docs/GenericBoundary.md): the collapse disappears.
Face-instantiating `Q` now computes, definitionally, to the
*boundary cells themselves* — the attachment maps of the cube
presheaf — so the strict layer realizes the **full representable**
`𝔻(−,[2])`, glued to the edges' own strict layers along the
boundary.  The probes below machine-check the attachment equations,
the corner computations, and that the De Morgan laws stay strict in
the presence of a generic boundary. -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

private def A : Raw := .var "A"
private def a00 : Raw := .var "a00"
private def a01 : Raw := .var "a01"
private def a10 : Raw := .var "a10"
private def a11 : Raw := .var "a11"
private def pE : Raw := .var "p"   -- i = 0 edge : Path A a00 a01
private def qE : Raw := .var "q"   -- i = 1 edge : Path A a10 a11
private def rE : Raw := .var "r"   -- j = 0 edge : Path A a00 a10
private def sE : Raw := .var "s"   -- j = 1 edge : Path A a01 a11
private def Qv : Raw := .var "Q"
private def vi : Raw := .var "i"
private def vj : Raw := .var "j"

/-- The generic-boundary square type
`Sq := PathP (⟨i⟩ Path A (r i) (s i)) p q`. -/
private def SqB : Raw :=
  .pathP "i"
    (.path A (.papp rE a00 a10 vi) (.papp sE a01 a11 vi))
    pE qE

private def ctxB (body : Raw) : Raw :=
  .pi "A" .univ
    (.pi "a00" A (.pi "a01" A (.pi "a10" A (.pi "a11" A
    (.pi "p" (.path A a00 a01) (.pi "q" (.path A a10 a11)
    (.pi "r" (.path A a00 a10) (.pi "s" (.path A a01 a11)
    (.pi "Q" SqB body)))))))))

/-- `Q(φ)(ψ)` with the boundary-typed endpoint annotations. -/
private def Qat (f g : Raw) : Raw :=
  .papp (.papp Qv pE qE f)
    (.papp rE a00 a10 f) (.papp sE a01 a11 f) g

private def lamsB (body : Raw) : Raw :=
  lams ["A", "a00", "a01", "a10", "a11", "p", "q", "r", "s", "Q"] body

/-! ## Attachment equations: faces compute to the boundary cells -/

/-- `⟨j⟩ Q(0)(j) ≐ p` — the `i = 0` face of the generic square *is*
its left edge, definitionally. -/
def gbAttPD : LibDef where
  name := "gbAttP"
  ty := ctxB (.path (.path A a00 a01) (.plam "j" (Qat .i0 vj)) pE)
  tm := lamsB (.plam "k" pE)

#guard gbAttPD.ok

/-- `⟨j⟩ Q(1)(j) ≐ q`. -/
def gbAttQD : LibDef where
  name := "gbAttQ"
  ty := ctxB (.path (.path A a10 a11) (.plam "j" (Qat .i1 vj)) qE)
  tm := lamsB (.plam "k" qE)

#guard gbAttQD.ok

/-- `⟨i⟩ Q(i)(0) ≐ r` — the stored endpoint annotation of the inner
application returns the reparametrized bottom edge. -/
def gbAttRD : LibDef where
  name := "gbAttR"
  ty := ctxB (.path (.path A a00 a10) (.plam "i" (Qat vi .i0)) rE)
  tm := lamsB (.plam "k" rE)

#guard gbAttRD.ok

/-- `⟨i⟩ Q(i)(1) ≐ s`. -/
def gbAttSD : LibDef where
  name := "gbAttS"
  ty := ctxB (.path (.path A a01 a11) (.plam "i" (Qat vi .i1)) sE)
  tm := lamsB (.plam "k" sE)

#guard gbAttSD.ok

/-- Corners: `⟨i⟩⟨j⟩ Q(0)(0) ≐ ⟨i⟩⟨j⟩ a00` (two-step collapse
through the boundary). -/
def gbCornerD : LibDef where
  name := "gbCorner"
  ty := ctxB (.path (.path (.path A a00 a00)
      (.plam "j" a00) (.plam "j" a00))
    (.plam "i" (.plam "j" (Qat .i0 .i0)))
    (.plam "i" (.plam "j" a00)))
  tm := lamsB (.plam "k" (.plam "i" (.plam "j" a00)))

#guard gbCornerD.ok

/-! ## No wedge collapse: degenerate images are the boundary layer -/

/-- The formerly-degenerate square `⟨i⟩⟨j⟩ Q(0)(j)` is now the
*edge square* `⟨i⟩⟨j⟩ p(j)` — not a constant: the face-factoring
morphisms land in the boundary's own strict layer instead of a
single wedge point. -/
def gbEdgeSqD : LibDef where
  name := "gbEdgeSq"
  ty := ctxB (.path (.path (.path A a00 a01) pE pE)
    (.plam "i" (.plam "j" (Qat .i0 vj)))
    (.plam "i" (.plam "j" (.papp pE a00 a01 vj))))
  tm := lamsB (.plam "k" (.plam "i" (.plam "j" (.papp pE a00 a01 vj))))

#guard gbEdgeSqD.ok

/-! ## The De Morgan laws stay strict with a generic boundary -/

/-- Cross-coordinate absorption at the full square type:
`⟨i⟩⟨j⟩ Q(i)(j∧(j∨i)) ≐ Q`. -/
def gbAbsorbD : LibDef where
  name := "gbAbsorb"
  ty := ctxB (.path SqB
    (.plam "i" (.plam "j" (Qat vi (.imin vj (.imax vj vi)))))
    Qv)
  tm := lamsB (.plam "k" Qv)

#guard gbAbsorbD.ok

/-! ## Transposition exists across types

With a generic boundary, transposition is a *well-typed* operation
to the transposed square type (edges exchanged) — a symmetry of the
cube category acting across boundary types, rather than a
same-type identification (which typing forbids). -/

def gbTransposeCtrlD : LibDef where
  name := "gbTransposeCtrl"
  ty := ctxB (.pathP "i"
    (.path A (.papp pE a00 a01 vi) (.papp qE a10 a11 vi))
    rE sE)
  tm := lamsB (.plam "i" (.plam "j" (Qat vj vi)))

#guard gbTransposeCtrlD.ok

/-! ## Unit law at the full square type -/

/-- `⟨i⟩⟨j⟩ Q(i)(j) ≐ Q` (nested path η at the dependent square
type). -/
def gbEtaD : LibDef where
  name := "gbEta"
  ty := ctxB (.path SqB (.plam "i" (.plam "j" (Qat vi vj))) Qv)
  tm := lamsB (.plam "k" Qv)

#guard gbEtaD.ok

/-- Perturbation by the minimal edge-vanishing element is absorbed:
`i ∨ (i∧¬i∧j∧¬j) = i` in the free De Morgan algebra, so
`⟨i⟩⟨j⟩ Q(i∨(i∧¬i∧j∧¬j))(j) ≐ Q`. -/
def gbAbsorbPerturbD : LibDef where
  name := "gbAbsorbPerturb"
  ty := ctxB (.path SqB
    (.plam "i" (.plam "j" (Qat
      (.imax vi (.imin (.imin vi (.ineg vi)) (.imin vj (.ineg vj))))
      vj)))
    Qv)
  tm := lamsB (.plam "k" Qv)

#guard gbAbsorbPerturbD.ok

/-! ## Non-uniqueness of strict fillers

The one-variable restrictions of `i∧¬i` and `(i∧¬i)∧(j∨¬j)` agree on
all four edges of the square, yet the two elements are DISTINCT in
the free De Morgan algebra (the second is not absorbed: `i∧¬i` is
not below `j∨¬j`).  Hence the squares
`⟨i⟩⟨j⟩ Q(i∧¬i)(j)` and `⟨i⟩⟨j⟩ Q((i∧¬i)∧(j∨¬j))(j)` inhabit the
SAME boundary type but are NOT convertible: **a boundary in the
strict layer can have several distinct strict fillers**. -/

private def DII : Raw := .imin vi (.ineg vi)

/-- The common boundary type of the two fillers:
`PathP (⟨i⟩ Path A (r(i∧¬i)) (s(i∧¬i))) p p`. -/
private def SqLEM : Raw :=
  .pathP "i"
    (.path A (.papp rE a00 a10 DII) (.papp sE a01 a11 DII))
    pE pE

def gbFill1D : LibDef where
  name := "gbFill1"
  ty := ctxB SqLEM
  tm := lamsB (.plam "i" (.plam "j" (Qat DII vj)))

#guard gbFill1D.ok

def gbFill2D : LibDef where
  name := "gbFill2"
  ty := ctxB SqLEM
  tm := lamsB (.plam "i" (.plam "j"
    (Qat (.imin DII (.imax vj (.ineg vj))) vj)))

#guard gbFill2D.ok

-- The two fillers of the SAME boundary are separated:
#guard !(okD
  (lamsB (.plam "k" (.plam "i" (.plam "j"
    (Qat (.imin DII (.imax vj (.ineg vj))) vj)))))
  (ctxB (.path SqLEM
    (.plam "i" (.plam "j" (Qat DII vj)))
    (.plam "i" (.plam "j"
      (Qat (.imin DII (.imax vj (.ineg vj))) vj))))))

end Cubical.Library

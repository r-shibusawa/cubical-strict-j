import FormalizedMathematics.Cubical.LibGenBoundary

/-! # Two squares sharing an edge: the gluing is exactly the shared face

The colimit form of the realization theorem (docs/GenericBoundary.md
§3.3) requires: in a computad where two generic squares `Q1, Q2`
share an edge `m`, the *only* cross-cell identifications are the
shared-face composites.  The probes below check both directions:

* positive — the `i = 1` face of `Q1` and the `i = 0` face of `Q2`
  are definitionally the same square (both compute to `m`): the
  pushout identification `𝔻(−,[2]) ⊔_{𝔻(−,[1])} 𝔻(−,[2])` holds on
  the nose;
* negative — squares from the two cells whose *entire boundaries*
  collapse onto the shared edge (via the edge-one element
  `i∨¬i∨j∨¬j` for `Q1` and the edge-zero element `i∧¬i∧j∧¬j` for
  `Q2`) inhabit the same type yet remain separated, and neither is
  the reparametrized edge itself: the gluing does not over-identify.
-/

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
private def a20 : Raw := .var "a20"
private def a21 : Raw := .var "a21"
private def pE : Raw := .var "p"    -- Path A a00 a01 (i=0 side of Q1)
private def mE : Raw := .var "m"    -- Path A a10 a11 (SHARED edge)
private def qE : Raw := .var "q"    -- Path A a20 a21 (i=1 side of Q2)
private def r1 : Raw := .var "r1"   -- Path A a00 a10
private def s1 : Raw := .var "s1"   -- Path A a01 a11
private def r2 : Raw := .var "r2"   -- Path A a10 a20
private def s2 : Raw := .var "s2"   -- Path A a11 a21
private def Q1v : Raw := .var "Q1"
private def Q2v : Raw := .var "Q2"
private def vi : Raw := .var "i"
private def vj : Raw := .var "j"

private def Sq1 : Raw :=
  .pathP "i" (.path A (.papp r1 a00 a10 vi) (.papp s1 a01 a11 vi))
    pE mE

private def Sq2 : Raw :=
  .pathP "i" (.path A (.papp r2 a10 a20 vi) (.papp s2 a11 a21 vi))
    mE qE

private def ctx2 (body : Raw) : Raw :=
  .pi "A" .univ
    (.pi "a00" A (.pi "a01" A (.pi "a10" A (.pi "a11" A
    (.pi "a20" A (.pi "a21" A
    (.pi "p" (.path A a00 a01) (.pi "m" (.path A a10 a11)
    (.pi "q" (.path A a20 a21)
    (.pi "r1" (.path A a00 a10) (.pi "s1" (.path A a01 a11)
    (.pi "r2" (.path A a10 a20) (.pi "s2" (.path A a11 a21)
    (.pi "Q1" Sq1 (.pi "Q2" Sq2 body)))))))))))))))

private def lams2 (body : Raw) : Raw :=
  lams ["A", "a00", "a01", "a10", "a11", "a20", "a21",
        "p", "m", "q", "r1", "s1", "r2", "s2", "Q1", "Q2"] body

private def Q1at (f g : Raw) : Raw :=
  .papp (.papp Q1v pE mE f)
    (.papp r1 a00 a10 f) (.papp s1 a01 a11 f) g

private def Q2at (f g : Raw) : Raw :=
  .papp (.papp Q2v mE qE f)
    (.papp r2 a10 a20 f) (.papp s2 a11 a21 f) g

/-- `Path A a10 a11` — the shared edge's type. -/
private def PTm : Raw := .path A a10 a11
/-- The type of squares constant on the shared edge. -/
private def SqM : Raw := .path PTm mE mE

/-! ## The gluing identifications (positive) -/

/-- `⟨j⟩ Q1(1)(j) ≐ m` — attachment of `Q1` to the shared edge. -/
def seAttM1D : LibDef where
  name := "seAttM1"
  ty := ctx2 (.path PTm (.plam "j" (Q1at .i1 vj)) mE)
  tm := lams2 (.plam "k" mE)

#guard seAttM1D.ok

/-- `⟨j⟩ Q2(0)(j) ≐ m` — attachment of `Q2` to the shared edge. -/
def seAttM2D : LibDef where
  name := "seAttM2"
  ty := ctx2 (.path PTm (.plam "j" (Q2at .i0 vj)) mE)
  tm := lams2 (.plam "k" mE)

#guard seAttM2D.ok

/-- The two faces agree *across cells*, in dimension 2:
`⟨i⟩⟨j⟩ Q1(1)(j) ≐ ⟨i⟩⟨j⟩ Q2(0)(j)` — the pushout identification
of the colimit, on the nose. -/
def seGlueD : LibDef where
  name := "seGlue"
  ty := ctx2 (.path SqM
    (.plam "i" (.plam "j" (Q1at .i1 vj)))
    (.plam "i" (.plam "j" (Q2at .i0 vj))))
  tm := lams2 (.plam "k" (.plam "i" (.plam "j" (Q2at .i0 vj))))

#guard seGlueD.ok

/-! ## The gluing does not over-identify (negative, with controls)

`S1 := ⟨i⟩⟨j⟩ Q1(i∨¬i∨j∨¬j)(j)` (edge-one element: every boundary
restriction is `1`, so the whole boundary collapses onto `m`) and
`S2 := ⟨i⟩⟨j⟩ Q2(i∧¬i∧j∧¬j)(j)` (edge-zero element, boundary
likewise on `m`) inhabit the SAME type `Path (Path A a10 a11) m m`;
so does the reparametrized shared edge `⟨i⟩⟨j⟩ m(j)`.  All three are
pairwise separated: interior material of distinct cells never merges,
and neither collapses to the edge. -/

private def E0 : Raw :=
  .imax (.imax vi (.ineg vi)) (.imax vj (.ineg vj))
private def D0 : Raw :=
  .imin (.imin vi (.ineg vi)) (.imin vj (.ineg vj))

private def S1 : Raw := .plam "i" (.plam "j" (Q1at E0 vj))
private def S2 : Raw := .plam "i" (.plam "j" (Q2at D0 vj))
private def Sm : Raw := .plam "i" (.plam "j" (.papp mE a10 a11 vj))

def seS1CtrlD : LibDef where
  name := "seS1Ctrl"
  ty := ctx2 SqM
  tm := lams2 S1

#guard seS1CtrlD.ok

def seS2CtrlD : LibDef where
  name := "seS2Ctrl"
  ty := ctx2 SqM
  tm := lams2 S2

#guard seS2CtrlD.ok

def seSmCtrlD : LibDef where
  name := "seSmCtrl"
  ty := ctx2 SqM
  tm := lams2 Sm

#guard seSmCtrlD.ok

-- Cross-cell separation: `S1 ≢ S2`.
#guard !(okD (lams2 (.plam "k" S2)) (ctx2 (.path SqM S1 S2)))

-- Neither is the edge square: `S1 ≢ ⟨i⟩⟨j⟩ m(j)` …
#guard !(okD (lams2 (.plam "k" Sm)) (ctx2 (.path SqM S1 Sm)))

-- … and `S2 ≢ ⟨i⟩⟨j⟩ m(j)`.
#guard !(okD (lams2 (.plam "k" Sm)) (ctx2 (.path SqM S2 Sm)))

end Cubical.Library

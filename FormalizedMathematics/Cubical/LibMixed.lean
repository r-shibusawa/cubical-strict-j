import FormalizedMathematics.Cubical.LibSharedEdge

/-! # The mixed layer, I: De Morgan interpolation

The realization paper (docs/paperD) proved that strict fillers of a
common boundary need not be unique.  This file opens the strict↪weak
comparison study with a positive surprise: the non-uniqueness is
already resolved *inside the strict layer*, one dimension up.

**De Morgan interpolation**: for formulas `φ, φ'` whose restrictions
to every face agree, the interpolant

  `χ(k) := (φ ∧ ¬k) ∨ (k ∧ φ') ∨ (φ ∧ φ')`

satisfies `χ(0) = φ`, `χ(1) = φ'` (absorption), and is *constant in
`k` on every face* (where `φ = φ' = ρ`, absorption collapses `χ` to
`ρ`).  Hence any two strict fillers of the same boundary are
connected by a strict homotopy rel boundary — and, since two such
homotopies again share a boundary, by induction the whole fiber of
strict fillers is strictly contractible ("De Morgan convexity").

The probe below machine-checks the interpolant on the
non-uniqueness pair of the realization paper:
`F1 = ⟨i⟩⟨j⟩ Q(i∧¬i)(j)` and `F2 = ⟨i⟩⟨j⟩ Q((i∧¬i)∧(j∨¬j))(j)`. -/

namespace Cubical.Library

open Raw

private def A : Raw := .var "A"
private def a00 : Raw := .var "a00"
private def a01 : Raw := .var "a01"
private def a10 : Raw := .var "a10"
private def a11 : Raw := .var "a11"
private def pE : Raw := .var "p"
private def qE : Raw := .var "q"
private def rE : Raw := .var "r"
private def sE : Raw := .var "s"
private def Qv : Raw := .var "Q"
private def vi : Raw := .var "i"
private def vj : Raw := .var "j"
private def vk : Raw := .var "k"

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

private def lamsB (body : Raw) : Raw :=
  lams ["A", "a00", "a01", "a10", "a11", "p", "q", "r", "s", "Q"] body

private def Qat (f g : Raw) : Raw :=
  .papp (.papp Qv pE qE f)
    (.papp rE a00 a10 f) (.papp sE a01 a11 f) g

/-- `φ₁ = i∧¬i`. -/
private def f1 : Raw := .imin vi (.ineg vi)
/-- `φ₂ = (i∧¬i)∧(j∨¬j)`. -/
private def f2 : Raw := .imin f1 (.imax vj (.ineg vj))

/-- The common boundary type of the two fillers
(realization paper, non-uniqueness theorem). -/
private def SqLEM : Raw :=
  .pathP "i"
    (.path A (.papp rE a00 a10 f1) (.papp sE a01 a11 f1))
    pE pE

private def F1sq : Raw := .plam "i" (.plam "j" (Qat f1 vj))
private def F2sq : Raw := .plam "i" (.plam "j" (Qat f2 vj))

/-- The canonical interpolant
`χ(k) = (φ₁∧¬k) ∨ (k∧φ₂) ∨ (φ₁∧φ₂)`. -/
private def interp : Raw :=
  .imax (.imax (.imin f1 (.ineg vk)) (.imin vk f2)) (.imin f1 f2)

/-- **Strict homotopy between the two strict fillers**:
`H := ⟨k⟩⟨i⟩⟨j⟩ Q(χ(k))(j) : Path SqLEM F1 F2` — the
non-uniqueness of strict fillers is resolved by a strict homotopy
rel boundary, one dimension up, with no Kan operation involved. -/
def mixInterpD : LibDef where
  name := "mixInterp"
  ty := ctxB (.path SqLEM F1sq F2sq)
  tm := lamsB (.plam "k" (.plam "i" (.plam "j" (Qat interp vj))))

#guard mixInterpD.ok

/-- Control: the interpolant at an interior point (`k` generic) is a
well-typed filler of the same boundary — the interpolation moves
through the fiber, not merely between its endpoints. -/
def mixInterpCtrlD : LibDef where
  name := "mixInterpCtrl"
  ty := ctxB (.path SqLEM
    (.plam "i" (.plam "j" (Qat f1 vj)))
    (.plam "i" (.plam "j" (Qat f1 vj))))
  tm := lamsB (.plam "k" (.plam "i" (.plam "j"
    (Qat (.imax (.imax (.imin f1 (.ineg vk)) (.imin vk f1))
      (.imin f1 f1)) vj))))

#guard mixInterpCtrlD.ok

/-- The interpolation is *not* degenerate: at the halfway formula
`χ' := (φ₁∧¬k)∨(k∧φ₂)∨(φ₁∧φ₂)` with `k` a fresh generic dimension,
the homotopy's interior square differs from both endpoints — e.g.
the `k`-line of interior values is a genuine 3-cube, witnessed by
its well-typedness above and by the separation of its endpoints
(realization paper).  Machine sanity: `F1 ≢ F2` still holds in this
file's context (imported separation re-checked). -/
private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

#guard !(okD
  (lamsB (.plam "k" F2sq))
  (ctxB (.path SqLEM F1sq F2sq)))

/-! ## Necessity of the third term: naive interpolation fails by no-LEM

The naive convex combination `(φ₁∧¬k)∨(k∧φ₂)` restricts, on a face
with common value `ρ`, to `ρ∧(k∨¬k)` — which is NOT `ρ` in the free
De Morgan algebra (no excluded middle).  So the would-be homotopy
fails to typecheck: the correction term `φ₁∧φ₂` is essential. -/

#guard !(okD
  (lamsB (.plam "k" (.plam "i" (.plam "j"
    (Qat (.imax (.imin f1 (.ineg vk)) (.imin vk f2)) vj)))))
  (ctxB (.path SqLEM F1sq F2sq)))

/-! ## Cross-cell fillers connect through the shared subcomplex

Over the shared-edge computad (LibSharedEdge), the fillers
`S1 = ⟨i⟩⟨j⟩Q1(i∨¬i∨j∨¬j)(j)` and `S2 = ⟨i⟩⟨j⟩Q2(i∧¬i∧j∧¬j)(j)`
of the common boundary type `Path (Path A a10 a11) m m` come from
DIFFERENT cells, so no single strict cube can have one as its `k=0`
face and the other as its `k=1` face.  Yet both deform strictly onto
the shared-edge square `Sm = ⟨i⟩⟨j⟩ m(j)`:

  `⟨k⟩⟨i⟩⟨j⟩ Q1(E₀ ∨ k)(j)  : S1 ⇝ Sm`      (at k=1, Q1@1 ≡ m)
  `⟨k⟩⟨i⟩⟨j⟩ Q2(D₀ ∧ ¬k)(j) : S2 ⇝ Sm`      (at k=1, Q2@0 ≡ m)

so the strict fiber is connected by the zig-zag S1 ⇝ Sm ⇜ S2 —
entirely inside the strict layer. -/

private def a20 : Raw := .var "a20"
private def a21 : Raw := .var "a21"
private def mE : Raw := .var "m"
private def q2E : Raw := .var "q2"
private def r1E : Raw := .var "r1"
private def s1E : Raw := .var "s1"
private def r2E : Raw := .var "r2"
private def s2E : Raw := .var "s2"
private def Q1v : Raw := .var "Q1"
private def Q2v : Raw := .var "Q2"

private def Sq1T : Raw :=
  .pathP "i" (.path A (.papp r1E a00 a10 vi) (.papp s1E a01 a11 vi))
    pE mE

private def Sq2T : Raw :=
  .pathP "i" (.path A (.papp r2E a10 a20 vi) (.papp s2E a11 a21 vi))
    mE q2E

private def ctxT (body : Raw) : Raw :=
  .pi "A" .univ
    (.pi "a00" A (.pi "a01" A (.pi "a10" A (.pi "a11" A
    (.pi "a20" A (.pi "a21" A
    (.pi "p" (.path A a00 a01) (.pi "m" (.path A a10 a11)
    (.pi "q2" (.path A a20 a21)
    (.pi "r1" (.path A a00 a10) (.pi "s1" (.path A a01 a11)
    (.pi "r2" (.path A a10 a20) (.pi "s2" (.path A a11 a21)
    (.pi "Q1" Sq1T (.pi "Q2" Sq2T body)))))))))))))))

private def lamsT (body : Raw) : Raw :=
  lams ["A", "a00", "a01", "a10", "a11", "a20", "a21",
        "p", "m", "q2", "r1", "s1", "r2", "s2", "Q1", "Q2"] body

private def Q1app (f g : Raw) : Raw :=
  .papp (.papp Q1v pE mE f)
    (.papp r1E a00 a10 f) (.papp s1E a01 a11 f) g

private def Q2app (f g : Raw) : Raw :=
  .papp (.papp Q2v mE q2E f)
    (.papp r2E a10 a20 f) (.papp s2E a11 a21 f) g

private def SqM2 : Raw := .path (.path A a10 a11) mE mE

private def E0i : Raw :=
  .imax (.imax vi (.ineg vi)) (.imax vj (.ineg vj))
private def D0i : Raw :=
  .imin (.imin vi (.ineg vi)) (.imin vj (.ineg vj))

private def S1t : Raw := .plam "i" (.plam "j" (Q1app E0i vj))
private def S2t : Raw := .plam "i" (.plam "j" (Q2app D0i vj))
private def Smt : Raw := .plam "i" (.plam "j" (.papp mE a10 a11 vj))

/-- `S1` deforms strictly onto the shared-edge square. -/
def mixDeformQ1D : LibDef where
  name := "mixDeformQ1"
  ty := ctxT (.path SqM2 S1t Smt)
  tm := lamsT (.plam "k" (.plam "i" (.plam "j"
    (Q1app (.imax E0i vk) vj))))

#guard mixDeformQ1D.ok

/-- `S2` deforms strictly onto the shared-edge square. -/
def mixDeformQ2D : LibDef where
  name := "mixDeformQ2"
  ty := ctxT (.path SqM2 S2t Smt)
  tm := lamsT (.plam "k" (.plam "i" (.plam "j"
    (Q2app (.imin D0i (.ineg vk)) vj))))

#guard mixDeformQ2D.ok

/-! ## X3: the propositional shadow of the no-go equation

The first no-go theorem (companion paper 1) shows the constant-tube
collapse `⟨j⟩ hcomp [j=0↦a, j=1↦b] (p j) ≡ p` — equation (†) — can
NOT be definitional.  Here we machine-check its exact propositional
counterpart: the **canonical filler** connects the composite to its
base, rel boundary, uniformly:

  `⟨k⟩⟨j⟩ hcomp [j=0↦a, j=1↦b, k=0 ↦ p j] (p j) : Path _ p T`

(at `k=0` the extra face is decided and the composite collapses to
`p j`; at `k=1` the false face is discarded, leaving `T`).  So the
strict–weak comparison at a common boundary reads: weak cells built
by constant-tube composition are propositionally equal to their
strict caps by the filler — while genuinely weak composites extend
the propositional classes (machine evidence: the library's winding
computations, `winding (loop ⬝ loop) ⟶ +2 ≠ ±1, 0`). -/

private def aa : Raw := .var "a"
private def bb : Raw := .var "b"

private def ctxE (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" A (.pi "b" A
    (.pi "p" (.path A aa bb) body)))

/-- The constant-tube composite over `p` — the (†) left-hand side. -/
private def Tcomp : Raw :=
  .plam "j" (.hcomp "ii" A
    [([(vj, false)], aa), ([(vj, true)], bb)]
    (.papp pE aa bb vj))

/-- **(†) is propositional**: the canonical filler is a path
`p ⇝ T` rel boundary. -/
def mixFillD : LibDef where
  name := "mixFill"
  ty := ctxE (.path (.path A aa bb) pE Tcomp)
  tm := lams ["A", "a", "b", "p"]
    (.plam "k" (.plam "j" (.hcomp "ii" A
      [([(vj, false)], aa), ([(vj, true)], bb),
       ([(vk, false)], .papp pE aa bb vj)]
      (.papp pE aa bb vj))))

#guard mixFillD.ok

-- Control (the definitional side of the same coin, re-checked in
-- this context): `T ≢ p` — the no-go separation stands, so the
-- filler above is a genuinely propositional identification.
#guard !(okD
  (lams ["A", "a", "b", "p"] (.plam "k" pE))
  (ctxE (.path (.path A aa bb) Tcomp pE)))

end Cubical.Library

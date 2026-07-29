import FormalizedMathematics.Cubical.LibSanov

/-! # Word problems over cellular contexts, III: internal presentation
complexes

The ⟹ direction of the undecidability transfer interprets relator
2-cells in the *realization* of the presentation complex.  This file
constructs the presentation complex of `⟨x ∣ x²⟩ = ℤ/2` internally:
the double-cover attaching map is `deg2 : S¹ → S¹` (`loop ↦ loop⬝loop`,
definitional on the generator), and the complex is its mapping cone

  `RP² := cofib deg2 = pushout (⊤ ← S¹ →deg2 S¹)`,

i.e. the real projective plane.  The probes check the two halves of
the realization statement at the presentation level:

* **the relator cell is realized**: the `ppush` cylinder over the
  circle folds into an explicit propositional identification
  `rp2Rel : x·x ≡ refl` of the generator loop `x = ⟨i⟩ pinr (sloop i)`
  (one `hcomp` square with the cone point as cap, then `congTrans`);
* **generic word derivations transfer by instantiation**: the
  presentation context of `LibWord` instantiates at
  `(RP², base, x, rp2Rel)`, so `wordX4` specializes to a
  machine-checked `x⁴ ≡ refl` *in `RP²`* — the compiler mechanism
  targeting an internal HIT;
* controls: the attachment path is well-typed, and the relator is
  *not* definitional (`⟨i⟩ pinr (deg2 (sloop i)) ≢ refl` as terms) —
  the identification genuinely lives in the propositional layer,
  matching the no-go boundary. -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

private def loopS : Raw := .plam "i" (.sloop (.var "i"))
private def LL : Raw :=
  apps transD.ref [.s1, .sbase, .sbase, .sbase, loopS, loopS]

/-- **The degree-2 map** `S¹ → S¹`: `base ↦ base`, `loop ↦ loop⬝loop`
— the attaching map of the presentation complex of `⟨x ∣ x²⟩`. -/
def deg2D : LibDef where
  name := "deg2"
  ty := .arr .s1 .s1
  tm := .lam "s" (.s1elim "k" .s1 .sbase LL (.var "s"))

#guard deg2D.ok

/-- `cong deg2 loop ≐ loop⬝loop` — the attachment is definitional on
the generator (a constant path-lambda inhabits the identification). -/
def deg2LoopD : LibDef where
  name := "deg2Loop"
  ty := .path (.path .s1 .sbase .sbase)
    (.plam "i" (.app deg2D.ref (.sloop (.var "i")))) LL
  tm := .plam "k" LL

#guard deg2LoopD.ok

/-! ## The presentation complex `RP² = cofib deg2` -/

/-- **The presentation complex of `⟨x ∣ x²⟩`**: the mapping cone of
`deg2` — the real projective plane. -/
def rp2D : LibDef where
  name := "rp2"
  ty := .univ
  tm := cofib .s1 .s1 deg2D.ref

#guard rp2D.ok

private def rp2T : Raw := cofib .s1 .s1 deg2D.ref
private def bT : Raw := .pinr .sbase
private def coneT : Raw := .pinl .tt
private def FF : Raw := .lam "u0" .tt
/-- The generator loop `x` of `RP²` (the 1-skeleton's circle). -/
def rp2LoopT : Raw := .plam "i" (.pinr (.sloop (.var "i")))
private def q0At (j : Raw) : Raw := .ppush FF deg2D.ref .sbase j
private def rfl0R : Raw := apps reflD.ref [rp2T, bT]
private def xxR : Raw :=
  apps transD.ref [rp2T, bT, bT, bT, rp2LoopT, rp2LoopT]
private def x4R : Raw := apps transD.ref [rp2T, bT, bT, bT, xxR, xxR]
/-- `⟨i⟩ pinr (deg2 (sloop i))` — the relator word as the image of the
attaching map. -/
private def X2 : Raw := .plam "i" (.pinr (.app deg2D.ref (.sloop (.var "i"))))

/-- The attachment path of the 2-cell (cone point to basepoint). -/
def rp2AttachD : LibDef where
  name := "rp2Attach"
  ty := .path rp2T coneT bT
  tm := .plam "j" (q0At (.var "j"))

#guard rp2AttachD.ok

/-- **The relator cell, realized**: the `ppush` cylinder folds into
`⟨i⟩ pinr (deg2 (sloop i)) ≡ refl` — one `hcomp` square whose cap is
the cone point and whose `k=0` wall is the cylinder itself. -/
def rp2RelSqD : LibDef where
  name := "rp2RelSq"
  ty := .path (.path rp2T bT bT) X2 rfl0R
  tm := .plam "k" (.plam "i" (.hcomp "j" rp2T
    [([(.var "i", false)], q0At (.var "j")),
     ([(.var "i", true)], q0At (.var "j")),
     ([(.var "k", false)], .ppush FF deg2D.ref (.sloop (.var "i")) (.var "j")),
     ([(.var "k", true)], q0At (.var "j"))]
    coneT))

#guard rp2RelSqD.ok

/-- **The relator in word form**: `x·x ≡ refl` — `congTrans` splits
the image of `loop⬝loop` into the composite of the generator with
itself, then the square above kills it. -/
def rp2RelD : LibDef where
  name := "rp2Rel"
  ty := .path (.path rp2T bT bT) xxR rfl0R
  tm :=
    let pinrFn : Raw := .lam "s" (.pinr (.var "s"))
    let ct : Raw := apps congTransD.ref
      [.s1, rp2T, pinrFn, .sbase, .sbase, .sbase, loopS, loopS]
    let PT : Raw := .path rp2T bT bT
    apps transD.ref [PT, xxR, X2, rfl0R,
      apps symmD.ref [PT, X2, xxR, ct],
      rp2RelSqD.ref]

#guard rp2RelD.ok

/-- **Instantiation of the generic derivation**: `wordX4` at
`(RP², base, x, rp2Rel)` — the relator-compiled proof of `x⁴ ≡ refl`
transfers from the presentation computad to its internal realization
by substitution alone. -/
def wordX4RP2D : LibDef where
  name := "wordX4RP2"
  ty := .path (.path rp2T bT bT) x4R rfl0R
  tm := apps wordX4D.ref [rp2T, bT, rp2LoopT, rp2RelD.ref]

#guard wordX4RP2D.ok

/-- So does the direct relator use: `wordRel` at the same instance. -/
def wordRelRP2D : LibDef where
  name := "wordRelRP2"
  ty := .path (.path rp2T bT bT) xxR rfl0R
  tm := apps wordRelD.ref [rp2T, bT, rp2LoopT, rp2RelD.ref]

#guard wordRelRP2D.ok

-- Control: the relator is NOT definitional — the constant path-lambda
-- fails against `X2 ≡ refl` (the identification lives strictly in the
-- propositional layer, as the no-go boundary demands).
#guard !(okD (.plam "k" X2) (.path (.path rp2T bT bT) X2 rfl0R))

-- Control: nor is the word form `x·x ≡ refl` definitional.
#guard !(okD (.plam "k" xxR) (.path (.path rp2T bT bT) xxR rfl0R))

/-! ## Toward the `Bool` cover (the 2-cell coherence)

The double cover of `RP²` sends the generator to `ua notEquiv`; for
the cover to extend over the relator 2-cell, the composite
`ua not ⬝ ua not` must be identified with `refl` — provable through
`uaInj` + `equivEq` + `funExt` (the `uaCompMul` pattern), with
`notNot` doing the pointwise work. -/

private def uaNot : Raw := apps uaD.ref [boolTy, boolTy, notEquivD.ref]
private def uaNot2 : Raw :=
  apps trans1D.ref [.univ, boolTy, boolTy, boolTy, uaNot, uaNot]

/-- `ua notEquiv ⬝ ua notEquiv ≡ refl`. -/
def uaNotNotD : LibDef where
  name := "uaNotNot"
  ty := .path (.path .univ boolTy boolTy) uaNot2 (.plam "k" boolTy)
  tm :=
    let pte (p : Raw) : Raw := apps pathToEquivD.ref [boolTy, boolTy, p]
    let Q : Raw := .plam "k" boolTy
    apps uaInjD.ref [boolTy, boolTy, uaNot2, Q,
      apps equivEqD.ref [boolTy, boolTy, pte uaNot2, pte Q,
        apps funExtD.ref [boolTy, boolTy,
          .fst (pte uaNot2), .fst (pte Q),
          .lam "x" (.app notNotD.ref (.var "x"))]]]

-- heavy (~110 s: symbolic transport along the `hcomp`-composite of
-- Glue lines) but machine-checked here, once per elaboration; kept
-- out of `allDefs` following the `uaCompMul` precedent.
#guard uaNotNotD.ok

end Cubical.Library

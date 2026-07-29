import FormalizedMathematics.Cubical.LibPresent

/-! # Word problems over cellular contexts, IV: the double cover of `RP²`

The computational core of `π₁(RP²) = ℤ/2` at the presentation level:
a `Bool`-valued cover of the internal presentation complex separating
the generator from `refl`.

The circle part sends `loop ↦ ua notEquiv` (`covS1`); extending over
the relator 2-cell requires exactly the coherence `uaNotNot`
(`ua not ⬝ ua not ≡ refl`): the `ppush` cell of the cover is the
`s1elim` square obtained by `J@1`-transporting the trivial square
along `uaNotNot` (after `congTrans@01` splits the image of
`loop⬝loop`).  Then

* `windRP2 refl ⟶ true` and `windRP2 x ⟶ false` — computed;
* `rp2LoopNontriv : (x ≡ refl) → ⊥` — the generator survives the
  relator: the presentation `⟨x ∣ x²⟩` is realized *faithfully*
  (`x ≠ 1` while `x² = 1`, the two halves being `rp2LoopNontriv`
  and `rp2Rel`). -/

namespace Cubical.Library

open Raw

private def loopS : Raw := .plam "i" (.sloop (.var "i"))
private def LL : Raw :=
  apps transD.ref [.s1, .sbase, .sbase, .sbase, loopS, loopS]
private def rp2T : Raw := cofib .s1 .s1 deg2D.ref
private def bT : Raw := .pinr .sbase
private def rfl0R : Raw := apps reflD.ref [rp2T, bT]
private def uaNot : Raw := apps uaD.ref [boolTy, boolTy, notEquivD.ref]
private def reflB : Raw := .plam "k" boolTy
/-- `Path U Bool Bool`. -/
private def PU : Raw := .path .univ boolTy boolTy

/-- The double cover of the circle: `loop ↦ ua notEquiv`. -/
def covS1D : LibDef where
  name := "covS1"
  ty := .arr .s1 .univ
  tm := .lam "s" (.s1elim "k" .univ boolTy uaNot (.var "s"))

#guard covS1D.ok

/-- The image of the relator word under the cover:
`⟨i⟩ covS1 (deg2 (sloop i))`. -/
private def Wc : Raw :=
  .plam "i" (.app covS1D.ref (.app deg2D.ref (.sloop (.var "i"))))
private def uaNot2 : Raw :=
  apps trans1D.ref [.univ, boolTy, boolTy, boolTy, uaNot, uaNot]

/-- `Wc ≡ refl` — split by `congTrans@01`, kill by `uaNotNot`. -/
private def Ec : Raw :=
  apps trans1D.ref [PU, Wc, uaNot2, reflB,
    apps congTrans01D.ref
      [.s1, .univ, covS1D.ref, .sbase, .sbase, .sbase, loopS, loopS],
    uaNotNotD.ref]

/-- The 2-cell of the cover: the `s1elim` square
`PathP (⟨i⟩ Path U Bool (Wc i)) refl refl`, by `J@1` along `Ec`. -/
private def SQc : Raw :=
  apps j1D.ref [PU, reflB,
    .lam "w" (.lam "e" (.pathP "i"
      (.path .univ boolTy (.papp (.var "w") boolTy boolTy (.var "i")))
      reflB reflB)),
    .plam "k" (.plam "j" boolTy),
    Wc,
    apps symm1D.ref [PU, Wc, reflB, Ec]]

/-- **The double cover of `RP²`** — `Bool` at the cone, `covS1` on the
1-skeleton, the `uaNotNot` square over the 2-cell. -/
def covRP2D : LibDef where
  name := "covRP2"
  ty := .arr rp2T .univ
  tm := .lam "p" (.pushrec "k" .univ
    (.lam "u" boolTy)
    (.lam "s" (.app covS1D.ref (.var "s")))
    (.lam "a" (.s1elim "z"
      (.path .univ boolTy (.app covS1D.ref (.app deg2D.ref (.var "z"))))
      (.plam "j" boolTy)
      SQc
      (.var "a")))
    (.var "p"))

#guard covRP2D.ok

/-- **The `ℤ/2` winding**: transport `true` along the cover. -/
def windRP2D : LibDef where
  name := "windRP2"
  ty := .arr (.path rp2T bT bT) boolTy
  tm := .lam "p" (.transp "i"
    (.app covRP2D.ref (.papp (.var "p") bT bT (.var "i"))) trueR)

#guard windRP2D.ok

-- `windRP2 refl ⟶ true`, `windRP2 x ⟶ false` — the cover computes.
#guard
  match normalize (.app windRP2D.ref rfl0R) boolTy with
  | .ok t => t == resolveClosed trueR
  | _ => false
#guard
  match normalize (.app windRP2D.ref rp2LoopT) boolTy with
  | .ok t => t == resolveClosed falseR
  | _ => false

/-- **The generator survives the relator**: `x ≡ refl` is refutable —
with `rp2Rel : x·x ≡ refl`, the presentation `⟨x ∣ x²⟩` is realized
faithfully at `π₁`. -/
def rp2LoopNontrivD : LibDef where
  name := "rp2LoopNontriv"
  ty := .arr (.path (.path rp2T bT bT) rp2LoopT rfl0R) .empty
  tm := .lam "h" (apps encodeBoolD.ref [falseR, trueR,
    apps congD.ref [.path rp2T bT bT, boolTy, windRP2D.ref,
      rp2LoopT, rfl0R, .var "h"]])

#guard rp2LoopNontrivD.ok

/-- Hence `RP²` is not a set (its `π₁` is nontrivial). -/
def rp2NotSetD : LibDef where
  name := "rp2NotSet"
  ty := .arr (isSetR rp2T) .empty
  tm := .lam "h" (.app rp2LoopNontrivD.ref
    (apps (.var "h") [bT, bT, rp2LoopT, rfl0R]))

#guard rp2NotSetD.ok

end Cubical.Library

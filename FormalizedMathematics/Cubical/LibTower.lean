import FormalizedMathematics.Cubical.LibCircleEM

/-! # The meta-level ω-groupoid tower

Two-level architecture in action: Lean (the strict metatheory) indexes
over external `n : Nat` the object-language coherence structure of
iterated loop spaces.  Because the untruncated cells of `LibCoherence`
are generic in the type, every rung — composition, associator, Mac
Lane's pentagon, and (from dimension 2) Eckmann–Hilton — is a single
instantiation, kernel-checked per level and uniform in the type: *every*
object-language type carries this structure at every finite level.  This
is the start of a van den Berg–Garner style weak ω-groupoid tower in
2LTT form. -/

namespace Cubical.Library

open Raw

/-- `Ωⁿ(A, a)` as (type, basepoint), over the ambient variables. -/
def omegaN (A a : Raw) : Nat → Raw × Raw
  | 0 => (A, a)
  | n + 1 =>
    let (T, b) := omegaN A a n
    (.path T b b, apps reflD.ref [T, b])

private def genPis (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") body)

private def genLams (body : Raw) : Raw :=
  lams ["A", "a"] body

/-- Level-`n` composition: loops of `Ωⁿ` compose. -/
def towerCompD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  { name := s!"towerComp{n}"
    ty := genPis (.arr (.path T b b) (.arr (.path T b b) (.path T b b)))
    tm := genLams (lams ["p", "q"]
      (apps transD.ref [T, b, b, b, .var "p", .var "q"])) }

/-- Level-`n` associator, untruncated. -/
def towerAssocD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  let t3 (p q : Raw) : Raw := apps transD.ref [T, b, b, b, p, q]
  { name := s!"towerAssoc{n}"
    ty := genPis (.pi "p" (.path T b b) (.pi "q" (.path T b b)
      (.pi "r" (.path T b b)
        (.path (.path T b b)
          (t3 (.var "p") (t3 (.var "q") (.var "r")))
          (t3 (t3 (.var "p") (.var "q")) (.var "r"))))))
    tm := genLams (lams ["p", "q", "r"]
      (apps assocConnD.ref [T, b, b, b, b, .var "p", .var "q", .var "r"])) }

/-- Level-`n` Mac Lane pentagon, untruncated (all five objects at the
basepoint). -/
def towerPentagonD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  let O : Raw := .path T b b
  let t3 (p q : Raw) : Raw := apps transD.ref [T, b, b, b, p, q]
  let c2 (X Y Z e1 e2 : Raw) : Raw := apps transD.ref [O, X, Y, Z, e1, e2]
  let asc (p q r : Raw) : Raw :=
    apps assocConnD.ref [T, b, b, b, b, p, q, r]
  let p : Raw := .var "p"
  let q : Raw := .var "q"
  let r : Raw := .var "r"
  let sP : Raw := .var "s"
  let qr : Raw := t3 q r
  let rs : Raw := t3 r sP
  let pq : Raw := t3 p q
  let V1 : Raw := t3 p (t3 q rs)
  let V2 : Raw := t3 pq rs
  let V3 : Raw := t3 (t3 pq r) sP
  let V4 : Raw := t3 (t3 p qr) sP
  let V5 : Raw := t3 p (t3 qr sP)
  let congB1 : Raw := apps congD.ref [O, O,
    .lam "h" (t3 p (.var "h")), t3 q rs, t3 qr sP, asc q r sP]
  let congB3 : Raw := apps congD.ref [O, O,
    .lam "h" (t3 (.var "h") sP), t3 p qr, t3 pq r, asc p q r]
  let routeA : Raw := c2 V1 V2 V3 (asc p q rs) (asc pq r sP)
  let routeB : Raw := c2 V1 V5 V3 congB1 (c2 V5 V4 V3 (asc p qr sP) congB3)
  { name := s!"towerPentagon{n}"
    ty := genPis (.pi "p" O (.pi "q" O (.pi "r" O (.pi "s" O
      (.path (.path O V1 V3) routeA routeB)))))
    tm := genLams (lams ["p", "q", "r", "s"]
      (apps pentagonConnD.ref [T, b, b, b, b, b, p, q, r, sP])) }

/-- Level-`n` Eckmann–Hilton (`n ≥ 2` implicitly: cells of `Ωⁿ⁺²`
commute). -/
def towerEHD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  let O : Raw := .path T b b
  let rb : Raw := apps reflD.ref [T, b]
  let O2 : Raw := .path O rb rb
  let c2 (e1 e2 : Raw) : Raw := apps transD.ref [O, rb, rb, rb, e1, e2]
  { name := s!"towerEH{n}"
    ty := genPis (.pi "al" O2 (.pi "be" O2
      (.path O2 (c2 (.var "al") (.var "be")) (c2 (.var "be") (.var "al")))))
    tm := genLams (lams ["al", "be"]
      (apps eckmannHiltonD.ref [T, b, .var "al", .var "be"])) }


/-- Level-`n` Mac Lane triangle, untruncated (middle object at the
basepoint's `refl`). -/
def towerTriangleD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  let O : Raw := .path T b b
  let rb : Raw := apps reflD.ref [T, b]
  let t3 (p q : Raw) : Raw := apps transD.ref [T, b, b, b, p, q]
  let asc (p q r : Raw) : Raw :=
    apps assocConnD.ref [T, b, b, b, b, p, q, r]
  let p : Raw := .var "p"
  let q : Raw := .var "q"
  let s00 : Raw := t3 p (t3 rb q)
  let s11 : Raw := t3 (t3 p rb) q
  let s01 : Raw := t3 p q
  let whisk : Raw := apps congD.ref [O, O,
    .lam "h" (t3 (.var "h") q), t3 p rb, p,
    apps transReflRD.ref [T, b, b, p]]
  let lhs : Raw := apps transD.ref [O, s00, s11, s01,
    asc p rb q, whisk]
  let rhs : Raw := apps congD.ref [O, O,
    .lam "h" (t3 p (.var "h")), t3 rb q, q,
    apps transReflLD.ref [T, b, b, q]]
  { name := s!"towerTriangle{n}"
    ty := genPis (.pi "p" O (.pi "q" O
      (.path (.path O s00 s01) lhs rhs)))
    tm := genLams (lams ["p", "q"]
      (apps triangleConnD.ref [T, b, b, b, p, q])) }


/-- Level-`n` interchange (middle-four exchange): for 2-cells `p, q`
between loops of `Ωⁿ⁺¹`, horizontal-then-vertical whiskering agrees with
vertical-then-horizontal — the `congSlide` instance for loop
composition.  This is the coherence that makes each `Ωⁿ⁺²` a *braided*
(indeed symmetric, via `towerEH`) structure. -/
def towerInterchangeD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  let O : Raw := .path T b b
  let cmp : Raw := lams ["u", "v"]
    (apps transD.ref [T, b, b, b, .var "u", .var "v"])
  let f (u v : Raw) : Raw := apps transD.ref [T, b, b, b, u, v]
  let x : Raw := .var "x"
  let x2 : Raw := .var "x2"
  let y : Raw := .var "y"
  let y2 : Raw := .var "y2"
  let cBottom : Raw := apps congD.ref [O, O,
    .lam "h" (f (.var "h") y), x, x2, .var "p"]
  let cRight : Raw := apps congD.ref [O, O,
    .lam "h" (f x2 (.var "h")), y, y2, .var "q"]
  let cLeft : Raw := apps congD.ref [O, O,
    .lam "h" (f x (.var "h")), y, y2, .var "q"]
  let cTop : Raw := apps congD.ref [O, O,
    .lam "h" (f (.var "h") y2), x, x2, .var "p"]
  { name := s!"towerInterchange{n}"
    ty := genPis (.pi "x" O (.pi "x2" O (.pi "y" O (.pi "y2" O
      (.pi "p" (.path O x x2) (.pi "q" (.path O y y2)
        (.path (.path O (f x y) (f x2 y2))
          (apps transD.ref [O, f x y, f x2 y, f x2 y2, cBottom, cRight])
          (apps transD.ref [O, f x y, f x y2, f x2 y2, cLeft, cTop]))))))))
    tm := genLams (lams ["x", "x2", "y", "y2", "p", "q"]
      (apps congSlideD.ref [O, O, O, cmp, x, x2, y, y2,
        .var "p", .var "q"])) }

/-- The tower, packaged: the coherence rungs at level `n`. -/
def towerLevel (n : Nat) : List LibDef :=
  [towerCompD n, towerAssocD n, towerTriangleD n, towerPentagonD n,
   towerEHD n, towerInterchangeD n]

-- Every rung of the first four levels is kernel-checked (uniformly in the
-- ambient type): every object-language type carries composition,
-- associator, triangle, pentagon, Eckmann–Hilton, and interchange
-- structure on its iterated loop spaces — the full Mac Lane coherence
-- data of a (braided, indeed symmetric) monoidal structure, per level.
#guard (towerLevel 0).all (·.ok)
#guard (towerLevel 1).all (·.ok)
#guard (towerLevel 2).all (·.ok)
#guard (towerLevel 3).all (·.ok)

/-- `Ωⁿ f`: the iterated loop map of `f`, based at the image point.
`omegaNMap A B f a n` is the `Raw` function `Ωⁿ(A,a) → Ωⁿ(B, f a)` —
level 0 is `f`, level `n+1` is `cong` of level `n`.  It preserves the
tower basepoints *definitionally* (`cong f refl ≐ refl`), which is what
lets the iteration proceed with no conjugation. -/
def omegaNMap (A B f a : Raw) : Nat → Raw
  | 0 => f
  | n + 1 =>
    let (TA, bA) := omegaN A a n
    let (TB, _) := omegaN B (.app f a) n
    let fn := omegaNMap A B f a n
    -- basepoint of the image tower at level n, as mapped: definitionally
    -- the tower basepoint of B, but stated via the map for the endpoints
    .lam "p" (apps congD.ref
      [TA, TB, fn, bA, bA, .var "p"])

/-- Level-`n` loop functor: `Ωⁿ f : Ωⁿ(A,a) → Ωⁿ(B, f a)`. -/
def towerMapD (n : Nat) : LibDef :=
  let (TA, _) := omegaN (.var "A") (.var "a") n
  let (TB, _) := omegaN (.var "B") (.app (.var "f") (.var "a")) n
  { name := s!"towerMap{n}"
    ty := .pi "A" .univ (.pi "B" .univ
      (.pi "f" (.arr (.var "A") (.var "B")) (.pi "a" (.var "A")
        (.arr TA TB))))
    tm := lams ["A", "B", "f", "a"]
      (omegaNMap (.var "A") (.var "B") (.var "f") (.var "a") n) }

/-- **Strict functoriality at every level** (`refl` proof, pointwise):
`Ωⁿ(g ∘ f) p ≡ Ωⁿ g (Ωⁿ f p)`. -/
def towerMapCompD (n : Nat) : LibDef :=
  let A : Raw := .var "A"
  let B : Raw := .var "B"
  let C : Raw := .var "C"
  let f : Raw := .var "f"
  let g : Raw := .var "g"
  let a : Raw := .var "a"
  let gf : Raw := .ann (.lam "t" (.app g (.app f (.var "t"))))
    (.arr A C)
  let (TA, _) := omegaN A a n
  let (TB, _) := omegaN B (.app f a) n
  let (TC, _) := omegaN C (.app g (.app f a)) n
  let lhs : Raw := .ann (omegaNMap A C gf a n) (.arr TA TC)
  let fn : Raw := .ann (omegaNMap A B f a n) (.arr TA TB)
  let gn : Raw := .ann (omegaNMap B C g (.app f a) n) (.arr TB TC)
  { name := s!"towerMapComp{n}"
    ty := .pi "A" .univ (.pi "B" .univ (.pi "C" .univ
      (.pi "f" (.arr A B) (.pi "g" (.arr B C) (.pi "a" A
        (.pi "p" TA
          (.path TC (.app lhs (.var "p"))
            (.app gn (.app fn (.var "p"))))))))))
    tm := lams ["A", "B", "C", "f", "g", "a", "p"]
      (.plam "i" (.app lhs (.var "p"))) }

-- The Ω-functor rungs: kernel-checked for the first four levels; the
-- functor laws hold by `refl` (strictness of `cong` composition,
-- iterated).
#guard (towerMapD 0).ok
#guard (towerMapD 1).ok
#guard (towerMapD 2).ok
#guard (towerMapD 3).ok
#guard (towerMapCompD 0).ok
#guard (towerMapCompD 1).ok
#guard (towerMapCompD 2).ok
#guard (towerMapCompD 3).ok

/-- Commutative monoids (carrier, operations, laws) as a Σ-tower —
no set-ness assumption: the laws are stated as bare paths, so this is
the *untruncated* notion. -/
def commMonoidTy : Raw :=
  let C : Raw := .var "mC"
  let mm (a b : Raw) : Raw := .app (.app (.var "mm") a) b
  .sigma "mC" .univ (.sigma "mm" (.arr C (.arr C C))
    (.sigma "me" C
    (.sigma "massoc" (.pi "a" C (.pi "b" C (.pi "c" C
      (.path C
        (mm (.var "a") (mm (.var "b") (.var "c")))
        (mm (mm (.var "a") (.var "b")) (.var "c"))))))
    (.sigma "munitL" (.pi "a" C
      (.path C (mm (.var "me") (.var "a")) (.var "a")))
    (.sigma "munitR" (.pi "a" C
      (.path C (mm (.var "a") (.var "me")) (.var "a")))
      (.pi "a" C (.pi "b" C
        (.path C (mm (.var "a") (.var "b")) (mm (.var "b") (.var "a"))))))))))

/-- **The second loop space of any type is a commutative monoid**
(untruncated): multiplication is composition, commutativity is
Eckmann–Hilton. -/
def loop2CommMonoidD : LibDef where
  name := "loop2CommMonoid"
  ty := .pi "A" .univ (.pi "a" (.var "A") commMonoidTy)
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let (T1, b1) := omegaN A a 1   -- Ω(A,a), refl
    let O2 : Raw := .path T1 b1 b1
    let tr (p q : Raw) : Raw := apps transD.ref [T1, b1, b1, b1, p, q]
    lams ["A", "a"]
      (.pair O2
      (.pair (lams ["p", "q"] (tr (.var "p") (.var "q")))
      (.pair (apps reflD.ref [T1, b1])
      (.pair (lams ["p", "q", "r"]
        (apps assocConnD.ref [T1, b1, b1, b1, b1,
          .var "p", .var "q", .var "r"]))
      (.pair (.lam "p" (apps transReflLD.ref [T1, b1, b1, .var "p"]))
      (.pair (.lam "p" (apps transReflRD.ref [T1, b1, b1, .var "p"]))
        (lams ["p", "q"]
          (apps eckmannHiltonD.ref [A, a, .var "p", .var "q"]))))))))

#guard loop2CommMonoidD.ok

/-- The commutative-monoid structure at every rung `Ωⁿ⁺²`: instantiate
at the iterated basepoint. -/
def towerCommMonoidD (n : Nat) : LibDef :=
  let (T, b) := omegaN (.var "A") (.var "a") n
  { name := s!"towerCommMonoid{n}"
    ty := .pi "A" .univ (.pi "a" (.var "A") commMonoidTy)
    tm := lams ["A", "a"]
      (apps loop2CommMonoidD.ref [T, b]) }

#guard (towerCommMonoidD 0).ok
#guard (towerCommMonoidD 1).ok
#guard (towerCommMonoidD 2).ok

/-! ## BGpd smoke tests: the classifying space of `(Unit, ℤ, +)`

Formation, the point/arrow/composition constructors, and computation of
the recursor on points — the first object-language uses of the new
general-groupoid Eilenberg–MacLane HIT. -/

private def homZ : Raw := lams ["x", "y"] .int
private def cmpZ : Raw := lams ["x", "y", "z", "f", "g"]
  (apps addD.ref [.var "f", .var "g"])
private def bgZ : Raw := .bgpd .unit homZ cmpZ

def bgZFormD : LibDef where
  name := "bgZForm"
  ty := .univ
  tm := bgZ

#guard bgZFormD.ok

def bgZPointD : LibDef where
  name := "bgZPoint"
  ty := bgZ
  tm := .bpt .tt

#guard bgZPointD.ok

/-- The arrow loop of `3 : ℤ` in `BGpd(Unit, ℤ)`. -/
def bgZArrD : LibDef where
  name := "bgZArr"
  ty := .path bgZ (.bpt .tt) (.bpt .tt)
  tm := .plam "i" (.barr .tt .tt (.ipos (.succ (.succ (.succ .zero))))
    (.var "i"))

#guard bgZArrD.ok

/-- The composition square of `1, 2`. -/
def bgZCompD : LibDef where
  name := "bgZComp"
  ty :=
    let a1 : Raw := .ipos (.succ .zero)
    let a2 : Raw := .ipos (.succ (.succ .zero))
    let arr (g : Raw) : Raw := .plam "i" (.barr .tt .tt g (.var "i"))
    .pathP "j"
      (.path bgZ (.bpt .tt)
        (.papp (.ann (arr (.ipos (.succ (.succ .zero))))
            (.path bgZ (.bpt .tt) (.bpt .tt)))
          (.bpt .tt) (.bpt .tt) (.var "j")))
      (arr a1)
      (arr (apps addD.ref [a1, a2]))
  tm :=
    let a1 : Raw := .ipos (.succ .zero)
    let a2 : Raw := .ipos (.succ (.succ .zero))
    .plam "j" (.plam "i" (.bcomp cmpZ .tt .tt .tt a1 a2
      (.var "j") (.var "i")))

#guard bgZCompD.ok

-- Recursion on points computes: fold `BGpd(Unit,ℤ)` to `ℤ` with the
-- constant-zero point map and reflexive cells, and evaluate at `bpt tt`.
#guard
  match normalize
    (.bgrec .int
      (apps isSetToGpdD.ref [.int, isSetZD.ref])
      (.lam "x" (.ipos .zero))
      (lams ["x", "y", "f"] (.plam "i" (.ipos .zero)))
      (lams ["x", "y", "z", "f", "g"]
        (.plam "j" (.plam "i" (.ipos .zero))))
      (.ann (.bpt .tt) bgZ))
    .int with
  | .ok t => t == .ipos .zero
  | .error _ => false

/-! ## Towards `BGpd(Π₁ A) ≃ A`: the counit

`gpdRec` folds the classifying space of the fundamental groupoid back
into the 1-type: the point map is the identity, the arrow map is the
identity on paths, and the composition cell is *exactly* the composition
filler `transFill` — the same coincidence that drove `loopRec`. -/

private def homOf (A : Raw) : Raw :=
  lams ["x", "y"] (.path A (.var "x") (.var "y"))
private def cmpOf (A : Raw) : Raw :=
  lams ["x", "y", "z", "f", "g"]
    (apps transD.ref [A, .var "x", .var "y", .var "z",
      .var "f", .var "g"])
/-- `BGpd(Π₁ A)` as a `Raw` type. -/
def bgFundR (A : Raw) : Raw := .bgpd A (homOf A) (cmpOf A)

/-- **The counit `BGpd(Π₁ A) → A`.** -/
def gpdRecD : LibDef where
  name := "gpdRec"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.arr (bgFundR (.var "A")) (.var "A")))
  tm :=
    let A : Raw := .var "A"
    lams ["A", "gA"]
      (.lam "t" (.bgrec A (.var "gA")
        (.lam "x" (.var "x"))
        (lams ["x", "y", "f"] (.var "f"))
        (lams ["x", "y", "z", "f", "g"]
          (apps transFillD.ref [A, .var "x", .var "y", .var "z",
            .var "f", .var "g"]))
        (.var "t")))

#guard gpdRecD.ok

/-- The counit splits the point inclusion — definitionally. -/
def gpdRecPtD : LibDef where
  name := "gpdRecPt"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A")
      (.path (.var "A")
        (.app (apps gpdRecD.ref [.var "A", .var "gA"])
          (.bpt (.var "a")))
        (.var "a"))))
  tm := lams ["A", "gA", "a"] (.plam "i" (.var "a"))

#guard gpdRecPtD.ok

/-- The counit computes on arrow paths — also definitionally: the image
of `barr a b p` is `p` itself. -/
def gpdRecArrD : LibDef where
  name := "gpdRecArr"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps congD.ref [bgFundR (.var "A"), .var "A",
          .lam "t" (.app (apps gpdRecD.ref [.var "A", .var "gA"])
            (.var "t")),
          .bpt (.var "a"), .bpt (.var "b"),
          .plam "i" (.barr (.var "a") (.var "b") (.var "p") (.var "i"))])
        (.var "p"))))))
  tm := lams ["A", "gA", "a", "b", "p"]
    (.plam "j" (.var "p"))

#guard gpdRecArrD.ok

/-- `BGpd` is a 1-type — the truncation constructor, verbatim
(mirrors `isGpdEM`). -/
def isGpdBGD : LibDef where
  name := "isGpdBG"
  ty := .pi "Ob" .univ
    (.pi "hom" (.arr (.var "Ob") (.arr (.var "Ob") .univ))
    (.pi "cmp" (.pi "x" (.var "Ob") (.pi "y" (.var "Ob")
      (.pi "z" (.var "Ob")
        (.arr (.app (.app (.var "hom") (.var "x")) (.var "y"))
          (.arr (.app (.app (.var "hom") (.var "y")) (.var "z"))
            (.app (.app (.var "hom") (.var "x")) (.var "z")))))))
      (isGpdR (.bgpd (.var "Ob") (.var "hom") (.var "cmp")))))
  tm := lams ["Ob", "hom", "cmp", "a", "b", "p", "q", "r", "s"]
    (.plam "i1" (.plam "i2" (.plam "i3"
      (.bsquash (.var "a") (.var "b") (.var "p") (.var "q")
        (.var "r") (.var "s") (.var "i1") (.var "i2") (.var "i3")))))

#guard isGpdBGD.ok

/-- `barr` of a composite is the composite of `barr`s (mirrors
`emloopComp`, with the composition square `bcomp` as the `k = 0` face). -/
def barrCompD : LibDef where
  name := "barrComp"
  ty :=
    let Ob : Raw := .var "Ob"
    let hom : Raw := .var "hom"
    let cmp : Raw := .var "cmp"
    let BG : Raw := .bgpd Ob hom cmp
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let z : Raw := .var "z"
    .pi "Ob" .univ
      (.pi "hom" (.arr Ob (.arr Ob .univ))
      (.pi "cmp" (.pi "x" Ob (.pi "y" Ob (.pi "z" Ob
        (.arr (.app (.app hom (.var "x")) (.var "y"))
          (.arr (.app (.app hom (.var "y")) (.var "z"))
            (.app (.app hom (.var "x")) (.var "z")))))))
      (.pi "x" Ob (.pi "y" Ob (.pi "z" Ob
      (.pi "f" (.app (.app hom x) y)
      (.pi "g" (.app (.app hom y) z)
        (.path (.path BG (.bpt x) (.bpt z))
          (.plam "i" (.barr x z
            (apps cmp [x, y, z, .var "f", .var "g"]) (.var "i")))
          (apps transD.ref [BG, .bpt x, .bpt y, .bpt z,
            .plam "i" (.barr x y (.var "f") (.var "i")),
            .plam "i" (.barr y z (.var "g") (.var "i"))])))))))))
  tm :=
    let BG : Raw := .bgpd (.var "Ob") (.var "hom") (.var "cmp")
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let z : Raw := .var "z"
    lams ["Ob", "hom", "cmp", "x", "y", "z", "f", "g"]
      (.plam "k" (.plam "i" (.hcomp "j" BG
        [([(.var "i", false)], .bpt x),
         ([(.var "i", true)], .barr y z (.var "g") (.var "j")),
         ([(.var "k", false)],
           .bcomp (.var "cmp") x y z (.var "f") (.var "g")
             (.var "j") (.var "i")),
         ([(.var "k", true)],
           .hcomp "k2" BG
             [([(.var "i", false)], .bpt x),
              ([(.var "i", true)],
                .barr y z (.var "g") (.imin (.var "k2") (.var "j"))),
              ([(.var "j", false)], .barr x y (.var "f") (.var "i"))]
             (.barr x y (.var "f") (.var "i")))]
        (.barr x y (.var "f") (.var "i")))))

#guard barrCompD.ok

/-- `barr refl ≡ refl` in `BGpd(Π₁ A)` — the group-style cancellation
argument from `barrComp`. -/
def barrReflD : LibDef where
  name := "barrRefl"
  ty :=
    let A : Raw := .var "A"
    let x : Raw := .var "x"
    let BG : Raw := bgFundR A
    .pi "A" .univ (.pi "x" A
      (.path (.path BG (.bpt x) (.bpt x))
        (.plam "i" (.barr x x (.plam "i0" x) (.var "i")))
        (apps reflD.ref [BG, .bpt x])))
  tm :=
    let A : Raw := .var "A"
    let x : Raw := .var "x"
    let BG : Raw := bgFundR A
    let O : Raw := .path BG (.bpt x) (.bpt x)
    let rx : Raw := .plam "i0" x                    -- refl x : Path A x x
    let a : Raw := .plam "i" (.barr x x rx (.var "i"))
    let rb : Raw := apps reflD.ref [BG, .bpt x]
    let tr (pp qq : Raw) : Raw :=
      apps transD.ref [BG, .bpt x, .bpt x, .bpt x, pp, qq]
    let ai : Raw := apps symmD.ref [BG, .bpt x, .bpt x, a]
    let rr : Raw := apps transD.ref [A, x, x, x, rx, rx]  -- refl⬝refl
    let brr : Raw := .plam "i" (.barr x x rr (.var "i"))
    -- E : a⬝a ≡ a
    let s1 : Raw := apps barrCompD.ref
      [A, homOf A, cmpOf A, x, x, x, rx, rx]       -- brr ≡ a⬝a
    let s2 : Raw := apps congD.ref
      [.path A x x, O,
       .lam "p" (.plam "i" (.barr x x (.var "p") (.var "i"))),
       rr, rx,
       apps transReflRD.ref [A, x, x, rx]]          -- brr ≡ a
    let E : Raw := apps transD.ref [O, tr a a, brr, a,
      apps symmD.ref [O, brr, tr a a, s1], s2]
    -- chain: a ≡ refl⬝a ≡ (a⁻¹⬝a)⬝a ≡ a⁻¹⬝(a⬝a) ≡ a⁻¹⬝a ≡ refl
    let X1 : Raw := a
    let X2 : Raw := tr rb a
    let X3 : Raw := tr (tr ai a) a
    let X4 : Raw := tr ai (tr a a)
    let X5 : Raw := tr ai a
    let cL : Raw := apps cancelLD.ref [BG, .bpt x, .bpt x, a]
    let m1 : Raw := apps symmD.ref [O, X2, X1,
      apps transReflLD.ref [BG, .bpt x, .bpt x, a]]
    let m2 : Raw := apps congD.ref [O, O,
      .lam "h" (tr (.var "h") a), rb, tr ai a,
      apps symmD.ref [O, tr ai a, rb, cL]]
    let m3 : Raw := apps symmD.ref [O, X4, X3,
      apps assocConnD.ref [BG, .bpt x, .bpt x, .bpt x, .bpt x, ai, a, a]]
    let m4 : Raw := apps congD.ref [O, O,
      .lam "h" (tr ai (.var "h")), tr a a, a, E]
    lams ["A", "x"]
      (apps transD.ref [O, X1, X2, rb, m1,
        apps transD.ref [O, X2, X3, rb, m2,
          apps transD.ref [O, X3, X4, rb, m3,
            apps transD.ref [O, X4, X5, rb, m4, cL]]]])

#guard barrReflD.ok

/-- **`barr p ≡ cong bpt p`** — the arrow constructor agrees with the
image of the path, by `J` (the `refl` case is `barrRefl`, since
`cong bpt refl ≐ refl`). -/
def barrCongBptD : LibDef where
  name := "barrCongBpt"
  ty :=
    let A : Raw := .var "A"
    let BG : Raw := bgFundR A
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    .pi "A" .univ (.pi "x" A (.pi "y" A
      (.pi "p" (.path A x y)
        (.path (.path BG (.bpt x) (.bpt y))
          (.plam "i" (.barr x y (.var "p") (.var "i")))
          (apps congD.ref [A, BG, .lam "t" (.bpt (.var "t")),
            x, y, .var "p"])))))
  tm :=
    let A : Raw := .var "A"
    let BG : Raw := bgFundR A
    let x : Raw := .var "x"
    let motive : Raw := lams ["y2", "p2"]
      (.path (.path BG (.bpt x) (.bpt (.var "y2")))
        (.plam "i" (.barr x (.var "y2") (.var "p2") (.var "i")))
        (apps congD.ref [A, BG, .lam "t" (.bpt (.var "t")),
          x, .var "y2", .var "p2"]))
    lams ["A", "x", "y", "p"]
      (apps jD.ref [A, x, motive,
        apps barrReflD.ref [A, x], .var "y", .var "p"])

#guard barrCongBptD.ok

/-- **The unit: `bpt (gpdRec t) ≡ t`** — by `bgelim`; the arrow cell is
`barrCongBpt` read as a path-over, the composition cell is the standard
set-family discharge. -/
def bgptRetrD : LibDef where
  name := "bgptRetr"
  ty :=
    let A : Raw := .var "A"
    let BG : Raw := bgFundR A
    let recF : Raw := apps gpdRecD.ref [A, .var "gA"]
    .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
      (.pi "t" BG
        (.path BG (.bpt (.app recF (.var "t"))) (.var "t"))))
  tm :=
    let A : Raw := .var "A"
    let BG : Raw := bgFundR A
    let recF : Raw := apps gpdRecD.ref [A, .var "gA"]
    let motAt (t : Raw) : Raw := .path BG (.bpt (.app recF t)) t
    let motLam : Raw := .lam "t0" (motAt (.var "t0"))
    let bgGpd : Raw := apps isGpdBGD.ref [A, homOf A, cmpOf A]
    -- isSet (motive t) = isGpdBG partially applied at the endpoints
    let msetAt (t : Raw) : Raw :=
      apps bgGpd [.bpt (.app recF t), t]
    let msetFam : Raw := .lam "t0" (msetAt (.var "t0"))
    let gP : Raw := .lam "t0" (apps isSetToGpdD.ref
      [motAt (.var "t0"), msetAt (.var "t0")])
    let pb : Raw := .lam "x" (.plam "j" (.bpt (.var "x")))
    -- arrow cell: barrCongBpt @ (¬j) @ i
    let plCell : Raw := lams ["x", "y", "f"]
      (.plam "i" (.plam "j"
        (.papp
          (.papp (apps barrCongBptD.ref
              [A, .var "x", .var "y", .var "f"])
            (.plam "i0" (.barr (.var "x") (.var "y") (.var "f")
              (.var "i0")))
            (apps congD.ref [A, BG, .lam "t" (.bpt (.var "t")),
              .var "x", .var "y", .var "f"])
            (.ineg (.var "j")))
          (.bpt (.var "x")) (.bpt (.var "y")) (.var "i"))))
    let plAnn : Raw := .ann plCell
      (.pi "x" A (.pi "y" A
        (.pi "f" (.path A (.var "x") (.var "y"))
          (.pathP "i9"
            (motAt (.barr (.var "x") (.var "y") (.var "f") (.var "i9")))
            (.plam "j" (.bpt (.var "x")))
            (.plam "j" (.bpt (.var "y")))))))
    -- composition cell: set-family discharge (toFrom pattern)
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let z : Raw := .var "z"
    let f : Raw := .var "f"
    let g : Raw := .var "g"
    let cmpfg : Raw := apps transD.ref [A, x, y, z, f, g]
    let Lof (jE : Raw) : Raw := .pathP "i2"
      (motAt (.bcomp (cmpOf A) x y z f g jE (.var "i2")))
      (.plam "j" (.bpt x))
      (.papp (apps plAnn [y, z, g])
        (.plam "j" (.bpt y)) (.plam "j" (.bpt z)) jE)
    let line : Raw := .plam "j0" (Lof (.var "j0"))
    let pcCell : Raw := lams ["x", "y", "z", "f", "g"]
      (apps toPathPD.ref
        [Lof .i0, Lof .i1, line,
         apps plAnn [x, y, f],
         apps plAnn [x, z, cmpfg],
         apps isPropPathPSetD.ref
           [BG, motLam, msetFam,
            .bpt x, .plam "j" (.bpt x),
            .bpt z,
            .plam "i" (.barr x z cmpfg (.var "i")),
            .plam "j" (.bpt z),
            apps transportD.ref [Lof .i0, Lof .i1, line,
              apps plAnn [x, y, f]],
            apps plAnn [x, z, cmpfg]]])
    lams ["A", "gA"]
      (.lam "t" (.bgelim "t2" (motAt (.var "t2"))
        gP pb plCell pcCell (.var "t")))

-- #guard bgptRetrD.ok -- possibly heavy; tried inline first
#guard bgptRetrD.ok

/-- **The classification theorem, dimension 1, no connectedness**:
`BGpd(Π₁ A) ≃ A` for every 1-type `A`. -/
def bgFundEquivD : LibDef where
  name := "bgFundEquiv"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (equivR (bgFundR (.var "A")) (.var "A")))
  tm :=
    let A : Raw := .var "A"
    lams ["A", "gA"]
      (apps isoToEquivD.ref
        [bgFundR A, A,
         apps gpdRecD.ref [A, .var "gA"],
         .lam "a" (.bpt (.var "a")),
         .lam "a" (apps gpdRecPtD.ref [A, .var "gA", .var "a"]),
         .lam "t" (apps bgptRetrD.ref [A, .var "gA", .var "t"])])

#guard bgFundEquivD.ok

/-- `BGpd(Π₁ A) ≡ A` in the universe. -/
def bgFundIsD : LibDef where
  name := "bgFundIs"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.path .univ (bgFundR (.var "A")) (.var "A")))
  tm := lams ["A", "gA"]
    (apps uaD.ref [bgFundR (.var "A"), .var "A",
      apps bgFundEquivD.ref [.var "A", .var "gA"]])

#guard bgFundIsD.ok

end Cubical.Library

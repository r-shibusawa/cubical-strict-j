import FormalizedMathematics.Cubical.LibHedberg

namespace Cubical.Library

open Raw

/-! ## Suspension: `S⁰ ≃ Bool`, `S² := Σ S¹`, functoriality, and σ

The kernel's second HIT.  `Σ ⊥` recovers the booleans (an equivalence, and
by `ua` an identification); `Σ S¹` **defines the 2-sphere**; `suspMap` is
the functorial action; and `σ : S¹ → Ω S²` (`merid x ⬝ (merid base)⁻¹`) is
the map underlying the generator of `π₂(S²)`. -/

def s0Ty : Raw := .susp .empty
def s2Ty : Raw := .susp .s1

def toBoolD : LibDef where
  name := "toBool"
  ty := .arr s0Ty boolTy
  tm := .lam "s" (.susprec "k" boolTy trueR falseR
    (.lam "a" (.emptyrec (.path boolTy trueR falseR) (.var "a")))
    (.var "s"))

def fromBoolD : LibDef where
  name := "fromBool"
  ty := .arr boolTy s0Ty
  tm := .lam "b" (.sumcase "k" s0Ty
    (.lam "u" .north) (.lam "u" .south) (.var "b"))

def s0SectD : LibDef where
  name := "s0Sect"
  ty := .pi "b" boolTy
    (.path boolTy (.app toBoolD.ref (.app fromBoolD.ref (.var "b"))) (.var "b"))
  tm := .lam "b" (.sumcase "k"
    (.path boolTy (.app toBoolD.ref (.app fromBoolD.ref (.var "k"))) (.var "k"))
    (.lam "u" (apps congD.ref [.unit, boolTy, .lam "w" (.inl (.var "w")),
      .tt, .var "u", apps isPropUnitD.ref [.tt, .var "u"]]))
    (.lam "u" (apps congD.ref [.unit, boolTy, .lam "w" (.inr (.var "w")),
      .tt, .var "u", apps isPropUnitD.ref [.tt, .var "u"]]))
    (.var "b"))

def s0RetrD : LibDef where
  name := "s0Retr"
  ty := .pi "s" s0Ty
    (.path s0Ty (.app fromBoolD.ref (.app toBoolD.ref (.var "s"))) (.var "s"))
  tm := .lam "s" (.susprec "k"
    (.path s0Ty (.app fromBoolD.ref (.app toBoolD.ref (.var "k"))) (.var "k"))
    (.plam "i0" .north)
    (.plam "i0" .south)
    (.lam "a" (.emptyrec
      (.pathP "j"
        (.path s0Ty
          (.app fromBoolD.ref (.app toBoolD.ref (.merid (.var "a") (.var "j"))))
          (.merid (.var "a") (.var "j")))
        (.plam "i0" .north) (.plam "i0" .south))
      (.var "a")))
    (.var "s"))

#guard toBoolD.ok
#guard fromBoolD.ok
#guard s0SectD.ok
#guard s0RetrD.ok

/-- **`S⁰ ≃ Bool`**. -/
def s0EquivBoolD : LibDef where
  name := "s0EquivBool"
  ty := equivR s0Ty boolTy
  tm := apps setIsoToEquivD.ref
    [s0Ty, boolTy, toBoolD.ref, fromBoolD.ref,
     s0SectD.ref, s0RetrD.ref, isSetBoolD.ref]

/-- `S⁰ ≡ Bool` in the universe. -/
def s0IsBoolD : LibDef where
  name := "s0IsBool"
  ty := .path .univ s0Ty boolTy
  tm := apps uaD.ref [s0Ty, boolTy, s0EquivBoolD.ref]

#guard s0EquivBoolD.ok
#guard s0IsBoolD.ok

-- and it computes: transporting `north` across gives `true`
#guard
  match normalize
    (apps transportD.ref [s0Ty, boolTy, s0IsBoolD.ref, .ann .north s0Ty])
    boolTy with
  | .ok t => t == resolveClosed trueR
  | .error _ => false

/-- Functorial action of suspension. -/
def suspMapD : LibDef where
  name := "suspMap"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (.arr (.var "A") (.var "B"))
      (.arr (.susp (.var "A")) (.susp (.var "B")))))
  tm := lams ["A", "B", "f", "s"] (.susprec "k" (.susp (.var "B"))
    .north .south
    (.lam "a" (.plam "j" (.merid (.app (.var "f") (.var "a")) (.var "j"))))
    (.var "s"))

/-- `suspMap id ≡ id`, by suspension induction (all cells definitional). -/
def suspMapIdD : LibDef where
  name := "suspMapId"
  ty := .pi "A" .univ (.pi "s" (.susp (.var "A"))
    (.path (.susp (.var "A"))
      (apps suspMapD.ref [.var "A", .var "A", .lam "x" (.var "x"), .var "s"])
      (.var "s")))
  tm := lams ["A", "s"] (.susprec "k"
    (.path (.susp (.var "A"))
      (apps suspMapD.ref [.var "A", .var "A", .lam "x" (.var "x"), .var "k"])
      (.var "k"))
    (.plam "i0" .north)
    (.plam "i0" .south)
    (.lam "a" (.plam "j" (.plam "i0" (.merid (.var "a") (.var "j")))))
    (.var "s"))

#guard suspMapD.ok
#guard suspMapIdD.ok

/-- **`σ : S¹ → Ω S²`** — `merid x ⬝ (merid base)⁻¹`, the map underlying
the generator of `π₂(S²)`. -/
def sigmaS1D : LibDef where
  name := "sigmaS1"
  ty := .arr .s1 (.path s2Ty .north .north)
  tm := .lam "x" (apps transD.ref [s2Ty, .north, .south, .north,
    .plam "j" (.merid (.var "x") (.var "j")),
    apps symmD.ref [s2Ty, .north, .south,
      .plam "j" (.merid .sbase (.var "j"))]])

#guard sigmaS1D.ok

/-! ## The torus is `S¹ × S¹`

The famous cubical showcase: the 2-cell `tsurf i j` maps to the product
square `(loop i, loop j)` and *vice versa*, so every cell of both round
trips is **definitional** — the entire isomorphism is refl-shaped, in
stark contrast to the Book-HoTT proof. -/

def prodS1 : Raw := .sigma "u" .s1 .s1

/-- `T² → S¹ × S¹`. -/
def t2ToS1S1D : LibDef where
  name := "t2ToS1S1"
  ty := .arr .torus prodS1
  tm := .lam "t" (.torusrec "k" prodS1
    (.pair .sbase .sbase)
    (.plam "i" (.pair (.sloop (.var "i")) .sbase))
    (.plam "j" (.pair .sbase (.sloop (.var "j"))))
    (.plam "i" (.plam "j" (.pair (.sloop (.var "i")) (.sloop (.var "j")))))
    (.var "t"))

/-- `S¹ × S¹ → T²` — the loop-loop coherence is exactly the 2-cell. -/
def s1s1ToT2D : LibDef where
  name := "s1s1ToT2"
  ty := .arr prodS1 .torus
  tm := .lam "pr" (.app
    (.s1elim "x2" (.arr .s1 .torus)
      (.lam "y" (.s1elim "y2" .torus .tbase
        (.plam "j" (.tloopQ (.var "j"))) (.var "y")))
      (.plam "i" (.lam "y" (.s1elim "y2" .torus
        (.tloopP (.var "i"))
        (.plam "j" (.tsurf (.var "i") (.var "j")))
        (.var "y"))))
      (.fst (.var "pr")))
    (.snd (.var "pr")))

#guard t2ToS1S1D.ok
#guard s1s1ToT2D.ok

/-- First round trip, componentwise — every cell is `refl`-shaped. -/
def t2SectD : LibDef where
  name := "t2Sect"
  ty := .pi "x" .s1 (.pi "y" .s1
    (.path prodS1
      (.app t2ToS1S1D.ref (.app s1s1ToT2D.ref
        (.pair (.var "x") (.var "y"))))
      (.pair (.var "x") (.var "y"))))
  tm :=
    let goal (xv yv : Raw) : Raw := .path prodS1
      (.app t2ToS1S1D.ref (.app s1s1ToT2D.ref (.pair xv yv))) (.pair xv yv)
    lams ["x", "y"] (.app
      (.s1elim "x2" (.pi "y2" .s1 (goal (.var "x2") (.var "y2")))
        (.lam "y2" (.s1elim "y3" (goal .sbase (.var "y3"))
          (.plam "k" (.pair .sbase .sbase))
          (.plam "j" (.plam "k" (.pair .sbase (.sloop (.var "j")))))
          (.var "y2")))
        (.plam "i" (.lam "y2" (.s1elim "y3"
          (goal (.sloop (.var "i")) (.var "y3"))
          (.plam "k" (.pair (.sloop (.var "i")) .sbase))
          (.plam "j" (.plam "k"
            (.pair (.sloop (.var "i")) (.sloop (.var "j")))))
          (.var "y2"))))
        (.var "x"))
      (.var "y"))

/-- Second round trip by torus induction — all four cells definitional. -/
def t2RetrD : LibDef where
  name := "t2Retr"
  ty := .pi "t" .torus
    (.path .torus
      (.app s1s1ToT2D.ref (.app t2ToS1S1D.ref (.var "t"))) (.var "t"))
  tm := .lam "t" (.torusrec "k"
    (.path .torus
      (.app s1s1ToT2D.ref (.app t2ToS1S1D.ref (.var "k"))) (.var "k"))
    (.plam "i0" .tbase)
    (.plam "i" (.plam "i0" (.tloopP (.var "i"))))
    (.plam "j" (.plam "i0" (.tloopQ (.var "j"))))
    (.plam "i" (.plam "j" (.plam "i0" (.tsurf (.var "i") (.var "j")))))
    (.var "t"))

#guard t2SectD.ok
#guard t2RetrD.ok

/-- **`T² ≅ S¹ × S¹`** (an `Iso`; the `Equiv` upgrade awaits the general
`gradLemma` — the product is not a set, so `setIsoToEquiv` cannot apply). -/
def t2IsoS1S1D : LibDef where
  name := "t2IsoS1S1"
  ty := isoTy .torus prodS1
  tm := .pair t2ToS1S1D.ref (.pair s1s1ToT2D.ref
    (.pair
      (.lam "b" (apps t2SectD.ref [.fst (.var "b"), .snd (.var "b")]))
      t2RetrD.ref))

#guard t2IsoS1S1D.ok

/-! ## The general grad lemma: every isomorphism is an equivalence

The last standard tool (no h-level assumption).  This is the `lemIso`
argument: three `hfill`s build the fiber path `p` and its filler, one
square corrects by the left inverse, and a final square maps through `f`
correcting by the right inverse.  `hfill`s are encoded as `hcomp`s with
`k ∧ j`-truncated tubes; compound faces like `(k ∧ j) = 1` become
conjunctions, and `(k ∧ j) = 0` splits into two branches with equal
bodies. -/

def isoToEquivD : LibDef where
  name := "isoToEquiv"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "s" (.pi "b" (.var "B")
      (.path (.var "B") (.app (.var "f") (.app (.var "g") (.var "b")))
        (.var "b")))
    (.pi "t" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (equivR (.var "A") (.var "B")))))))
  tm :=
    let gy : Raw := .app (.var "g") (.var "y")
    let fgy : Raw := .app (.var "f") gy
    let x1 : Raw := .fst (.var "fib")
    let fx1 : Raw := .app (.var "f") x1
    -- q0 : y ≡ f (g y)  (the center's fiber path), q1 : y ≡ f x1
    let q0 : Raw := apps symmD.ref [.var "B", fgy, .var "y",
      .app (.var "s") (.var "y")]
    let q0At (e : Raw) : Raw := .papp q0 (.var "y") fgy e
    let q1At (e : Raw) : Raw := .papp (.snd (.var "fib")) (.var "y") fx1 e
    let tx0At (e : Raw) : Raw := .papp (.app (.var "t") gy)
      (.app (.var "g") fgy) gy e
    let tx1At (e : Raw) : Raw := .papp (.app (.var "t") x1)
      (.app (.var "g") fx1) x1 e
    let sAt (b lhs : Raw) (e : Raw) : Raw :=
      .papp (.app (.var "s") b) lhs b e
    -- hfill for the corrected paths g y ⇝ x0 / x1:
    --   fill (i, j) = hcomp k [ (i=1) ↦ t x @ (k∧j), (i=0) ↦ g y,
    --                           (j=0) ↦ g (q @ i) ]  (g (q @ i))
    -- i1 / i0 are the DNF face lists for iE = 1 / iE = 0; jf for jE = 0.
    let fill (kb : String) (qAt txAt : Raw → Raw)
        (i1 i0 jf : List (List (Raw × Bool))) (iE jE : Raw) : Raw :=
      .hcomp kb (.var "A")
        ((i1.map fun c => (c, txAt (.imin (.var kb) jE)))
          ++ (i0.map fun c => (c, gy))
          ++ (jf.map fun c => (c, .app (.var "g") (qAt iE))))
        (.app (.var "g") (qAt iE))
    -- p i := fill2 i 1 (no j-face); fill2 at generic j has one.
    let fill2Full (iv : String) : Raw :=
      .hcomp "k2" (.var "A")
        [([(.var iv, true)],
           fill "k1" q1At tx1At [[(.var "k2", true)]] [[(.var "k2", false)]]
             [] (.var "k2") .i1),
         ([(.var iv, false)],
           fill "k0" q0At tx0At [[(.var "k2", true)]] [[(.var "k2", false)]]
             [] (.var "k2") .i1)]
        gy
    let fill2At (iv jv : String) : Raw :=
      .hcomp "k2" (.var "A")
        [([(.var iv, true)],
           fill "k1" q1At tx1At
             [[(.var "k2", true), (.var jv, true)]]
             [[(.var "k2", false)], [(.var jv, false)]]
             [] (.imin (.var "k2") (.var jv)) .i1),
         ([(.var iv, false)],
           fill "k0" q0At tx0At
             [[(.var "k2", true), (.var jv, true)]]
             [[(.var "k2", false)], [(.var jv, false)]]
             [] (.imin (.var "k2") (.var jv)) .i1),
         ([(.var jv, false)], gy)]
        gy
    -- sq i j : corrects fill2 back to the g-image square
    let sq (iv jv : String) : Raw :=
      .hcomp "k3" (.var "A")
        [([(.var iv, true)],
           fill "k1" q1At tx1At [[(.var jv, true)]] [[(.var jv, false)]]
             [[(.var "k3", true)]] (.var jv) (.ineg (.var "k3"))),
         ([(.var iv, false)],
           fill "k0" q0At tx0At [[(.var jv, true)]] [[(.var jv, false)]]
             [[(.var "k3", true)]] (.var jv) (.ineg (.var "k3"))),
         ([(.var jv, true)],
           .papp (.app (.var "t") (fill2Full iv))
             (.app (.var "g") (.app (.var "f") (fill2Full iv)))
             (fill2Full iv) (.ineg (.var "k3"))),
         ([(.var jv, false)], gy)]
        (fill2At iv jv)
    -- sq1 i j : maps through f, corrected by the right inverse s
    let sq1 (iv jv : String) : Raw :=
      .hcomp "k4" (.var "B")
        [([(.var iv, false)], sAt (q0At (.var jv)) (.app (.var "f")
           (.app (.var "g") (q0At (.var jv)))) (.var "k4")),
         ([(.var iv, true)], sAt (q1At (.var jv)) (.app (.var "f")
           (.app (.var "g") (q1At (.var jv)))) (.var "k4")),
         ([(.var jv, false)], sAt (.var "y") fgy (.var "k4")),
         ([(.var jv, true)], sAt (.app (.var "f") (fill2Full iv))
           (.app (.var "f") (.app (.var "g")
             (.app (.var "f") (fill2Full iv)))) (.var "k4"))]
        (.app (.var "f") (sq iv jv))
    lams ["A", "B", "f", "g", "s", "t"]
      (.pair (.var "f") (.lam "y" (.pair
        (.pair gy q0)
        (.lam "fib" (.plam "i" (.pair
          (fill2Full "i")
          (.plam "j" (sq1 "i" "j"))))))))

#guard isoToEquivD.ok

/-- **`T² ≃ S¹ × S¹`** — the Iso upgraded by the general grad lemma. -/
def t2EquivS1S1D : LibDef where
  name := "t2EquivS1S1"
  ty := equivR .torus prodS1
  tm := apps isoToEquivD.ref
    [.torus, prodS1, t2ToS1S1D.ref, s1s1ToT2D.ref,
     .lam "b" (apps t2SectD.ref [.fst (.var "b"), .snd (.var "b")]),
     t2RetrD.ref]

/-- **`T² ≡ S¹ × S¹`** in the universe. -/
def t2IsS1S1D : LibDef where
  name := "t2IsS1S1"
  ty := .path .univ .torus prodS1
  tm := apps uaD.ref [.torus, prodS1, t2EquivS1S1D.ref]

#guard t2EquivS1S1D.ok
#guard t2IsS1S1D.ok

/-! ## Propositional truncation: the logic layer

`∥ A ∥` makes *mere existence* expressible.  `squash` is definitionally
`isProp ∥A∥`; idempotence is the first application of the general
`isoToEquiv` (its section is `refl`!); and connectivity of the circle is a
new *kind* of theorem — a mere-existence statement proven by `s1elim` into
a proposition. -/

/-- `∥ A ∥` is a proposition — the constructor, verbatim. -/
def isPropTruncD : LibDef where
  name := "isPropTrunc"
  ty := .pi "A" .univ (isPropR (.trunc (.var "A")))
  tm := lams ["A", "xp", "yp"] (.plam "i"
    (.squash (.var "xp") (.var "yp") (.var "i")))

/-- Functoriality of truncation. -/
def truncMapD : LibDef where
  name := "truncMap"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (.arr (.var "A") (.var "B"))
      (.arr (.trunc (.var "A")) (.trunc (.var "B")))))
  tm := lams ["A", "B", "f", "t"] (.truncrec (.trunc (.var "B"))
    (.app isPropTruncD.ref (.var "B"))
    (.lam "a" (.tin (.app (.var "f") (.var "a"))))
    (.var "t"))

/-- `∥ ∥A∥ ∥ ≃ ∥A∥` — idempotence, via the general grad lemma (the
section is definitional). -/
def truncIdemD : LibDef where
  name := "truncIdem"
  ty := .pi "A" .univ
    (equivR (.trunc (.trunc (.var "A"))) (.trunc (.var "A")))
  tm := .lam "A" (apps isoToEquivD.ref
    [.trunc (.trunc (.var "A")), .trunc (.var "A"),
     .lam "t" (.truncrec (.trunc (.var "A"))
       (.app isPropTruncD.ref (.var "A"))
       (.lam "u" (.var "u")) (.var "t")),
     .lam "t" (.tin (.var "t")),
     .lam "b" (.plam "i0" (.var "b")),
     .lam "a" (apps (.app isPropTruncD.ref (.trunc (.var "A")))
       [.tin (.truncrec (.trunc (.var "A"))
         (.app isPropTruncD.ref (.var "A"))
         (.lam "u" (.var "u")) (.var "a")),
        .var "a"])])

#guard isPropTruncD.ok
#guard truncMapD.ok
#guard truncIdemD.ok

/-- **The circle is connected**: `Π (x : S¹). ∥ base ≡ x ∥`. -/
def s1ConnectedD : LibDef where
  name := "s1Connected"
  ty := .pi "x" .s1 (.trunc (.path .s1 .sbase (.var "x")))
  tm :=
    let X : Raw := .trunc (.path .s1 .sbase .sbase)
    let line : Raw := .plam "i"
      (.trunc (.path .s1 .sbase (.sloop (.var "i"))))
    let reflB : Raw := .tin (.plam "i0" .sbase)
    .lam "x" (.s1elim "x2" (.trunc (.path .s1 .sbase (.var "x2")))
      reflB
      (apps toPathPD.ref [X, X, line, reflB, reflB,
        .plam "k" (.squash
          (apps transportD.ref [X, X, line, reflB])
          reflB (.var "k"))])
      (.var "x"))

#guard s1ConnectedD.ok

/-- `winding` is *merely* surjective: `Π z. ∥ Σ p. winding p ≡ z ∥`. -/
def windingSurjD : LibDef where
  name := "windingSurj"
  ty := .pi "z" .int (.trunc (.sigma "p" (.path .s1 .sbase .sbase)
    (.path .int (.app windingD.ref (.var "p")) (.var "z"))))
  tm := .lam "z" (.tin (.pair
    (.app intLoopD.ref (.var "z"))
    (.app encodeDecodeD.ref (.var "z"))))

#guard windingSurjD.ok

/-! ## Pushouts: suspension as a pushout, wedges, cofibers

The generic colimit HIT.  Flagship: `Σ A ≃ pushout (⊤ ← A → ⊤)` with every
cell of both round trips definitional (the same phenomenon as the torus).
Wedges and cofibers become one-liners. -/

private def cconst : Raw := .lam "c0" .tt
private def poSusp (A : Raw) : Raw := .pushout .unit .unit A cconst cconst

def suspToPushD : LibDef where
  name := "suspToPush"
  ty := .pi "A" .univ (.arr (.susp (.var "A")) (poSusp (.var "A")))
  tm := lams ["A", "s"] (.susprec "k" (poSusp (.var "A"))
    (.pinl .tt) (.pinr .tt)
    (.lam "a" (.plam "j" (.ppush cconst cconst (.var "a") (.var "j"))))
    (.var "s"))

def pushToSuspD : LibDef where
  name := "pushToSusp"
  ty := .pi "A" .univ (.arr (poSusp (.var "A")) (.susp (.var "A")))
  tm := lams ["A", "p"] (.pushrec "k" (.susp (.var "A"))
    (.lam "u" .north) (.lam "u" .south)
    (.lam "a" (.plam "j" (.merid (.var "a") (.var "j"))))
    (.var "p"))

/-- Round trip on the pushout side (`⊤`-payloads via `isProp ⊤`). -/
def suspPushSectD : LibDef where
  name := "suspPushSect"
  ty := .pi "A" .univ (.pi "p" (poSusp (.var "A"))
    (.path (poSusp (.var "A"))
      (apps suspToPushD.ref [.var "A",
        apps pushToSuspD.ref [.var "A", .var "p"]])
      (.var "p")))
  tm := lams ["A", "p"] (.pushrec "k"
    (.path (poSusp (.var "A"))
      (apps suspToPushD.ref [.var "A",
        apps pushToSuspD.ref [.var "A", .var "k"]])
      (.var "k"))
    (.lam "u" (apps congD.ref [.unit, poSusp (.var "A"),
      .lam "w" (.pinl (.var "w")), .tt, .var "u",
      apps isPropUnitD.ref [.tt, .var "u"]]))
    (.lam "u" (apps congD.ref [.unit, poSusp (.var "A"),
      .lam "w" (.pinr (.var "w")), .tt, .var "u",
      apps isPropUnitD.ref [.tt, .var "u"]]))
    (.lam "a" (.plam "j" (.plam "i0"
      (.ppush cconst cconst (.var "a") (.var "j")))))
    (.var "p"))

/-- Round trip on the suspension side — fully definitional. -/
def suspPushRetrD : LibDef where
  name := "suspPushRetr"
  ty := .pi "A" .univ (.pi "s" (.susp (.var "A"))
    (.path (.susp (.var "A"))
      (apps pushToSuspD.ref [.var "A",
        apps suspToPushD.ref [.var "A", .var "s"]])
      (.var "s")))
  tm := lams ["A", "s"] (.susprec "k"
    (.path (.susp (.var "A"))
      (apps pushToSuspD.ref [.var "A",
        apps suspToPushD.ref [.var "A", .var "k"]])
      (.var "k"))
    (.plam "i0" .north)
    (.plam "i0" .south)
    (.lam "a" (.plam "j" (.plam "i0" (.merid (.var "a") (.var "j")))))
    (.var "s"))

#guard suspToPushD.ok
#guard pushToSuspD.ok
#guard suspPushSectD.ok
#guard suspPushRetrD.ok

/-- **`Σ A ≃ pushout (⊤ ← A → ⊤)`** — suspension *is* a pushout. -/
def suspIsPushoutD : LibDef where
  name := "suspIsPushout"
  ty := .pi "A" .univ (equivR (.susp (.var "A")) (poSusp (.var "A")))
  tm := .lam "A" (apps isoToEquivD.ref
    [.susp (.var "A"), poSusp (.var "A"),
     .app suspToPushD.ref (.var "A"),
     .app pushToSuspD.ref (.var "A"),
     .app suspPushSectD.ref (.var "A"),
     .app suspPushRetrD.ref (.var "A")])

#guard suspIsPushoutD.ok

/-- The wedge `A ∨ B` (pushout of the two basepoint inclusions). -/
def wedge (A B a0 b0 : Raw) : Raw :=
  .pushout A B .unit (.lam "u0" a0) (.lam "u0" b0)

/-- The cofiber (mapping cone) of `f : A → B`. -/
def cofib (A B f : Raw) : Raw :=
  .pushout .unit B A (.lam "u0" .tt) f

/-- `S¹ ∨ S¹` — the figure eight, as a concrete type. -/
def figureEightD : LibDef where
  name := "figureEight"
  ty := .univ
  tm := wedge .s1 .s1 .sbase .sbase

#guard figureEightD.ok

end Cubical.Library

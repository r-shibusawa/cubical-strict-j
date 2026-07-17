import FormalizedMathematics.Cubical.LibLoop

namespace Cubical.Library

open Raw

/-! ## The functor category

Objects: functors `C → D`; morphisms: natural transformations; composition:
vertical.  Since functors live in `U₁`, the functor category is a
`precatTy 1` — the universe hierarchy earning its keep.  Equality of natural
transformations is componentwise (`natTransEq`): the naturality field is a
*proposition* when `D` has hom-sets, so it rides along by `toPathP`. -/

/-- Associativity projection of the precategory Σ-encoding. -/
def catAssoc (c : Raw) : Raw := .snd (.snd (.snd (.snd (.snd (.snd c)))))

/-- Categories with hom-sets. -/
def setCatTy : Raw :=
  .sigma "C0" (precatTy 0)
    (.pi "sx" (catOb (.var "C0")) (.pi "sy" (catOb (.var "C0"))
      (isSetR (apps (catHom (.var "C0")) [.var "sx", .var "sy"]))))

/-- `isProp` closure under Π, one universe up. -/
def isPropPi11D : LibDef where
  name := "isPropPi@11"
  ty := .pi "A" (.univN 1) (.pi "B" (.arr (.var "A") (.univN 1))
    (.arr (.pi "x" (.var "A") (isPropR (.app (.var "B") (.var "x"))))
      (.pi "f" (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
        (.pi "g" (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
          (.path (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
            (.var "f") (.var "g"))))))
  tm := isPropPiD.tm

def transport1D : LibDef where
  name := "transport@1"
  ty := .pi "A" (.univN 1) (.pi "B" (.univN 1)
    (.arr (.path (.univN 1) (.var "A") (.var "B"))
      (.arr (.var "A") (.var "B"))))
  tm := transportD.tm

def toPathP1D : LibDef where
  name := "toPathP@1"
  ty := .pi "X" (.univN 1) (.pi "Y" (.univN 1)
    (.pi "A" (.path (.univN 1) (.var "X") (.var "Y"))
      (.pi "x" (.var "X") (.pi "y" (.var "Y")
        (.arr
          (.path (.var "Y")
            (apps transport1D.ref [.var "X", .var "Y", .var "A", .var "x"])
            (.var "y"))
          (.pathP "i" (.papp (.var "A") (.var "X") (.var "Y") (.var "i"))
            (.var "x") (.var "y")))))))
  tm := lams ["X", "Y", "A", "x", "y", "h"]
    (.plam "i" (.hcomp "j"
      (.papp (.var "A") (.var "X") (.var "Y") (.var "i"))
      [([(.var "i", false)], .var "x"),
       ([(.var "i", true)],
         .papp (.var "h")
           (apps transport1D.ref [.var "X", .var "Y", .var "A", .var "x"])
           (.var "y") (.var "j"))]
      (.transp "j2"
        (.papp (.var "A") (.var "X") (.var "Y")
          (.imin (.var "i") (.var "j2")))
        (.var "x"))))

/-- `cong` with a level-1 domain and codomain. -/
def cong11D : LibDef where
  name := "cong@11"
  ty := .pi "A" (.univN 1) (.pi "B" (.univN 1)
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
      (.arr (.path (.var "A") (.var "a") (.var "b"))
        (.path (.var "B") (.app (.var "f") (.var "a"))
          (.app (.var "f") (.var "b"))))))))
  tm := congD.tm

#guard isPropPi11D.ok
#guard transport1D.ok
#guard toPathP1D.ok
#guard cong11D.ok

/-- Vertical composition of natural transformations (naturality: two
associativities and the two component naturalities). -/
def compNatD : LibDef where
  name := "compNat"
  ty := .pi "Cc" (precatTy 0) (.pi "Dd" (precatTy 0)
    (.pi "Ff" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Gg" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Hh" (functorTy (.var "Cc") (.var "Dd"))
    (.arr (natTransTy (.var "Cc") (.var "Dd") (.var "Ff") (.var "Gg"))
    (.arr (natTransTy (.var "Cc") (.var "Dd") (.var "Gg") (.var "Hh"))
      (natTransTy (.var "Cc") (.var "Dd") (.var "Ff") (.var "Hh"))))))))
  tm :=
    let D := .var "Dd"
    let cmpd (a b c fg gh : Raw) : Raw := apps (catCmp D) [a, b, c, fg, gh]
    let homd (a b : Raw) : Raw := apps (catHom D) [a, b]
    let F0 (v : Raw) : Raw := .app (funF0 (.var "Ff")) v
    let G0 (v : Raw) : Raw := .app (funF0 (.var "Gg")) v
    let H0 (v : Raw) : Raw := .app (funF0 (.var "Hh")) v
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let Ff1 : Raw := apps (funF1 (.var "Ff")) [x, y, .var "f"]
    let G1f : Raw := apps (funF1 (.var "Gg")) [x, y, .var "f"]
    let H1f : Raw := apps (funF1 (.var "Hh")) [x, y, .var "f"]
    let alx : Raw := .app (.fst (.var "al")) x
    let aly : Raw := .app (.fst (.var "al")) y
    let bex : Raw := .app (.fst (.var "be")) x
    let bey : Raw := .app (.fst (.var "be")) y
    let PT := homd (F0 x) (H0 y)
    let X1 := cmpd (F0 x) (F0 y) (H0 y) Ff1 (cmpd (F0 y) (G0 y) (H0 y) aly bey)
    let X2 := cmpd (F0 x) (G0 y) (H0 y) (cmpd (F0 x) (F0 y) (G0 y) Ff1 aly) bey
    let X3 := cmpd (F0 x) (G0 y) (H0 y) (cmpd (F0 x) (G0 x) (G0 y) alx G1f) bey
    let X4 := cmpd (F0 x) (G0 x) (H0 y) alx (cmpd (G0 x) (G0 y) (H0 y) G1f bey)
    let X5 := cmpd (F0 x) (G0 x) (H0 y) alx (cmpd (G0 x) (H0 x) (H0 y) bex H1f)
    let X6 := cmpd (F0 x) (H0 x) (H0 y) (cmpd (F0 x) (G0 x) (H0 x) alx bex) H1f
    let L12 := apps symmD.ref [PT, X2, X1,
      apps (catAssoc D) [F0 x, F0 y, G0 y, H0 y, Ff1, aly, bey]]
    let L23 := apps congD.ref [homd (F0 x) (G0 y), PT,
      .lam "h2" (cmpd (F0 x) (G0 y) (H0 y) (.var "h2") bey),
      cmpd (F0 x) (F0 y) (G0 y) Ff1 aly,
      cmpd (F0 x) (G0 x) (G0 y) alx G1f,
      apps (.snd (.var "al")) [x, y, .var "f"]]
    let L34 := apps (catAssoc D) [F0 x, G0 x, G0 y, H0 y, alx, G1f, bey]
    let L45 := apps congD.ref [homd (G0 x) (H0 y), PT,
      .lam "h2" (cmpd (F0 x) (G0 x) (H0 y) alx (.var "h2")),
      cmpd (G0 x) (G0 y) (H0 y) G1f bey,
      cmpd (G0 x) (H0 x) (H0 y) bex H1f,
      apps (.snd (.var "be")) [x, y, .var "f"]]
    let L56 := apps symmD.ref [PT, X6, X5,
      apps (catAssoc D) [F0 x, G0 x, H0 x, H0 y, alx, bex, H1f]]
    lams ["Cc", "Dd", "Ff", "Gg", "Hh", "al", "be"]
      (.pair
        (.lam "x" (cmpd (F0 x) (G0 x) (H0 x)
          (.app (.fst (.var "al")) x) (.app (.fst (.var "be")) x)))
        (lams ["x", "y", "f"]
          (apps transD.ref [PT, X1, X2, X6, L12,
            apps transD.ref [PT, X2, X3, X6, L23,
              apps transD.ref [PT, X3, X4, X6, L34,
                apps transD.ref [PT, X4, X5, X6, L45, L56]]]])))

#guard compNatD.ok

/-- Componentwise equal natural transformations are equal (`D` a
set-category: the naturality field is propositional and rides along). -/
def natTransEqD : LibDef where
  name := "natTransEq"
  ty := .pi "Cc" (precatTy 0) (.pi "Dp" setCatTy
    (.pi "Ff" (functorTy (.var "Cc") (.fst (.var "Dp")))
    (.pi "Gg" (functorTy (.var "Cc") (.fst (.var "Dp")))
    (.pi "al" (natTransTy (.var "Cc") (.fst (.var "Dp")) (.var "Ff") (.var "Gg"))
    (.pi "be" (natTransTy (.var "Cc") (.fst (.var "Dp")) (.var "Ff") (.var "Gg"))
    (.arr
      (.pi "x" (catOb (.var "Cc"))
        (.path (apps (catHom (.fst (.var "Dp")))
            [.app (funF0 (.var "Ff")) (.var "x"),
             .app (funF0 (.var "Gg")) (.var "x")])
          (.app (.fst (.var "al")) (.var "x"))
          (.app (.fst (.var "be")) (.var "x"))))
      (.path (natTransTy (.var "Cc") (.fst (.var "Dp")) (.var "Ff") (.var "Gg"))
        (.var "al") (.var "be"))))))))
  tm :=
    let D := .fst (.var "Dp")
    let homSet := .snd (.var "Dp")
    let F0 (v : Raw) : Raw := .app (funF0 (.var "Ff")) v
    let G0 (v : Raw) : Raw := .app (funF0 (.var "Gg")) v
    let etaTy : Raw := .pi "x" (catOb (.var "Cc"))
      (apps (catHom D) [F0 (.var "x"), G0 (.var "x")])
    let etaPath : Raw := .plam "i" (.lam "x"
      (.papp (.app (.var "hc") (.var "x"))
        (.app (.fst (.var "al")) (.var "x"))
        (.app (.fst (.var "be")) (.var "x"))
        (.var "i")))
    -- isProp of the naturality square at a given eta
    let isPropNat (e : Raw) : Raw :=
      apps isPropPi11D.ref [catOb (.var "Cc"),
        .lam "x" (.pi "y" (catOb (.var "Cc"))
          (.pi "f" (apps (catHom (.var "Cc")) [.var "x", .var "y"])
            (.path (apps (catHom D) [F0 (.var "x"), G0 (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), F0 (.var "y"), G0 (.var "y"),
                apps (funF1 (.var "Ff")) [.var "x", .var "y", .var "f"],
                .app e (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), G0 (.var "x"), G0 (.var "y"),
                .app e (.var "x"),
                apps (funF1 (.var "Gg")) [.var "x", .var "y", .var "f"]])))),
        .lam "x" (apps isPropPi11D.ref [catOb (.var "Cc"),
          .lam "y" (.pi "f" (apps (catHom (.var "Cc")) [.var "x", .var "y"])
            (.path (apps (catHom D) [F0 (.var "x"), G0 (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), F0 (.var "y"), G0 (.var "y"),
                apps (funF1 (.var "Ff")) [.var "x", .var "y", .var "f"],
                .app e (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), G0 (.var "x"), G0 (.var "y"),
                .app e (.var "x"),
                apps (funF1 (.var "Gg")) [.var "x", .var "y", .var "f"]]))),
          .lam "y" (apps isPropPiD.ref [
            apps (catHom (.var "Cc")) [.var "x", .var "y"],
            .lam "f" (.path (apps (catHom D) [F0 (.var "x"), G0 (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), F0 (.var "y"), G0 (.var "y"),
                apps (funF1 (.var "Ff")) [.var "x", .var "y", .var "f"],
                .app e (.var "y")])
              (apps (catCmp D) [F0 (.var "x"), G0 (.var "x"), G0 (.var "y"),
                .app e (.var "x"),
                apps (funF1 (.var "Gg")) [.var "x", .var "y", .var "f"]])),
            .lam "f" (apps homSet [F0 (.var "x"), G0 (.var "y"),
              apps (catCmp D) [F0 (.var "x"), F0 (.var "y"), G0 (.var "y"),
                apps (funF1 (.var "Ff")) [.var "x", .var "y", .var "f"],
                .app e (.var "y")],
              apps (catCmp D) [F0 (.var "x"), G0 (.var "x"), G0 (.var "y"),
                .app e (.var "x"),
                apps (funF1 (.var "Gg")) [.var "x", .var "y", .var "f"]]])])])]
    let natAl : Raw := natSquareTy (.var "Cc") D (.var "Ff") (.var "Gg")
      (.fst (.var "al"))
    let natBe : Raw := natSquareTy (.var "Cc") D (.var "Ff") (.var "Gg")
      (.fst (.var "be"))
    let etaPathAnn0 : Raw := .ann etaPath
      (.path etaTy (.fst (.var "al")) (.fst (.var "be")))
    let line : Raw := .plam "i"
      (natSquareTy (.var "Cc") D (.var "Ff") (.var "Gg")
        (.papp etaPathAnn0 (.fst (.var "al")) (.fst (.var "be")) (.var "i")))
    let natPathP : Raw := apps toPathP1D.ref [natAl, natBe, line,
      .snd (.var "al"), .snd (.var "be"),
      apps (isPropNat (.fst (.var "be")))
        [apps transport1D.ref [natAl, natBe, line, .snd (.var "al")],
         .snd (.var "be")]]
    let etaPathAnn : Raw := .ann etaPath
      (.path etaTy (.fst (.var "al")) (.fst (.var "be")))
    lams ["Cc", "Dp", "Ff", "Gg", "al", "be", "hc"]
      (.plam "i" (.pair
        (.papp etaPathAnn (.fst (.var "al")) (.fst (.var "be")) (.var "i"))
        (.papp natPathP (.snd (.var "al")) (.snd (.var "be")) (.var "i"))))

#guard natTransEqD.ok

/-- **The functor category `[C, D]`** — a `precatTy 1` (objects live one
universe up), its laws proven componentwise via `natTransEq` from the laws
of `D`. -/
def functorCatD : LibDef where
  name := "functorCat"
  ty := .pi "Cc" (precatTy 0) (.arr setCatTy (precatTy 1))
  tm :=
    let D := .fst (.var "Dp")
    let obT : Raw := functorTy (.var "Cc") D
    let F0of (F v : Raw) : Raw := .app (funF0 F) v
    let etaOf (a v : Raw) : Raw := .app (.fst a) v
    let cmpd (a b c fg gh : Raw) : Raw := apps (catCmp D) [a, b, c, fg, gh]
    let compN (F G H a b : Raw) : Raw :=
      apps compNatD.ref [.var "Cc", D, F, G, H, a, b]
    let idN (F : Raw) : Raw := apps idNatD.ref [.var "Cc", D, F]
    let nteq (F G a b h : Raw) : Raw :=
      apps natTransEqD.ref [.var "Cc", .var "Dp", F, G, a, b, h]
    lams ["Cc", "Dp"]
      (.pair obT
      (.pair (lams ["Ff", "Gg"]
        (natTransTy (.var "Cc") D (.var "Ff") (.var "Gg")))
      (.pair (.lam "Ff" (idN (.var "Ff")))
      (.pair (lams ["Ff", "Gg", "Hh", "al", "be"]
        (compN (.var "Ff") (.var "Gg") (.var "Hh") (.var "al") (.var "be")))
      (.pair
        -- left unit: (idNat F) ⬝v α ≡ α, componentwise idl of D
        (lams ["Ff", "Gg", "al"]
          (nteq (.var "Ff") (.var "Gg")
            (compN (.var "Ff") (.var "Ff") (.var "Gg")
              (idN (.var "Ff")) (.var "al"))
            (.var "al")
            (.lam "x" (apps (catIdl D)
              [F0of (.var "Ff") (.var "x"), F0of (.var "Gg") (.var "x"),
               etaOf (.var "al") (.var "x")]))))
      (.pair
        -- right unit
        (lams ["Ff", "Gg", "al"]
          (nteq (.var "Ff") (.var "Gg")
            (compN (.var "Ff") (.var "Gg") (.var "Gg")
              (.var "al") (idN (.var "Gg")))
            (.var "al")
            (.lam "x" (apps (catIdr D)
              [F0of (.var "Ff") (.var "x"), F0of (.var "Gg") (.var "x"),
               etaOf (.var "al") (.var "x")]))))
        -- associativity, componentwise assoc of D
        (lams ["Ff", "Gg", "Hh", "Kk", "al", "be", "ga"]
          (nteq (.var "Ff") (.var "Kk")
            (compN (.var "Ff") (.var "Hh") (.var "Kk")
              (compN (.var "Ff") (.var "Gg") (.var "Hh") (.var "al") (.var "be"))
              (.var "ga"))
            (compN (.var "Ff") (.var "Gg") (.var "Kk")
              (.var "al")
              (compN (.var "Gg") (.var "Hh") (.var "Kk") (.var "be") (.var "ga")))
            (.lam "x" (apps (catAssoc D)
              [F0of (.var "Ff") (.var "x"), F0of (.var "Gg") (.var "x"),
               F0of (.var "Hh") (.var "x"), F0of (.var "Kk") (.var "x"),
               etaOf (.var "al") (.var "x"), etaOf (.var "be") (.var "x"),
               etaOf (.var "ga") (.var "x")]))))))))))

#guard functorCatD.ok

/-- **`Bℤ`**: the one-object category of the group `(ℤ, +)` — a set-category
whose laws are the ported addition laws. -/
def intDeloopD : LibDef where
  name := "intDeloop"
  ty := setCatTy
  tm := .pair
    (.pair .unit
    (.pair (lams ["u1", "u2"] .int)
    (.pair (.lam "u1" (.ipos .zero))
    (.pair (lams ["u1", "u2", "u3", "m", "n"]
      (apps addD.ref [.var "m", .var "n"]))
    (.pair (lams ["u1", "u2", "f"]
      (.app addZeroLD.ref (.var "f")))
    (.pair (lams ["u1", "u2", "f"]
      (.app addZeroRD.ref (.var "f")))
      (lams ["u1", "u2", "u3", "u4", "f", "g", "h"]
        (apps addAssocD.ref [.var "f", .var "g", .var "h"]))))))))
    (lams ["u1", "u2"] isSetZD.ref)

#guard intDeloopD.ok

/-- The functor category `[Bℤ, Bℤ]` — a concrete `precatTy 1`. -/
def endoBZCatD : LibDef where
  name := "endoBZCat"
  ty := precatTy 1
  tm := apps functorCatD.ref [.fst intDeloopD.ref, intDeloopD.ref]

#guard endoBZCatD.ok

/-! ## The loop space of the circle *is* the integers

Everything converges: the isomorphism (`pi1S1Iso`), the fact that ℤ is a
set (`setIsoToEquiv` needs only the codomain to be a set), and univalence
turn `Ω S¹ ≅ ℤ` into an *identification of types* — and then `isSet (Ω S¹)`
falls out by transport. -/

def loopSpaceTy : Raw := .path .s1 .sbase .sbase

/-- The loop-space equivalence, via `setIsoToEquiv` (ℤ is a set). -/
def pi1S1EquivD : LibDef where
  name := "pi1S1Equiv"
  ty := equivR loopSpaceTy .int
  tm := apps setIsoToEquivD.ref
    [loopSpaceTy, .int, windingD.ref, intLoopD.ref,
     encodeDecodeD.ref,
     .lam "a" (apps decodeEncodeD2.ref [.sbase, .var "a"]),
     isSetZD.ref]

/-- **`Ω S¹ ≡ ℤ`** — an identification of types in the universe. -/
def loopSpaceIsIntD : LibDef where
  name := "loopSpaceIsInt"
  ty := .path .univ loopSpaceTy .int
  tm := apps uaD.ref [loopSpaceTy, .int, pi1S1EquivD.ref]

#guard pi1S1EquivD.ok
#guard loopSpaceIsIntD.ok

-- Note: `transport loopSpaceIsInt loop` does normalize to `+1`, but the
-- evaluation walks the large embedded equivalence proof and takes tens of
-- minutes — too slow for a build-time guard.  The computation law
-- `transport (ua e) ≡ e.fst` is already guard-verified generically.

/- `isSet (Ω S¹)` by transporting `isSet ℤ` along `loopSpaceIsInt` TYPECHECKS
in principle, but the conversion walks the embedded equivalence proof and
explodes (tens of minutes).  The cheap route — a generic "retract of a set
is a set" lemma applied to (winding, intLoop, decodeEncode) — is on the
roadmap (needs the inverse law `p⁻¹ ⬝ p ≡ refl` first). -/

/-! ## Functor composition and whiskering -/

def funFid (F : Raw) : Raw := .fst (.snd (.snd F))
def funFcomp (F : Raw) : Raw := .snd (.snd (.snd F))

/-- Composition of functors; the laws are `cong`/`trans` chains through the
component laws. -/
def compFunctorD : LibDef where
  name := "compFunctor"
  ty := .pi "Cc" (precatTy 0) (.pi "Dd" (precatTy 0) (.pi "Ee" (precatTy 0)
    (.pi "Ff" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Gg" (functorTy (.var "Dd") (.var "Ee"))
      (functorTy (.var "Cc") (.var "Ee"))))))
  tm :=
    let F0 (v : Raw) : Raw := .app (funF0 (.var "Ff")) v
    let G0 (v : Raw) : Raw := .app (funF0 (.var "Gg")) v
    let F1 (a b v : Raw) : Raw := apps (funF1 (.var "Ff")) [a, b, v]
    let G1 (a b v : Raw) : Raw := apps (funF1 (.var "Gg")) [a, b, v]
    let homD (a b : Raw) : Raw := apps (catHom (.var "Dd")) [a, b]
    let homE (a b : Raw) : Raw := apps (catHom (.var "Ee")) [a, b]
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let z : Raw := .var "z"
    lams ["Cc", "Dd", "Ee", "Ff", "Gg"]
      (.pair (.lam "x" (G0 (F0 x)))
      (.pair (lams ["x", "y", "f"]
        (G1 (F0 x) (F0 y) (F1 x y (.var "f"))))
      (.pair
        -- identity law
        (.lam "x" (apps transD.ref
          [homE (G0 (F0 x)) (G0 (F0 x)),
           G1 (F0 x) (F0 x) (F1 x x (.app (catId (.var "Cc")) x)),
           G1 (F0 x) (F0 x) (.app (catId (.var "Dd")) (F0 x)),
           .app (catId (.var "Ee")) (G0 (F0 x)),
           apps congD.ref [homD (F0 x) (F0 x), homE (G0 (F0 x)) (G0 (F0 x)),
             .lam "h2" (G1 (F0 x) (F0 x) (.var "h2")),
             F1 x x (.app (catId (.var "Cc")) x),
             .app (catId (.var "Dd")) (F0 x),
             .app (funFid (.var "Ff")) x],
           .app (funFid (.var "Gg")) (F0 x)]))
        -- composition law
        (lams ["x", "y", "z", "f", "g"] (apps transD.ref
          [homE (G0 (F0 x)) (G0 (F0 z)),
           G1 (F0 x) (F0 z) (F1 x z
             (apps (catCmp (.var "Cc")) [x, y, z, .var "f", .var "g"])),
           G1 (F0 x) (F0 z)
             (apps (catCmp (.var "Dd")) [F0 x, F0 y, F0 z,
               F1 x y (.var "f"), F1 y z (.var "g")]),
           apps (catCmp (.var "Ee")) [G0 (F0 x), G0 (F0 y), G0 (F0 z),
             G1 (F0 x) (F0 y) (F1 x y (.var "f")),
             G1 (F0 y) (F0 z) (F1 y z (.var "g"))],
           apps congD.ref [homD (F0 x) (F0 z), homE (G0 (F0 x)) (G0 (F0 z)),
             .lam "h2" (G1 (F0 x) (F0 z) (.var "h2")),
             F1 x z (apps (catCmp (.var "Cc")) [x, y, z, .var "f", .var "g"]),
             apps (catCmp (.var "Dd")) [F0 x, F0 y, F0 z,
               F1 x y (.var "f"), F1 y z (.var "g")],
             apps (funFcomp (.var "Ff")) [x, y, z, .var "f", .var "g"]],
           apps (funFcomp (.var "Gg")) [F0 x, F0 y, F0 z,
             F1 x y (.var "f"), F1 y z (.var "g")]])))))

#guard compFunctorD.ok

/-- Left whiskering `F ◁ α`: naturality is α's naturality at `F`-images. -/
def whiskerLD : LibDef where
  name := "whiskerL"
  ty := .pi "Cc" (precatTy 0) (.pi "Dd" (precatTy 0) (.pi "Ee" (precatTy 0)
    (.pi "Ff" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Gg" (functorTy (.var "Dd") (.var "Ee"))
    (.pi "Hh" (functorTy (.var "Dd") (.var "Ee"))
    (.arr (natTransTy (.var "Dd") (.var "Ee") (.var "Gg") (.var "Hh"))
      (natTransTy (.var "Cc") (.var "Ee")
        (apps compFunctorD.ref [.var "Cc", .var "Dd", .var "Ee",
          .var "Ff", .var "Gg"])
        (apps compFunctorD.ref [.var "Cc", .var "Dd", .var "Ee",
          .var "Ff", .var "Hh"]))))))))
  tm :=
    let F0 (v : Raw) : Raw := .app (funF0 (.var "Ff")) v
    lams ["Cc", "Dd", "Ee", "Ff", "Gg", "Hh", "al"]
      (.pair
        (.lam "x" (.app (.fst (.var "al")) (F0 (.var "x"))))
        (lams ["x", "y", "f"]
          (apps (.snd (.var "al"))
            [F0 (.var "x"), F0 (.var "y"),
             apps (funF1 (.var "Ff")) [.var "x", .var "y", .var "f"]])))

/-- Right whiskering `α ▷ H`: conjugate α's naturality by `H`'s
functoriality. -/
def whiskerRD : LibDef where
  name := "whiskerR"
  ty := .pi "Cc" (precatTy 0) (.pi "Dd" (precatTy 0) (.pi "Ee" (precatTy 0)
    (.pi "Ff" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Gg" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Hh" (functorTy (.var "Dd") (.var "Ee"))
    (.arr (natTransTy (.var "Cc") (.var "Dd") (.var "Ff") (.var "Gg"))
      (natTransTy (.var "Cc") (.var "Ee")
        (apps compFunctorD.ref [.var "Cc", .var "Dd", .var "Ee",
          .var "Ff", .var "Hh"])
        (apps compFunctorD.ref [.var "Cc", .var "Dd", .var "Ee",
          .var "Gg", .var "Hh"]))))))))
  tm :=
    let F0 (v : Raw) : Raw := .app (funF0 (.var "Ff")) v
    let G0 (v : Raw) : Raw := .app (funF0 (.var "Gg")) v
    let H1 (a b v : Raw) : Raw := apps (funF1 (.var "Hh")) [a, b, v]
    let F1 (a b v : Raw) : Raw := apps (funF1 (.var "Ff")) [a, b, v]
    let G1 (a b v : Raw) : Raw := apps (funF1 (.var "Gg")) [a, b, v]
    let H0 (v : Raw) : Raw := .app (funF0 (.var "Hh")) v
    let homD (a b : Raw) : Raw := apps (catHom (.var "Dd")) [a, b]
    let homE (a b : Raw) : Raw := apps (catHom (.var "Ee")) [a, b]
    let cmpD (a b c fg gh : Raw) : Raw :=
      apps (catCmp (.var "Dd")) [a, b, c, fg, gh]
    let cmpE (a b c fg gh : Raw) : Raw :=
      apps (catCmp (.var "Ee")) [a, b, c, fg, gh]
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let alx : Raw := .app (.fst (.var "al")) x
    let aly : Raw := .app (.fst (.var "al")) y
    let Ff1 : Raw := F1 x y (.var "f")
    let G1f : Raw := G1 x y (.var "f")
    let PT := homE (H0 (F0 x)) (H0 (G0 y))
    let X1 := cmpE (H0 (F0 x)) (H0 (F0 y)) (H0 (G0 y))
      (H1 (F0 x) (F0 y) Ff1) (H1 (F0 y) (G0 y) aly)
    let X2 := H1 (F0 x) (G0 y) (cmpD (F0 x) (F0 y) (G0 y) Ff1 aly)
    let X3 := H1 (F0 x) (G0 y) (cmpD (F0 x) (G0 x) (G0 y) alx G1f)
    let X4 := cmpE (H0 (F0 x)) (H0 (G0 x)) (H0 (G0 y))
      (H1 (F0 x) (G0 x) alx) (H1 (G0 x) (G0 y) G1f)
    lams ["Cc", "Dd", "Ee", "Ff", "Gg", "Hh", "al"]
      (.pair
        (.lam "x" (H1 (F0 x) (G0 x) (.app (.fst (.var "al")) x)))
        (lams ["x", "y", "f"]
          (apps transD.ref [PT, X1, X2, X4,
            apps symmD.ref [PT, X2, X1,
              apps (funFcomp (.var "Hh"))
                [F0 x, F0 y, G0 y, Ff1, aly]],
            apps transD.ref [PT, X2, X3, X4,
              apps congD.ref [homD (F0 x) (G0 y), PT,
                .lam "h2" (H1 (F0 x) (G0 y) (.var "h2")),
                cmpD (F0 x) (F0 y) (G0 y) Ff1 aly,
                cmpD (F0 x) (G0 x) (G0 y) alx G1f,
                apps (.snd (.var "al")) [x, y, .var "f"]],
              apps (funFcomp (.var "Hh"))
                [F0 x, G0 x, G0 y, alx, G1f]]])))

#guard whiskerLD.ok
#guard whiskerRD.ok

end Cubical.Library

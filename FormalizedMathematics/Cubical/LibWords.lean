import FormalizedMathematics.Cubical.LibQuot

/-! # Words over the two-generator alphabet

Groundwork for `π₁(S¹ ∨ S¹) = F₂`: letters are `Bool × Bool`
(generator, sign), words are lists of letters, and `isSet Word` comes from
**Hedberg's theorem** via decidable equality of lists — no list codes
needed. -/

namespace Cubical.Library

open Raw

/-- Letters: `(generator, sign)`. -/
def letterTy : Raw := .sigma "u" boolTy boolTy
def wordTy : Raw := .list letterTy

/-- Decidable equality of products. -/
def decEqProdD : LibDef where
  name := "decEqProd"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "dA" (.pi "hx" (.var "A") (.pi "hy" (.var "A")
      (decR (.path (.var "A") (.var "hx") (.var "hy")))))
    (.pi "dB" (.pi "hx" (.var "B") (.pi "hy" (.var "B")
      (decR (.path (.var "B") (.var "hx") (.var "hy")))))
    (.pi "x" (.sigma "u" (.var "A") (.var "B"))
    (.pi "y" (.sigma "u" (.var "A") (.var "B"))
      (decR (.path (.sigma "u" (.var "A") (.var "B"))
        (.var "x") (.var "y"))))))))
  tm :=
    let PT : Raw := .sigma "u" (.var "A") (.var "B")
    lams ["A", "B", "dA", "dB", "x", "y"] (.sumcase "k"
      (decR (.path PT (.var "x") (.var "y")))
      (.lam "p1" (.sumcase "k2"
        (decR (.path PT (.var "x") (.var "y")))
        (.lam "p2" (.inl (.plam "i" (.pair
          (.papp (.var "p1") (.fst (.var "x")) (.fst (.var "y")) (.var "i"))
          (.papp (.var "p2") (.snd (.var "x")) (.snd (.var "y")) (.var "i"))))))
        (.lam "n2" (.inr (.lam "p" (.app (.var "n2")
          (apps congD.ref [PT, .var "B", .lam "w" (.snd (.var "w")),
            .var "x", .var "y", .var "p"])))))
        (apps (.var "dB") [.snd (.var "x"), .snd (.var "y")])))
      (.lam "n1" (.inr (.lam "p" (.app (.var "n1")
        (apps congD.ref [PT, .var "A", .lam "w" (.fst (.var "w")),
          .var "x", .var "y", .var "p"])))))
      (apps (.var "dA") [.fst (.var "x"), .fst (.var "y")]))

def decEqLetterD : LibDef where
  name := "decEqLetter"
  ty := .pi "hx" letterTy (.pi "hy" letterTy
    (decR (.path letterTy (.var "hx") (.var "hy"))))
  tm := apps decEqProdD.ref [boolTy, boolTy, decEqBoolD.ref, decEqBoolD.ref]

#guard decEqProdD.ok
#guard decEqLetterD.ok

/-- `nil`/`cons` discrimination code. -/
def lcodeNilD : LibDef where
  name := "lcodeNil"
  ty := .pi "A" .univ (.arr (.list (.var "A")) .univ)
  tm := lams ["A", "w"] (.listrec "k" .univ .unit
    (lams ["h", "t", "ih"] .empty) (.var "w"))

def headDD : LibDef where
  name := "headD"
  ty := .pi "A" .univ (.arr (.var "A")
    (.arr (.list (.var "A")) (.var "A")))
  tm := lams ["A", "d", "w"] (.listrec "k" (.var "A") (.var "d")
    (lams ["h", "t", "ih"] (.var "h")) (.var "w"))

def tailDD : LibDef where
  name := "tailD"
  ty := .pi "A" .univ (.arr (.list (.var "A")) (.list (.var "A")))
  tm := lams ["A", "w"] (.listrec "k" (.list (.var "A")) .lnil
    (lams ["h", "t", "ih"] (.var "t")) (.var "w"))

#guard lcodeNilD.ok
#guard headDD.ok
#guard tailDD.ok

/-- Decidable equality of lists. -/
def decEqListD : LibDef where
  name := "decEqList"
  ty := .pi "A" .univ
    (.pi "dA" (.pi "hx" (.var "A") (.pi "hy" (.var "A")
      (decR (.path (.var "A") (.var "hx") (.var "hy")))))
    (.pi "xs" (.list (.var "A")) (.pi "ys" (.list (.var "A"))
      (decR (.path (.list (.var "A")) (.var "xs") (.var "ys"))))))
  tm :=
    let LA : Raw := .list (.var "A")
    -- refute a path between a cons and nil via the discrimination code
    let refuteConsNil (chd ctl : Raw) : Raw := .lam "p"
      (apps substD.ref [LA,
        .lam "k" (apps lcodeNilD.ref [.var "A", .var "k"]),
        .lnil, .lcons chd ctl,
        apps symmD.ref [LA, .lcons chd ctl, .lnil, .var "p"],
        .tt])
    lams ["A", "dA", "xs"] (.listrec "k"
      (.pi "ys" LA (decR (.path LA (.var "k") (.var "ys"))))
      -- xs = nil
      (.lam "ys" (.listrec "k2"
        (decR (.path LA .lnil (.var "k2")))
        (.inl (.plam "i" .lnil))
        (lams ["h", "t", "ih2"] (.inr (.lam "p"
          (apps substD.ref [LA,
            .lam "k3" (apps lcodeNilD.ref [.var "A", .var "k3"]),
            .lnil, .lcons (.var "h") (.var "t"), .var "p", .tt]))))
        (.var "ys")))
      -- xs = cons h t, ih : Π ys. Dec (t ≡ ys)
      (lams ["h", "t", "ih"] (.lam "ys" (.listrec "k2"
        (decR (.path LA (.lcons (.var "h") (.var "t")) (.var "k2")))
        (.inr (refuteConsNil (.var "h") (.var "t")))
        (lams ["h2", "t2", "ih2"] (.sumcase "k3"
          (decR (.path LA (.lcons (.var "h") (.var "t"))
            (.lcons (.var "h2") (.var "t2"))))
          (.lam "ph" (.sumcase "k4"
            (decR (.path LA (.lcons (.var "h") (.var "t"))
              (.lcons (.var "h2") (.var "t2"))))
            (.lam "pt" (.inl (.plam "i" (.lcons
              (.papp (.var "ph") (.var "h") (.var "h2") (.var "i"))
              (.papp (.var "pt") (.var "t") (.var "t2") (.var "i"))))))
            (.lam "nt" (.inr (.lam "p" (.app (.var "nt")
              (apps congD.ref [LA, LA,
                .lam "w" (apps tailDD.ref [.var "A", .var "w"]),
                .lcons (.var "h") (.var "t"),
                .lcons (.var "h2") (.var "t2"), .var "p"])))))
            (apps (.var "ih") [.var "t2"])))
          (.lam "nh" (.inr (.lam "p" (.app (.var "nh")
            (apps congD.ref [LA, .var "A",
              .lam "w" (apps headDD.ref [.var "A", .var "h", .var "w"]),
              .lcons (.var "h") (.var "t"),
              .lcons (.var "h2") (.var "t2"), .var "p"])))))
          (apps (.var "dA") [.var "h", .var "h2"])))
        (.var "ys"))))
      (.var "xs"))

#guard decEqListD.ok

/-- Decidable equality of words. -/
def decEqWordD : LibDef where
  name := "decEqWord"
  ty := .pi "hx" wordTy (.pi "hy" wordTy
    (decR (.path wordTy (.var "hx") (.var "hy"))))
  tm := apps decEqListD.ref [letterTy, decEqLetterD.ref]

/-- **`isSet Word`** — Hedberg pays off: no list codes needed. -/
def isSetWordD : LibDef where
  name := "isSetWord"
  ty := isSetR wordTy
  tm := apps hedbergD.ref [wordTy, decEqWordD.ref]

#guard decEqWordD.ok
#guard isSetWordD.ok

-- the four letters, and a compute check that word equality decides
def letL : Raw := .pair trueR trueR
def letLinv : Raw := .pair trueR falseR
def letR : Raw := .pair falseR trueR
def letRinv : Raw := .pair falseR falseR

#guard
  match normalize (apps decEqWordD.ref
    [.lcons letL (.lcons letR .lnil), .lcons letL (.lcons letR .lnil)])
    (decR (.path wordTy (.lcons letL (.lcons letR .lnil))
      (.lcons letL (.lcons letR .lnil)))) with
  | .ok (.inl _) => true
  | _ => false
#guard
  match normalize (apps decEqWordD.ref
    [.lcons letL (.lcons letR .lnil), .lcons letR (.lcons letL .lnil)])
    (decR (.path wordTy (.lcons letL (.lcons letR .lnil))
      (.lcons letR (.lcons letL .lnil)))) with
  | .ok (.inr _) => true
  | _ => false

/-! ## Boolean lemma kit -/

def andBoolD : LibDef where
  name := "andBool"
  ty := .arr boolTy (.arr boolTy boolTy)
  tm := lams ["a", "b"] (.sumcase "k" boolTy
    (.lam "u" (.var "b")) (.lam "u" falseR) (.var "a"))

def eqBoolD : LibDef where
  name := "eqBool"
  ty := .arr boolTy (.arr boolTy boolTy)
  tm := lams ["a", "b"] (.sumcase "k" boolTy
    (.lam "u" (.var "b"))
    (.lam "u" (.app notBoolD.ref (.var "b")))
    (.var "a"))

/-- `IsTrue : Bool → U` (a propositional predicate). -/
def isTrueD : LibDef where
  name := "isTrue"
  ty := .arr boolTy .univ
  tm := .lam "b" (.sumcase "k" .univ
    (.lam "u" .unit) (.lam "u" .empty) (.var "b"))

private def istr (b : Raw) : Raw := .app isTrueD.ref b
private def andB (a b : Raw) : Raw := apps andBoolD.ref [a, b]
private def eqB (a b : Raw) : Raw := apps eqBoolD.ref [a, b]
private def notB (a : Raw) : Raw := .app notBoolD.ref a

def isPropIsTrueD : LibDef where
  name := "isPropIsTrue"
  ty := .pi "b" boolTy (isPropR (istr (.var "b")))
  tm := .lam "b" (.sumcase "k" (isPropR (istr (.var "k")))
    (.lam "u" isPropUnitD.ref) (.lam "u" isPropEmptyD.ref) (.var "b"))

def andElimLD : LibDef where
  name := "andElimL"
  ty := .pi "a" boolTy (.pi "b" boolTy
    (.arr (istr (andB (.var "a") (.var "b"))) (istr (.var "a"))))
  tm := lams ["a", "b"] (.sumcase "k"
    (.arr (istr (andB (.var "k") (.var "b"))) (istr (.var "k")))
    (.lam "u" (.lam "w" .tt))
    (.lam "u" (.lam "w" (.var "w")))
    (.var "a"))

def andElimRD : LibDef where
  name := "andElimR"
  ty := .pi "a" boolTy (.pi "b" boolTy
    (.arr (istr (andB (.var "a") (.var "b"))) (istr (.var "b"))))
  tm := lams ["a", "b"] (.sumcase "k"
    (.arr (istr (andB (.var "k") (.var "b"))) (istr (.var "b")))
    (.lam "u" (.lam "w" (.var "w")))
    (.lam "u" (.lam "w" (.emptyrec (istr (.var "b")) (.var "w"))))
    (.var "a"))

/-- Introduce a conjunction. -/
def andIntroD : LibDef where
  name := "andIntro"
  ty := .pi "a" boolTy (.pi "b" boolTy
    (.arr (istr (.var "a")) (.arr (istr (.var "b"))
      (istr (andB (.var "a") (.var "b"))))))
  tm := lams ["a", "b"] (.sumcase "k"
    (.arr (istr (.var "k")) (.arr (istr (.var "b"))
      (istr (andB (.var "k") (.var "b")))))
    (.lam "u" (lams ["w1", "w2"] (.var "w2")))
    (.lam "u" (lams ["w1", "w2"]
      (.emptyrec (istr (andB falseR (.var "b"))) (.var "w1"))))
    (.var "a"))

/-- `IsTrue (not b) → b ≡ false`. -/
def notTrueFalseD : LibDef where
  name := "notTrueFalse"
  ty := .pi "b" boolTy (.arr (istr (notB (.var "b")))
    (.path boolTy (.var "b") falseR))
  tm := .lam "b" (.sumcase "k"
    (.arr (istr (notB (.var "k"))) (.path boolTy (.var "k") falseR))
    (.lam "u" (.lam "w" (.emptyrec
      (.path boolTy (.inl (.var "u")) falseR) (.var "w"))))
    (.lam "u" (.lam "w" (apps congD.ref [.unit, boolTy,
      .lam "w2" (.inr (.var "w2")), .var "u", .tt,
      apps isPropUnitD.ref [.var "u", .tt]])))
    (.var "b"))

/-- `eqBool b b ≡ true`. -/
def eqBoolReflD : LibDef where
  name := "eqBoolRefl"
  ty := .pi "b" boolTy (.path boolTy (eqB (.var "b") (.var "b")) trueR)
  tm := .lam "b" (.sumcase "k"
    (.path boolTy (eqB (.var "k") (.var "k")) trueR)
    (.lam "u" (apps congD.ref [.unit, boolTy,
      .lam "w" (.inl (.var "w")), .var "u", .tt,
      apps isPropUnitD.ref [.var "u", .tt]]))
    (.lam "u" (.plam "i" trueR))
    (.var "b"))

/-- `IsTrue (eqBool x y) → x ≡ y`. -/
def eqBoolSoundD : LibDef where
  name := "eqBoolSound"
  ty := .pi "x" boolTy (.pi "y" boolTy
    (.arr (istr (eqB (.var "x") (.var "y")))
      (.path boolTy (.var "x") (.var "y"))))
  tm :=
    let congIn (ctor : Raw → Raw) (a b : Raw) : Raw :=
      apps congD.ref [.unit, boolTy,
        .lam "w3" (ctor (.var "w3")), a, b,
        apps isPropUnitD.ref [a, b]]
    lams ["x", "y"] (.sumcase "k"
      (.arr (istr (eqB (.var "k") (.var "y")))
        (.path boolTy (.var "k") (.var "y")))
      (.lam "u" (.lam "w" (.app (.sumcase "k2"
        (.arr (istr (.var "k2"))
          (.path boolTy (.inl (.var "u")) (.var "k2")))
        (.lam "v" (.lam "w2" (congIn .inl (.var "u") (.var "v"))))
        (.lam "v" (.lam "w2" (.emptyrec
          (.path boolTy (.inl (.var "u")) (.inr (.var "v"))) (.var "w2"))))
        (.var "y")) (.var "w"))))
      (.lam "u" (.lam "w" (.app (.sumcase "k2"
        (.arr (istr (notB (.var "k2")))
          (.path boolTy (.inr (.var "u")) (.var "k2")))
        (.lam "v" (.lam "w2" (.emptyrec
          (.path boolTy (.inr (.var "u")) (.inl (.var "v"))) (.var "w2"))))
        (.lam "v" (.lam "w2" (congIn .inr (.var "u") (.var "v"))))
        (.var "y")) (.var "w"))))
      (.var "x"))

/-- `IsTrue (not (eqBool x y)) → x ≡ not y`. -/
def eqBoolFalseD : LibDef where
  name := "eqBoolFalse"
  ty := .pi "x" boolTy (.pi "y" boolTy
    (.arr (istr (notB (eqB (.var "x") (.var "y"))))
      (.path boolTy (.var "x") (notB (.var "y")))))
  tm :=
    let congIn (ctor : Raw → Raw) (a b : Raw) : Raw :=
      apps congD.ref [.unit, boolTy,
        .lam "w3" (ctor (.var "w3")), a, b,
        apps isPropUnitD.ref [a, b]]
    lams ["x", "y"] (.sumcase "k"
      (.arr (istr (notB (eqB (.var "k") (.var "y"))))
        (.path boolTy (.var "k") (notB (.var "y"))))
      (.lam "u" (.lam "w" (.app (.sumcase "k2"
        (.arr (istr (notB (.var "k2")))
          (.path boolTy (.inl (.var "u")) (notB (.var "k2"))))
        (.lam "v" (.lam "w2" (.emptyrec
          (.path boolTy (.inl (.var "u")) (notB (.inl (.var "v"))))
          (.var "w2"))))
        (.lam "v" (.lam "w2" (congIn .inl (.var "u") .tt)))
        (.var "y")) (.var "w"))))
      (.lam "u" (.lam "w" (.app (.sumcase "k2"
        (.arr (istr (notB (notB (.var "k2"))))
          (.path boolTy (.inr (.var "u")) (notB (.var "k2"))))
        (.lam "v" (.lam "w2" (congIn .inr (.var "u") .tt)))
        (.lam "v" (.lam "w2" (.emptyrec
          (.path boolTy (.inr (.var "u")) (notB (.inr (.var "v"))))
          (.var "w2"))))
        (.var "y")) (.var "w"))))
      (.var "x"))

#guard andBoolD.ok
#guard eqBoolD.ok
#guard isTrueD.ok
#guard isPropIsTrueD.ok
#guard andElimLD.ok
#guard andElimRD.ok
#guard andIntroD.ok
#guard notTrueFalseD.ok
#guard eqBoolReflD.ok
#guard eqBoolSoundD.ok
#guard eqBoolFalseD.ok

/-! ## Σ with propositional fibers: paths and set-ness -/

/-- A Σ-path from a base path, when the fibers are propositions. -/
def sigmaPropEqD : LibDef where
  name := "sigmaPropEq"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.pi "hB" (.pi "a" (.var "A") (isPropR (.app (.var "B") (.var "a"))))
    (.pi "u" (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
    (.pi "v" (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
    (.arr (.path (.var "A") (.fst (.var "u")) (.fst (.var "v")))
      (.path (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
        (.var "u") (.var "v")))))))
  tm :=
    let pAt (e : Raw) : Raw := .papp (.var "p")
      (.fst (.var "u")) (.fst (.var "v")) e
    let line : Raw := .plam "i" (.app (.var "B") (pAt (.var "i")))
    let sndP : Raw := apps toPathPD.ref
      [.app (.var "B") (.fst (.var "u")),
       .app (.var "B") (.fst (.var "v")),
       line, .snd (.var "u"), .snd (.var "v"),
       apps (.app (.var "hB") (.fst (.var "v")))
         [apps transportD.ref [.app (.var "B") (.fst (.var "u")),
            .app (.var "B") (.fst (.var "v")), line, .snd (.var "u")],
          .snd (.var "v")]]
    lams ["A", "B", "hB", "u", "v", "p"]
      (.plam "i" (.pair (pAt (.var "i"))
        (.papp sndP (.snd (.var "u")) (.snd (.var "v")) (.var "i"))))

#guard sigmaPropEqD.ok

/-- Σ-types over a set with propositional fibers are sets. -/
def isSetSigmaPropD : LibDef where
  name := "isSetSigmaProp"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.pi "hA" (isSetR (.var "A"))
    (.pi "hB" (.pi "a" (.var "A") (isPropR (.app (.var "B") (.var "a"))))
      (isSetR (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))))))
  tm :=
    let ST : Raw := .sigma "a" (.var "A") (.app (.var "B") (.var "a"))
    let x1 : Raw := .fst (.var "xs")
    let y1 : Raw := .fst (.var "ys")
    let cf (pp : Raw) : Raw := apps congD.ref [ST, .var "A",
      .lam "w" (.fst (.var "w")), .var "xs", .var "ys", pp]
    let cfp : Raw := cf (.var "xp")
    let cfq : Raw := cf (.var "yp")
    -- the base square from isSet A
    let baseSq : Raw := apps (.var "hA") [x1, y1, cfp, cfq]
    -- second components of the given paths, as dependent paths
    let sndp : Raw := .ann
      (.plam "j" (.snd (.papp (.var "xp") (.var "xs") (.var "ys") (.var "j"))))
      (.pathP "j" (.app (.var "B") (.papp cfp x1 y1 (.var "j")))
        (.snd (.var "xs")) (.snd (.var "ys")))
    let sndq : Raw := .ann
      (.plam "j" (.snd (.papp (.var "yp") (.var "xs") (.var "ys") (.var "j"))))
      (.pathP "j" (.app (.var "B") (.papp cfq x1 y1 (.var "j")))
        (.snd (.var "xs")) (.snd (.var "ys")))
    let Lof (pp : Raw) : Raw := .pathP "j"
      (.app (.var "B") (.papp pp x1 y1 (.var "j")))
      (.snd (.var "xs")) (.snd (.var "ys"))
    let line : Raw := .plam "i"
      (Lof (.papp baseSq cfp cfq (.var "i")))
    let prf : Raw := apps isPropPathPSetD.ref
      [.var "A", .var "B",
       .lam "a0" (apps isPropToIsSetD.ref
         [.app (.var "B") (.var "a0"), .app (.var "hB") (.var "a0")]),
       x1, .snd (.var "xs"), y1, cfq, .snd (.var "ys"),
       apps transport1D.ref [Lof cfp, Lof cfq, line, sndp]
         |> fun t => t,
       sndq]
    let SND : Raw := apps toPathP1D.ref
      [Lof cfp, Lof cfq, line, sndp, sndq, prf]
    lams ["A", "B", "hA", "hB", "xs", "ys", "xp", "yp"]
      (.plam "i" (.plam "j" (.pair
        (.papp (.papp baseSq cfp cfq (.var "i")) x1 y1 (.var "j"))
        (.papp (.papp SND sndp sndq (.var "i"))
          (.snd (.var "xs")) (.snd (.var "ys")) (.var "j")))))

#guard isSetSigmaPropD.ok

/-! ## Letters: inversion and cancellation -/

def invLetD : LibDef where
  name := "invLet"
  ty := .arr letterTy letterTy
  tm := .lam "l" (.pair (.fst (.var "l")) (notB (.snd (.var "l"))))

/-- `cancels a b`: `b` is the inverse letter of `a`. -/
def cancelsD : LibDef where
  name := "cancels"
  ty := .arr letterTy (.arr letterTy boolTy)
  tm := lams ["a", "b"] (andB
    (eqB (.fst (.var "a")) (.fst (.var "b")))
    (notB (eqB (.snd (.var "a")) (.snd (.var "b")))))

private def cancelsR (a b : Raw) : Raw := apps cancelsD.ref [a, b]
private def invL (a : Raw) : Raw := .app invLetD.ref a

/-- `eqBool (not b) b ≡ false`. -/
def eqBoolNotLD : LibDef where
  name := "eqBoolNotL"
  ty := .pi "b" boolTy (.path boolTy (eqB (notB (.var "b")) (.var "b")) falseR)
  tm := .lam "b" (.sumcase "k"
    (.path boolTy (eqB (notB (.var "k")) (.var "k")) falseR)
    (.lam "u" (.plam "i" falseR))
    (.lam "u" (apps congD.ref [.unit, boolTy,
      .lam "w" (.inr (.var "w")), .var "u", .tt,
      apps isPropUnitD.ref [.var "u", .tt]]))
    (.var "b"))

/-- `cancels (invLet g) g ≡ true`. -/
def cancelsInvD : LibDef where
  name := "cancelsInv"
  ty := .pi "g" letterTy (.path boolTy (cancelsR (invL (.var "g")) (.var "g")) trueR)
  tm :=
    let g1 : Raw := .fst (.var "g")
    let g2 : Raw := .snd (.var "g")
    let Y : Raw := notB (eqB (notB g2) g2)
    .lam "g" (apps transD.ref [boolTy,
      andB (eqB g1 g1) Y, Y, trueR,
      apps congD.ref [boolTy, boolTy, .lam "b" (andB (.var "b") Y),
        eqB g1 g1, trueR, .app eqBoolReflD.ref g1],
      apps congD.ref [boolTy, boolTy, .lam "b" (notB (.var "b")),
        eqB (notB g2) g2, falseR, .app eqBoolNotLD.ref g2]])

/-- `IsTrue (cancels g h) → h ≡ invLet g`. -/
def cancelsCharacD : LibDef where
  name := "cancelsCharac"
  ty := .pi "g" letterTy (.pi "h" letterTy
    (.arr (istr (cancelsR (.var "g") (.var "h")))
      (.path letterTy (.var "h") (invL (.var "g")))))
  tm :=
    let g1 : Raw := .fst (.var "g")
    let g2 : Raw := .snd (.var "g")
    let h1 : Raw := .fst (.var "h")
    let h2 : Raw := .snd (.var "h")
    -- e1 : g1 ≡ h1, e2 : g2 ≡ not h2 → components of h ≡ (g1, not g2)
    let e1 : Raw := apps eqBoolSoundD.ref [g1, h1,
      apps andElimLD.ref [eqB g1 h1, notB (eqB g2 h2), .var "w"]]
    let e2 : Raw := apps eqBoolFalseD.ref [g2, h2,
      apps andElimRD.ref [eqB g1 h1, notB (eqB g2 h2), .var "w"]]
    -- h1 ≡ g1
    let p1 : Raw := apps symmD.ref [boolTy, g1, h1, e1]
    -- h2 ≡ not g2 :  h2 ≡ not (not h2) ≡ not g2
    let p2 : Raw := apps transD.ref [boolTy, h2, notB (notB h2), notB g2,
      apps symmD.ref [boolTy, notB (notB h2), h2, .app notNotD.ref h2],
      apps congD.ref [boolTy, boolTy, .lam "b" (notB (.var "b")),
        notB h2, g2,
        apps symmD.ref [boolTy, g2, notB h2, e2]]]
    lams ["g", "h", "w"] (.plam "i" (.pair
      (.papp p1 h1 g1 (.var "i"))
      (.papp p2 h2 (notB g2) (.var "i"))))

#guard invLetD.ok
#guard cancelsD.ok
#guard eqBoolNotLD.ok
#guard cancelsInvD.ok
#guard cancelsCharacD.ok

/-! ## The reduced-word predicate and the F₂ carrier -/

def optLetTy : Raw := .sum .unit letterTy

/-- `redAux w prev`: `w` is reduced, given the preceding letter. -/
def redAuxD : LibDef where
  name := "redAux"
  ty := .arr wordTy (.arr optLetTy boolTy)
  tm := .lam "w" (.listrec "k" (.arr optLetTy boolTy)
    (.lam "prev" trueR)
    (lams ["h", "t", "ih"] (.lam "prev" (andB
      (.sumcase "k2" boolTy (.lam "u" trueR)
        (.lam "p" (notB (cancelsR (.var "p") (.var "h")))) (.var "prev"))
      (.app (.var "ih") (.inr (.var "h"))))))
    (.var "w"))

private def redAux (w prev : Raw) : Raw := apps redAuxD.ref [w, prev]
private def redW (w : Raw) : Raw := redAux w (.inl .tt)

/-- Reducedness is independent of a *stricter* head constraint. -/
def redRelaxD : LibDef where
  name := "redRelax"
  ty := .pi "t" wordTy (.pi "prev" optLetTy
    (.arr (istr (redAux (.var "t") (.var "prev")))
      (istr (redW (.var "t")))))
  tm := .lam "t" (.listrec "k"
    (.pi "prev" optLetTy
      (.arr (istr (redAux (.var "k") (.var "prev")))
        (istr (redW (.var "k")))))
    (lams ["prev", "w2"] (.var "w2"))
    (lams ["h", "t2", "ih"] (lams ["prev", "w2"]
      (apps andElimRD.ref
        [.sumcase "k2" boolTy (.lam "u" trueR)
          (.lam "p" (notB (cancelsR (.var "p") (.var "h")))) (.var "prev"),
         redAux (.var "t2") (.inr (.var "h")),
         .var "w2"])))
    (.var "t"))

/-- **The F₂ carrier**: reduced words. -/
def f2Ty : Raw := .sigma "w" wordTy (istr (redW (.var "w")))

def isSetF2D : LibDef where
  name := "isSetF2"
  ty := isSetR f2Ty
  tm := apps isSetSigmaPropD.ref
    [wordTy, .lam "w" (istr (redW (.var "w"))),
     isSetWordD.ref,
     .lam "w" (.app isPropIsTrueD.ref (redW (.var "w")))]

#guard redAuxD.ok
#guard redRelaxD.ok
#guard isSetF2D.ok

/-! ## Cancelling prepend

`consStep g h t rt b e` is the branch on `b` (with `e : cancels g h ≡ b`
— the *inspect idiom*): if the head cancels, drop it; otherwise prepend.
Exposing the scrutinee as an argument lets proofs move along paths of
booleans by a **connection** (`e @ (i ∧ j)`), with no `J` needed. -/

def consStepD : LibDef where
  name := "consStep"
  ty := .pi "g" letterTy (.pi "h" letterTy (.pi "t" wordTy
    (.pi "rt" (istr (redAux (.var "t") (.inr (.var "h"))))
    (.pi "b" boolTy
      (.arr (.path boolTy (cancelsR (.var "g") (.var "h")) (.var "b"))
        f2Ty)))))
  tm := lams ["g", "h", "t", "rt", "b"] (.sumcase "k"
    (.arr (.path boolTy (cancelsR (.var "g") (.var "h")) (.var "k")) f2Ty)
    (.lam "u" (.lam "e" (.pair (.var "t")
      (apps redRelaxD.ref [.var "t", .inr (.var "h"), .var "rt"]))))
    (.lam "u" (.lam "e" (.pair
      (.lcons (.var "g") (.lcons (.var "h") (.var "t")))
      (apps substD.ref [boolTy,
        .lam "b2" (istr (andB (notB (.var "b2"))
          (redAux (.var "t") (.inr (.var "h"))))),
        .inr (.var "u"), cancelsR (.var "g") (.var "h"),
        apps symmD.ref [boolTy, cancelsR (.var "g") (.var "h"),
          .inr (.var "u"), .var "e"],
        .var "rt"]))))
    (.var "b"))

#guard consStepD.ok

/-- Prepend a letter with cancellation. -/
def consGD : LibDef where
  name := "consG"
  ty := .arr letterTy (.arr f2Ty f2Ty)
  tm := lams ["g", "x"] (.app
    (.listrec "k" (.arr (istr (redW (.var "k"))) f2Ty)
      (.lam "r" (.pair (.lcons (.var "g") .lnil) .tt))
      (lams ["h", "t", "ih"] (.lam "r"
        (apps consStepD.ref [.var "g", .var "h", .var "t", .var "r",
          cancelsR (.var "g") (.var "h"),
          .plam "i" (cancelsR (.var "g") (.var "h"))])))
      (.fst (.var "x")))
    (.snd (.var "x")))

#guard consGD.ok

-- computation checks: cons and cancel
private def emptyF2 : Raw := .pair .lnil .tt
#guard
  match normalize (apps consGD.ref [letL,
    apps consGD.ref [letR, emptyF2]]) f2Ty with
  | .ok t => t == (.pair (.lcons (resolveClosed letL)
      (.lcons (resolveClosed letR) .lnil)) .tt)
  | _ => false
#guard
  match normalize (apps consGD.ref [letLinv,
    apps consGD.ref [letL, emptyF2]]) f2Ty with
  | .ok t => t == (.pair .lnil .tt)
  | _ => false

/-! ## The round trip: `consG (inv g) ∘ consG g ≡ id`

Case analysis via the inspect idiom; every rewrite of a `consStep`
scrutinee travels along a **connection** `prf @ (i ∧ j)`.  The head-cancel
branch needs an inner case split on the tail (the outer inverse letter
either meets `nil` or must *not* cancel the next letter, by reducedness);
the prepend branch cancels immediately by `cancelsInv`. -/

def consGRoundD : LibDef where
  name := "consGRound"
  ty := .pi "g" letterTy (.pi "x" f2Ty
    (.path f2Ty
      (.app (.app consGD.ref (invL (.var "g")))
        (apps consGD.ref [.var "g", .var "x"]))
      (.var "x")))
  tm :=
    let g : Raw := .var "g"
    let invg : Raw := invL g
    let fibB : Raw := .lam "w9" (istr (redW (.var "w9")))
    let fibP : Raw := .lam "w9" (.app isPropIsTrueD.ref (redW (.var "w9")))
    let spEq (u v fp : Raw) : Raw :=
      apps sigmaPropEqD.ref [wordTy, fibB, fibP, u, v, fp]
    let tr (a b c pp q : Raw) : Raw := apps transD.ref [f2Ty, a, b, c, pp, q]
    let reflC (gg hh : Raw) : Raw := .plam "i9" (cancelsR gg hh)
    let stepT (gg hh tt rt bb ee : Raw) : Raw :=
      apps consStepD.ref [gg, hh, tt, rt, bb, ee]
    -- connection move: rewrite the scrutinee of a consStep along prf
    let mv (gg hh tt rt prf cLit : Raw) : Raw :=
      .plam "i" (stepT gg hh tt rt
        (.papp prf (cancelsR gg hh) cLit (.var "i"))
        (.plam "j" (.papp prf (cancelsR gg hh) cLit
          (.imin (.var "i") (.var "j")))))
    let cInv (aT bT pT : Raw) : Raw := apps congD.ref [f2Ty, f2Ty,
      .app consGD.ref invg, aT, bT, pT]
    -- the target x = ⟨cons h w', r⟩ and pieces
    lams ["g", "x"] (.app
      (.listrec "w0"
        (.pi "r" (istr (redW (.var "w0")))
          (.path f2Ty
            (.app (.app consGD.ref invg)
              (apps consGD.ref [g, .pair (.var "w0") (.var "r")]))
            (.pair (.var "w0") (.var "r"))))
        -- w = nil : cons then cancel, definitional except the final prop
        (.lam "r" (
          let inner : Raw := .pair (.lcons g .lnil) .tt
          let m1 : Raw := stepT invg g .lnil .tt trueR
            (.app cancelsInvD.ref g)
          tr (.app (.app consGD.ref invg)
              (apps consGD.ref [g, .pair .lnil (.var "r")]))
            m1 (.pair .lnil (.var "r"))
            (mv invg g .lnil .tt (.app cancelsInvD.ref g) trueR)
            (spEq m1 (.pair .lnil (.var "r")) (.plam "i9" .lnil))))
        -- w = cons h t
        (lams ["h", "t", "ih"] (.lam "r" (
          let h : Raw := .var "h"
          let t : Raw := .var "t"
          let r : Raw := .var "r"
          let x0 : Raw := .pair (.lcons h t) r
          let lhs : Raw := .app (.app consGD.ref invg)
            (apps consGD.ref [g, x0])
          let goalT : Raw := .path f2Ty lhs x0
          .app (.sumcase "k"
            (.arr (.path boolTy (cancelsR g h) (.var "k")) goalT)
            -- cancels g h ≡ true: the inner tail-case
            (.lam "u" (.lam "e" (
              let e : Raw := .var "e"
              let charac : Raw := apps cancelsCharacD.ref [g, h,
                apps substD.ref [boolTy, .lam "b9" (istr (.var "b9")),
                  .inl (.var "u"), cancelsR g h,
                  apps symmD.ref [boolTy, cancelsR g h, .inl (.var "u"), e],
                  .tt]]
              let moved (tt2 rr : Raw) : Raw :=
                stepT g h tt2 rr (.inl (.var "u")) e
              .app (.listrec "t0"
                (.pi "r2" (istr (redW (.lcons h (.var "t0"))))
                  (.path f2Ty
                    (.app (.app consGD.ref invg)
                      (apps consGD.ref [g, .pair (.lcons h (.var "t0"))
                        (.var "r2")]))
                    (.pair (.lcons h (.var "t0")) (.var "r2"))))
                -- t = nil: inverse meets nil, heads relate by charac
                (.lam "r2" (
                  let mid : Raw := .app (.app consGD.ref invg)
                    (moved .lnil (.var "r2"))
                  tr (.app (.app consGD.ref invg)
                      (apps consGD.ref [g, .pair (.lcons h .lnil) (.var "r2")]))
                    mid (.pair (.lcons h .lnil) (.var "r2"))
                    (cInv (stepT g h .lnil (.var "r2")
                        (cancelsR g h) (reflC g h))
                      (moved .lnil (.var "r2"))
                      (mv g h .lnil (.var "r2") (.var "e") (.inl (.var "u"))))
                    (spEq mid (.pair (.lcons h .lnil) (.var "r2"))
                      (apps congD.ref [letterTy, wordTy,
                        .lam "l9" (.lcons (.var "l9") .lnil),
                        invg, h,
                        apps symmD.ref [letterTy, h, invg, charac]]))))
                -- t = cons h2 t2: inverse must NOT cancel h2 (reducedness)
                (lams ["h2", "t2", "ih2"] (.lam "r2" (
                  let h2 : Raw := .var "h2"
                  let t2 : Raw := .var "t2"
                  let r2 : Raw := .var "r2"
                  let tW : Raw := .lcons h2 t2
                  let rr : Raw := apps redRelaxD.ref [tW, .inr h, r2]
                  let prfF : Raw := apps transD.ref [boolTy,
                    cancelsR invg h2, cancelsR h h2, falseR,
                    apps congD.ref [letterTy, boolTy,
                      .lam "l9" (cancelsR (.var "l9") h2),
                      invg, h,
                      apps symmD.ref [letterTy, h, invg, charac]],
                    apps notTrueFalseD.ref [cancelsR h h2,
                      apps andElimLD.ref [notB (cancelsR h h2),
                        redAux t2 (.inr h2), r2]]]
                  let mid1 : Raw := .app (.app consGD.ref invg)
                    (moved tW r2)
                  let mid2 : Raw := stepT invg h2 t2 rr falseR prfF
                  tr (.app (.app consGD.ref invg)
                      (apps consGD.ref [g, .pair (.lcons h tW) r2]))
                    mid1 (.pair (.lcons h tW) r2)
                    (cInv (stepT g h tW r2 (cancelsR g h) (reflC g h))
                      (moved tW r2)
                      (mv g h tW r2 (.var "e") (.inl (.var "u"))))
                    (tr mid1 mid2 (.pair (.lcons h tW) r2)
                      (mv invg h2 t2 rr prfF falseR)
                      (spEq mid2 (.pair (.lcons h tW) r2)
                        (apps congD.ref [letterTy, wordTy,
                          .lam "l9" (.lcons (.var "l9") tW),
                          invg, h,
                          apps symmD.ref [letterTy, h, invg, charac]]))))))
                t) r)))
            -- cancels g h ≡ false: prepend, then cancel by cancelsInv
            (.lam "u" (.lam "e" (
              let e : Raw := .var "e"
              let movedF : Raw := stepT g h t r (.inr (.var "u")) e
              let pf : Raw := .snd movedF
              let mid1 : Raw := .app (.app consGD.ref invg) movedF
              let mid2 : Raw := stepT invg g (.lcons h t) pf trueR
                (.app cancelsInvD.ref g)
              tr lhs mid1 x0
                (cInv (stepT g h t r (cancelsR g h) (reflC g h))
                  movedF
                  (mv g h t r e (.inr (.var "u"))))
                (tr mid1 mid2 x0
                  (mv invg g (.lcons h t) pf (.app cancelsInvD.ref g) trueR)
                  (spEq mid2 x0 (.plam "i9" (.lcons h t)))))))
            (cancelsR g h))
            (.plam "i9" (cancelsR g h)))))
        (.fst (.var "x")))
      (.snd (.var "x")))

#guard consGRoundD.ok

/-! ## The F₂ cover of the figure eight -/

/-- `invLet` is an involution. -/
def invInvLetD : LibDef where
  name := "invInvLet"
  ty := .pi "g" letterTy
    (.path letterTy (invL (invL (.var "g"))) (.var "g"))
  tm := .lam "g" (.plam "i" (.pair (.fst (.var "g"))
    (.papp (.app notNotD.ref (.snd (.var "g")))
      (notB (notB (.snd (.var "g")))) (.snd (.var "g")) (.var "i"))))

#guard invInvLetD.ok

/-- Cancelling prepend is an equivalence. -/
def consGEquivD : LibDef where
  name := "consGEquiv"
  ty := .pi "g" letterTy (equivR f2Ty f2Ty)
  tm :=
    let g : Raw := .var "g"
    let invg : Raw := invL g
    .lam "g" (apps setIsoToEquivD.ref
      [f2Ty, f2Ty,
       .app consGD.ref g,
       .app consGD.ref invg,
       -- section: consG g (consG g⁻¹ x) ≡ x, via the round trip at g⁻¹
       -- corrected by the involution
       .lam "x" (
         let inner : Raw := apps consGD.ref [invg, .var "x"]
         apps transD.ref [f2Ty,
           .app (.app consGD.ref g) inner,
           .app (.app consGD.ref (invL invg)) inner,
           .var "x",
           apps congD.ref [letterTy, f2Ty,
             .lam "l9" (.app (.app consGD.ref (.var "l9")) inner),
             g, invL invg,
             apps symmD.ref [letterTy, invL invg, g,
               .app invInvLetD.ref g]],
           apps consGRoundD.ref [invg, .var "x"]]),
       -- retraction: the round trip itself
       .lam "x" (apps consGRoundD.ref [g, .var "x"]),
       isSetF2D.ref])

#guard consGEquivD.ok

/-- **The F₂ cover**: each circle of the figure eight winds by prepending
its own generator (with cancellation). -/
def helixF2D : LibDef where
  name := "helixF2"
  ty := .arr (wedge .s1 .s1 .sbase .sbase) .univ
  tm := .lam "p" (.pushrec "k" .univ
    (.lam "x" (.s1elim "x2" .univ f2Ty
      (apps uaD.ref [f2Ty, f2Ty, .app consGEquivD.ref letL]) (.var "x")))
    (.lam "x" (.s1elim "x2" .univ f2Ty
      (apps uaD.ref [f2Ty, f2Ty, .app consGEquivD.ref letR]) (.var "x")))
    (.lam "u" (.plam "i" f2Ty))
    (.var "p"))

private def w8T : Raw := wedge .s1 .s1 .sbase .sbase
private def w8baseT : Raw := .pinl .sbase

/-- **The F₂-winding of the figure eight** — the non-abelian invariant. -/
def windF2D : LibDef where
  name := "windF2"
  ty := .arr (.path w8T w8baseT w8baseT) f2Ty
  tm := .lam "p" (.transp "i"
    (.app helixF2D.ref (.papp (.var "p") w8baseT w8baseT (.var "i")))
    (.pair .lnil .tt))

#guard helixF2D.ok
#guard windF2D.ok

private def loopLT : Raw := .plam "i" (.pinl (.sloop (.var "i")))
private def loopLinvT : Raw := .plam "i" (.pinl (.sloop (.ineg (.var "i"))))
private def compW8T (p q : Raw) : Raw :=
  apps transD.ref [w8T, w8baseT, w8baseT, w8baseT, p, q]

-- the left generator winds by [L] (≈3 s) …
#guard
  match normalize (.app windF2D.ref loopLT) f2Ty with
  | .ok t => t == (.pair (.lcons (resolveClosed letL) .lnil) .tt)
  | _ => false

/- Composite loops (e.g. `windF2 (loopL ⬝ loopL) ⟶ [L,L]`,
   `windF2 (loopL ⬝ loopL⁻¹) ⟶ []`, and the non-abelian `LR ≠ RL`) are
   *provable in principle* — the cover equivalence is fully verified — but
   currently exceed a practical normalization budget: each Kan step walks
   the large embedded `isSetF2` proof inside `consGEquiv` (the same
   embedded-proof-size wall as `loopSpaceIsInt`).  The identified fix is
   kernel value-sharing/memoization; see HANDOFF. -/

/-! ## Decoding: reduced words back into loops of the figure eight

`genLoop` sends a letter to its generator loop (the right-circle
generators are conjugated through the wedge path `ppush`), `decodeWord`
folds a word into a composite loop (inner-first, matching the transport
order of `windF2`). -/

private def pushPT : Raw := .plam "i"
  (.ppush (.lam "u0" .sbase) (.lam "u0" .sbase) .tt (.var "i"))
private def pinrBaseT : Raw := .pinr .sbase
private def omega8T : Raw := .path w8T w8baseT w8baseT
private def reflW8 : Raw := apps reflD.ref [w8T, w8baseT]

def genLoopD : LibDef where
  name := "genLoop"
  ty := .arr letterTy omega8T
  tm :=
    let loopL : Raw := .plam "i" (.pinl (.sloop (.var "i")))
    let loopLinv : Raw := .plam "i" (.pinl (.sloop (.ineg (.var "i"))))
    let rloop : Raw := .plam "i" (.pinr (.sloop (.var "i")))
    let rloopInv : Raw := .plam "i" (.pinr (.sloop (.ineg (.var "i"))))
    let conj (mid : Raw) : Raw :=
      apps transD.ref [w8T, w8baseT, pinrBaseT, w8baseT,
        apps transD.ref [w8T, w8baseT, pinrBaseT, pinrBaseT, pushPT, mid],
        apps symmD.ref [w8T, w8baseT, pinrBaseT, pushPT]]
    .lam "l" (.sumcase "k" omega8T
      (.lam "u" (.sumcase "k2" omega8T
        (.lam "u2" loopL) (.lam "u2" loopLinv) (.snd (.var "l"))))
      (.lam "u" (.sumcase "k2" omega8T
        (.lam "u2" (conj rloop)) (.lam "u2" (conj rloopInv))
        (.snd (.var "l"))))
      (.fst (.var "l")))

#guard genLoopD.ok

/-- Fold a word into a loop, inner-first:
`decodeWord (l :: rest) = decodeWord rest ⬝ genLoop l`. -/
def decodeWordD : LibDef where
  name := "decodeWord"
  ty := .arr wordTy omega8T
  tm := .lam "w" (.listrec "k" omega8T reflW8
    (lams ["h", "t", "ih"]
      (apps transD.ref [w8T, w8baseT, w8baseT, w8baseT,
        .var "ih", .app genLoopD.ref (.var "h")]))
    (.var "w"))

#guard decodeWordD.ok

/-- Decoding of reduced words. -/
def decodeF2D : LibDef where
  name := "decodeF2"
  ty := .arr f2Ty omega8T
  tm := .lam "s" (.app decodeWordD.ref (.fst (.var "s")))

#guard decodeF2D.ok


end Cubical.Library

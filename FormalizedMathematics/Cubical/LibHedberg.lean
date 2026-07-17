import FormalizedMathematics.Cubical.LibCats

namespace Cubical.Library

open Raw

/-! ## Retracts and inverses

`isSetRetract` is the same four-tube square as `isPropToIsSet`: push the
set-square of `B` through `g` and correct all four faces by the retraction.
It gives `isSet (Ω S¹)` cheaply — the predicate-transport route exploded.
The inverse laws complete the groupoid structure of paths; the left one is
a one-liner thanks to the *strict* De Morgan involution. -/

/-- A retract of a proposition is a proposition. -/
def isPropRetractD : LibDef where
  name := "isPropRetract"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "h" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (.arr (isPropR (.var "B")) (isPropR (.var "A")))))))
  tm := lams ["A", "B", "f", "g", "h", "pB", "xp", "yp"]
    (.plam "i" (.hcomp "k" (.var "A")
      [([(.var "i", false)],
         .papp (.app (.var "h") (.var "xp"))
           (.app (.var "g") (.app (.var "f") (.var "xp"))) (.var "xp")
           (.var "k")),
       ([(.var "i", true)],
         .papp (.app (.var "h") (.var "yp"))
           (.app (.var "g") (.app (.var "f") (.var "yp"))) (.var "yp")
           (.var "k"))]
      (.app (.var "g")
        (.papp (apps (.var "pB")
            [.app (.var "f") (.var "xp"), .app (.var "f") (.var "yp")])
          (.app (.var "f") (.var "xp")) (.app (.var "f") (.var "yp"))
          (.var "i")))))

/-- A retract of a set is a set (the four-tube square). -/
def isSetRetractD : LibDef where
  name := "isSetRetract"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "h" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (.arr (isSetR (.var "B")) (isSetR (.var "A")))))))
  tm :=
    let fx : Raw := .app (.var "f") (.var "xs")
    let fy : Raw := .app (.var "f") (.var "ys")
    let congf (pp : Raw) : Raw := apps congD.ref
      [.var "A", .var "B", .var "f", .var "xs", .var "ys", pp]
    let sq : Raw := apps (.var "sB") [fx, fy, congf (.var "xp"), congf (.var "yp")]
    let pAt (v : Raw) : Raw := .papp (.var "xp") (.var "xs") (.var "ys") v
    let qAt (v : Raw) : Raw := .papp (.var "yp") (.var "xs") (.var "ys") v
    let hAt (a : Raw) : Raw := .papp (.app (.var "h") a)
      (.app (.var "g") (.app (.var "f") a)) a (.var "k")
    lams ["A", "B", "f", "g", "h", "sB", "xs", "ys", "xp", "yp"]
      (.plam "j" (.plam "i" (.hcomp "k" (.var "A")
        [([(.var "i", false)], hAt (.var "xs")),
         ([(.var "i", true)], hAt (.var "ys")),
         ([(.var "j", false)], hAt (pAt (.var "i"))),
         ([(.var "j", true)], hAt (qAt (.var "i")))]
        (.app (.var "g")
          (.papp
            (.papp sq (congf (.var "xp")) (congf (.var "yp")) (.var "j"))
            fx fy (.var "i"))))))

#guard isPropRetractD.ok
#guard isSetRetractD.ok

/-- `isSet (Ω S¹)`: the loop space is a retract of ℤ. -/
def isSetLoopS1D : LibDef where
  name := "isSetLoopS1"
  ty := isSetR loopSpaceTy
  tm := apps isSetRetractD.ref
    [loopSpaceTy, .int, windingD.ref, intLoopD.ref,
     .lam "a" (apps decodeEncodeD2.ref [.sbase, .var "a"]),
     isSetZD.ref]

#guard isSetLoopS1D.ok

/-- Right inverse law `p ⬝ p⁻¹ ≡ refl`, by a connection-shaped cap. -/
def transInvRD : LibDef where
  name := "transInvR"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "a"))
        (apps transD.ref [.var "A", .var "a", .var "b", .var "a", .var "p",
          apps symmD.ref [.var "A", .var "a", .var "b", .var "p"]])
        (apps reflD.ref [.var "A", .var "a"])))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "j" (.plam "i" (.hcomp "k" (.var "A")
      [([(.var "i", false)], .var "a"),
       ([(.var "i", true)],
         .papp (.var "p") (.var "a") (.var "b")
           (.imin (.ineg (.var "k")) (.ineg (.var "j")))),
       ([(.var "j", true)], .var "a")]
      (.papp (.var "p") (.var "a") (.var "b")
        (.imin (.var "i") (.ineg (.var "j")))))))

/-- Left inverse law `p⁻¹ ⬝ p ≡ refl` — the right law at `p⁻¹`, since
`(p⁻¹)⁻¹ ≡ p` holds *strictly*. -/
def transInvLD : LibDef where
  name := "transInvL"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "b") (.var "b"))
        (apps transD.ref [.var "A", .var "b", .var "a", .var "b",
          apps symmD.ref [.var "A", .var "a", .var "b", .var "p"], .var "p"])
        (apps reflD.ref [.var "A", .var "b"])))))
  tm := lams ["A", "a", "b", "p"]
    (apps transInvRD.ref [.var "A", .var "b", .var "a",
      apps symmD.ref [.var "A", .var "a", .var "b", .var "p"]])

#guard transInvRD.ok
#guard transInvLD.ok

/-! ## Booleans, decidable equality, and Hedberg's theorem

Sums give the object language its first coproducts: `Bool := ⊤ ⊎ ⊤`,
`Dec A := A ⊎ (A → ⊥)`, and Hedberg's theorem — decidable equality implies
`isSet` — whose `refl` case is closed by the inverse law `transInvL` and
whose collapse-constancy is a dependent case split (the refutation branch
discharges *any* goal via `⊥`). -/

def boolTy : Raw := .sum .unit .unit
def trueR : Raw := .inl .tt
def falseR : Raw := .inr .tt
def decR (A : Raw) : Raw := .sum A (.arr A .empty)

def notBoolD : LibDef where
  name := "notBool"
  ty := .arr boolTy boolTy
  tm := .lam "b" (.sumcase "k" boolTy
    (.lam "u" falseR) (.lam "u" trueR) (.var "b"))

/-- `not (not b) ≡ b` (per case, up to `isProp ⊤` on the payload). -/
def notNotD : LibDef where
  name := "notNot"
  ty := .pi "b" boolTy
    (.path boolTy (.app notBoolD.ref (.app notBoolD.ref (.var "b"))) (.var "b"))
  tm := .lam "b" (.sumcase "k"
    (.path boolTy (.app notBoolD.ref (.app notBoolD.ref (.var "k"))) (.var "k"))
    (.lam "u" (apps congD.ref [.unit, boolTy, .lam "w" (.inl (.var "w")),
      .tt, .var "u", apps isPropUnitD.ref [.tt, .var "u"]]))
    (.lam "u" (apps congD.ref [.unit, boolTy, .lam "w" (.inr (.var "w")),
      .tt, .var "u", apps isPropUnitD.ref [.tt, .var "u"]]))
    (.var "b"))

#guard notBoolD.ok
#guard notNotD.ok

def codeBoolD : LibDef where
  name := "codeBool"
  ty := .arr boolTy (.arr boolTy .univ)
  tm := lams ["x", "y"] (.sumcase "k" .univ
    (.lam "u" (.sumcase "k2" .univ (.lam "v" .unit) (.lam "v" .empty) (.var "y")))
    (.lam "u" (.sumcase "k2" .univ (.lam "v" .empty) (.lam "v" .unit) (.var "y")))
    (.var "x"))

def rBoolD : LibDef where
  name := "rBool"
  ty := .pi "x" boolTy (apps codeBoolD.ref [.var "x", .var "x"])
  tm := .lam "x" (.sumcase "k" (apps codeBoolD.ref [.var "k", .var "k"])
    (.lam "u" .tt) (.lam "u" .tt) (.var "x"))

def encodeBoolD : LibDef where
  name := "encodeBool"
  ty := .pi "x" boolTy (.pi "y" boolTy
    (.arr (.path boolTy (.var "x") (.var "y"))
      (apps codeBoolD.ref [.var "x", .var "y"])))
  tm := lams ["x", "y"] (.lam "p" (apps substD.ref [boolTy,
    .lam "k" (apps codeBoolD.ref [.var "x", .var "k"]),
    .var "x", .var "y", .var "p",
    .app rBoolD.ref (.var "x")]))

/-- Equality of booleans is decidable. -/
def decEqBoolD : LibDef where
  name := "decEqBool"
  ty := .pi "x" boolTy (.pi "y" boolTy (decR (.path boolTy (.var "x") (.var "y"))))
  tm := lams ["x", "y"] (.sumcase "k"
    (decR (.path boolTy (.var "k") (.var "y")))
    (.lam "u" (.sumcase "k2"
      (decR (.path boolTy (.inl (.var "u")) (.var "k2")))
      (.lam "v" (.inl (apps congD.ref [.unit, boolTy,
        .lam "w" (.inl (.var "w")), .var "u", .var "v",
        apps isPropUnitD.ref [.var "u", .var "v"]])))
      (.lam "v" (.inr (.lam "p"
        (apps encodeBoolD.ref [.inl (.var "u"), .inr (.var "v"), .var "p"]))))
      (.var "y")))
    (.lam "u" (.sumcase "k2"
      (decR (.path boolTy (.inr (.var "u")) (.var "k2")))
      (.lam "v" (.inr (.lam "p"
        (apps encodeBoolD.ref [.inr (.var "u"), .inl (.var "v"), .var "p"]))))
      (.lam "v" (.inl (apps congD.ref [.unit, boolTy,
        .lam "w" (.inr (.var "w")), .var "u", .var "v",
        apps isPropUnitD.ref [.var "u", .var "v"]])))
      (.var "y")))
    (.var "x"))

#guard codeBoolD.ok
#guard rBoolD.ok
#guard encodeBoolD.ok
#guard decEqBoolD.ok

/-- **Hedberg's theorem**: decidable equality implies `isSet`. -/
def hedbergD : LibDef where
  name := "hedberg"
  ty := .pi "A" .univ
    (.arr (.pi "hx" (.var "A") (.pi "hy" (.var "A")
      (decR (.path (.var "A") (.var "hx") (.var "hy")))))
      (isSetR (.var "A")))
  tm :=
    let PT := .path (.var "A") (.var "xs") (.var "ys")
    let PTxx := .path (.var "A") (.var "xs") (.var "xs")
    -- collapse of a path through the decision
    let constAt (y pp : Raw) : Raw := .sumcase "k"
      (.path (.var "A") (.var "xs") y)
      (.lam "d" (.var "d"))
      (.lam "nd" (.emptyrec (.path (.var "A") (.var "xs") y)
        (.app (.var "nd") pp)))
      (apps (.var "dec") [.var "xs", y])
    let reflx : Raw := apps reflD.ref [.var "A", .var "xs"]
    let cxx : Raw := constAt (.var "xs") reflx
    let tOf (pp : Raw) : Raw := apps transD.ref [.var "A",
      .var "xs", .var "xs", .var "ys",
      apps symmD.ref [.var "A", .var "xs", .var "xs", cxx],
      constAt (.var "ys") pp]
    -- keyLemma p : p ≡ (c_xx)⁻¹ ⬝ const p, by J (refl case: transInvL)
    let keyLemma (pp : Raw) : Raw := apps jD.ref [.var "A", .var "xs",
      lams ["y2", "p2"] (.path (.path (.var "A") (.var "xs") (.var "y2"))
        (.var "p2")
        (apps transD.ref [.var "A", .var "xs", .var "xs", .var "y2",
          apps symmD.ref [.var "A", .var "xs", .var "xs", cxx],
          constAt (.var "y2") (.var "p2")])),
      apps symmD.ref [PTxx,
        apps transD.ref [.var "A", .var "xs", .var "xs", .var "xs",
          apps symmD.ref [.var "A", .var "xs", .var "xs", cxx],
          constAt (.var "xs") reflx],
        reflx,
        apps transInvLD.ref [.var "A", .var "xs", .var "xs", cxx]],
      .var "ys", pp]
    -- constEq : const p ≡ const q, by case split on the decision
    let constEq : Raw := .sumcase "D2"
      (.path PT
        (.sumcase "k" PT (.lam "d" (.var "d"))
          (.lam "nd" (.emptyrec PT (.app (.var "nd") (.var "xp"))))
          (.var "D2"))
        (.sumcase "k" PT (.lam "d" (.var "d"))
          (.lam "nd" (.emptyrec PT (.app (.var "nd") (.var "yp"))))
          (.var "D2")))
      (.lam "d" (.plam "ci" (.var "d")))
      (.lam "nd" (
        let ndAnn : Raw := .ann (.inr (.var "nd"))
          (.sum PT (.arr PT .empty))
        .emptyrec
        (.path PT
          (.sumcase "k" PT (.lam "d" (.var "d"))
            (.lam "nd2" (.emptyrec PT (.app (.var "nd2") (.var "xp"))))
            ndAnn)
          (.sumcase "k" PT (.lam "d" (.var "d"))
            (.lam "nd2" (.emptyrec PT (.app (.var "nd2") (.var "yp"))))
            ndAnn))
        (.app (.var "nd") (.var "xp"))))
      (apps (.var "dec") [.var "xs", .var "ys"])
    lams ["A", "dec", "xs", "ys", "xp", "yp"]
      (apps transD.ref [PT, .var "xp", tOf (.var "xp"), .var "yp",
        keyLemma (.var "xp"),
        apps transD.ref [PT, tOf (.var "xp"), tOf (.var "yp"), .var "yp",
          apps congD.ref [PT, PT,
            .lam "h2" (apps transD.ref [.var "A",
              .var "xs", .var "xs", .var "ys",
              apps symmD.ref [.var "A", .var "xs", .var "xs", cxx],
              .var "h2"]),
            constAt (.var "ys") (.var "xp"),
            constAt (.var "ys") (.var "yp"),
            constEq],
          apps symmD.ref [PT, .var "yp", tOf (.var "yp"),
            keyLemma (.var "yp")]]])

#guard hedbergD.ok

/-- `isSet Bool`, by Hedberg. -/
def isSetBoolD : LibDef where
  name := "isSetBool"
  ty := isSetR boolTy
  tm := apps hedbergD.ref [boolTy, decEqBoolD.ref]

/-- Negation is an equivalence of booleans. -/
def notEquivD : LibDef where
  name := "notEquiv"
  ty := equivR boolTy boolTy
  tm := apps setIsoToEquivD.ref
    [boolTy, boolTy, notBoolD.ref, notBoolD.ref,
     notNotD.ref, notNotD.ref, isSetBoolD.ref]

#guard isSetBoolD.ok
#guard notEquivD.ok

-- **the classic**: transport (ua not) true ⟶ false
#guard
  match normalize
    (apps transportD.ref [boolTy, boolTy,
      apps uaD.ref [boolTy, boolTy, notEquivD.ref], trueR]) boolTy with
  | .ok t => t == resolveClosed falseR
  | .error _ => false

/-! ## Horizontal composition and the interchange law

The two ways of composing `α : F ⇒ G` (over `C → D`) with `β : H ⇒ K`
(over `D → E`) horizontally agree — componentwise this is exactly β's
naturality at α's components, and `natTransEq` does the rest.  With this,
the 2-categorical structure of functors/natural transformations is
verified. -/

/-- The interchange law for whiskering. -/
def interchangeD : LibDef where
  name := "interchange"
  ty := .pi "Cc" (precatTy 0) (.pi "Dd" (precatTy 0) (.pi "Ep" setCatTy
    (.pi "Ff" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Gg" (functorTy (.var "Cc") (.var "Dd"))
    (.pi "Hh" (functorTy (.var "Dd") (.fst (.var "Ep")))
    (.pi "Kk" (functorTy (.var "Dd") (.fst (.var "Ep")))
    (.pi "al" (natTransTy (.var "Cc") (.var "Dd") (.var "Ff") (.var "Gg"))
    (.pi "be" (natTransTy (.var "Dd") (.fst (.var "Ep")) (.var "Hh") (.var "Kk"))
      (
        let E := .fst (.var "Ep")
        let HF := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
          .var "Ff", .var "Hh"]
        let KF := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
          .var "Ff", .var "Kk"]
        let HG := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
          .var "Gg", .var "Hh"]
        let KG := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
          .var "Gg", .var "Kk"]
        .path (natTransTy (.var "Cc") E HF KG)
          (apps compNatD.ref [.var "Cc", E, HF, KF, KG,
            apps whiskerLD.ref [.var "Cc", .var "Dd", E,
              .var "Ff", .var "Hh", .var "Kk", .var "be"],
            apps whiskerRD.ref [.var "Cc", .var "Dd", E,
              .var "Ff", .var "Gg", .var "Kk", .var "al"]])
          (apps compNatD.ref [.var "Cc", E, HF, HG, KG,
            apps whiskerRD.ref [.var "Cc", .var "Dd", E,
              .var "Ff", .var "Gg", .var "Hh", .var "al"],
            apps whiskerLD.ref [.var "Cc", .var "Dd", E,
              .var "Gg", .var "Hh", .var "Kk", .var "be"]]))))))))))
  tm :=
    let E := .fst (.var "Ep")
    let HF := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
      .var "Ff", .var "Hh"]
    let KG := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
      .var "Gg", .var "Kk"]
    let KF := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
      .var "Ff", .var "Kk"]
    let HG := apps compFunctorD.ref [.var "Cc", .var "Dd", E,
      .var "Gg", .var "Hh"]
    let F0x : Raw := .app (funF0 (.var "Ff")) (.var "x")
    let G0x : Raw := .app (funF0 (.var "Gg")) (.var "x")
    let alx : Raw := .app (.fst (.var "al")) (.var "x")
    lams ["Cc", "Dd", "Ep", "Ff", "Gg", "Hh", "Kk", "al", "be"]
      (apps natTransEqD.ref [.var "Cc", .var "Ep", HF, KG,
        apps compNatD.ref [.var "Cc", E, HF, KF, KG,
          apps whiskerLD.ref [.var "Cc", .var "Dd", E,
            .var "Ff", .var "Hh", .var "Kk", .var "be"],
          apps whiskerRD.ref [.var "Cc", .var "Dd", E,
            .var "Ff", .var "Gg", .var "Kk", .var "al"]],
        apps compNatD.ref [.var "Cc", E, HF, HG, KG,
          apps whiskerRD.ref [.var "Cc", .var "Dd", E,
            .var "Ff", .var "Gg", .var "Hh", .var "al"],
          apps whiskerLD.ref [.var "Cc", .var "Dd", E,
            .var "Gg", .var "Hh", .var "Kk", .var "be"]],
        .lam "x" (apps symmD.ref [
          apps (catHom E) [.app (funF0 (.var "Hh")) F0x,
            .app (funF0 (.var "Kk")) G0x],
          apps (catCmp E) [.app (funF0 (.var "Hh")) F0x,
            .app (funF0 (.var "Hh")) G0x, .app (funF0 (.var "Kk")) G0x,
            apps (funF1 (.var "Hh")) [F0x, G0x, alx],
            .app (.fst (.var "be")) G0x],
          apps (catCmp E) [.app (funF0 (.var "Hh")) F0x,
            .app (funF0 (.var "Kk")) F0x, .app (funF0 (.var "Kk")) G0x,
            .app (.fst (.var "be")) F0x,
            apps (funF1 (.var "Kk")) [F0x, G0x, alx]],
          apps (.snd (.var "be")) [F0x, G0x, alx]])])

#guard interchangeD.ok

/-! ## Decidable equality of ℕ and ℤ (and Hedberg cross-checks) -/

def decCodeNatD : LibDef where
  name := "decCodeNat"
  ty := .pi "m" .nat (.pi "n" .nat (decR (apps codeNatD.ref [.var "m", .var "n"])))
  tm := .lam "m" (.natrec "k"
    (.pi "n" .nat (decR (apps codeNatD.ref [.var "k", .var "n"])))
    (.lam "n" (.natrec "k2"
      (decR (apps codeNatD.ref [.zero, .var "k2"]))
      (.inl .tt)
      (lams ["n2", "ih2"] (.inr (.lam "c" (.var "c"))))
      (.var "n")))
    (lams ["m2", "ihm"] (.lam "n" (.natrec "k2"
      (decR (apps codeNatD.ref [.succ (.var "m2"), .var "k2"]))
      (.inr (.lam "c" (.var "c")))
      (lams ["n2", "ih2"] (.app (.var "ihm") (.var "n2")))
      (.var "n"))))
    (.var "m"))

/-- Equality of naturals is decidable. -/
def decEqNatD : LibDef where
  name := "decEqNat"
  ty := .pi "m" .nat (.pi "n" .nat (decR (.path .nat (.var "m") (.var "n"))))
  tm := lams ["m", "n"] (.sumcase "d"
    (decR (.path .nat (.var "m") (.var "n")))
    (.lam "c" (.inl (apps decodeNatD.ref [.var "m", .var "n", .var "c"])))
    (.lam "nc" (.inr (.lam "p" (.app (.var "nc")
      (apps encodeNatD.ref [.var "m", .var "n", .var "p"])))))
    (apps decCodeNatD.ref [.var "m", .var "n"]))

def decCodeZD : LibDef where
  name := "decCodeZ"
  ty := .pi "z" .int (.pi "w" .int (decR (apps codeZD.ref [.var "z", .var "w"])))
  tm := .lam "z" (.intcase "k"
    (.pi "w" .int (decR (apps codeZD.ref [.var "k", .var "w"])))
    (.lam "n" (.lam "w" (.intcase "k2"
      (decR (apps codeZD.ref [.ipos (.var "n"), .var "k2"]))
      (.lam "n2" (apps decCodeNatD.ref [.var "n", .var "n2"]))
      (.lam "n2" (.inr (.lam "c" (.var "c"))))
      (.var "w"))))
    (.lam "n" (.lam "w" (.intcase "k2"
      (decR (apps codeZD.ref [.inegsuc (.var "n"), .var "k2"]))
      (.lam "n2" (.inr (.lam "c" (.var "c"))))
      (.lam "n2" (apps decCodeNatD.ref [.var "n", .var "n2"]))
      (.var "w"))))
    (.var "z"))

/-- Equality of integers is decidable. -/
def decEqZD : LibDef where
  name := "decEqZ"
  ty := .pi "z" .int (.pi "w" .int (decR (.path .int (.var "z") (.var "w"))))
  tm := lams ["z", "w"] (.sumcase "d"
    (decR (.path .int (.var "z") (.var "w")))
    (.lam "c" (.inl (apps decodeZD.ref [.var "z", .var "w", .var "c"])))
    (.lam "nc" (.inr (.lam "p" (.app (.var "nc")
      (apps encodeZD.ref [.var "z", .var "w", .var "p"])))))
    (apps decCodeZD.ref [.var "z", .var "w"]))

#guard decCodeNatD.ok
#guard decEqNatD.ok
#guard decCodeZD.ok
#guard decEqZD.ok

-- Hedberg cross-checks: independent second proofs of `isSet ℕ` / `isSet ℤ`
#guard
  match checkDef (apps hedbergD.ref [.nat, decEqNatD.ref]) (isSetR .nat) with
  | .ok _ => true | .error _ => false
#guard
  match checkDef (apps hedbergD.ref [.int, decEqZD.ref]) (isSetR .int) with
  | .ok _ => true | .error _ => false

/-! ## Σ-closure of propositions -/

/-- `isProp` is closed under Σ (the second component rides by `toPathP`). -/
def isPropSigmaD : LibDef where
  name := "isPropSigma"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.arr (isPropR (.var "A"))
    (.arr (.pi "a" (.var "A") (isPropR (.app (.var "B") (.var "a"))))
      (isPropR (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))))))
  tm :=
    let p1 : Raw := .ann
      (apps (.var "hA") [.fst (.var "xp"), .fst (.var "yp")])
      (.path (.var "A") (.fst (.var "xp")) (.fst (.var "yp")))
    let line : Raw := .plam "i" (.app (.var "B")
      (.papp p1 (.fst (.var "xp")) (.fst (.var "yp")) (.var "i")))
    let sndPath : Raw := apps toPathPD.ref
      [.app (.var "B") (.fst (.var "xp")),
       .app (.var "B") (.fst (.var "yp")),
       line, .snd (.var "xp"), .snd (.var "yp"),
       apps (.var "hB") [.fst (.var "yp"),
         apps transportD.ref [.app (.var "B") (.fst (.var "xp")),
           .app (.var "B") (.fst (.var "yp")), line, .snd (.var "xp")],
         .snd (.var "yp")]]
    lams ["A", "B", "hA", "hB", "xp", "yp"]
      (.plam "i" (.pair
        (.papp p1 (.fst (.var "xp")) (.fst (.var "yp")) (.var "i"))
        (.papp sndPath (.snd (.var "xp")) (.snd (.var "yp")) (.var "i"))))

#guard isPropSigmaD.ok

end Cubical.Library

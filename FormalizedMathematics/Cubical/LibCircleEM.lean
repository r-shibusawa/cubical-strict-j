import FormalizedMathematics.Cubical.LibCoherence

/-! # `S¹ ≃ K(ℤ,1)`: the two circles are one

The concrete circle is the classifying space of `(ℤ,+)`.  Stage A:
`intLoop` is a homomorphism (`intLoop (g+h) ≡ intLoop g ⬝ intLoop h`),
by ℤ-induction with generic cancellation chains. -/

namespace Cubical.Library

open Raw

private def PS : Raw := .path .s1 .sbase .sbase
private def cmpS (p q : Raw) : Raw :=
  apps transD.ref [.s1, .sbase, .sbase, .sbase, p, q]
private def loopP : Raw := .plam "i9" (.sloop (.var "i9"))
private def loopInvP : Raw := .plam "i9" (.sloop (.ineg (.var "i9")))
private def reflS : Raw := .plam "i9" .sbase
private def iLoop (z : Raw) : Raw := .app intLoopD.ref z


/-- `intLoop (suc z) ≡ intLoop z ⬝ loop`. -/
def intLoopSucD : LibDef where
  name := "intLoopSuc"
  ty := .pi "z" .int (.path PS
    (iLoop (.app sucZD.ref (.var "z")))
    (cmpS (iLoop (.var "z")) loopP))
  tm := .lam "z" (.intcase "k"
    (.path PS (iLoop (.app sucZD.ref (.var "k")))
      (cmpS (iLoop (.var "k")) loopP))
    (.lam "n" (.plam "k9" (cmpS (iLoop (.ipos (.var "n"))) loopP)))
    (.lam "n" (.natrec "k2"
      (.path PS (iLoop (.app sucZD.ref (.inegsuc (.var "k2"))))
        (cmpS (iLoop (.inegsuc (.var "k2"))) loopP))
      (apps symmD.ref [PS, cmpS (iLoop (.inegsuc .zero)) loopP,
        iLoop (.ipos .zero),
        apps cancelRD.ref [.s1, .sbase, .sbase, .sbase, reflS, loopP]])
      (lams ["m", "ih"] (apps symmD.ref [PS,
        cmpS (iLoop (.inegsuc (.succ (.var "m")))) loopP,
        iLoop (.inegsuc (.var "m")),
        apps cancelRD.ref [.s1, .sbase, .sbase, .sbase,
          iLoop (.inegsuc (.var "m")), loopP]]))
      (.var "n")))
    (.var "z"))

/-- `intLoop (pred z) ≡ intLoop z ⬝ loop⁻¹`. -/
def intLoopPredD : LibDef where
  name := "intLoopPred"
  ty := .pi "z" .int (.path PS
    (iLoop (.app predZD.ref (.var "z")))
    (cmpS (iLoop (.var "z")) loopInvP))
  tm := .lam "z" (.intcase "k"
    (.path PS (iLoop (.app predZD.ref (.var "k")))
      (cmpS (iLoop (.var "k")) loopInvP))
    (.lam "n" (.natrec "k2"
      (.path PS (iLoop (.app predZD.ref (.ipos (.var "k2"))))
        (cmpS (iLoop (.ipos (.var "k2"))) loopInvP))
      (.plam "k9" (cmpS reflS loopInvP))
      (lams ["m", "ih"] (apps symmD.ref [PS,
        cmpS (iLoop (.ipos (.succ (.var "m")))) loopInvP,
        iLoop (.ipos (.var "m")),
        apps cancelRD.ref [.s1, .sbase, .sbase, .sbase,
          iLoop (.ipos (.var "m")), loopInvP]]))
      (.var "n")))
    (.lam "n" (.plam "k9" (cmpS (iLoop (.inegsuc (.var "n"))) loopInvP)))
    (.var "z"))

#guard intLoopSucD.ok
#guard intLoopPredD.ok

/-- **`intLoop` is a homomorphism**: `intLoop (g+h) ≡ intLoop g ⬝ intLoop h`. -/
def intLoopCompD : LibDef where
  name := "intLoopComp"
  ty := .pi "g" .int (.pi "h" .int
    (.path PS (iLoop (apps addD.ref [.var "g", .var "h"]))
      (cmpS (iLoop (.var "g")) (iLoop (.var "h")))))
  tm :=
    let g : Raw := .var "g"
    let addg (h : Raw) : Raw := apps addD.ref [g, h]
    lams ["g", "h"] (.intcase "k"
      (.path PS (iLoop (addg (.var "k")))
        (cmpS (iLoop g) (iLoop (.var "k"))))
      (.lam "n" (.natrec "k2"
        (.path PS (iLoop (addg (.ipos (.var "k2"))))
          (cmpS (iLoop g) (iLoop (.ipos (.var "k2")))))
        (apps symmD.ref [PS, cmpS (iLoop g) (iLoop (.ipos .zero)),
          iLoop g,
          apps transReflRD.ref [.s1, .sbase, .sbase, iLoop g]])
        (lams ["m", "ih"] (apps transD.ref [PS,
          iLoop (.app sucZD.ref (addg (.ipos (.var "m")))),
          cmpS (iLoop (addg (.ipos (.var "m")))) loopP,
          cmpS (iLoop g) (iLoop (.ipos (.succ (.var "m")))),
          .app intLoopSucD.ref (addg (.ipos (.var "m"))),
          apps transD.ref [PS,
            cmpS (iLoop (addg (.ipos (.var "m")))) loopP,
            cmpS (cmpS (iLoop g) (iLoop (.ipos (.var "m")))) loopP,
            cmpS (iLoop g) (iLoop (.ipos (.succ (.var "m")))),
            apps congD.ref [PS, PS,
              .lam "h2" (cmpS (.var "h2") loopP),
              iLoop (addg (.ipos (.var "m"))),
              cmpS (iLoop g) (iLoop (.ipos (.var "m"))),
              .var "ih"],
            apps transAssocD.ref [.s1, .sbase, .sbase, .sbase, .sbase,
              iLoop g, iLoop (.ipos (.var "m")), loopP]]]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path PS (iLoop (addg (.inegsuc (.var "k2"))))
          (cmpS (iLoop g) (iLoop (.inegsuc (.var "k2")))))
        (apps transD.ref [PS,
          iLoop (.app predZD.ref g),
          cmpS (iLoop g) loopInvP,
          cmpS (iLoop g) (iLoop (.inegsuc .zero)),
          .app intLoopPredD.ref g,
          apps congD.ref [PS, PS,
            .lam "h2" (cmpS (iLoop g) (.var "h2")),
            loopInvP, cmpS reflS loopInvP,
            apps symmD.ref [PS, cmpS reflS loopInvP, loopInvP,
              apps transReflLD.ref [.s1, .sbase, .sbase, loopInvP]]]])
        (lams ["m", "ih"] (apps transD.ref [PS,
          iLoop (.app predZD.ref (addg (.inegsuc (.var "m")))),
          cmpS (iLoop (addg (.inegsuc (.var "m")))) loopInvP,
          cmpS (iLoop g) (iLoop (.inegsuc (.succ (.var "m")))),
          .app intLoopPredD.ref (addg (.inegsuc (.var "m"))),
          apps transD.ref [PS,
            cmpS (iLoop (addg (.inegsuc (.var "m")))) loopInvP,
            cmpS (cmpS (iLoop g) (iLoop (.inegsuc (.var "m")))) loopInvP,
            cmpS (iLoop g) (iLoop (.inegsuc (.succ (.var "m")))),
            apps congD.ref [PS, PS,
              .lam "h2" (cmpS (.var "h2") loopInvP),
              iLoop (addg (.inegsuc (.var "m"))),
              cmpS (iLoop g) (iLoop (.inegsuc (.var "m"))),
              .var "ih"],
            apps transAssocD.ref [.s1, .sbase, .sbase, .sbase, .sbase,
              iLoop g, iLoop (.inegsuc (.var "m")), loopInvP]]]))
        (.var "n")))
      (.var "h"))

#guard intLoopCompD.ok

/-- Dependent paths over propositional fibers (generic: keeping the
fibers abstract keeps the conversion problems small). -/
def propFillD : LibDef where
  name := "propFill"
  ty := .pi "X" .univ (.pi "P" (.arr (.var "X") .univ)
    (.pi "mprp" (.pi "x0" (.var "X") (isPropR (.app (.var "P") (.var "x0"))))
    (.pi "x" (.var "X") (.pi "y" (.var "X")
    (.pi "pth" (.path (.var "X") (.var "x") (.var "y"))
    (.pi "u" (.app (.var "P") (.var "x"))
    (.pi "v" (.app (.var "P") (.var "y"))
      (.pathP "i9" (.app (.var "P")
          (.papp (.var "pth") (.var "x") (.var "y") (.var "i9")))
        (.var "u") (.var "v")))))))))
  tm :=
    let line : Raw := .plam "i9" (.app (.var "P")
      (.papp (.var "pth") (.var "x") (.var "y") (.var "i9")))
    lams ["X", "P", "mprp", "x", "y", "pth", "u", "v"]
      (apps toPathPD.ref
        [.app (.var "P") (.var "x"), .app (.var "P") (.var "y"),
         line, .var "u", .var "v",
         apps (.app (.var "mprp") (.var "y"))
           [apps transportD.ref [.app (.var "P") (.var "x"),
              .app (.var "P") (.var "y"), line, .var "u"],
            .var "v"]])

#guard propFillD.ok

/-- **The circle is a groupoid** — double circle induction into the
proposition `isSet`, both loop cells by the generic `propFill`. -/
def isGroupoidS1D : LibDef where
  name := "isGroupoidS1"
  ty := isGpdR .s1
  tm :=
    let innerFam : Raw := .lam "b2" (isSetR (.path .s1 .sbase (.var "b2")))
    let inner : Raw := .lam "b" (.s1elim "b2"
      (isSetR (.path .s1 .sbase (.var "b2")))
      isSetLoopS1D.ref
      (apps propFillD.ref [.s1, innerFam,
        .lam "b2" (.app isPropIsSetD.ref (.path .s1 .sbase (.var "b2"))),
        .sbase, .sbase, loopP, isSetLoopS1D.ref, isSetLoopS1D.ref])
      (.var "b"))
    let outerFam : Raw := .lam "a2" (.pi "b" .s1
      (isSetR (.path .s1 (.var "a2") (.var "b"))))
    lams ["a", "b"] (apps
      (.app (.s1elim "a2"
        (.pi "b" .s1 (isSetR (.path .s1 (.var "a2") (.var "b"))))
        inner
        (apps propFillD.ref [.s1, outerFam,
          .lam "a2" (apps isPropPiD.ref
            [.s1,
             .lam "b" (isSetR (.path .s1 (.var "a2") (.var "b"))),
             .lam "b" (.app isPropIsSetD.ref
               (.path .s1 (.var "a2") (.var "b")))]),
          .sbase, .sbase, loopP, inner, inner])
        (.var "a"))
        (.var "b"))
      [])

-- #guard isGroupoidS1D.ok -- PENDING: evaluator value-sharing (HANDOFF)

/-! ## `S¹ ≃ K(ℤ,1)`: the maps and the circle-side round trip -/

private def emZ : Raw := .em1 .int addD.ref
private def PE : Raw := .path emZ .embase .embase
private def one1 : Raw := .ipos (.succ .zero)

/-- `S¹ → K(ℤ,1)`: the loop goes to `emloop 1`. -/
def toEMD : LibDef where
  name := "toEM"
  ty := .arr .s1 emZ
  tm := .lam "x" (.s1elim "x2" emZ .embase
    (.plam "i" (.emloop one1 (.var "i"))) (.var "x"))

/-- `K(ℤ,1) → S¹`: `emloop z ↦ intLoop z`; the composition cell is the
`trans`-filler corrected along `intLoopComp`. -/
def fromEMD : LibDef where
  name := "fromEM"
  ty := .arr emZ .s1
  tm :=
    let g : Raw := .var "g"
    let h : Raw := .var "h"
    let iLh (e : Raw) : Raw := .papp (iLoop h) .sbase .sbase e
    let iLg (e : Raw) : Raw := .papp (iLoop g) .sbase .sbase e
    let gph : Raw := apps addD.ref [g, h]
    let filler : Raw := .plam "i" (.hcomp "k2" .s1
      [([(.var "i", false)], .sbase),
       ([(.var "i", true)], iLh (.imin (.var "k2") (.var "j"))),
       ([(.var "j", false)], iLg (.var "i"))]
      (iLg (.var "i")))
    let ccell : Raw := lams ["g", "h"] (.plam "j" (.hcomp "k"
      (.path .s1 .sbase (iLh (.var "j")))
      [([(.var "j", false)], iLoop g),
       ([(.var "j", true)],
         .papp (apps symmD.ref [PS, iLoop gph, cmpS (iLoop g) (iLoop h),
             apps intLoopCompD.ref [g, h]])
           (cmpS (iLoop g) (iLoop h)) (iLoop gph) (.var "k"))]
      filler))
    .lam "y" (.em1rec .s1 isGroupoidS1D.ref .sbase intLoopD.ref ccell
      (.var "y"))

-- #guard toEMD.ok -- checked natively (Test/CircleEM)
-- #guard fromEMD.ok -- checked natively (Test/CircleEM)

/-- Circle-side round trip: the loop cell is the unit-law square read as
a path-over. -/
def fromToD : LibDef where
  name := "fromTo"
  ty := .pi "x" .s1
    (.path .s1 (.app fromEMD.ref (.app toEMD.ref (.var "x"))) (.var "x"))
  tm := .lam "x" (.s1elim "x2"
    (.path .s1 (.app fromEMD.ref (.app toEMD.ref (.var "x2"))) (.var "x2"))
    (.plam "i0" .sbase)
    (.plam "i" (.plam "j" (.papp
      (.papp (apps transReflLD.ref [.s1, .sbase, .sbase, loopP])
        (cmpS reflS loopP) loopP (.var "j"))
      .sbase .sbase (.var "i"))))
    (.var "x"))

-- #guard fromToD.ok -- checked natively (Test/CircleEM)

/-! ## The EM-side round trip

`cong toEM` distributes over composition *definitionally* (the constant-
motive eliminator commutes with `hcomp`), so `toIntLoop` closes by
ℤ-induction with `emloopComp`; the inverse case uses uniqueness of
inverses in the path groupoid. -/

private def toA : Raw := toEMD.ref
private def congTo (p : Raw) : Raw :=
  apps congD.ref [.s1, emZ, toA, .sbase, .sbase, p]
private def cmpE (p q : Raw) : Raw :=
  apps transD.ref [emZ, .embase, .embase, .embase, p, q]
private def emlp (z : Raw) : Raw := apps emloopD.ref [.int, addD.ref, z]

/-- Uniqueness of inverses: `p ⬝ q ≡ refl → p ≡ q⁻¹`. -/
def invUniqueD : LibDef where
  name := "invUnique"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
    (.pi "q" (.path (.var "A") (.var "b") (.var "a"))
    (.arr (.path (.path (.var "A") (.var "a") (.var "a"))
        (apps transD.ref [.var "A", .var "a", .var "b", .var "a",
          .var "p", .var "q"])
        (apps reflD.ref [.var "A", .var "a"]))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (.var "p")
        (apps symmD.ref [.var "A", .var "b", .var "a", .var "q"])))))))
  tm :=
    let A : Raw := .var "A"
    let PT : Raw := .path A (.var "a") (.var "b")
    let qi : Raw := apps symmD.ref [A, .var "b", .var "a", .var "q"]
    let cm (x y z p q : Raw) : Raw := apps transD.ref [A, x, y, z, p, q]
    -- p ≡ (p⬝q)⬝q⁻¹ ≡ refl⬝q⁻¹ ≡ q⁻¹   (via cancelR backwards and w)
    lams ["A", "a", "b", "p", "q", "w"] (apps transD.ref [PT,
      .var "p",
      cm (.var "a") (.var "a") (.var "b")
        (cm (.var "a") (.var "b") (.var "a") (.var "p") (.var "q")) qi,
      qi,
      apps symmD.ref [PT,
        cm (.var "a") (.var "a") (.var "b")
          (cm (.var "a") (.var "b") (.var "a") (.var "p") (.var "q")) qi,
        .var "p",
        apps cancelRD.ref [A, .var "a", .var "b", .var "a",
          .var "p", qi]],
      apps transD.ref [PT,
        cm (.var "a") (.var "a") (.var "b")
          (cm (.var "a") (.var "b") (.var "a") (.var "p") (.var "q")) qi,
        cm (.var "a") (.var "a") (.var "b")
          (apps reflD.ref [A, .var "a"]) qi,
        qi,
        apps congD.ref [.path A (.var "a") (.var "a"), PT,
          .lam "h" (cm (.var "a") (.var "a") (.var "b") (.var "h") qi),
          cm (.var "a") (.var "b") (.var "a") (.var "p") (.var "q"),
          apps reflD.ref [A, .var "a"], .var "w"],
        apps transReflLD.ref [A, .var "a", .var "b", qi]]])

/-- `emloop (-1) ≡ (emloop 1)⁻¹`. -/
def emNegOneD : LibDef where
  name := "emNegOne"
  ty := .path PE (emlp (.inegsuc .zero))
    (apps symmD.ref [emZ, .embase, .embase, emlp one1])
  tm :=
    let ue : Raw := .app addZeroLD.ref (.ipos .zero)
    apps invUniqueD.ref [emZ, .embase, .embase,
      emlp (.inegsuc .zero), emlp one1,
      apps transD.ref [.path emZ .embase .embase,
        cmpE (emlp (.inegsuc .zero)) (emlp one1),
        emlp (.ipos .zero),
        apps reflD.ref [emZ, .embase],
        apps symmD.ref [PE, emlp (.ipos .zero),
          cmpE (emlp (.inegsuc .zero)) (emlp one1),
          apps emloopCompD.ref [.int, addD.ref, .inegsuc .zero, one1]],
        apps emloopOneD.ref [.int, addD.ref, .ipos .zero, ue]]]

/-- `cong toEM (intLoop z) ≡ emloop z`, by ℤ-induction (the composite
images are definitional; only `emloopComp` and the unit/inverse lemmas
enter as paths). -/
def toIntLoopD : LibDef where
  name := "toIntLoop"
  ty := .pi "z" .int
    (.path PE (congTo (iLoop (.var "z"))) (emlp (.var "z")))
  tm :=
    let ue : Raw := .app addZeroLD.ref (.ipos .zero)
    let emOne : Raw := apps emloopOneD.ref [.int, addD.ref, .ipos .zero, ue]
    let em1i : Raw := apps symmD.ref [emZ, .embase, .embase, emlp one1]
    .lam "z" (.intcase "k"
      (.path PE (congTo (iLoop (.var "k"))) (emlp (.var "k")))
      (.lam "n" (.natrec "k2"
        (.path PE (congTo (iLoop (.ipos (.var "k2"))))
          (emlp (.ipos (.var "k2"))))
        (apps symmD.ref [PE, emlp (.ipos .zero),
          apps reflD.ref [emZ, .embase], emOne])
        (lams ["m", "ih"] (
          let mZ : Raw := .ipos (.var "m")
          apps transD.ref [PE,
            cmpE (congTo (iLoop mZ)) (emlp one1),
            cmpE (emlp mZ) (emlp one1),
            emlp (.ipos (.succ (.var "m"))),
            apps congD.ref [PE, PE,
              .lam "h" (cmpE (.var "h") (emlp one1)),
              congTo (iLoop mZ), emlp mZ, .var "ih"],
            apps symmD.ref [PE, emlp (.ipos (.succ (.var "m"))),
              cmpE (emlp mZ) (emlp one1),
              apps emloopCompD.ref [.int, addD.ref, mZ, one1]]]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path PE (congTo (iLoop (.inegsuc (.var "k2"))))
          (emlp (.inegsuc (.var "k2"))))
        (apps transD.ref [PE,
          cmpE (apps reflD.ref [emZ, .embase]) em1i,
          em1i,
          emlp (.inegsuc .zero),
          apps transReflLD.ref [emZ, .embase, .embase, em1i],
          apps symmD.ref [PE, emlp (.inegsuc .zero), em1i, emNegOneD.ref]])
        (lams ["m", "ih"] (
          let mZ : Raw := .inegsuc (.var "m")
          apps transD.ref [PE,
            cmpE (congTo (iLoop mZ)) em1i,
            cmpE (emlp mZ) em1i,
            emlp (.inegsuc (.succ (.var "m"))),
            apps congD.ref [PE, PE,
              .lam "h" (cmpE (.var "h") em1i),
              congTo (iLoop mZ), emlp mZ, .var "ih"],
            apps transD.ref [PE,
              cmpE (emlp mZ) em1i,
              cmpE (emlp mZ) (emlp (.inegsuc .zero)),
              emlp (.inegsuc (.succ (.var "m"))),
              apps congD.ref [PE, PE,
                .lam "h" (cmpE (emlp mZ) (.var "h")),
                em1i, emlp (.inegsuc .zero),
                apps symmD.ref [PE, emlp (.inegsuc .zero), em1i,
                  emNegOneD.ref]],
              apps symmD.ref [PE, emlp (.inegsuc (.succ (.var "m"))),
                cmpE (emlp mZ) (emlp (.inegsuc .zero)),
                apps emloopCompD.ref [.int, addD.ref, mZ,
                  .inegsuc .zero]]]]))
        (.var "n")))
      (.var "z"))

#guard invUniqueD.ok
private def fromA : Raw := fromEMD.ref
private def addTm : Raw := addD.ref
private def motAt (y : Raw) : Raw :=
  .path emZ (.app toA (.app fromA y)) y
private def reflEm : Raw := .plam "i0" .embase

/-- EM-side round trip, by the dependent eliminator: the loop cells are
`toIntLoop` read as paths-over; the composition cells live in a family
of sets and are discharged by `isPropPathPSet`. -/
def toFromD : LibDef where
  name := "toFrom"
  ty := .pi "y" emZ (.path emZ
    (.app toA (.app fromA (.var "y"))) (.var "y"))
  tm :=
    let lcell : Raw := .lam "z" (.plam "i" (.plam "j" (.papp
      (.papp (.app toIntLoopD.ref (.var "z"))
        (congTo (iLoop (.var "z"))) (emlp (.var "z")) (.var "j"))
      .embase .embase (.var "i"))))
    let lTy : Raw := .pi "z0" .int (.pathP "i3"
      (motAt (.emloop (.var "z0") (.var "i3"))) reflEm reflEm)
    let lAnn : Raw := .ann lcell lTy
    let Lof (jE : Raw) : Raw := .pathP "i2"
      (motAt (.emcomp addTm (.var "g") (.var "h") jE (.var "i2")))
      reflEm
      (.papp (.app lAnn (.var "h")) reflEm reflEm jE)
    let msetFam : Raw := .lam "x0" (apps isGpdEMD.ref
      [.int, addTm, .app toA (.app fromA (.var "x0")), .var "x0"])
    let gh : Raw := apps addTm [.var "g", .var "h"]
    let ccell : Raw :=
      let line : Raw := .plam "j0" (Lof (.var "j0"))
      lams ["g", "h"] (apps toPathPD.ref
        [Lof .i0, Lof .i1, line,
         .app lAnn (.var "g"), .app lAnn gh,
         apps isPropPathPSetD.ref
           [emZ, .lam "x0" (motAt (.var "x0")), msetFam,
            .embase, reflEm, .embase, emlp gh, reflEm,
            apps transportD.ref [Lof .i0, Lof .i1, line,
              .app lAnn (.var "g")],
            .app lAnn gh]])
    .lam "y" (.em1elim "y2" (motAt (.var "y2"))
      (.lam "y2" (apps isSetToGpdD.ref
        [motAt (.var "y2"),
         apps isGpdEMD.ref [.int, addTm,
           .app toA (.app fromA (.var "y2")), .var "y2"]]))
      reflEm lcell ccell (.var "y"))

/-- **`S¹ ≃ K(ℤ,1)`** — the two circles are one. -/
def s1EquivEMD : LibDef where
  name := "s1EquivEM"
  ty := equivR .s1 emZ
  tm := apps isoToEquivD.ref
    [.s1, emZ, toA, fromA, toFromD.ref, fromToD.ref]

/-- `S¹ ≡ K(ℤ,1)` in the universe. -/
def s1IsEMD : LibDef where
  name := "s1IsEM"
  ty := .path .univ .s1 emZ
  tm := apps uaD.ref [.s1, emZ, s1EquivEMD.ref]

-- toFrom / s1EquivEM / s1IsEM: checked natively (Test/CircleEM)

/-! ## Dimension-1 homotopy hypothesis: the counit

For any pointed 1-type `(A, a)` the loop space `Ω(A,a)` is a group —
every group law is one of the *untruncated* coherence cells of
LibCoherence, no truncation hypotheses beyond `isGpd A` (used only for
set-ness of `Ω`).  `K(Ω(A,a),1)` then maps to `A` by `em1rec` with the
*identity* loop map, whose composition cell is precisely the composition
filler `transFill`.  On loops the realization computes to the identity
definitionally. -/

/-- **The loop group of a pointed 1-type.** -/
def loopGroupD : LibDef where
  name := "loopGroup"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") groupTy))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let O : Raw := .path A a a
    let tr (x y : Raw) : Raw := apps transD.ref [A, a, a, a, x, y]
    let rfla : Raw := apps reflD.ref [A, a]
    lams ["A", "gA", "a"]
      (.pair O
      (.pair (lams ["p", "q"] (tr (.var "p") (.var "q")))
      (.pair rfla
      (.pair (.lam "p" (apps symmD.ref [A, a, a, .var "p"]))
      (.pair (lams ["p", "q", "r"]
        (apps symmD.ref [O,
          tr (.var "p") (tr (.var "q") (.var "r")),
          tr (tr (.var "p") (.var "q")) (.var "r"),
          apps assocConnD.ref [A, a, a, a, a,
            .var "p", .var "q", .var "r"]]))
      (.pair (.lam "p" (apps transReflLD.ref [A, a, a, .var "p"]))
      (.pair (.lam "p" (apps transReflRD.ref [A, a, a, .var "p"]))
      (.pair (.lam "p" (apps cancelLD.ref [A, a, a, .var "p"]))
      (.pair (.lam "p" (apps cancelLD.ref [A, a, a,
        apps symmD.ref [A, a, a, .var "p"]]))
        (lams ["xs", "ys", "us", "vs"]
          (apps (.var "gA") [a, a, .var "xs", .var "ys",
            .var "us", .var "vs"])))))))))))

#guard loopGroupD.ok

/-- **The realization map `K(Ω(A,a),1) → A`**: `em1rec` with the
identity loop map; the composition cell is `transFill`. -/
def loopRecD : LibDef where
  name := "loopRec"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let O : Raw := .path A a a
    let mul : Raw := lams ["p", "q"]
      (apps transD.ref [A, a, a, a, .var "p", .var "q"])
    .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
      (.pi "a" (.var "A") (.arr (.em1 O mul) A)))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    lams ["A", "gA", "a"]
      (.lam "t" (.em1rec A (.var "gA") a
        (.lam "p" (.var "p"))
        (lams ["p", "q"]
          (apps transFillD.ref [A, a, a, a, .var "p", .var "q"]))
        (.var "t")))

#guard loopRecD.ok

/-- **The realization computes on loops**: `cong (loopRec) (emloop p) ≡ p`
— definitionally (`refl` proof). -/
def loopRecLoopD : LibDef where
  name := "loopRecLoop"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let O : Raw := .path A a a
    let mul : Raw := lams ["p", "q"]
      (apps transD.ref [A, a, a, a, .var "p", .var "q"])
    let emT : Raw := .em1 O mul
    let f : Raw := apps loopRecD.ref [A, .var "gA", a]
    .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
      (.pi "a" (.var "A") (.pi "p" O
        (.path O
          (apps congD.ref [emT, A, f, .embase, .embase,
            apps emloopD.ref [O, mul, .var "p"]])
          (.var "p")))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    lams ["A", "gA", "a", "p"]
      (apps reflD.ref [.path A a a, .var "p"])

#guard loopRecLoopD.ok

/-! ## Connectedness

`isConn (X, x₀) := Π x. ∥ x₀ = x ∥`.  `K(C,m)` and `S¹` are connected:
eliminate into the propositional family `∥ base = t ∥` — the loop cell is
the generic `propFill`, and (for `em1elim`) the 2-cell obligation is the
standard `toPathP` + `isPropPathPSet` discharge. -/

/-- Pointed connectedness, as a `Raw`-level abbreviation. -/
def isConnR (X x0 : Raw) : Raw :=
  .pi "xc" X (.trunc (.path X x0 (.var "xc")))

/-- Propositions are sets (the four-tube square). -/
def propToSetD : LibDef where
  name := "propToSet"
  ty := .pi "P" .univ (.arr (isPropR (.var "P")) (isSetR (.var "P")))
  tm :=
    let P : Raw := .var "P"
    let h (x y k : Raw) : Raw :=
      .papp (apps (.var "hP") [x, y]) x y k
    let xs : Raw := .var "xs"
    let ys : Raw := .var "ys"
    let pj : Raw := .papp (.var "pp") xs ys (.var "j")
    let qj : Raw := .papp (.var "qq") xs ys (.var "j")
    lams ["P", "hP", "xs", "ys", "pp", "qq"]
      (.plam "i" (.plam "j" (.hcomp "k" P
        [([(.var "i", false)], h xs pj (.var "k")),
         ([(.var "i", true)], h xs qj (.var "k")),
         ([(.var "j", false)], h xs xs (.var "k")),
         ([(.var "j", true)], h xs ys (.var "k"))]
        xs)))

#guard propToSetD.ok

/-- **`K(C,m)` is connected** (no group laws needed). -/
def emConnD : LibDef where
  name := "emConn"
  ty := .pi "C" .univ
    (.pi "m" (.arr (.var "C") (.arr (.var "C") (.var "C")))
      (isConnR (.em1 (.var "C") (.var "m")) .embase))
  tm :=
    let C : Raw := .var "C"
    let mTm : Raw := .var "m"
    let emT : Raw := .em1 C mTm
    let motAt (t : Raw) : Raw := .trunc (.path emT .embase t)
    let famLam : Raw := .lam "x0" (motAt (.var "x0"))
    let ipAt (t : Raw) : Raw := .app isPropTruncD.ref (.path emT .embase t)
    let ipFam : Raw := .lam "x0" (ipAt (.var "x0"))
    let b : Raw := .tin (apps reflD.ref [emT, .embase])
    let emlpOf (g : Raw) : Raw := apps emloopD.ref [C, mTm, g]
    let lcellRaw : Raw := .lam "g" (apps propFillD.ref
      [emT, famLam, ipFam, .embase, .embase, emlpOf (.var "g"), b, b])
    let lTy : Raw := .pi "z0" C (.pathP "i3"
      (motAt (.emloop (.var "z0") (.var "i3"))) b b)
    let lAnn : Raw := .ann lcellRaw lTy
    let gh : Raw := .app (.app mTm (.var "g")) (.var "h")
    let Lof (jE : Raw) : Raw := .pathP "i2"
      (motAt (.emcomp mTm (.var "g") (.var "h") jE (.var "i2")))
      b
      (.papp (.app lAnn (.var "h")) b b jE)
    let msetFam : Raw := .lam "x0" (apps propToSetD.ref
      [motAt (.var "x0"), ipAt (.var "x0")])
    let ccell : Raw :=
      let line : Raw := .plam "j0" (Lof (.var "j0"))
      lams ["g", "h"] (apps toPathPD.ref
        [Lof .i0, Lof .i1, line,
         .app lAnn (.var "g"), .app lAnn gh,
         apps isPropPathPSetD.ref
           [emT, famLam, msetFam,
            .embase, b, .embase, emlpOf gh, b,
            apps transportD.ref [Lof .i0, Lof .i1, line,
              .app lAnn (.var "g")],
            .app lAnn gh]])
    lams ["C", "m"]
      (.lam "xc" (.em1elim "y2" (motAt (.var "y2"))
        (.lam "y2" (apps isSetToGpdD.ref
          [motAt (.var "y2"),
           apps propToSetD.ref [motAt (.var "y2"), ipAt (.var "y2")]]))
        b lcellRaw ccell (.var "xc")))

#guard emConnD.ok

/-- **`S¹` is connected**. -/
def s1ConnD : LibDef where
  name := "s1Conn"
  ty := isConnR .s1 .sbase
  tm :=
    let motAt (t : Raw) : Raw := .trunc (.path .s1 .sbase t)
    let famLam : Raw := .lam "x0" (motAt (.var "x0"))
    let ipFam : Raw := .lam "x0"
      (.app isPropTruncD.ref (.path .s1 .sbase (.var "x0")))
    let b : Raw := .tin (apps reflD.ref [.s1, .sbase])
    let loopP : Raw := .plam "i0" (.sloop (.var "i0"))
    .lam "xc" (.s1elim "x2" (motAt (.var "x2")) b
      (apps propFillD.ref
        [.s1, famLam, ipFam, .sbase, .sbase, loopP, b, b])
      (.var "xc"))

#guard s1ConnD.ok

/-! ## Dimension-1 homotopy hypothesis: the loop equivalence

`cong loopRec : Ω K(Ω A,1) → Ω A` is an equivalence: it agrees with
`encodeEM` (2-step chain through `decodeEncodeEM`, using that `decodeEM`
at `embase` *is* `emloop` definitionally and `loopRecLoop` is `refl`),
so `emloop`/`decode` is its two-sided inverse. -/

namespace HH1

/-- Common context pieces (functions of the ambient vars A gA a). -/
def O : Raw := .path (.var "A") (.var "a") (.var "a")
def mulT : Raw := lams ["p", "q"]
  (apps transD.ref [.var "A", .var "a", .var "a", .var "a",
    .var "p", .var "q"])
def emT : Raw := .em1 O mulT
def G : Raw := apps loopGroupD.ref [.var "A", .var "gA", .var "a"]
def fmap : Raw := apps loopRecD.ref [.var "A", .var "gA", .var "a"]
def OK : Raw := .path emT .embase .embase
def cf (q : Raw) : Raw :=
  apps congD.ref [emT, .var "A", fmap, .embase, .embase, q]
def enc (q : Raw) : Raw := apps encodeEMD.ref [G, .embase, q]
def dec (z : Raw) : Raw := apps decodeEMD.ref [G, .embase, z]

end HH1

/-- `cong loopRec ≡ encodeEM` on loops. -/
def loopRecCongEncD : LibDef where
  name := "loopRecCongEnc"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "q" HH1.OK
      (.path HH1.O (HH1.cf (.var "q")) (HH1.enc (.var "q"))))))
  tm :=
    let q : Raw := .var "q"
    lams ["A", "gA", "a", "q"]
      (apps transD.ref [HH1.O,
        HH1.cf q, HH1.cf (HH1.dec (HH1.enc q)), HH1.enc q,
        apps congD.ref [HH1.OK, HH1.O,
          .lam "h" (HH1.cf (.var "h")),
          q, HH1.dec (HH1.enc q),
          apps symmD.ref [HH1.OK, HH1.dec (HH1.enc q), q,
            apps decodeEncodeEMD.ref [HH1.G, .embase, q]]],
        apps loopRecLoopD.ref [.var "A", .var "gA", .var "a",
          HH1.enc q]])

-- #guard loopRecCongEncD.ok -- checked natively (Test/HH1)

/-- Retraction: `decode (cong loopRec q) ≡ q`. -/
def loopRecRetrD : LibDef where
  name := "loopRecRetr"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "q" HH1.OK
      (.path HH1.OK (HH1.dec (HH1.cf (.var "q"))) (.var "q")))))
  tm :=
    let q : Raw := .var "q"
    lams ["A", "gA", "a", "q"]
      (apps transD.ref [HH1.OK,
        HH1.dec (HH1.cf q), HH1.dec (HH1.enc q), q,
        apps congD.ref [HH1.O, HH1.OK,
          .lam "h" (HH1.dec (.var "h")),
          HH1.cf q, HH1.enc q,
          apps loopRecCongEncD.ref [.var "A", .var "gA", .var "a", q]],
        apps decodeEncodeEMD.ref [HH1.G, .embase, q]])

-- #guard loopRecRetrD.ok -- checked natively (Test/HH1)

/-- **`Ω K(ΩA,1) ≃ ΩA`, via `cong loopRec`.** -/
def loopRecOmegaEquivD : LibDef where
  name := "loopRecOmegaEquiv"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (equivR HH1.OK HH1.O)))
  tm :=
    lams ["A", "gA", "a"]
      (apps isoToEquivD.ref
        [HH1.OK, HH1.O,
         .lam "q" (HH1.cf (.var "q")),
         .lam "z" (HH1.dec (.var "z")),
         .lam "z" (apps loopRecLoopD.ref
           [.var "A", .var "gA", .var "a", .var "z"]),
         .lam "q" (apps loopRecRetrD.ref
           [.var "A", .var "gA", .var "a", .var "q"])])

-- #guard loopRecOmegaEquivD.ok -- checked natively (Test/HH1)

namespace HH1

/-- `cong loopRec` at a general endpoint `t`. -/
def cft (t q : Raw) : Raw :=
  apps congD.ref [emT, .var "A", fmap, .embase, t, q]
/-- The isEquiv predicate of `cong loopRec` at `t`. -/
def congEquivPred (t : Raw) : Raw :=
  .pi "yb" (.path (.var "A") (.var "a") (.app fmap t))
    (isContrR (fiberR (.path emT .embase t)
      (.path (.var "A") (.var "a") (.app fmap t))
      (.lam "q0" (cft t (.var "q0"))) (.var "yb")))

end HH1

/-- `cong loopRec` is an equivalence at *every* endpoint: transport the
basepoint case along `emConn` (the predicate is a proposition). -/
def loopRecCongAllD : LibDef where
  name := "loopRecCongAll"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "t" HH1.emT
      (HH1.congEquivPred (.var "t")))))
  tm :=
    let t : Raw := .var "t"
    let predAt (u : Raw) : Raw := HH1.congEquivPred u
    lams ["A", "gA", "a", "t"]
      (.truncrec (predAt t)
        (apps isPropIsEquivD.ref
          [.path HH1.emT .embase t,
           .path (.var "A") (.var "a") (.app HH1.fmap t),
           .lam "q0" (HH1.cft t (.var "q0"))])
        (.lam "pth" (apps transportD.ref
          [predAt .embase, predAt t,
           .plam "i0" (predAt (.papp (.var "pth") .embase t (.var "i0"))),
           .snd (apps loopRecOmegaEquivD.ref
             [.var "A", .var "gA", .var "a"])]))
        (.app (apps emConnD.ref [HH1.O, HH1.mulT]) t))

-- #guard loopRecCongAllD.ok -- checked natively (Test/HH1)

/-- **The basepoint fiber of `loopRec` is contractible** — the
contraction is a pair-path whose second component is the corrected
singular filler. -/
def loopRecFibBaseD : LibDef where
  name := "loopRecFibBase"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A")
      (isContrR (fiberR HH1.emT (.var "A") HH1.fmap (.var "a")))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let t : Raw := .fst (.var "s")
    let pfib : Raw := .snd (.var "s")
    let fT : Raw := .app HH1.fmap t
    let PA : Raw := .path A a fT
    let ctr : Raw := .fst (.app (.app
      (apps loopRecCongAllD.ref [A, .var "gA", a]) t) pfib)
    let q0 : Raw := .fst ctr
    let h0 : Raw := .snd ctr
    let hcell : Raw := apps symmD.ref [PA, pfib, HH1.cft t q0, h0]
    let w : Raw := .plam "j" (.hcomp "k" A
      [([(.var "i", false)], a),
       ([(.var "i", true)],
         .papp (.papp hcell (HH1.cft t q0) pfib (.var "k"))
           a fT (.var "j")),
       ([(.var "j", false)], a),
       ([(.var "j", true)], .app HH1.fmap (.papp q0 .embase t (.var "i")))]
      (.papp (HH1.cft t q0) a fT (.imin (.var "i") (.var "j"))))
    lams ["A", "gA", "a"]
      (.pair (.pair .embase (apps reflD.ref [A, a]))
        (.lam "s" (.plam "i"
          (.pair (.papp q0 .embase t (.var "i")) w))))

-- #guard loopRecFibBaseD.ok -- checked natively (Test/HH1)

/-- **`loopRec` is an equivalence** for pointed *connected* 1-types. -/
def loopRecEquivD : LibDef where
  name := "loopRecEquiv"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "cA" (isConnR (.var "A") (.var "a"))
      (.pi "x" (.var "A")
        (isContrR (fiberR HH1.emT (.var "A") HH1.fmap (.var "x")))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let x : Raw := .var "x"
    let fibC (u : Raw) : Raw :=
      isContrR (fiberR HH1.emT A HH1.fmap u)
    lams ["A", "gA", "a", "cA", "x"]
      (.truncrec (fibC x)
        (apps isPropIsContrD.ref
          [fiberR HH1.emT A HH1.fmap x])
        (.lam "pth" (apps transportD.ref
          [fibC a, fibC x,
           .plam "i0" (fibC (.papp (.var "pth") a x (.var "i0"))),
           apps loopRecFibBaseD.ref [A, .var "gA", a]]))
        (.app (.var "cA") x))

-- #guard loopRecEquivD.ok -- checked natively (Test/HH1)

/-- **The dimension-1 homotopy hypothesis**: every pointed connected
1-type is a `K(G,1)` — `K(Ω(A,a),1) ≡ A` in the universe. -/
def homotopyHyp1D : LibDef where
  name := "homotopyHyp1"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A") (.pi "cA" (isConnR (.var "A") (.var "a"))
      (.path .univ HH1.emT (.var "A")))))
  tm :=
    let A : Raw := .var "A"
    lams ["A", "gA", "a", "cA"]
      (apps uaD.ref [HH1.emT, A,
        .pair HH1.fmap
          (.lam "x" (apps loopRecEquivD.ref
            [A, .var "gA", .var "a", .var "cA", .var "x"]))])

-- #guard homotopyHyp1D.ok -- checked natively (Test/HH1)

/-! ## Groupoid cells for the figure-eight decode square

(Placed here rather than in `LibWords` because they use the untruncated
coherence cells of `LibCoherence`.) -/

private def w8CT : Raw := wedge .s1 .s1 .sbase .sbase
private def w8CbaseT : Raw := .pinl .sbase
private def omega8CT : Raw := .path w8CT w8CbaseT w8CbaseT
private def reflW8C : Raw := apps reflD.ref [w8CT, w8CbaseT]
private def pushPCT : Raw := .plam "i"
  (.ppush (.lam "u0" .sbase) (.lam "u0" .sbase) .tt (.var "i"))
private def pinrBaseCT : Raw := .pinr .sbase

/-- `(P ⬝ q₁) ⬝ q₂ ≡ P` from `q₁ ⬝ q₂ ≡ refl`. -/
def cancelViaD : LibDef where
  name := "cancelVia"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let t3 (x y z pp qq : Raw) : Raw := apps transD.ref [A, x, y, z, pp, qq]
    .pi "A" .univ (.pi "a" A (.pi "b" A
      (.pi "P" (.path A a b)
      (.pi "q1" (.path A b b) (.pi "q2" (.path A b b)
      (.arr (.path (.path A b b)
          (t3 b b b (.var "q1") (.var "q2")) (apps reflD.ref [A, b]))
        (.path (.path A a b)
          (t3 a b b (t3 a b b (.var "P") (.var "q1")) (.var "q2"))
          (.var "P"))))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let b : Raw := .var "b"
    let P : Raw := .var "P"
    let q1 : Raw := .var "q1"
    let q2 : Raw := .var "q2"
    let PT : Raw := .path A a b
    let rb : Raw := apps reflD.ref [A, b]
    let t3 (x y z pp qq : Raw) : Raw := apps transD.ref [A, x, y, z, pp, qq]
    lams ["A", "a", "b", "P", "q1", "q2", "h"]
      (apps transD.ref [PT,
        t3 a b b (t3 a b b P q1) q2,
        t3 a b b P (t3 b b b q1 q2), P,
        apps symmD.ref [PT,
          t3 a b b P (t3 b b b q1 q2),
          t3 a b b (t3 a b b P q1) q2,
          apps assocConnD.ref [A, a, b, b, b, P, q1, q2]],
        apps transD.ref [PT,
          t3 a b b P (t3 b b b q1 q2), t3 a b b P rb, P,
          apps congD.ref [.path A b b, PT,
            .lam "h2" (t3 a b b P (.var "h2")),
            t3 b b b q1 q2, rb, .var "h"],
          apps transReflRD.ref [A, a, b, P]]])

#guard cancelViaD.ok

/-- Conjugation cancels:
`((u⬝p)⬝u⁻¹) ⬝ ((u⬝q)⬝u⁻¹) ≡ refl` from `p⬝q ≡ refl`. -/
def conjCancelGenD : LibDef where
  name := "conjCancelGen"
  ty :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let x : Raw := .var "x"
    let u : Raw := .var "u"
    let t3 (x1 y z pp qq : Raw) : Raw := apps transD.ref [A, x1, y, z, pp, qq]
    let ui : Raw := apps symmD.ref [A, a, x, u]
    let conj (m : Raw) : Raw := t3 a x a (t3 a x x u m) ui
    .pi "A" .univ (.pi "a" A (.pi "x" A
      (.pi "u" (.path A a x)
      (.pi "p" (.path A x x) (.pi "q" (.path A x x)
      (.arr (.path (.path A x x)
          (t3 x x x (.var "p") (.var "q")) (apps reflD.ref [A, x]))
        (.path (.path A a a)
          (t3 a a a (conj (.var "p")) (conj (.var "q")))
          (apps reflD.ref [A, a]))))))))
  tm :=
    let A : Raw := .var "A"
    let a : Raw := .var "a"
    let x : Raw := .var "x"
    let u : Raw := .var "u"
    let p : Raw := .var "p"
    let q : Raw := .var "q"
    let t3 (x1 y z pp qq : Raw) : Raw := apps transD.ref [A, x1, y, z, pp, qq]
    let ui : Raw := apps symmD.ref [A, a, x, u]
    let up : Raw := t3 a x x u p
    let uq : Raw := t3 a x x u q
    let cp : Raw := t3 a x a up ui
    let cq : Raw := t3 a x a uq ui
    let ra : Raw := apps reflD.ref [A, a]
    let rx : Raw := apps reflD.ref [A, x]
    let O : Raw := .path A a a
    let AX : Raw := .path A a x
    let qui : Raw := t3 x x a q ui
    let pq : Raw := t3 x x x p q
    let X1 : Raw := t3 a a a cp cq
    let X2 : Raw := t3 a a a cp (t3 a x a u qui)
    let X3 : Raw := t3 a x a (t3 a a x cp u) qui
    let X4 : Raw := t3 a x a up qui
    let X5 : Raw := t3 a x a (t3 a x x up q) ui
    let X6 : Raw := t3 a x a (t3 a x x u pq) ui
    let X7 : Raw := t3 a x a (t3 a x x u rx) ui
    let X8 : Raw := t3 a x a u ui
    let whiskLcp (Y Z e : Raw) : Raw := apps congD.ref [O, O,
      .lam "h9" (t3 a a a cp (.var "h9")), Y, Z, e]
    let whiskRqui (Y Z e : Raw) : Raw := apps congD.ref [AX, O,
      .lam "h9" (t3 a x a (.var "h9") qui), Y, Z, e]
    let whiskRui (Y Z e : Raw) : Raw := apps congD.ref [AX, O,
      .lam "h9" (t3 a x a (.var "h9") ui), Y, Z, e]
    let m1 : Raw := whiskLcp cq (t3 a x a u qui)
      (apps symmD.ref [O, t3 a x a u qui, cq,
        apps assocConnD.ref [A, a, x, x, a, u, q, ui]])
    let m2 : Raw := apps assocConnD.ref [A, a, a, x, a, cp, u, qui]
    let m3 : Raw := whiskRqui (t3 a a x cp u) up
      (apps cancelRD.ref [A, a, x, a, up, u])
    let m4 : Raw := apps assocConnD.ref [A, a, x, x, a, up, q, ui]
    let m5 : Raw := whiskRui (t3 a x x up q) (t3 a x x u pq)
      (apps symmD.ref [AX, t3 a x x u pq, t3 a x x up q,
        apps assocConnD.ref [A, a, x, x, x, u, p, q]])
    let m6 : Raw := whiskRui (t3 a x x u pq) (t3 a x x u rx)
      (apps congD.ref [.path A x x, AX,
        .lam "h9" (t3 a x x u (.var "h9")), pq, rx, .var "h"])
    let m7 : Raw := whiskRui (t3 a x x u rx) u
      (apps transReflRD.ref [A, a, x, u])
    let m8 : Raw := apps cancelLD.ref [A, a, x, ui]
    let steps : List (Raw × Raw × Raw) :=
      [(X1, X2, m1), (X2, X3, m2), (X3, X4, m3), (X4, X5, m4),
       (X5, X6, m5), (X6, X7, m6), (X7, X8, m7)]
    lams ["A", "a", "x", "u", "p", "q", "h"]
      (steps.foldr
        (fun (st : Raw × Raw × Raw) (acc : Raw) =>
          apps transD.ref [O, st.1, st.2.1, ra, st.2.2, acc])
        m8)

#guard conjCancelGenD.ok

/-- **Generator cancellation, all four letters**. -/
def gcancelD : LibDef where
  name := "gcancel"
  ty :=
    let gl (l : Raw) : Raw := .app genLoopD.ref l
    let nb (b : Raw) : Raw := .app notBoolD.ref b
    .pi "b1" boolTy (.pi "b2" boolTy
      (.path omega8CT
        (apps transD.ref [w8CT, w8CbaseT, w8CbaseT, w8CbaseT,
          gl (.pair (.var "b1") (nb (.var "b2"))),
          gl (.pair (.var "b1") (.var "b2"))])
        reflW8C))
  tm :=
    let gl (l : Raw) : Raw := .app genLoopD.ref l
    let nb (b : Raw) : Raw := .app notBoolD.ref b
    let goal (k1 k2 : Raw) : Raw := .path omega8CT
      (apps transD.ref [w8CT, w8CbaseT, w8CbaseT, w8CbaseT,
        gl (.pair k1 (nb k2)), gl (.pair k1 k2)])
      reflW8C
    let loopL : Raw := .plam "i" (.pinl (.sloop (.var "i")))
    let loopLinv : Raw := .plam "i" (.pinl (.sloop (.ineg (.var "i"))))
    let rloop : Raw := .plam "i" (.pinr (.sloop (.var "i")))
    let rloopInv : Raw := .plam "i" (.pinr (.sloop (.ineg (.var "i"))))
    lams ["b1", "b2"]
      (.sumcase "k1" (goal (.var "k1") (.var "b2"))
        (.lam "u1" (.sumcase "k2" (goal trueR (.var "k2"))
          (.lam "u2" (apps cancelLD.ref
            [w8CT, w8CbaseT, w8CbaseT, loopL]))
          (.lam "u2" (apps cancelLD.ref
            [w8CT, w8CbaseT, w8CbaseT, loopLinv]))
          (.var "b2")))
        (.lam "u1" (.sumcase "k2" (goal falseR (.var "k2"))
          (.lam "u2" (apps conjCancelGenD.ref
            [w8CT, w8CbaseT, pinrBaseCT, pushPCT, rloopInv, rloop,
             apps cancelLD.ref [w8CT, pinrBaseCT, pinrBaseCT, rloop]]))
          (.lam "u2" (apps conjCancelGenD.ref
            [w8CT, w8CbaseT, pinrBaseCT, pushPCT, rloop, rloopInv,
             apps cancelLD.ref [w8CT, pinrBaseCT, pinrBaseCT, rloopInv]]))
          (.var "b2")))
        (.var "b1"))

#guard gcancelD.ok

/-! ## The decode homomorphism equation

`decodeWord (consG g s) ≡ decodeWord s ⬝ genLoop g` — the bridge lemma
for both round trips of `π₁(S¹∨S¹) = F₂`.  Proved against `consStep`'s
`(b, e)`-parametric structure, so the proof's `sumcase` reduces in step
with `consStep`'s own: the non-cancelling branch is definitional, the
cancelling branch is `cancelVia` ∘ `gcancel` after rewriting the head
letter along `cancelsCharac`. -/

private def glC (l : Raw) : Raw := .app genLoopD.ref l
private def dwC (w : Raw) : Raw := .app decodeWordD.ref w
private def t8 (p q : Raw) : Raw :=
  apps transD.ref [w8CT, w8CbaseT, w8CbaseT, w8CbaseT, p, q]

def decodeConsStepD : LibDef where
  name := "decodeConsStep"
  ty :=
    let g : Raw := .var "g"
    let h : Raw := .var "h"
    let t : Raw := .var "t"
    let rhs : Raw := t8 (dwC (.lcons h t)) (glC g)
    .pi "g" letterTy (.pi "h" letterTy (.pi "t" wordTy
      (.pi "rt" (.app isTrueD.ref (apps redAuxD.ref [t, .inr h]))
      (.pi "b" boolTy
        (.pi "e2" (.path boolTy (apps cancelsD.ref [g, h]) (.var "b"))
          (.path omega8CT
            (dwC (.fst (apps consStepD.ref
              [g, h, t, .var "rt", .var "b", .var "e2"])))
            rhs))))))
  tm :=
    let g : Raw := .var "g"
    let h : Raw := .var "h"
    let t : Raw := .var "t"
    let rhs : Raw := t8 (dwC (.lcons h t)) (glC g)
    let cgh : Raw := apps cancelsD.ref [g, h]
    let invg : Raw := .app invLetD.ref g
    -- cancelling branch: (dw t ⬝ gl h) ⬝ gl g  ≡  dw t
    let charac (w : Raw) : Raw := apps cancelsCharacD.ref [g, h, w]
    let congCell (w : Raw) : Raw := apps congD.ref [letterTy, omega8CT,
      .lam "h2" (t8 (t8 (dwC t) (glC (.var "h2"))) (glC g)),
      h, invg, charac w]
    let viaCell : Raw := apps cancelViaD.ref
      [w8CT, w8CbaseT, w8CbaseT, dwC t, glC invg, glC g,
       apps gcancelD.ref [.fst g, .snd g]]
    let fwd (w : Raw) : Raw := apps transD.ref [omega8CT,
      rhs, t8 (t8 (dwC t) (glC invg)) (glC g), dwC t,
      congCell w, viaCell]
    let istrWitness : Raw := apps substD.ref [boolTy,
      .lam "b2" (.app isTrueD.ref (.var "b2")),
      .inl (.var "u"), cgh,
      apps symmD.ref [boolTy, cgh, .inl (.var "u"), .var "e2"],
      .tt]
    lams ["g", "h", "t", "rt", "b"]
      (.sumcase "k"
        (.pi "e2" (.path boolTy cgh (.var "k"))
          (.path omega8CT
            (dwC (.fst (apps consStepD.ref
              [g, h, t, .var "rt", .var "k", .var "e2"])))
            rhs))
        (.lam "u" (.lam "e2"
          (apps symmD.ref [omega8CT, rhs, dwC t, fwd istrWitness])))
        (.lam "u" (.lam "e2"
          (apps reflD.ref [omega8CT, rhs])))
        (.var "b"))

#guard decodeConsStepD.ok

/-- **`decode` is a homomorphism**:
`decodeWord (consG g s) ≡ decodeWord s ⬝ genLoop g`. -/
def decodeConsD : LibDef where
  name := "decodeCons"
  ty := .pi "g" letterTy (.pi "s" f2Ty
    (.path omega8CT
      (dwC (.fst (apps consGD.ref [.var "g", .var "s"])))
      (t8 (dwC (.fst (.var "s"))) (glC (.var "g")))))
  tm :=
    let g : Raw := .var "g"
    let goal (w r : Raw) : Raw := .path omega8CT
      (dwC (.fst (apps consGD.ref [g, .pair w r])))
      (t8 (dwC w) (glC g))
    lams ["g", "s"]
      (.app
        (.listrec "k"
          (.pi "r" (.app isTrueD.ref
            (apps redAuxD.ref [.var "k", .inl .tt]))
            (goal (.var "k") (.var "r")))
          (.lam "r" (apps reflD.ref [omega8CT,
            t8 (dwC .lnil) (glC g)]))
          (lams ["h", "t", "ih"] (.lam "r"
            (apps decodeConsStepD.ref
              [g, .var "h", .var "t", .var "r",
               apps cancelsD.ref [g, .var "h"],
               .plam "i" (apps cancelsD.ref [g, .var "h"])])))
          (.fst (.var "s")))
        (.snd (.var "s")))

#guard decodeConsD.ok

/-! ## The full decode family over the figure eight

Both circle cells reduce to `decodeCons` + cancellation: the kernel
computes the reverse `ua`-transport (`≐ consG (invLet g)`) and the
moving-endpoint path transport (`≐ right composition`) definitionally. -/

def decodeAllD : LibDef where
  name := "decodeAll"
  ty := .pi "x" w8CT (.arr (.app helixF2D.ref (.var "x"))
    (.path w8CT w8CbaseT (.var "x")))
  tm :=
    let hx (t : Raw) : Raw := .app helixF2D.ref t
    let pB (t : Raw) : Raw := .path w8CT w8CbaseT t
    let M (t : Raw) : Raw := .arr (hx t) (pB t)
    let t3w (x y z p q : Raw) : Raw := apps transD.ref [w8CT, x, y, z, p, q]
    let b0 : Raw := w8CbaseT
    let pinrB : Raw := pinrBaseCT
    let loopL : Raw := .plam "i" (.pinl (.sloop (.var "i")))
    let rloop : Raw := .plam "i" (.pinr (.sloop (.var "i")))
    let uP : Raw := pushPCT
    let decS (s : Raw) : Raw := dwC (.fst s)
    let sV : Raw := .var "s"
    -- ===== left circle =====
    let baseL : Raw := .lam "s" (decS sV)
    let lineL : Raw := .plam "i9" (M (.pinl (.sloop (.var "i9"))))
    let F0L : Raw := M (.pinl .sbase)
    let cgL : Raw := apps consGD.ref [letLinv, sV]
    let cellL : Raw := .lam "s"
      (apps transD.ref [omega8CT,
        t8 (dwC (.fst cgL)) loopL,
        t8 (t8 (decS sV) (glC letLinv)) loopL,
        decS sV,
        apps congD.ref [omega8CT, omega8CT,
          .lam "h9" (t8 (.var "h9") loopL),
          dwC (.fst cgL), t8 (decS sV) (glC letLinv),
          apps decodeConsD.ref [letLinv, sV]],
        apps cancelViaD.ref [w8CT, b0, b0,
          decS sV, glC letLinv, loopL,
          apps gcancelD.ref [trueR, trueR]]])
    let lcellL : Raw := apps toPathPD.ref
      [F0L, F0L, lineL, baseL, baseL,
       apps funExtD.ref [hx (.pinl .sbase), pB (.pinl .sbase),
         apps transportD.ref [F0L, F0L, lineL, baseL],
         baseL, cellL]]
    let lc : Raw := .lam "a" (.s1elim "a2" (M (.pinl (.var "a2")))
      baseL lcellL (.var "a"))
    -- ===== right circle =====
    let baseR : Raw := .lam "s" (t3w b0 b0 pinrB (decS sV) uP)
    let lineR : Raw := .plam "i9" (M (.pinr (.sloop (.var "i9"))))
    let F0R : Raw := M (.pinr .sbase)
    let cgR : Raw := apps consGD.ref [letRinv, sV]
    let P : Raw := decS sV
    let CC : Raw := glC letRinv
    let m9 : Raw := .plam "i" (.pinr (.sloop (.ineg (.var "i"))))
    let PBR : Raw := pB pinrB
    let um : Raw := t3w b0 pinrB pinrB uP m9
    let PC : Raw := t3w b0 b0 b0 P CC
    let Pu : Raw := t3w b0 b0 pinrB P uP
    let CCu : Raw := t3w b0 b0 pinrB CC uP
    let mr : Raw := t3w pinrB b0 pinrB m9 rloop
    let rfr : Raw := apps reflD.ref [w8CT, pinrB]
    let X1 : Raw := t3w b0 pinrB pinrB
      (t3w b0 b0 pinrB (dwC (.fst cgR)) uP) rloop
    let X2 : Raw := t3w b0 pinrB pinrB (t3w b0 b0 pinrB PC uP) rloop
    let X3 : Raw := t3w b0 pinrB pinrB (t3w b0 b0 pinrB P CCu) rloop
    let X4 : Raw := t3w b0 pinrB pinrB (t3w b0 b0 pinrB P um) rloop
    let X5 : Raw := t3w b0 pinrB pinrB (t3w b0 pinrB pinrB Pu m9) rloop
    let X6 : Raw := t3w b0 pinrB pinrB Pu mr
    let X7 : Raw := t3w b0 pinrB pinrB Pu rfr
    let X8 : Raw := Pu
    let whRr (Y Z e : Raw) : Raw := apps congD.ref [PBR, PBR,
      .lam "h9" (t3w b0 pinrB pinrB (.var "h9") rloop), Y, Z, e]
    let n1 : Raw := whRr (t3w b0 b0 pinrB (dwC (.fst cgR)) uP)
      (t3w b0 b0 pinrB PC uP)
      (apps congD.ref [omega8CT, PBR,
        .lam "h9" (t3w b0 b0 pinrB (.var "h9") uP),
        dwC (.fst cgR), PC,
        apps decodeConsD.ref [letRinv, sV]])
    let n2 : Raw := whRr (t3w b0 b0 pinrB PC uP) (t3w b0 b0 pinrB P CCu)
      (apps symmD.ref [PBR, t3w b0 b0 pinrB P CCu,
        t3w b0 b0 pinrB PC uP,
        apps assocConnD.ref [w8CT, b0, b0, b0, pinrB, P, CC, uP]])
    let n3 : Raw := whRr (t3w b0 b0 pinrB P CCu) (t3w b0 b0 pinrB P um)
      (apps congD.ref [PBR, PBR,
        .lam "h9" (t3w b0 b0 pinrB P (.var "h9")),
        CCu, um,
        apps cancelRD.ref [w8CT, b0, pinrB, b0, um, uP]])
    let n4 : Raw := whRr (t3w b0 b0 pinrB P um)
      (t3w b0 pinrB pinrB Pu m9)
      (apps assocConnD.ref [w8CT, b0, b0, pinrB, pinrB, P, uP, m9])
    let n5 : Raw := apps symmD.ref [PBR, X6, X5,
      apps assocConnD.ref [w8CT, b0, pinrB, pinrB, pinrB, Pu, m9, rloop]]
    let n6 : Raw := apps congD.ref [.path w8CT pinrB pinrB, PBR,
      .lam "h9" (t3w b0 pinrB pinrB Pu (.var "h9")),
      mr, rfr,
      apps cancelLD.ref [w8CT, pinrB, pinrB, rloop]]
    let n7 : Raw := apps transReflRD.ref [w8CT, b0, pinrB, Pu]
    let steps : List (Raw × Raw × Raw) :=
      [(X1, X2, n1), (X2, X3, n2), (X3, X4, n3), (X4, X5, n4),
       (X5, X6, n5), (X6, X7, n6)]
    let cellR : Raw := .lam "s"
      (steps.foldr
        (fun (st : Raw × Raw × Raw) (acc : Raw) =>
          apps transD.ref [PBR, st.1, st.2.1, X8, st.2.2, acc])
        n7)
    let lcellR : Raw := apps toPathPD.ref
      [F0R, F0R, lineR, baseR, baseR,
       apps funExtD.ref [hx (.pinr .sbase), pB (.pinr .sbase),
         apps transportD.ref [F0R, F0R, lineR, baseR],
         baseR, cellR]]
    let rc : Raw := .lam "a" (.s1elim "a2" (M (.pinr (.var "a2")))
      baseR lcellR (.var "a"))
    -- ===== the wedge path cell =====
    let cmap : Raw := .lam "u0" .sbase
    let lineP : Raw := .plam "i9"
      (M (.ppush cmap cmap (.var "u") (.var "i9")))
    let pcCell : Raw := .lam "u" (apps toPathPD.ref
      [M (.pinl .sbase), M (.pinr .sbase), lineP, baseL, baseR,
       apps funExtD.ref [hx (.pinr .sbase), pB (.pinr .sbase),
         apps transportD.ref [M (.pinl .sbase), M (.pinr .sbase),
           lineP, baseL],
         baseR,
         .lam "s" (apps reflD.ref [PBR,
           t3w b0 b0 pinrB (decS sV) uP])]])
    .lam "x" (.pushrec "k" (M (.var "k")) lc rc pcCell (.var "x"))

-- #guard decodeAllD.ok -- checked natively (Test/WedgeF2)

/-! ## decode ∘ encode ≡ id for the figure eight -/

private def nilF2C : Raw := .pair .lnil .tt

/-- Endpoint-generic winding (`windF2` for arbitrary target). -/
def windAllD : LibDef where
  name := "windAll"
  ty := .pi "x" w8CT (.arr (.path w8CT w8CbaseT (.var "x"))
    (.app helixF2D.ref (.var "x")))
  tm := lams ["x", "p"] (.transp "i"
    (.app helixF2D.ref
      (.papp (.var "p") w8CbaseT (.var "x") (.var "i")))
    nilF2C)

-- #guard windAllD.ok -- checked natively (Test/WedgeF2)

/-- **`decodeAll ∘ windAll ≡ id`** — winding is split-injective on all
path spaces of the figure eight.  By `J`; the `refl` case is
definitional (transport constancy + `decodeAll base nil ≐ refl`). -/
def decodeEncodeF2D : LibDef where
  name := "decodeEncodeF2"
  ty := .pi "x" w8CT
    (.pi "p" (.path w8CT w8CbaseT (.var "x"))
      (.path (.path w8CT w8CbaseT (.var "x"))
        (.app (.app decodeAllD.ref (.var "x"))
          (apps windAllD.ref [.var "x", .var "p"]))
        (.var "p")))
  tm :=
    let motive : Raw := lams ["x2", "p2"]
      (.path (.path w8CT w8CbaseT (.var "x2"))
        (.app (.app decodeAllD.ref (.var "x2"))
          (apps windAllD.ref [.var "x2", .var "p2"]))
        (.var "p2"))
    lams ["x", "p"] (apps jD.ref [w8CT, w8CbaseT, motive,
      apps reflD.ref [omega8CT, reflW8C],
      .var "x", .var "p"])

-- #guard decodeEncodeF2D.ok -- checked natively (Test/WedgeF2)

/-! ## Winding computes on generators; transport along composites -/

/-- **Transport along any generator loop is the `consG` action** — all
four letters, definitionally in each branch (the `transpGlue` machinery
computes even the conjugated right-circle composites). -/
def windGenD : LibDef where
  name := "windGen"
  ty :=
    let l (k1 k2 : Raw) : Raw := .pair k1 k2
    .pi "b1" boolTy (.pi "b2" boolTy (.pi "s" f2Ty
      (.path f2Ty
        (.transp "i" (.app helixF2D.ref
          (.papp (.app genLoopD.ref (l (.var "b1") (.var "b2")))
            w8CbaseT w8CbaseT (.var "i")))
          (.var "s"))
        (apps consGD.ref [l (.var "b1") (.var "b2"), .var "s"]))))
  tm :=
    let l (k1 k2 : Raw) : Raw := .pair k1 k2
    let goal (k1 k2 : Raw) : Raw := .path f2Ty
      (.transp "i" (.app helixF2D.ref
        (.papp (.app genLoopD.ref (l k1 k2))
          w8CbaseT w8CbaseT (.var "i")))
        (.var "s"))
      (apps consGD.ref [l k1 k2, .var "s"])
    let rfl (k1 k2 : Raw) : Raw :=
      apps reflD.ref [f2Ty, apps consGD.ref [l k1 k2, .var "s"]]
    lams ["b1", "b2", "s"]
      (.sumcase "k1" (goal (.var "k1") (.var "b2"))
        (.lam "u1" (.sumcase "k2" (goal trueR (.var "k2"))
          (.lam "u2" (rfl trueR trueR))
          (.lam "u2" (rfl trueR falseR))
          (.var "b2")))
        (.lam "u1" (.sumcase "k2" (goal falseR (.var "k2"))
          (.lam "u2" (rfl falseR trueR))
          (.lam "u2" (rfl falseR falseR))
          (.var "b2")))
        (.var "b1"))

-- #guard windGenD.ok -- checked natively (Test/WedgeF2)

/-- Transport in `helixF2` along a composite splits. -/
def transpCompW8D : LibDef where
  name := "transpCompW8"
  ty :=
    let hAt (t : Raw) : Raw := .app helixF2D.ref t
    let trW (pp qq : Raw) (yy zz : Raw) : Raw :=
      apps transD.ref [w8CT, w8CbaseT, yy, zz, pp, qq]
    .pi "y" w8CT (.pi "z" w8CT
      (.pi "p" (.path w8CT w8CbaseT (.var "y"))
      (.pi "q" (.path w8CT (.var "y") (.var "z"))
      (.pi "u" f2Ty
        (.path (hAt (.var "z"))
          (.transp "i" (hAt (.papp
            (trW (.var "p") (.var "q") (.var "y") (.var "z"))
            w8CbaseT (.var "z") (.var "i")))
            (.var "u"))
          (.transp "i" (hAt (.papp (.var "q") (.var "y") (.var "z")
              (.var "i")))
            (.transp "i" (hAt (.papp (.var "p") w8CbaseT (.var "y")
                (.var "i")))
              (.var "u"))))))))
  tm :=
    let hAt (t : Raw) : Raw := .app helixF2D.ref t
    let p : Raw := .var "p"
    let u : Raw := .var "u"
    let y : Raw := .var "y"
    let trW (pp qq : Raw) (yy zz : Raw) : Raw :=
      apps transD.ref [w8CT, w8CbaseT, yy, zz, pp, qq]
    let motive : Raw := lams ["z2", "q2"]
      (.path (hAt (.var "z2"))
        (.transp "i" (hAt (.papp
          (trW p (.var "q2") y (.var "z2"))
          w8CbaseT (.var "z2") (.var "i")))
          u)
        (.transp "i" (hAt (.papp (.var "q2") y (.var "z2") (.var "i")))
          (.transp "i" (hAt (.papp p w8CbaseT y (.var "i"))) u)))
    let prfl : Raw := trW p (apps reflD.ref [w8CT, y]) y y
    let dcase : Raw := apps congD.ref
      [.path w8CT w8CbaseT y, hAt y,
       .lam "r" (.transp "i" (hAt (.papp (.var "r") w8CbaseT y (.var "i")))
         u),
       prfl, p,
       apps transReflRD.ref [w8CT, w8CbaseT, y, p]]
    lams ["y", "z", "p", "q", "u"]
      (apps jD.ref [w8CT, y, motive, dcase, .var "z", .var "q"])

-- #guard transpCompW8D.ok -- checked natively (Test/WedgeF2)

/-! ## encode ∘ decode ≡ id, and the fundamental group of the figure
eight

`redW (g::w) ≐ redAux w (inr g)` definitionally (the head check against
`inl tt` computes to `true` and `and true x ≐ x`), so the reducedness of
a cons *is* the tail constraint. -/

private def istrC (b : Raw) : Raw := .app isTrueD.ref b
private def redAuxC (w prev : Raw) : Raw := apps redAuxD.ref [w, prev]
private def redWC (w : Raw) : Raw := redAuxC w (.inl .tt)
private def istrRedFam : Raw := .lam "w9" (istrC (redWC (.var "w9")))
private def istrRedProp : Raw := .lam "w9"
  (.app isPropIsTrueD.ref (redWC (.var "w9")))

/-- `consG` on a reduced cons does not cancel:
`consG g (w, _) ≡ (g::w, r)`. -/
def consGNoCancelD : LibDef where
  name := "consGNoCancel"
  ty := .pi "g" letterTy (.pi "w" wordTy
    (.pi "rgw" (istrC (redAuxC (.var "w") (.inr (.var "g"))))
      (.path f2Ty
        (apps consGD.ref [.var "g",
          .pair (.var "w")
            (apps redRelaxD.ref [.var "w", .inr (.var "g"), .var "rgw"])])
        (.pair (.lcons (.var "g") (.var "w")) (.var "rgw")))))
  tm :=
    let g : Raw := .var "g"
    let rgw : Raw := .var "rgw"
    let tailWit (w : Raw) : Raw :=
      apps redRelaxD.ref [w, .inr g, rgw]
    let goal (w : Raw) : Raw := .path f2Ty
      (apps consGD.ref [g, .pair w (tailWit w)])
      (.pair (.lcons g w) rgw)
    let sigEq (u v fp : Raw) : Raw := apps sigmaPropEqD.ref
      [wordTy, istrRedFam, istrRedProp, u, v, fp]
    lams ["g", "w"]
      (.app
        (.listrec "k"
          (.pi "rgw" (istrC (redAuxC (.var "k") (.inr g)))
            (goal (.var "k")))
          (.lam "rgw" (sigEq
            (.pair (.lcons g .lnil) .tt)
            (.pair (.lcons g .lnil) rgw)
            (apps reflD.ref [wordTy, .lcons g .lnil])))
          (lams ["h2", "t2", "ih"] (.lam "rgw"
            (let h2 : Raw := .var "h2"
             let t2 : Raw := .var "t2"
             let cgh : Raw := apps cancelsD.ref [g, h2]
             let w2 : Raw := .lcons h2 t2
             let eFalse : Raw := apps notTrueFalseD.ref [cgh,
               apps andElimLD.ref
                 [.app notBoolD.ref cgh, redAuxC t2 (.inr h2), rgw]]
             -- fst of the consStep result, at any (b, e); at b = false it
             -- is g::h2::t2 by reduction
             let fstFam : Raw := .lam "b2"
               (.pi "e3" (.path boolTy cgh (.var "b2"))
                 (.path wordTy
                   (.fst (apps consStepD.ref
                     [g, h2, t2,
                      apps redRelaxD.ref [w2, .inr g, rgw],
                      .var "b2", .var "e3"]))
                   (.lcons g w2)))
             let atFalse : Raw := .lam "e3"
               (apps reflD.ref [wordTy, .lcons g w2])
             let fstPath : Raw := .app
               (apps substD.ref [boolTy, fstFam, falseR, cgh,
                 apps symmD.ref [boolTy, cgh, falseR, eFalse],
                 atFalse])
               (.plam "i" cgh)
             sigEq
               (apps consGD.ref [g, .pair w2 (tailWit w2)])
               (.pair (.lcons g w2) rgw)
               fstPath)))
          (.var "w"))
        (.var "rgw"))

-- #guard consGNoCancelD.ok -- checked natively (Test/WedgeF2)

/-- **`encode ∘ decode ≡ id`**: winding a decoded reduced word gives the
word back. -/
def encodeDecodeF2D : LibDef where
  name := "encodeDecodeF2"
  ty := .pi "s" f2Ty
    (.path f2Ty
      (.app windF2D.ref (.app decodeF2D.ref (.var "s")))
      (.var "s"))
  tm :=
    let glh (h : Raw) : Raw := .app genLoopD.ref h
    let trGlh (h x : Raw) : Raw := .transp "i"
      (.app helixF2D.ref
        (.papp (glh h) w8CbaseT w8CbaseT (.var "i"))) x
    let wind (p : Raw) : Raw := .app windF2D.ref p
    let dw (w : Raw) : Raw := .app decodeWordD.ref w
    let goal (w r : Raw) : Raw := .path f2Ty (wind (dw w)) (.pair w r)
    let wordLemma : Raw :=
      .listrec "k"
        (.pi "r" (istrC (redWC (.var "k"))) (goal (.var "k") (.var "r")))
        (.lam "r" (apps sigmaPropEqD.ref
          [wordTy, istrRedFam, istrRedProp,
           .pair .lnil .tt, .pair .lnil (.var "r"),
           apps reflD.ref [wordTy, .lnil]]))
        (lams ["h", "t", "ih"] (.lam "r"
          (let h : Raw := .var "h"
           let t : Raw := .var "t"
           let r : Raw := .var "r"
           let tailW : Raw := apps redRelaxD.ref [t, .inr h, r]
           let ihApp : Raw := .app (.var "ih") tailW
           let X1 : Raw := wind (dw (.lcons h t))
           let X2 : Raw := trGlh h (wind (dw t))
           let X3 : Raw := trGlh h (.pair t tailW)
           let X4 : Raw := apps consGD.ref [h, .pair t tailW]
           let X5 : Raw := .pair (.lcons h t) r
           let m1 : Raw := apps transpCompW8D.ref
             [w8CbaseT, w8CbaseT, dw t, glh h, .pair .lnil .tt]
           let m2 : Raw := apps congD.ref [f2Ty, f2Ty,
             .lam "x2" (trGlh h (.var "x2")),
             wind (dw t), .pair t tailW, ihApp]
           let m3 : Raw := apps windGenD.ref
             [.fst h, .snd h, .pair t tailW]
           let m4 : Raw := apps consGNoCancelD.ref [h, t, r]
           apps transD.ref [f2Ty, X1, X2, X5, m1,
             apps transD.ref [f2Ty, X2, X3, X5, m2,
               apps transD.ref [f2Ty, X3, X4, X5, m3, m4]]])))
        (.fst (.var "s"))
    .lam "s" (.app wordLemma (.snd (.var "s")))

-- #guard encodeDecodeF2D.ok -- checked natively (Test/WedgeF2)

/-- **`Ω(S¹∨S¹) ≃ F₂`** — the fundamental group of the figure eight is
the free group on two generators. -/
def omegaW8F2EquivD : LibDef where
  name := "omegaW8F2Equiv"
  ty := equivR omega8CT f2Ty
  tm := apps isoToEquivD.ref
    [omega8CT, f2Ty, windF2D.ref, decodeF2D.ref,
     encodeDecodeF2D.ref,
     .lam "p" (apps decodeEncodeF2D.ref [w8CbaseT, .var "p"])]

-- #guard omegaW8F2EquivD.ok -- checked natively (Test/WedgeF2)

/-- `Ω(S¹∨S¹) ≡ F₂` in the universe. -/
def w8LoopIsF2D : LibDef where
  name := "w8LoopIsF2"
  ty := .path .univ omega8CT f2Ty
  tm := apps uaD.ref [omega8CT, f2Ty, omegaW8F2EquivD.ref]

-- #guard w8LoopIsF2D.ok -- checked natively (Test/WedgeF2)

/-! ## Groupoids ≃ 1-types, chapter 1: the fundamental groupoid

Internal groupoid structure (multi-object `groupTy`), and the
**fundamental groupoid** of any 1-type — every law is a one-line
instance of the untruncated coherence cells: associativity is
`assocConn`, the units are the two unitors, both inverse laws are
`cancelL` (the right one via the definitional `symm (symm f) ≐ f`), and
only set-ness of the homs uses the 1-type hypothesis. -/

/-- Groupoid structure on a type of objects `Ob`. -/
def groupoidTy (Ob : Raw) : Raw :=
  let H (x y : Raw) : Raw := .app (.app (.var "gH") x) y
  let cmp (x y z f g : Raw) : Raw :=
    apps (.var "gc") [x, y, z, f, g]
  .sigma "gH" (.arr Ob (.arr Ob .univ))
    (.sigma "gid" (.pi "x" Ob (H (.var "x") (.var "x")))
    (.sigma "gc" (.pi "x" Ob (.pi "y" Ob (.pi "z" Ob
      (.arr (H (.var "x") (.var "y"))
        (.arr (H (.var "y") (.var "z")) (H (.var "x") (.var "z")))))))
    (.sigma "gi" (.pi "x" Ob (.pi "y" Ob
      (.arr (H (.var "x") (.var "y")) (H (.var "y") (.var "x")))))
    (.sigma "gassoc" (.pi "x" Ob (.pi "y" Ob (.pi "z" Ob (.pi "w" Ob
      (.pi "f" (H (.var "x") (.var "y"))
      (.pi "g" (H (.var "y") (.var "z"))
      (.pi "h" (H (.var "z") (.var "w"))
        (.path (H (.var "x") (.var "w"))
          (cmp (.var "x") (.var "y") (.var "w") (.var "f")
            (cmp (.var "y") (.var "z") (.var "w") (.var "g") (.var "h")))
          (cmp (.var "x") (.var "z") (.var "w")
            (cmp (.var "x") (.var "y") (.var "z") (.var "f") (.var "g"))
            (.var "h"))))))))))
    (.sigma "gunitL" (.pi "x" Ob (.pi "y" Ob
      (.pi "f" (H (.var "x") (.var "y"))
        (.path (H (.var "x") (.var "y"))
          (cmp (.var "x") (.var "x") (.var "y")
            (.app (.var "gid") (.var "x")) (.var "f"))
          (.var "f")))))
    (.sigma "gunitR" (.pi "x" Ob (.pi "y" Ob
      (.pi "f" (H (.var "x") (.var "y"))
        (.path (H (.var "x") (.var "y"))
          (cmp (.var "x") (.var "y") (.var "y") (.var "f")
            (.app (.var "gid") (.var "y")))
          (.var "f")))))
    (.sigma "ginvL" (.pi "x" Ob (.pi "y" Ob
      (.pi "f" (H (.var "x") (.var "y"))
        (.path (H (.var "y") (.var "y"))
          (cmp (.var "y") (.var "x") (.var "y")
            (apps (.var "gi") [.var "x", .var "y", .var "f"]) (.var "f"))
          (.app (.var "gid") (.var "y"))))))
    (.sigma "ginvR" (.pi "x" Ob (.pi "y" Ob
      (.pi "f" (H (.var "x") (.var "y"))
        (.path (H (.var "x") (.var "x"))
          (cmp (.var "x") (.var "y") (.var "x") (.var "f")
            (apps (.var "gi") [.var "x", .var "y", .var "f"]))
          (.app (.var "gid") (.var "x"))))))
      (.pi "x" Ob (.pi "y" Ob (isSetR (H (.var "x") (.var "y")))))))))))))

/-- **The fundamental groupoid of a 1-type.** -/
def fundGpdD : LibDef where
  name := "fundGpd"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (groupoidTy (.var "A")))
  tm :=
    let A : Raw := .var "A"
    let P (x y : Raw) : Raw := .path A x y
    let tr (x y z p q : Raw) : Raw := apps transD.ref [A, x, y, z, p, q]
    lams ["A", "gA"]
      (.pair (lams ["x", "y"] (P (.var "x") (.var "y")))
      (.pair (.lam "x" (apps reflD.ref [A, .var "x"]))
      (.pair (lams ["x", "y", "z", "f", "g"]
        (tr (.var "x") (.var "y") (.var "z") (.var "f") (.var "g")))
      (.pair (lams ["x", "y", "f"]
        (apps symmD.ref [A, .var "x", .var "y", .var "f"]))
      (.pair (lams ["x", "y", "z", "w", "f", "g", "h"]
        (apps assocConnD.ref [A, .var "x", .var "y", .var "z", .var "w",
          .var "f", .var "g", .var "h"]))
      (.pair (lams ["x", "y", "f"]
        (apps transReflLD.ref [A, .var "x", .var "y", .var "f"]))
      (.pair (lams ["x", "y", "f"]
        (apps transReflRD.ref [A, .var "x", .var "y", .var "f"]))
      (.pair (lams ["x", "y", "f"]
        (apps cancelLD.ref [A, .var "y", .var "x", .var "f"]))
      (.pair (lams ["x", "y", "f"]
        (apps cancelLD.ref [A, .var "x", .var "y",
          apps symmD.ref [A, .var "x", .var "y", .var "f"]]))
        (lams ["x", "y", "p", "q", "r", "s"]
          (apps (.var "gA") [.var "x", .var "y", .var "p", .var "q",
            .var "r", .var "s"])))))))))))

#guard fundGpdD.ok

/-- Extract the vertex group of a groupoid at a point. -/
def gpdAtD : LibDef where
  name := "gpdAt"
  ty := .pi "Ob" .univ (.arr (groupoidTy (.var "Ob"))
    (.arr (.var "Ob") groupTy))
  tm :=
    let G : Raw := .var "G"
    let x : Raw := .var "x"
    let gH : Raw := .fst G
    let gid : Raw := .fst (.snd G)
    let gc : Raw := .fst (.snd (.snd G))
    let gi : Raw := .fst (.snd (.snd (.snd G)))
    let gas : Raw := .fst (.snd (.snd (.snd (.snd G))))
    let guL : Raw := .fst (.snd (.snd (.snd (.snd (.snd G)))))
    let guR : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd G))))))
    let giL : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd G)))))))
    let giR : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
    let gst : Raw := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
    let H : Raw := apps gH [x, x]
    let mm (a b : Raw) : Raw := apps gc [x, x, x, a, b]
    lams ["Ob", "G", "x"]
      (.pair H
      (.pair (apps gc [x, x, x])
      (.pair (.app gid x)
      (.pair (apps gi [x, x])
      (.pair (lams ["a", "b", "c"]
        (apps symmD.ref [H,
          mm (.var "a") (mm (.var "b") (.var "c")),
          mm (mm (.var "a") (.var "b")) (.var "c"),
          apps gas [x, x, x, x, .var "a", .var "b", .var "c"]]))
      (.pair (.lam "a" (apps guL [x, x, .var "a"]))
      (.pair (.lam "a" (apps guR [x, x, .var "a"]))
      (.pair (.lam "a" (apps giL [x, x, .var "a"]))
      (.pair (.lam "a" (apps giR [x, x, .var "a"]))
        (apps gst [x, x]))))))))))

#guard gpdAtD.ok

/-- A group is a one-object groupoid. -/
def groupToUnitGpdD : LibDef where
  name := "groupToUnitGpd"
  ty := .arr groupTy (groupoidTy .unit)
  tm :=
    let G : Raw := .var "G"
    let C : Raw := .fst G
    let gm : Raw := .fst (.snd G)
    let ge : Raw := .fst (.snd (.snd G))
    let gi : Raw := .fst (.snd (.snd (.snd G)))
    let gas : Raw := .fst (.snd (.snd (.snd (.snd G))))
    let guL : Raw := .fst (.snd (.snd (.snd (.snd (.snd G)))))
    let guR : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd G))))))
    let giL : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd G)))))))
    let giR : Raw := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
    let gst : Raw := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
    let mm (a b : Raw) : Raw := apps gm [a, b]
    .lam "G"
      (.pair (lams ["x", "y"] C)
      (.pair (.lam "x" ge)
      (.pair (lams ["x", "y", "z", "f", "g"] (mm (.var "f") (.var "g")))
      (.pair (lams ["x", "y", "f"] (.app gi (.var "f")))
      (.pair (lams ["x", "y", "z", "w", "f", "g", "h"]
        (apps symmD.ref [C,
          mm (mm (.var "f") (.var "g")) (.var "h"),
          mm (.var "f") (mm (.var "g") (.var "h")),
          apps gas [.var "f", .var "g", .var "h"]]))
      (.pair (lams ["x", "y", "f"] (.app guL (.var "f")))
      (.pair (lams ["x", "y", "f"] (.app guR (.var "f")))
      (.pair (lams ["x", "y", "f"] (.app giL (.var "f")))
      (.pair (lams ["x", "y", "f"] (.app giR (.var "f")))
        (lams ["x", "y"] gst))))))))))

#guard groupToUnitGpdD.ok

/-- **The vertex group of the fundamental groupoid is the loop group —
definitionally** (`refl` proof): both sides assemble the same untruncated
coherence cells. -/
def fundGpdLoopD : LibDef where
  name := "fundGpdLoop"
  ty := .pi "A" .univ (.pi "gA" (isGpdR (.var "A"))
    (.pi "a" (.var "A")
      (.path groupTy
        (apps gpdAtD.ref [.var "A",
          apps fundGpdD.ref [.var "A", .var "gA"], .var "a"])
        (apps loopGroupD.ref [.var "A", .var "gA", .var "a"]))))
  tm := lams ["A", "gA", "a"]
    (.plam "i" (apps loopGroupD.ref [.var "A", .var "gA", .var "a"]))

#guard fundGpdLoopD.ok

/-! ## Groupoids ≃ 1-types, chapter 3: morphisms and functoriality -/

/-- `cong f (p ⬝ q) ≡ cong f p ⬝ cong f q` (both levels 0), by `J`. -/
def congTransD : LibDef where
  name := "congTrans"
  ty :=
    let fx : Raw := .app (.var "f") (.var "x")
    let fy : Raw := .app (.var "f") (.var "y")
    .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "x" (.var "A") (.pi "y" (.var "A") (.pi "z" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
    (.pi "q" (.path (.var "A") (.var "y") (.var "z"))
      (.path (.path (.var "B") fx (.app (.var "f") (.var "z")))
        (apps congD.ref [.var "A", .var "B", .var "f", .var "x", .var "z",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z",
            .var "p", .var "q"]])
        (apps transD.ref [.var "B", fx, fy, .app (.var "f") (.var "z"),
          apps congD.ref [.var "A", .var "B", .var "f", .var "x", .var "y",
            .var "p"],
          apps congD.ref [.var "A", .var "B", .var "f", .var "y", .var "z",
            .var "q"]])))))))))
  tm :=
    let fx : Raw := .app (.var "f") (.var "x")
    let fy : Raw := .app (.var "f") (.var "y")
    let congP := apps congD.ref
      [.var "A", .var "B", .var "f", .var "x", .var "y", .var "p"]
    let pRefl := apps transD.ref [.var "A", .var "x", .var "y", .var "y",
      .var "p", apps reflD.ref [.var "A", .var "y"]]
    let pathBxy : Raw := .path (.var "B") fx fy
    let x1 := apps congD.ref
      [.var "A", .var "B", .var "f", .var "x", .var "y", pRefl]
    let x3 := apps transD.ref [.var "B", fx, fy, fy, congP,
      apps congD.ref [.var "A", .var "B", .var "f", .var "y", .var "y",
        apps reflD.ref [.var "A", .var "y"]]]
    let leg1 := apps congD.ref
      [.path (.var "A") (.var "x") (.var "y"), pathBxy,
       .lam "r" (apps congD.ref
         [.var "A", .var "B", .var "f", .var "x", .var "y", .var "r"]),
       pRefl, .var "p",
       apps transReflRD.ref [.var "A", .var "x", .var "y", .var "p"]]
    let leg2 := apps symmD.ref [pathBxy, x3, congP,
      apps transReflRD.ref [.var "B", fx, fy, congP]]
    let dCase := apps transD.ref [pathBxy, x1, congP, x3, leg1, leg2]
    let motive := .lam "z2" (.lam "q2"
      (.path (.path (.var "B") fx (.app (.var "f") (.var "z2")))
        (apps congD.ref [.var "A", .var "B", .var "f", .var "x", .var "z2",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z2",
            .var "p", .var "q2"]])
        (apps transD.ref [.var "B", fx, fy, .app (.var "f") (.var "z2"),
          congP,
          apps congD.ref [.var "A", .var "B", .var "f", .var "y", .var "z2",
            .var "q2"]])))
    lams ["A", "B", "f", "x", "y", "z", "p", "q"]
      (apps jD.ref [.var "A", .var "y", motive, dCase, .var "z", .var "q"])

#guard congTransD.ok

/-- Morphisms of groupoids: object map, hom map, preservation of
identity and composition. -/
def gpdMorTy (Ob1 G1 Ob2 G2 : Raw) : Raw :=
  let H1 (x y : Raw) : Raw := apps (.fst G1) [x, y]
  let H2 (x y : Raw) : Raw := apps (.fst G2) [x, y]
  let id1 (x : Raw) : Raw := .app (.fst (.snd G1)) x
  let id2 (x : Raw) : Raw := .app (.fst (.snd G2)) x
  let c1 (x y z f g : Raw) : Raw :=
    apps (.fst (.snd (.snd G1))) [x, y, z, f, g]
  let c2 (x y z f g : Raw) : Raw :=
    apps (.fst (.snd (.snd G2))) [x, y, z, f, g]
  let F0 (x : Raw) : Raw := .app (.var "F0") x
  let F1 (x y f : Raw) : Raw := apps (.var "F1") [x, y, f]
  .sigma "F0" (.arr Ob1 Ob2)
    (.sigma "F1" (.pi "x" Ob1 (.pi "y" Ob1
      (.arr (H1 (.var "x") (.var "y"))
        (H2 (F0 (.var "x")) (F0 (.var "y"))))))
    (.sigma "Fid" (.pi "x" Ob1
      (.path (H2 (F0 (.var "x")) (F0 (.var "x")))
        (F1 (.var "x") (.var "x") (id1 (.var "x")))
        (id2 (F0 (.var "x")))))
      (.pi "x" Ob1 (.pi "y" Ob1 (.pi "z" Ob1
        (.pi "f" (H1 (.var "x") (.var "y"))
        (.pi "g" (H1 (.var "y") (.var "z"))
          (.path (H2 (F0 (.var "x")) (F0 (.var "z")))
            (F1 (.var "x") (.var "z")
              (c1 (.var "x") (.var "y") (.var "z") (.var "f") (.var "g")))
            (c2 (F0 (.var "x")) (F0 (.var "y")) (F0 (.var "z"))
              (F1 (.var "x") (.var "y") (.var "f"))
              (F1 (.var "y") (.var "z") (.var "g")))))))))))

/-- **Functoriality of the fundamental groupoid**: any map of 1-types
induces a groupoid morphism — `cong` preserves `refl` definitionally and
`trans` by `congTrans`. -/
def fundGpdMapD : LibDef where
  name := "fundGpdMap"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "gA" (isGpdR (.var "A")) (.pi "gB" (isGpdR (.var "B"))
    (.pi "f" (.arr (.var "A") (.var "B"))
      (gpdMorTy (.var "A")
        (apps fundGpdD.ref [.var "A", .var "gA"])
        (.var "B")
        (apps fundGpdD.ref [.var "B", .var "gB"]))))))
  tm :=
    let A : Raw := .var "A"
    let B : Raw := .var "B"
    let f : Raw := .var "f"
    lams ["A", "B", "gA", "gB", "f"]
      (.pair f
      (.pair (lams ["x", "y", "p"]
        (apps congD.ref [A, B, f, .var "x", .var "y", .var "p"]))
      (.pair (.lam "x" (.plam "j"
        (apps reflD.ref [B, .app f (.var "x")])))
        (lams ["x", "y", "z", "p", "q"]
          (apps congTransD.ref [A, B, f, .var "x", .var "y", .var "z",
            .var "p", .var "q"])))))

#guard fundGpdMapD.ok

/-- **`cong` is strictly functorial**: `cong (g ∘ f) p ≡ cong g (cong f p)`
definitionally (`refl` proof) — both sides evaluate to
`⟨i⟩ g (f (p i))`. -/
def congCompD : LibDef where
  name := "congComp"
  ty :=
    let gf (t : Raw) : Raw := .app (.var "g") (.app (.var "f") t)
    .pi "A" .univ (.pi "B" .univ (.pi "C" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "C"))
    (.pi "x" (.var "A") (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
      (.path (.path (.var "C") (gf (.var "x")) (gf (.var "y")))
        (apps congD.ref [.var "A", .var "C",
          .lam "t" (gf (.var "t")), .var "x", .var "y", .var "p"])
        (apps congD.ref [.var "B", .var "C", .var "g",
          .app (.var "f") (.var "x"), .app (.var "f") (.var "y"),
          apps congD.ref [.var "A", .var "B", .var "f",
            .var "x", .var "y", .var "p"]])))))))))
  tm :=
    let gf (t : Raw) : Raw := .app (.var "g") (.app (.var "f") t)
    lams ["A", "B", "C", "f", "g", "x", "y", "p"]
      (.plam "j" (apps congD.ref [.var "A", .var "C",
        .lam "t" (gf (.var "t")), .var "x", .var "y", .var "p"]))

#guard congCompD.ok

/-- The identity groupoid morphism. -/
def gpdMorIdD : LibDef where
  name := "gpdMorId"
  ty := .pi "Ob" .univ (.pi "G" (groupoidTy (.var "Ob"))
    (gpdMorTy (.var "Ob") (.var "G") (.var "Ob") (.var "G")))
  tm :=
    let G : Raw := .var "G"
    let H (x y : Raw) : Raw := apps (.fst G) [x, y]
    let id1 (x : Raw) : Raw := .app (.fst (.snd G)) x
    let c1 (x y z f g : Raw) : Raw :=
      apps (.fst (.snd (.snd G))) [x, y, z, f, g]
    lams ["Ob", "G"]
      (.pair (.lam "x" (.var "x"))
      (.pair (lams ["x", "y", "p"] (.var "p"))
      (.pair (.lam "x" (apps reflD.ref
        [H (.var "x") (.var "x"), id1 (.var "x")]))
        (lams ["x", "y", "z", "f", "g"] (apps reflD.ref
          [H (.var "x") (.var "z"),
           c1 (.var "x") (.var "y") (.var "z") (.var "f") (.var "g")])))))

#guard gpdMorIdD.ok

/-- Composition of groupoid morphisms. -/
def gpdMorCompD : LibDef where
  name := "gpdMorComp"
  ty := .pi "Ob1" .univ (.pi "G1" (groupoidTy (.var "Ob1"))
    (.pi "Ob2" .univ (.pi "G2" (groupoidTy (.var "Ob2"))
    (.pi "Ob3" .univ (.pi "G3" (groupoidTy (.var "Ob3"))
    (.arr (gpdMorTy (.var "Ob1") (.var "G1") (.var "Ob2") (.var "G2"))
      (.arr (gpdMorTy (.var "Ob2") (.var "G2") (.var "Ob3") (.var "G3"))
        (gpdMorTy (.var "Ob1") (.var "G1") (.var "Ob3") (.var "G3")))))))))
  tm :=
    let F : Raw := .var "F"
    let K : Raw := .var "K"
    let F0 (x : Raw) : Raw := .app (.fst F) x
    let K0 (x : Raw) : Raw := .app (.fst K) x
    let F1 (x y f : Raw) : Raw := apps (.fst (.snd F)) [x, y, f]
    let K1 (x y f : Raw) : Raw := apps (.fst (.snd K)) [x, y, f]
    let Fid (x : Raw) : Raw := .app (.fst (.snd (.snd F))) x
    let Kid (x : Raw) : Raw := .app (.fst (.snd (.snd K))) x
    let Fc (x y z f g : Raw) : Raw :=
      apps (.snd (.snd (.snd F))) [x, y, z, f, g]
    let Kc (x y z f g : Raw) : Raw :=
      apps (.snd (.snd (.snd K))) [x, y, z, f, g]
    let G2 : Raw := .var "G2"
    let G3 : Raw := .var "G3"
    let H2 (x y : Raw) : Raw := apps (.fst G2) [x, y]
    let H3 (x y : Raw) : Raw := apps (.fst G3) [x, y]
    let id2 (x : Raw) : Raw := .app (.fst (.snd G2)) x
    let id3 (x : Raw) : Raw := .app (.fst (.snd G3)) x
    let c2 (x y z f g : Raw) : Raw :=
      apps (.fst (.snd (.snd G2))) [x, y, z, f, g]
    let c3 (x y z f g : Raw) : Raw :=
      apps (.fst (.snd (.snd G3))) [x, y, z, f, g]
    let x : Raw := .var "x"
    let y : Raw := .var "y"
    let z : Raw := .var "z"
    let f : Raw := .var "f"
    let g : Raw := .var "g"
    lams ["Ob1", "G1", "Ob2", "G2", "Ob3", "G3", "F", "K"]
      (.pair (.lam "x" (K0 (F0 x)))
      (.pair (lams ["x", "y", "p"]
        (K1 (F0 x) (F0 y) (F1 x y (.var "p"))))
      (.pair (.lam "x"
        (apps transD.ref
          [H3 (K0 (F0 x)) (K0 (F0 x)),
           K1 (F0 x) (F0 x) (F1 x x (.app (.fst (.snd (.var "G1"))) x)),
           K1 (F0 x) (F0 x) (id2 (F0 x)),
           id3 (K0 (F0 x)),
           apps congD.ref
             [H2 (F0 x) (F0 x), H3 (K0 (F0 x)) (K0 (F0 x)),
              .lam "h" (K1 (F0 x) (F0 x) (.var "h")),
              F1 x x (.app (.fst (.snd (.var "G1"))) x),
              id2 (F0 x), Fid x],
           Kid (F0 x)]))
        (lams ["x", "y", "z", "f", "g"]
          (apps transD.ref
            [H3 (K0 (F0 x)) (K0 (F0 z)),
             K1 (F0 x) (F0 z)
               (F1 x z (apps (.fst (.snd (.snd (.var "G1"))))
                 [x, y, z, f, g])),
             K1 (F0 x) (F0 z) (c2 (F0 x) (F0 y) (F0 z)
               (F1 x y f) (F1 y z g)),
             c3 (K0 (F0 x)) (K0 (F0 y)) (K0 (F0 z))
               (K1 (F0 x) (F0 y) (F1 x y f))
               (K1 (F0 y) (F0 z) (F1 y z g)),
             apps congD.ref
               [H2 (F0 x) (F0 z), H3 (K0 (F0 x)) (K0 (F0 z)),
                .lam "h" (K1 (F0 x) (F0 z) (.var "h")),
                F1 x z (apps (.fst (.snd (.snd (.var "G1"))))
                  [x, y, z, f, g]),
                c2 (F0 x) (F0 y) (F0 z) (F1 x y f) (F1 y z g),
                Fc x y z f g],
             Kc (F0 x) (F0 y) (F0 z) (F1 x y f) (F1 y z g)])))))

#guard gpdMorCompD.ok

end Cubical.Library

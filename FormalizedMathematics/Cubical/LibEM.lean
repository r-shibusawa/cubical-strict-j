import FormalizedMathematics.Cubical.LibWords

/-! # Eilenberg–MacLane spaces `K(G,1)`, round 1

The kernel HIT `em1 C m` (with `emcomp` the composition 2-cell and
`emsquash` the 1-truncation).  Here: `isSet → isGroupoid`, instantiation
at `(ℤ, +)`, a computing recursor demo, and **`emloopComp`** — `emloop`
is a homomorphism, by a `compPath`-uniqueness cube against the `emcomp`
cell. -/

namespace Cubical.Library

open Raw

/-- `isGroupoid` (the library-side builder, matching the kernel's). -/
def isGpdR (B : Raw) : Raw :=
  .pi "a" B (.pi "b" B
    (.pi "p" (.path B (.var "a") (.var "b"))
    (.pi "q" (.path B (.var "a") (.var "b"))
    (.pi "r" (.path (.path B (.var "a") (.var "b"))
        (.var "p") (.var "q"))
    (.pi "s" (.path (.path B (.var "a") (.var "b"))
        (.var "p") (.var "q"))
      (.path (.path (.path B (.var "a") (.var "b"))
          (.var "p") (.var "q"))
        (.var "r") (.var "s")))))))

/-- Sets are groupoids. -/
def isSetToGpdD : LibDef where
  name := "isSetToGpd"
  ty := .pi "B" .univ (.arr (isSetR (.var "B")) (isGpdR (.var "B")))
  tm := lams ["B", "hB", "a", "b"] (apps isPropToIsSetD.ref
    [.path (.var "B") (.var "a") (.var "b"),
     apps (.var "hB") [.var "a", .var "b"]])

#guard isSetToGpdD.ok

/-- `K(ℤ,1)` as a type. -/
def em1ZD : LibDef where
  name := "em1Z"
  ty := .univ
  tm := .em1 .int addD.ref

#guard em1ZD.ok

-- the recursor computes on `embase`
#guard
  match normalize (.em1rec .int
    (apps isSetToGpdD.ref [.int, isSetZD.ref])
    (.ipos .zero)
    (.lam "g" (.plam "i" (.ipos .zero)))
    (lams ["g", "h"] (.plam "j" (.plam "i" (.ipos .zero))))
    (.ann .embase (.em1 .int addD.ref))) .int with
  | .ok t => t == resolveClosed (posZ 0)
  | _ => false

/-- `emloop` as a path. -/
def emloopD : LibDef where
  name := "emloop"
  ty := .pi "C" .univ
    (.pi "m" (.arr (.var "C") (.arr (.var "C") (.var "C")))
    (.arr (.var "C")
      (.path (.em1 (.var "C") (.var "m")) .embase .embase)))
  tm := lams ["C", "m", "g"] (.plam "i" (.emloop (.var "g") (.var "i")))

#guard emloopD.ok

/-- **`emloop` is a homomorphism**: `emloop (g·h) ≡ emloop g ⬝ emloop h`,
by comparing the `emcomp` cell with the composition filler in a single
3-dimensional `hcomp`. -/
def emloopCompD : LibDef where
  name := "emloopComp"
  ty := .pi "C" .univ
    (.pi "m" (.arr (.var "C") (.arr (.var "C") (.var "C")))
    (.pi "g" (.var "C") (.pi "h" (.var "C")
      (.path
        (.path (.em1 (.var "C") (.var "m")) .embase .embase)
        (apps emloopD.ref [.var "C", .var "m",
          .app (.app (.var "m") (.var "g")) (.var "h")])
        (apps transD.ref [.em1 (.var "C") (.var "m"),
          .embase, .embase, .embase,
          apps emloopD.ref [.var "C", .var "m", .var "g"],
          apps emloopD.ref [.var "C", .var "m", .var "h"]])))))
  tm :=
    let emT : Raw := .em1 (.var "C") (.var "m")
    lams ["C", "m", "g", "h"] (.plam "k" (.plam "i" (.hcomp "j" emT
      [([(.var "i", false)], .embase),
       ([(.var "i", true)], .emloop (.var "h") (.var "j")),
       ([(.var "k", false)],
         .emcomp (.var "m") (.var "g") (.var "h") (.var "j") (.var "i")),
       ([(.var "k", true)],
         .hcomp "k2" emT
           [([(.var "i", false)], .embase),
            ([(.var "i", true)],
              .emloop (.var "h") (.imin (.var "k2") (.var "j"))),
            ([(.var "j", false)], .emloop (.var "g") (.var "i"))]
           (.emloop (.var "g") (.var "i")))]
      (.emloop (.var "g") (.var "i")))))

#guard emloopCompD.ok

/-! ## Groups, the ℤ-instance, and `emloop 1 ≡ refl` -/

/-- Negation on ℤ. -/
def negZD : LibDef where
  name := "negZ"
  ty := .arr .int .int
  tm := .lam "z" (.intcase "k" .int
    (.lam "n" (.natrec "k2" .int (.ipos .zero)
      (lams ["m", "ih"] (.inegsuc (.var "m"))) (.var "n")))
    (.lam "n" (.ipos (.succ (.var "n"))))
    (.var "z"))

private def addZ (a b : Raw) : Raw := apps addD.ref [a, b]
private def negZ' (a : Raw) : Raw := .app negZD.ref a
private def zeroZ : Raw := .ipos .zero

def addInvPosD : LibDef where
  name := "addInvPos"
  ty := .pi "m" .nat
    (.path .int (addZ (.ipos (.succ (.var "m"))) (.inegsuc (.var "m"))) zeroZ)
  tm := .lam "m" (.natrec "k"
    (.path .int (addZ (.ipos (.succ (.var "k"))) (.inegsuc (.var "k"))) zeroZ)
    (.plam "i" zeroZ)
    (lams ["m2", "ih"] (apps congD.ref [.int, .int, predZD.ref,
      addZ (.ipos (.succ (.succ (.var "m2")))) (.inegsuc (.var "m2")),
      .ipos (.succ .zero),
      apps transD.ref [.int,
        addZ (.ipos (.succ (.succ (.var "m2")))) (.inegsuc (.var "m2")),
        .app sucZD.ref (addZ (.ipos (.succ (.var "m2"))) (.inegsuc (.var "m2"))),
        .ipos (.succ .zero),
        apps addSucLD.ref [.ipos (.succ (.var "m2")), .inegsuc (.var "m2")],
        apps congD.ref [.int, .int, sucZD.ref,
          addZ (.ipos (.succ (.var "m2"))) (.inegsuc (.var "m2")),
          zeroZ, .var "ih"]]]))
    (.var "m"))

def addInvNegD : LibDef where
  name := "addInvNeg"
  ty := .pi "m" .nat
    (.path .int (addZ (.inegsuc (.var "m")) (.ipos (.succ (.var "m")))) zeroZ)
  tm := .lam "m" (.natrec "k"
    (.path .int (addZ (.inegsuc (.var "k")) (.ipos (.succ (.var "k")))) zeroZ)
    (.plam "i" zeroZ)
    (lams ["m2", "ih"] (
      let Y : Raw := addZ (.inegsuc (.var "m2")) (.ipos (.succ (.var "m2")))
      apps transD.ref [.int,
        .app sucZD.ref (addZ (.inegsuc (.succ (.var "m2")))
          (.ipos (.succ (.var "m2")))),
        .app sucZD.ref (.app predZD.ref Y),
        zeroZ,
        apps congD.ref [.int, .int, sucZD.ref,
          addZ (.inegsuc (.succ (.var "m2"))) (.ipos (.succ (.var "m2"))),
          .app predZD.ref Y,
          apps addPredLD.ref [.inegsuc (.var "m2"), .ipos (.succ (.var "m2"))]],
        apps transD.ref [.int,
          .app sucZD.ref (.app predZD.ref Y), Y, zeroZ,
          .app sucPredZD.ref Y,
          .var "ih"]]))
    (.var "m"))

def addInvRD : LibDef where
  name := "addInvR"
  ty := .pi "z" .int (.path .int (addZ (.var "z") (negZ' (.var "z"))) zeroZ)
  tm := .lam "z" (.intcase "k"
    (.path .int (addZ (.var "k") (negZ' (.var "k"))) zeroZ)
    (.lam "n" (.natrec "k2"
      (.path .int (addZ (.ipos (.var "k2")) (negZ' (.ipos (.var "k2")))) zeroZ)
      (.plam "i" zeroZ)
      (lams ["m", "ih"] (.app addInvPosD.ref (.var "m")))
      (.var "n")))
    (.lam "n" (.app addInvNegD.ref (.var "n")))
    (.var "z"))

def addInvLD : LibDef where
  name := "addInvL"
  ty := .pi "z" .int (.path .int (addZ (negZ' (.var "z")) (.var "z")) zeroZ)
  tm := .lam "z" (apps transD.ref [.int,
    addZ (negZ' (.var "z")) (.var "z"),
    addZ (.var "z") (negZ' (.var "z")),
    zeroZ,
    apps addCommD.ref [negZ' (.var "z"), .var "z"],
    .app addInvRD.ref (.var "z")])

#guard negZD.ok
#guard addInvPosD.ok
#guard addInvNegD.ok
#guard addInvRD.ok
#guard addInvLD.ok

/-- Groups (carrier, operations, laws, set-ness) as a Σ-tower. -/
def groupTy : Raw :=
  let C : Raw := .var "gC"
  let mm (a b : Raw) : Raw := .app (.app (.var "gm") a) b
  .sigma "gC" .univ (.sigma "gm" (.arr C (.arr C C))
    (.sigma "ge" C (.sigma "gi" (.arr C C)
    (.sigma "gassoc" (.pi "a" C (.pi "b" C (.pi "c" C
      (.path C (mm (mm (.var "a") (.var "b")) (.var "c"))
        (mm (.var "a") (mm (.var "b") (.var "c")))))))
    (.sigma "gunitL" (.pi "a" C (.path C (mm (.var "ge") (.var "a")) (.var "a")))
    (.sigma "gunitR" (.pi "a" C (.path C (mm (.var "a") (.var "ge")) (.var "a")))
    (.sigma "ginvL" (.pi "a" C
      (.path C (mm (.app (.var "gi") (.var "a")) (.var "a")) (.var "ge")))
    (.sigma "ginvR" (.pi "a" C
      (.path C (mm (.var "a") (.app (.var "gi") (.var "a"))) (.var "ge")))
      (isSetR C)))))))))

/-- **The group `(ℤ, +, 0, −)`**. -/
def zGroupD : LibDef where
  name := "zGroup"
  ty := groupTy
  tm := .pair .int (.pair addD.ref (.pair zeroZ (.pair negZD.ref
    (.pair (lams ["a", "b", "c"]
      (apps addAssocD.ref [.var "a", .var "b", .var "c"]))
    (.pair addZeroLD.ref (.pair addZeroRD.ref
    (.pair (.lam "a" (.app addInvLD.ref (.var "a")))
    (.pair (.lam "a" (.app addInvRD.ref (.var "a")))
      isSetZD.ref))))))))

#guard zGroupD.ok

/-- **`emloop e ≡ refl`** — from `emloopComp` and the groupoid laws of
paths (cancel `p` on the left). -/
def emloopOneD : LibDef where
  name := "emloopOne"
  ty := .pi "C" .univ
    (.pi "m" (.arr (.var "C") (.arr (.var "C") (.var "C")))
    (.pi "e" (.var "C")
    (.pi "ue" (.path (.var "C")
        (.app (.app (.var "m") (.var "e")) (.var "e")) (.var "e"))
      (.path (.path (.em1 (.var "C") (.var "m")) .embase .embase)
        (apps emloopD.ref [.var "C", .var "m", .var "e"])
        (apps reflD.ref [.em1 (.var "C") (.var "m"), .embase])))))
  tm :=
    let emT : Raw := .em1 (.var "C") (.var "m")
    let PT : Raw := .path emT .embase .embase
    let pE : Raw := apps emloopD.ref [.var "C", .var "m", .var "e"]
    let piE : Raw := apps symmD.ref [emT, .embase, .embase, pE]
    let comp (x y : Raw) : Raw :=
      apps transD.ref [emT, .embase, .embase, .embase, x, y]
    let reflE : Raw := apps reflD.ref [emT, .embase]
    -- Q : p ≡ p ⬝ p
    let Q : Raw := apps transD.ref [PT, pE,
      apps emloopD.ref [.var "C", .var "m",
        .app (.app (.var "m") (.var "e")) (.var "e")],
      comp pE pE,
      apps congD.ref [.var "C", PT,
        .lam "g2" (apps emloopD.ref [.var "C", .var "m", .var "g2"]),
        .var "e", .app (.app (.var "m") (.var "e")) (.var "e"),
        apps symmD.ref [.var "C",
          .app (.app (.var "m") (.var "e")) (.var "e"), .var "e",
          .var "ue"]],
      apps emloopCompD.ref [.var "C", .var "m", .var "e", .var "e"]]
    lams ["C", "m", "e", "ue"]
      (apps transD.ref [PT, pE, comp reflE pE, reflE,
        apps symmD.ref [PT, comp reflE pE, pE,
          apps transReflLD.ref [emT, .embase, .embase, pE]],
        apps transD.ref [PT, comp reflE pE, comp (comp piE pE) pE, reflE,
          apps congD.ref [PT, PT,
            .lam "h2" (comp (.var "h2") pE),
            reflE, comp piE pE,
            apps symmD.ref [PT, comp piE pE, reflE,
              apps transInvLD.ref [emT, .embase, .embase, pE]]],
          apps transD.ref [PT, comp (comp piE pE) pE,
            comp piE (comp pE pE), reflE,
            apps transAssocD.ref [emT, .embase, .embase, .embase, .embase,
              piE, pE, pE],
            apps transD.ref [PT, comp piE (comp pE pE), comp piE pE, reflE,
              apps congD.ref [PT, PT,
                .lam "h2" (comp piE (.var "h2")),
                comp pE pE, pE,
                apps symmD.ref [PT, pE, comp pE pE, Q]],
              apps transInvLD.ref [emT, .embase, .embase, pE]]]]])

#guard emloopOneD.ok

/-! ## The h-level tower toward `Codes`

`isPropIsContr` is the classical single-`hcomp` square; `isPropIsEquiv`
follows by Π-closure; `isSetPi` is η-driven like `isSetProd`; and
equivalences between sets form a set (`isSetSigmaProp`). -/

/-- Contractibility is a proposition (one 4-tube `hcomp`). -/
def isPropIsContrD : LibDef where
  name := "isPropIsContr"
  ty := .pi "X" .univ (isPropR (isContrR (.var "X")))
  tm :=
    let c0 : Raw := .fst (.var "xp")
    let h0 : Raw := .snd (.var "xp")
    let c1 : Raw := .fst (.var "yp")
    let h1 : Raw := .snd (.var "yp")
    let h0At (a e : Raw) : Raw := .papp (.app h0 a) c0 a e
    let h1At (a e : Raw) : Raw := .papp (.app h1 a) c1 a e
    lams ["X", "xp", "yp"] (.plam "j" (.pair
      (h0At c1 (.var "j"))
      (.lam "y" (.plam "i" (.hcomp "k" (.var "X")
        [([(.var "i", false)],
           h0At (h0At c1 (.var "j")) (.var "k")),
         ([(.var "i", true)], h0At (.var "y") (.var "k")),
         ([(.var "j", false)],
           h0At (h0At (.var "y") (.var "i")) (.var "k")),
         ([(.var "j", true)],
           h0At (h1At (.var "y") (.var "i")) (.var "k"))]
        c0)))))

#guard isPropIsContrD.ok

/-- Being an equivalence is a proposition. -/
def isPropIsEquivD : LibDef where
  name := "isPropIsEquiv"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
      (isPropR (.pi "yb" (.var "B")
        (isContrR (fiberR (.var "A") (.var "B") (.var "f") (.var "yb")))))))
  tm := lams ["A", "B", "f"] (apps isPropPiD.ref
    [.var "B",
     .lam "yb" (isContrR (fiberR (.var "A") (.var "B") (.var "f") (.var "yb"))),
     .lam "yb" (.app isPropIsContrD.ref
       (fiberR (.var "A") (.var "B") (.var "f") (.var "yb")))])

#guard isPropIsEquivD.ok

/-- Function types into a set are a set (η-driven, no `hcomp`). -/
def isSetPiD : LibDef where
  name := "isSetPi"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (isSetR (.var "B")) (isSetR (.arr (.var "A") (.var "B")))))
  tm :=
    let FT : Raw := .arr (.var "A") (.var "B")
    let atX (ff : Raw) : Raw := .app ff (.var "x")
    let congX (pp : Raw) : Raw := apps congD.ref [FT, .var "B",
      .lam "w" (.app (.var "w") (.var "x")), .var "xs", .var "ys", pp]
    lams ["A", "B", "hB", "xs", "ys", "xp", "yp"]
      (.plam "i" (.plam "j" (.lam "x"
        (.papp
          (.papp
            (apps (.var "hB") [atX (.var "xs"), atX (.var "ys"),
              congX (.var "xp"), congX (.var "yp")])
            (congX (.var "xp")) (congX (.var "yp")) (.var "i"))
          (atX (.var "xs")) (atX (.var "ys")) (.var "j")))))

#guard isSetPiD.ok

/-- Equivalences between sets form a set. -/
def isSetEquivD : LibDef where
  name := "isSetEquiv"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (isSetR (.var "B")) (isSetR (equivR (.var "A") (.var "B")))))
  tm := lams ["A", "B", "hB"] (apps isSetSigmaPropD.ref
    [.arr (.var "A") (.var "B"),
     .lam "f" (.pi "yb" (.var "B")
       (isContrR (fiberR (.var "A") (.var "B") (.var "f") (.var "yb")))),
     apps isSetPiD.ref [.var "A", .var "B", .var "hB"],
     .lam "f" (apps isPropIsEquivD.ref [.var "A", .var "B", .var "f"])])

#guard isSetEquivD.ok

/-! ## Univalence η and the path-space of the universe

`ua (idEquiv) ≡ refl` is a single `Glue` cube; with `pathToEquiv` (which
is *definitionally* `idEquiv` on `refl`, by the constancy rule) and `J`
one universe up, paths between sets in `U` form a **set**. -/

/-- `J` one universe up. -/
def j1D : LibDef where
  name := "J@1"
  ty := .pi "A" (.univN 1) (.pi "x" (.var "A")
    (.pi "P" (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y")) (.univN 1)))
    (.pi "d" (apps (.var "P") [.var "x", .plam "k" (.var "x")])
    (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
      (apps (.var "P") [.var "y", .var "p"]))))))
  tm := jD.tm

/-- **`ua (idEquiv) ≡ refl`** — one `Glue` square. -/
def uaIdEquivD : LibDef where
  name := "uaIdEquiv"
  ty := .pi "X" .univ
    (.path (.path .univ (.var "X") (.var "X"))
      (apps uaD.ref [.var "X", .var "X", .app idEquivD.ref (.var "X")])
      (.plam "k" (.var "X")))
  tm := .lam "X" (.plam "i" (.plam "j"
    (.glueTy
      [([(.var "j", false)], .var "X", .app idEquivD.ref (.var "X")),
       ([(.var "j", true)], .var "X", .app idEquivD.ref (.var "X")),
       ([(.var "i", true)], .var "X", .app idEquivD.ref (.var "X"))]
      (.var "X"))))

#guard j1D.ok
#guard uaIdEquivD.ok

/-- `ua (pathToEquiv p) ≡ p`, by `J` (the `refl` case is `uaIdEquiv`). -/
def uaEtaD : LibDef where
  name := "uaEta"
  ty := .pi "X" .univ (.pi "Y" .univ
    (.pi "p" (.path .univ (.var "X") (.var "Y"))
      (.path (.path .univ (.var "X") (.var "Y"))
        (apps uaD.ref [.var "X", .var "Y",
          apps pathToEquivD.ref [.var "X", .var "Y", .var "p"]])
        (.var "p"))))
  tm := lams ["X", "Y", "p"] (apps j1D.ref [.univ, .var "X",
    lams ["Y2", "p2"] (.path (.path .univ (.var "X") (.var "Y2"))
      (apps uaD.ref [.var "X", .var "Y2",
        apps pathToEquivD.ref [.var "X", .var "Y2", .var "p2"]])
      (.var "p2")),
    .app uaIdEquivD.ref (.var "X"),
    .var "Y", .var "p"])

#guard uaEtaD.ok

/-- `isSetRetract`, mixed levels (`A : U₁`, `B : U₀`). -/
def isSetRetract10D : LibDef where
  name := "isSetRetract@10"
  ty := .pi "A" (.univN 1) (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "h" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (.arr (isSetR (.var "B")) (isSetR (.var "A")))))))
  tm :=
    let fx : Raw := .app (.var "f") (.var "xs")
    let fy : Raw := .app (.var "f") (.var "ys")
    let congf (pp : Raw) : Raw := apps cong10D.ref
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

/-- **Paths between sets in the universe form a set.** -/
def isSetPathUD : LibDef where
  name := "isSetPathU"
  ty := .pi "X" .univ (.pi "Y" .univ
    (.arr (isSetR (.var "Y")) (isSetR (.path .univ (.var "X") (.var "Y")))))
  tm := lams ["X", "Y", "hY"] (apps isSetRetract10D.ref
    [.path .univ (.var "X") (.var "Y"),
     equivR (.var "X") (.var "Y"),
     .lam "p" (apps pathToEquivD.ref [.var "X", .var "Y", .var "p"]),
     .lam "e" (apps uaD.ref [.var "X", .var "Y", .var "e"]),
     .lam "p" (apps uaEtaD.ref [.var "X", .var "Y", .var "p"]),
     apps isSetEquivD.ref [.var "X", .var "Y", .var "hY"]])

#guard isSetRetract10D.ok
#guard isSetPathUD.ok

/-! ## `hSet` and its groupoid structure

Being a set is a proposition; `hSet`-paths are a retract of carrier paths
in the universe (prop fibers ride by `toPathP`); with `isSetPathU` the
retract makes **`hSet` a groupoid** — the codomain the `Codes` family
needs. -/

/-- Being a set is a proposition. -/
def isPropIsSetD : LibDef where
  name := "isPropIsSet"
  ty := .pi "Y" .univ (isPropR (isSetR (.var "Y")))
  tm := lams ["Y", "s1", "s2"] (.plam "i" (lams ["a", "b", "p", "q"]
    (.papp
      (apps (apps isPropToIsSetD.ref
          [.path (.var "Y") (.var "a") (.var "b"),
           apps (.var "s1") [.var "a", .var "b"]])
        [.var "p", .var "q",
         apps (.var "s1") [.var "a", .var "b", .var "p", .var "q"],
         apps (.var "s2") [.var "a", .var "b", .var "p", .var "q"]])
      (apps (.var "s1") [.var "a", .var "b", .var "p", .var "q"])
      (apps (.var "s2") [.var "a", .var "b", .var "p", .var "q"])
      (.var "i"))))

#guard isPropIsSetD.ok

/-- `sigmaPropEq`, base one universe up. -/
def sigmaPropEq10D : LibDef where
  name := "sigmaPropEq@10"
  ty := .pi "A" (.univN 1) (.pi "B" (.arr (.var "A") .univ)
    (.pi "hB" (.pi "a" (.var "A") (isPropR (.app (.var "B") (.var "a"))))
    (.pi "u" (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
    (.pi "v" (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
    (.arr (.path (.var "A") (.fst (.var "u")) (.fst (.var "v")))
      (.path (.sigma "a" (.var "A") (.app (.var "B") (.var "a")))
        (.var "u") (.var "v")))))))
  tm := sigmaPropEqD.tm

/-- `isPropPathPSet`, base one universe up (rebuilt on `J@1`). -/
def isPropPathPSet1D : LibDef where
  name := "isPropPathPSet@1"
  ty :=
    let pp (pv ye : Raw) : Raw := .pathP "j"
      (.app (.var "P") (.papp pv (.var "x") ye (.var "j")))
      (.var "u") (.var "v")
    .pi "X" (.univN 1) (.pi "P" (.arr (.var "X") .univ)
    (.pi "mset" (.pi "x0" (.var "X") (isSetR (.app (.var "P") (.var "x0"))))
    (.pi "x" (.var "X") (.pi "u" (.app (.var "P") (.var "x"))
    (.pi "y" (.var "X") (.pi "pth" (.path (.var "X") (.var "x") (.var "y"))
    (.pi "v" (.app (.var "P") (.var "y"))
    (.pi "al" (pp (.var "pth") (.var "y"))
    (.pi "be" (pp (.var "pth") (.var "y"))
      (.path (pp (.var "pth") (.var "y")) (.var "al") (.var "be")))))))))))
  tm :=
    let pp (pv ye : Raw) : Raw := .pathP "j"
      (.app (.var "P") (.papp pv (.var "x") ye (.var "j")))
      (.var "u") (.var "v")
    lams ["X", "P", "mset", "x", "u", "y", "pth"]
      (apps j1D.ref [.var "X", .var "x",
        lams ["y2", "p2"] (.pi "v" (.app (.var "P") (.var "y2"))
          (.pi "al" (pp (.var "p2") (.var "y2"))
          (.pi "be" (pp (.var "p2") (.var "y2"))
            (.path (pp (.var "p2") (.var "y2")) (.var "al") (.var "be"))))),
        lams ["v", "al", "be"]
          (apps (.app (.var "mset") (.var "x"))
            [.var "u", .var "v", .var "al", .var "be"]),
        .var "y", .var "pth"])

#guard sigmaPropEq10D.ok
#guard isPropPathPSet1D.ok

/-- `isSetRetract`, both types one universe up (rebuilt on `cong@11`). -/
def isSetRetract11D : LibDef where
  name := "isSetRetract@11"
  ty := .pi "A" (.univN 1) (.pi "B" (.univN 1)
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "h" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (.arr (isSetR (.var "B")) (isSetR (.var "A")))))))
  tm :=
    let fx : Raw := .app (.var "f") (.var "xs")
    let fy : Raw := .app (.var "f") (.var "ys")
    let congf (pp : Raw) : Raw := apps cong11D.ref
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

#guard isSetRetract11D.ok

def hSetTy : Raw := .sigma "X" .univ (isSetR (.var "X"))

/-- Lift a carrier path to an `hSet` path. -/
def hSetPathD : LibDef where
  name := "hSetPath"
  ty := .pi "A" hSetTy (.pi "B" hSetTy
    (.arr (.path .univ (.fst (.var "A")) (.fst (.var "B")))
      (.path hSetTy (.var "A") (.var "B"))))
  tm := lams ["A", "B"] (apps sigmaPropEq10D.ref
    [.univ, .lam "X" (isSetR (.var "X")),
     .lam "X" (.app isPropIsSetD.ref (.var "X")),
     .var "A", .var "B"])

#guard hSetPathD.ok

private def fstH (x : Raw) : Raw := .fst x
private def isSetFam : Raw := .lam "X0" (isSetR (.var "X0"))
private def isSetFamProp : Raw := .lam "X0" (.app isPropIsSetD.ref (.var "X0"))
private def congFstH (A B p : Raw) : Raw := apps cong11D.ref
  [hSetTy, .univ, .lam "w0" (.fst (.var "w0")), A, B, p]

/-- `hSetPath (cong fst p) ≡ p` — carrier paths determine `hSet` paths. -/
def hSetPathEtaD : LibDef where
  name := "hSetPathEta"
  ty := .pi "A" hSetTy (.pi "B" hSetTy
    (.pi "p" (.path hSetTy (.var "A") (.var "B"))
      (.path (.path hSetTy (.var "A") (.var "B"))
        (apps hSetPathD.ref [.var "A", .var "B",
          congFstH (.var "A") (.var "B") (.var "p")])
        (.var "p"))))
  tm :=
    let A : Raw := .var "A"
    let B : Raw := .var "B"
    let fA : Raw := .fst A
    let fB : Raw := .fst B
    let cfp : Raw := congFstH A B (.var "p")
    let cfpAt (e : Raw) : Raw := .papp cfp fA fB e
    let line : Raw := .plam "i0" (isSetR (cfpAt (.var "i0")))
    -- the fill `sigmaPropEq` produces (same construction, for the k=0 face)
    let al : Raw := apps toPathPD.ref
      [isSetR fA, isSetR fB, line, .snd A, .snd B,
       apps (.app isPropIsSetD.ref fB)
         [apps transportD.ref [isSetR fA, isSetR fB, line, .snd A],
          .snd B]]
    let ppTy : Raw := .pathP "i0" (isSetR (cfpAt (.var "i0")))
      (.snd A) (.snd B)
    let be : Raw := .ann
      (.plam "i0" (.snd (.papp (.var "p") A B (.var "i0")))) ppTy
    let SND : Raw := apps isPropPathPSet1D.ref
      [.univ, isSetFam,
       .lam "X0" (apps isPropToIsSetD.ref
         [isSetR (.var "X0"), .app isPropIsSetD.ref (.var "X0")]),
       fA, .snd A, fB, cfp, .snd B, al, be]
    lams ["A", "B", "p"] (.plam "k" (.plam "i" (.pair
      (cfpAt (.var "i"))
      (.papp (.papp SND al be (.var "k"))
        (.snd A) (.snd B) (.var "i")))))

#guard hSetPathEtaD.ok

/-- `hSet` paths with equal carrier paths are equal. -/
def hSetPathUniqueD : LibDef where
  name := "hSetPathUnique"
  ty := .pi "A" hSetTy (.pi "B" hSetTy
    (.pi "p" (.path hSetTy (.var "A") (.var "B"))
    (.pi "q" (.path hSetTy (.var "A") (.var "B"))
    (.arr (.path (.path .univ (.fst (.var "A")) (.fst (.var "B")))
        (congFstH (.var "A") (.var "B") (.var "p"))
        (congFstH (.var "A") (.var "B") (.var "q")))
      (.path (.path hSetTy (.var "A") (.var "B"))
        (.var "p") (.var "q"))))))
  tm :=
    let A : Raw := .var "A"
    let B : Raw := .var "B"
    let PT : Raw := .path hSetTy A B
    let hp (u : Raw) : Raw := apps hSetPathD.ref [A, B, u]
    lams ["A", "B", "p", "q", "w"] (apps trans1D.ref [PT,
      .var "p", hp (congFstH A B (.var "q")), .var "q",
      apps trans1D.ref [PT,
        .var "p", hp (congFstH A B (.var "p")),
        hp (congFstH A B (.var "q")),
        apps symm1D.ref [PT, hp (congFstH A B (.var "p")), .var "p",
          apps hSetPathEtaD.ref [A, B, .var "p"]],
        apps cong11D.ref
          [.path .univ (.fst A) (.fst B), PT,
           .lam "u0" (apps hSetPathD.ref [A, B, .var "u0"]),
           congFstH A B (.var "p"), congFstH A B (.var "q"), .var "w"]],
      apps hSetPathEtaD.ref [A, B, .var "q"]])

#guard hSetPathUniqueD.ok

/-- **`hSet` is a groupoid** — via the carrier-path retraction and
`isSetPathU`. -/
def isGroupoidHSetD : LibDef where
  name := "isGroupoidHSet"
  ty := isGpdR hSetTy
  tm := lams ["a", "b"] (apps isSetRetract11D.ref
    [.path hSetTy (.var "a") (.var "b"),
     .path .univ (.fst (.var "a")) (.fst (.var "b")),
     .lam "p" (congFstH (.var "a") (.var "b") (.var "p")),
     .lam "u" (apps hSetPathD.ref [.var "a", .var "b", .var "u"]),
     .lam "p" (apps hSetPathEtaD.ref [.var "a", .var "b", .var "p"]),
     apps isSetPathUD.ref
       [.fst (.var "a"), .fst (.var "b"), .snd (.var "b")]])

#guard isGroupoidHSetD.ok

/-! ## Group plumbing: right multiplication is an equivalence -/

private def gCf (G : Raw) : Raw := .fst G
private def gmf (G : Raw) : Raw := .fst (.snd G)
private def gef (G : Raw) : Raw := .fst (.snd (.snd G))
private def gif (G : Raw) : Raw := .fst (.snd (.snd (.snd G)))
private def gassocf (G : Raw) : Raw := .fst (.snd (.snd (.snd (.snd G))))
private def gunitLf (G : Raw) : Raw :=
  .fst (.snd (.snd (.snd (.snd (.snd G)))))
private def gunitRf (G : Raw) : Raw :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd G))))))
private def ginvLf (G : Raw) : Raw :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd G)))))))
private def ginvRf (G : Raw) : Raw :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
private def gsetf (G : Raw) : Raw :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd G))))))))
private def gmul (G a b : Raw) : Raw := .app (.app (gmf G) a) b

/-- Right multiplication by a group element is an equivalence. -/
def mulREquivD : LibDef where
  name := "mulREquiv"
  ty := .pi "G" groupTy (.arr (gCf (.var "G"))
    (equivR (gCf (.var "G")) (gCf (.var "G"))))
  tm :=
    let G : Raw := .var "G"
    let C : Raw := gCf G
    let ig : Raw := .app (gif G) (.var "g")
    -- m (m x a) b ≡ m x c whenever m a b ≡ c pointwise:
    let side (a b lawPath : Raw) : Raw :=
      -- Π x. m (m x a) b ≡ x : assoc, then the inverse law, then unitR
      .lam "x" (apps transD.ref [C,
        gmul G (gmul G (.var "x") a) b,
        gmul G (.var "x") (gmul G a b),
        .var "x",
        apps (gassocf G) [.var "x", a, b],
        apps transD.ref [C,
          gmul G (.var "x") (gmul G a b),
          gmul G (.var "x") (gef G),
          .var "x",
          apps congD.ref [C, C,
            .lam "y0" (gmul G (.var "x") (.var "y0")),
            gmul G a b, gef G, lawPath],
          .app (gunitRf G) (.var "x")]])
    lams ["G", "g"] (apps setIsoToEquivD.ref
      [C, C,
       .lam "x" (gmul G (.var "x") (.var "g")),
       .lam "x" (gmul G (.var "x") ig),
       side ig (.var "g") (.app (ginvLf G) (.var "g")),
       side (.var "g") ig (.app (ginvRf G) (.var "g")),
       gsetf G])

#guard mulREquivD.ok

/-- Equivalences with equal underlying functions are equal. -/
def equivEqD : LibDef where
  name := "equivEq"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "e1" (equivR (.var "A") (.var "B"))
    (.pi "e2" (equivR (.var "A") (.var "B"))
    (.arr (.path (.arr (.var "A") (.var "B"))
        (.fst (.var "e1")) (.fst (.var "e2")))
      (.path (equivR (.var "A") (.var "B")) (.var "e1") (.var "e2"))))))
  tm := lams ["A", "B", "e1", "e2"] (apps sigmaPropEqD.ref
    [.arr (.var "A") (.var "B"),
     .lam "f" (.pi "yb" (.var "B")
       (isContrR (fiberR (.var "A") (.var "B") (.var "f") (.var "yb")))),
     .lam "f" (apps isPropIsEquivD.ref [.var "A", .var "B", .var "f"]),
     .var "e1", .var "e2"])

#guard equivEqD.ok

/-- `ua` is injective (paths in the universe with equal transports agree). -/
def uaInjD : LibDef where
  name := "uaInj"
  ty := .pi "X" .univ (.pi "Y" .univ
    (.pi "p" (.path .univ (.var "X") (.var "Y"))
    (.pi "q" (.path .univ (.var "X") (.var "Y"))
    (.arr (.path (equivR (.var "X") (.var "Y"))
        (apps pathToEquivD.ref [.var "X", .var "Y", .var "p"])
        (apps pathToEquivD.ref [.var "X", .var "Y", .var "q"]))
      (.path (.path .univ (.var "X") (.var "Y")) (.var "p") (.var "q"))))))
  tm :=
    let PU : Raw := .path .univ (.var "X") (.var "Y")
    let uaXY (e : Raw) : Raw := apps uaD.ref [.var "X", .var "Y", e]
    let pte (pp : Raw) : Raw :=
      apps pathToEquivD.ref [.var "X", .var "Y", pp]
    lams ["X", "Y", "p", "q", "w"] (apps trans1D.ref [PU,
      .var "p", uaXY (pte (.var "q")), .var "q",
      apps trans1D.ref [PU,
        .var "p", uaXY (pte (.var "p")), uaXY (pte (.var "q")),
        apps symm1D.ref [PU, uaXY (pte (.var "p")), .var "p",
          apps uaEtaD.ref [.var "X", .var "Y", .var "p"]],
        apps cong01D.ref [equivR (.var "X") (.var "Y"), PU,
          .lam "e0" (uaXY (.var "e0")),
          pte (.var "p"), pte (.var "q"), .var "w"]],
      apps uaEtaD.ref [.var "X", .var "Y", .var "q"]])

#guard uaInjD.ok

/-! ## The `Codes` family over `K(G,1)`

`ua` of right multiplications composes (`uaCompMul` — the underlying
transports are *definitional*, so only associativity is a real path);
lifted to `hSet` by `hSetPathUnique`, the composition cell is the
`trans`-filler corrected along that identification. -/

private def mR (G g : Raw) : Raw := apps mulREquivD.ref [G, g]
private def uaC (G e : Raw) : Raw := apps uaD.ref [gCf G, gCf G, e]
private def CS (G : Raw) : Raw := .pair (gCf G) (gsetf G)
private def lG (G g : Raw) : Raw :=
  apps hSetPathD.ref [CS G, CS G, uaC G (mR G g)]
private def puC (G : Raw) : Raw := .path .univ (gCf G) (gCf G)

/-- `ua (·(g·h)) ≡ ua (·g) ⬝ ua (·h)`. -/
def uaCompMulD : LibDef where
  name := "uaCompMul"
  ty := .pi "G" groupTy
    (.pi "g" (gCf (.var "G")) (.pi "h" (gCf (.var "G"))
      (.path (puC (.var "G"))
        (uaC (.var "G") (mR (.var "G")
          (gmul (.var "G") (.var "g") (.var "h"))))
        (apps trans1D.ref [.univ, gCf (.var "G"), gCf (.var "G"),
          gCf (.var "G"),
          uaC (.var "G") (mR (.var "G") (.var "g")),
          uaC (.var "G") (mR (.var "G") (.var "h"))]))))
  tm :=
    let G : Raw := .var "G"
    let C : Raw := gCf G
    let lhsP : Raw := uaC G (mR G (gmul G (.var "g") (.var "h")))
    let rhsP : Raw := apps trans1D.ref [.univ, C, C, C,
      uaC G (mR G (.var "g")), uaC G (mR G (.var "h"))]
    let pte (pp : Raw) : Raw := apps pathToEquivD.ref [C, C, pp]
    lams ["G", "g", "h"] (apps uaInjD.ref [C, C, lhsP, rhsP,
      apps equivEqD.ref [C, C, pte lhsP, pte rhsP,
        apps funExtD.ref [C, C,
          .fst (pte lhsP), .fst (pte rhsP),
          .lam "x" (apps symmD.ref [C,
            gmul G (gmul G (.var "x") (.var "g")) (.var "h"),
            gmul G (.var "x") (gmul G (.var "g") (.var "h")),
            apps (gassocf G) [.var "x", .var "g", .var "h"]])]]])

-- #guard uaCompMulD.ok (heavy)

/-- The `hSet`-level composition identification. -/
def lGCompD : LibDef where
  name := "lGComp"
  ty := .pi "G" groupTy
    (.pi "g" (gCf (.var "G")) (.pi "h" (gCf (.var "G"))
      (.path (.path hSetTy (CS (.var "G")) (CS (.var "G")))
        (lG (.var "G") (gmul (.var "G") (.var "g") (.var "h")))
        (apps trans1D.ref [hSetTy, CS (.var "G"), CS (.var "G"),
          CS (.var "G"),
          lG (.var "G") (.var "g"), lG (.var "G") (.var "h")]))))
  tm :=
    let G : Raw := .var "G"
    lams ["G", "g", "h"] (apps hSetPathUniqueD.ref
      [CS G, CS G,
       lG G (gmul G (.var "g") (.var "h")),
       apps trans1D.ref [hSetTy, CS G, CS G, CS G,
         lG G (.var "g"), lG G (.var "h")],
       apps uaCompMulD.ref [G, .var "g", .var "h"]])

-- #guard lGCompD.ok (heavy)

/-- **The `Codes` family** — `em1rec` into the groupoid `hSet`; the
composition cell is the `trans`-filler corrected along `lGComp`. -/
def codesD : LibDef where
  name := "codes"
  ty := .pi "G" groupTy
    (.arr (.em1 (gCf (.var "G")) (gmf (.var "G"))) hSetTy)
  tm :=
    let G : Raw := .var "G"
    let cs : Raw := CS G
    let lgh : Raw := lG G (.var "h")
    let lgg : Raw := lG G (.var "g")
    let lmgh : Raw := lG G (gmul G (.var "g") (.var "h"))
    let PT (e : Raw) : Raw := .path hSetTy cs e
    let lghAt (e : Raw) : Raw := .papp lgh cs cs e
    let lggAt (e : Raw) : Raw := .papp lgg cs cs e
    -- hfill of trans (lG g) (lG h) in direction j
    let filler : Raw := .hcomp "k2" hSetTy
      [([(.var "i", false)], cs),
       ([(.var "i", true)], lghAt (.imin (.var "k2") (.var "j"))),
       ([(.var "j", false)], lggAt (.var "i"))]
      (lggAt (.var "i"))
    let transGH : Raw := apps trans1D.ref [hSetTy, cs, cs, cs, lgg, lgh]
    let ccell : Raw := .plam "j" (.hcomp "k"
      (PT (lghAt (.var "j")))
      [([(.var "j", false)], lgg),
       ([(.var "j", true)],
         .papp (apps symm1D.ref [.path hSetTy cs cs, lmgh, transGH,
             apps lGCompD.ref [G, .var "g", .var "h"]])
           transGH lmgh (.var "k"))]
      (.plam "i" filler))
    lams ["G", "x"] (.em1rec hSetTy isGroupoidHSetD.ref cs
      (.lam "g" (lG G (.var "g")))
      (lams ["g", "h"] ccell)
      (.var "x"))

-- #guard codesD.ok (heavy)

/-- `encode : embase ≡ x → ⟨Codes x⟩`. -/
def encodeEMD : LibDef where
  name := "encodeEM"
  ty := .pi "G" groupTy
    (.pi "x" (.em1 (gCf (.var "G")) (gmf (.var "G")))
    (.arr (.path (.em1 (gCf (.var "G")) (gmf (.var "G"))) .embase (.var "x"))
      (.fst (apps codesD.ref [.var "G", .var "x"]))))
  tm := lams ["G", "x", "p"] (.transp "i"
    (.fst (apps codesD.ref [.var "G",
      .papp (.var "p") .embase (.var "x") (.var "i")]))
    (gef (.var "G")))

-- #guard encodeEMD.ok (heavy)

/-! ## Decode and `π₁(K(G,1)) ≃ G`

`EM₁` is a groupoid by its own constructor; the decode loop-cell is the
Π-level `hcomp` (the Γ-restriction workaround) whose base is the **`emcomp`
constructor itself**, corrected on both faces by the group inverse laws;
the composition-cell obligation lands in a family of *sets*, so
`isPropPathPSet` discharges it. -/

/-- EM₁ is a groupoid — the truncation constructor. -/
def isGpdEMD : LibDef where
  name := "isGpdEM"
  ty := .pi "C" .univ
    (.pi "m" (.arr (.var "C") (.arr (.var "C") (.var "C")))
      (isGpdR (.em1 (.var "C") (.var "m"))))
  tm := lams ["C", "m", "a", "b", "p", "q", "r", "s"]
    (.plam "i1" (.plam "i2" (.plam "i3"
      (.emsquash (.var "a") (.var "b") (.var "p") (.var "q")
        (.var "r") (.var "s") (.var "i1") (.var "i2") (.var "i3")))))

/-- Groupoids are closed under function types (η-driven). -/
def isGpdPiD : LibDef where
  name := "isGpdPi"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (isGpdR (.var "B")) (isGpdR (.arr (.var "A") (.var "B")))))
  tm :=
    let FT : Raw := .arr (.var "A") (.var "B")
    let fx : Raw := .app (.var "f") (.var "x")
    let gx : Raw := .app (.var "g") (.var "x")
    let c1 (pp : Raw) : Raw := apps congD.ref [FT, .var "B",
      .lam "w0" (.app (.var "w0") (.var "x")), .var "f", .var "g", pp]
    let c2 (rr : Raw) : Raw := apps congD.ref
      [.path FT (.var "f") (.var "g"),
       .path (.var "B") fx gx,
       .lam "w1" (apps congD.ref [FT, .var "B",
         .lam "w0" (.app (.var "w0") (.var "x")),
         .var "f", .var "g", .var "w1"]),
       .var "p", .var "q", rr]
    lams ["A", "B", "gB", "f", "g", "p", "q", "r", "s"]
      (.plam "i" (.plam "j" (.plam "k" (.lam "x"
        (.papp
          (.papp
            (.papp
              (apps (.var "gB") [fx, gx, c1 (.var "p"), c1 (.var "q"),
                c2 (.var "r"), c2 (.var "s")])
              (c2 (.var "r")) (c2 (.var "s")) (.var "i"))
            (c1 (.var "p")) (c1 (.var "q")) (.var "j"))
          fx gx (.var "k"))))))

#guard isGpdPiD.ok

#guard isGpdEMD.ok

private def emTyG (G : Raw) : Raw := .em1 (gCf G) (gmf G)
private def emPathT (G x : Raw) : Raw := .path (emTyG G) .embase x
private def loopT2 (G : Raw) : Raw := emPathT G .embase
private def emloopP (G z : Raw) : Raw :=
  apps emloopD.ref [gCf G, gmf G, z]
private def codesFst (G x : Raw) : Raw := .fst (apps codesD.ref [G, x])

/-- `decode`, by the dependent eliminator: the loop cell is a Π-level
`hcomp` whose base is the `emcomp` constructor, corrected on both faces
by the inverse laws. -/
def decodeEMD : LibDef where
  name := "decodeEM"
  ty := .pi "G" groupTy (.pi "x" (emTyG (.var "G"))
    (.arr (codesFst (.var "G") (.var "x"))
      (emPathT (.var "G") (.var "x"))))
  tm :=
    let G : Raw := .var "G"
    let C : Raw := gCf G
    let mT : Raw := gmf G
    let iv (g : Raw) : Raw := .app (gif G) g
    -- chains  m (m y a) b ≡ y  given  m a b ≡ e
    let chain (y a b lawPath : Raw) : Raw :=
      apps transD.ref [C,
        gmul G (gmul G y a) b, gmul G y (gmul G a b), y,
        apps (gassocf G) [y, a, b],
        apps transD.ref [C,
          gmul G y (gmul G a b), gmul G y (gef G), y,
          apps congD.ref [C, C, .lam "y0" (gmul G y (.var "y0")),
            gmul G a b, gef G, lawPath],
          .app (gunitRf G) y]]
    let bcase : Raw := .lam "z" (emloopP G (.var "z"))
    -- the loop cell at a generic g
    let gV : Raw := .var "g"
    let ung : Raw := .unglue (codesFst G (.emloop gV (.var "i"))) (.var "y")
    let dsBase : Raw := .lam "y" (.plam "s0"
      (.emcomp mT (gmul G ung (iv gV)) gV (.var "i") (.var "s0")))
    let lcell : Raw := .lam "g" (.plam "i" (.hcomp "k"
      (.arr (codesFst G (.emloop gV (.var "i")))
        (emPathT G (.emloop gV (.var "i"))))
      [([(.var "i", false)],
         .lam "y" (.papp
           (apps congD.ref [C, loopT2 G,
             .lam "z0" (emloopP G (.var "z0")),
             gmul G (gmul G (.var "y") gV) (iv gV), .var "y",
             chain (.var "y") gV (iv gV) (.app (ginvRf G) gV)])
           (emloopP G (gmul G (gmul G (.var "y") gV) (iv gV)))
           (emloopP G (.var "y")) (.var "k"))),
       ([(.var "i", true)],
         .lam "y" (.papp
           (apps congD.ref [C, loopT2 G,
             .lam "z0" (emloopP G (.var "z0")),
             gmul G (gmul G (.var "y") (iv gV)) gV, .var "y",
             chain (.var "y") (iv gV) gV (.app (ginvLf G) gV)])
           (emloopP G (gmul G (gmul G (.var "y") (iv gV)) gV))
           (emloopP G (.var "y")) (.var "k")))]
      dsBase))
    -- the comp-cell obligation: a PathP over a line of propositions
    let motAt (x : Raw) : Raw := .arr (codesFst G x) (emPathT G x)
    let msetFam : Raw := .lam "x0" (apps isSetPiD.ref
      [codesFst G (.var "x0"), emPathT G (.var "x0"),
       apps isGpdEMD.ref [C, mT, .embase, .var "x0"]])
    let hV : Raw := .var "h"
    let mgh : Raw := gmul G gV hV
    let Lof (jE : Raw) : Raw := .pathP "i2"
      (motAt (.emcomp mT gV hV jE (.var "i2")))
      bcase
      (.papp (.ann lcell (.pi "g0" C (.pathP "i3"
          (motAt (.emloop (.var "g0") (.var "i3"))) bcase bcase))
        |> fun lc => .app lc hV) bcase bcase jE)
    let ccell : Raw :=
      let line : Raw := .plam "j0" (Lof (.var "j0"))
      let lcAnn : Raw := .ann lcell (.pi "g0" C (.pathP "i3"
        (motAt (.emloop (.var "g0") (.var "i3"))) bcase bcase))
      lams ["g", "h"] (apps toPathPD.ref
        [Lof .i0, Lof .i1, line,
         .app lcAnn gV, .app lcAnn mgh,
         apps isPropPathPSetD.ref
           [emTyG G, .lam "x0" (motAt (.var "x0")), msetFam,
            .embase, bcase, .embase, emloopP G mgh, bcase,
            apps transportD.ref [Lof .i0, Lof .i1, line, .app lcAnn gV],
            .app lcAnn mgh]])
    lams ["G", "x"] (.em1elim "x2" (motAt (.var "x2"))
      (.lam "x2" (apps isGpdPiD.ref
        [codesFst G (.var "x2"), emPathT G (.var "x2"),
         apps isSetToGpdD.ref [emPathT G (.var "x2"),
           apps isGpdEMD.ref [C, mT, .embase, .var "x2"]]]))
      bcase lcell ccell (.var "x"))

-- #guard decodeEMD.ok (heavy)

/-- `encode (emloop z) ≡ z` — definitional up to the left unit law. -/
def encodeLoopD : LibDef where
  name := "encodeLoop"
  ty := .pi "G" groupTy (.pi "z" (gCf (.var "G"))
    (.path (gCf (.var "G"))
      (apps encodeEMD.ref [.var "G", .embase, emloopP (.var "G") (.var "z")])
      (.var "z")))
  tm := lams ["G", "z"] (.app (gunitLf (.var "G")) (.var "z"))

/-- `decode (encode p) ≡ p`, by `J` (the `refl` case is `emloopOne`). -/
def decodeEncodeEMD : LibDef where
  name := "decodeEncodeEM"
  ty := .pi "G" groupTy (.pi "x" (emTyG (.var "G"))
    (.pi "p" (emPathT (.var "G") (.var "x"))
      (.path (emPathT (.var "G") (.var "x"))
        (apps decodeEMD.ref [.var "G", .var "x",
          apps encodeEMD.ref [.var "G", .var "x", .var "p"]])
        (.var "p"))))
  tm :=
    let G : Raw := .var "G"
    lams ["G", "x", "p"] (apps jD.ref [emTyG G, .embase,
      lams ["x2", "p2"] (.path (emPathT G (.var "x2"))
        (apps decodeEMD.ref [G, .var "x2",
          apps encodeEMD.ref [G, .var "x2", .var "p2"]])
        (.var "p2")),
      apps emloopOneD.ref [gCf G, gmf G, gef G,
        .app (gunitLf G) (gef G)],
      .var "x", .var "p"])

-- #guard encodeLoopD.ok (heavy)
-- #guard decodeEncodeEMD.ok (heavy)

/-- **`π₁(K(G,1)) ≃ G`** — the level-1 homotopy hypothesis, one direction
of "groups are pointed connected 1-types". -/
def pi1EM1D : LibDef where
  name := "pi1EM1"
  ty := .pi "G" groupTy (equivR (loopT2 (.var "G")) (gCf (.var "G")))
  tm :=
    let G : Raw := .var "G"
    .lam "G" (apps setIsoToEquivD.ref
      [loopT2 G, gCf G,
       .lam "p" (apps encodeEMD.ref [G, .embase, .var "p"]),
       .lam "z" (emloopP G (.var "z")),
       .lam "z" (apps encodeLoopD.ref [G, .var "z"]),
       .lam "p" (apps decodeEncodeEMD.ref [G, .embase, .var "p"]),
       gsetf G])

-- #guard pi1EM1D.ok (heavy)

end Cubical.Library

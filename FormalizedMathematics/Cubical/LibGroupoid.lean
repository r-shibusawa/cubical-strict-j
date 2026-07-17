import FormalizedMathematics.Cubical.LibSets

namespace Cubical.Library

open Raw

/-! ## Two-dimensional path algebra

The groupoid laws of path composition are *squares*, proven by `hcomp`
fillers (units) and by `J` (associativity). -/

/-- `symm (symm p) ≡ p` holds by `refl`: the De Morgan involution is
strict (`¬¬i` cancels in the interval algebra). -/
def symmInvolD : LibDef where
  name := "symmInvol"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps symmD.ref [.var "A", .var "b", .var "a",
          apps symmD.ref [.var "A", .var "a", .var "b", .var "p"]])
        (.var "p")))))
  tm := lams ["A", "a", "b", "p"] (.plam "j" (.var "p"))

/-- Right unit: `p ⬝ refl ≡ p`, by capping the composition square. -/
def transReflRD : LibDef where
  name := "transReflR"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps transD.ref [.var "A", .var "a", .var "b", .var "b", .var "p",
          apps reflD.ref [.var "A", .var "b"]])
        (.var "p")))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "j" (.plam "i" (.hcomp "k" (.var "A")
      [([(.var "i", false)], .var "a"),
       ([(.var "i", true)], .var "b"),
       ([(.var "j", true)],
         .papp (.var "p") (.var "a") (.var "b") (.var "i"))]
      (.papp (.var "p") (.var "a") (.var "b") (.var "i")))))

/-- Left unit: `refl ⬝ p ≡ p`, by a connection-shaped cap. -/
def transReflLD : LibDef where
  name := "transReflL"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps transD.ref [.var "A", .var "a", .var "a", .var "b",
          apps reflD.ref [.var "A", .var "a"], .var "p"])
        (.var "p")))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "j" (.plam "i" (.hcomp "k" (.var "A")
      [([(.var "i", false)], .var "a"),
       ([(.var "i", true)],
         .papp (.var "p") (.var "a") (.var "b") (.var "k")),
       ([(.var "j", true)],
         .papp (.var "p") (.var "a") (.var "b")
           (.imin (.var "i") (.var "k")))]
      (.var "a"))))

#guard symmInvolD.ok
#guard transReflRD.ok
#guard transReflLD.ok

/-- Associativity of composition, by `J` on the third path: the `refl` case
reduces to the right-unit square, transported through `cong`. -/
def transAssocD : LibDef where
  name := "transAssoc"
  ty := .pi "A" .univ (.pi "w" (.var "A") (.pi "x" (.var "A")
    (.pi "y" (.var "A") (.pi "z" (.var "A")
    (.pi "p" (.path (.var "A") (.var "w") (.var "x"))
    (.pi "q" (.path (.var "A") (.var "x") (.var "y"))
    (.pi "r" (.path (.var "A") (.var "y") (.var "z"))
      (.path (.path (.var "A") (.var "w") (.var "z"))
        (apps transD.ref [.var "A", .var "w", .var "y", .var "z",
          apps transD.ref [.var "A", .var "w", .var "x", .var "y",
            .var "p", .var "q"],
          .var "r"])
        (apps transD.ref [.var "A", .var "w", .var "x", .var "z", .var "p",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z",
            .var "q", .var "r"]])))))))))
  tm :=
    -- shorthands (Lean-level): the composite p⬝q and the two unit lemmas
    let pq := apps transD.ref [.var "A", .var "w", .var "x", .var "y",
      .var "p", .var "q"]
    let qRefl := apps transD.ref [.var "A", .var "x", .var "y", .var "y",
      .var "q", apps reflD.ref [.var "A", .var "y"]]
    let pqRefl := apps transD.ref [.var "A", .var "w", .var "y", .var "y",
      pq, apps reflD.ref [.var "A", .var "y"]]
    let pQRefl := apps transD.ref [.var "A", .var "w", .var "x", .var "y",
      .var "p", qRefl]
    let pathWY := .path (.var "A") (.var "w") (.var "y")
    -- cong (trans p ·) (transReflR q) : Path (p ⬝ (q ⬝ refl)) (p ⬝ q)
    let congStep := apps congD.ref
      [.path (.var "A") (.var "x") (.var "y"), pathWY,
       .lam "s" (apps transD.ref [.var "A", .var "w", .var "x", .var "y",
         .var "p", .var "s"]),
       qRefl, .var "q",
       apps transReflRD.ref [.var "A", .var "x", .var "y", .var "q"]]
    -- d : Path ((p⬝q)⬝refl) (p⬝(q⬝refl))
    let dCase := apps transD.ref
      [pathWY, pqRefl, pq, pQRefl,
       apps transReflRD.ref [.var "A", .var "w", .var "y", pq],
       apps symmD.ref [pathWY, pQRefl, pq, congStep]]
    let motive := .lam "z2" (.lam "r2"
      (.path (.path (.var "A") (.var "w") (.var "z2"))
        (apps transD.ref [.var "A", .var "w", .var "y", .var "z2",
          pq, .var "r2"])
        (apps transD.ref [.var "A", .var "w", .var "x", .var "z2", .var "p",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z2",
            .var "q", .var "r2"]])))
    lams ["A", "w", "x", "y", "z", "p", "q", "r"]
      (apps jD.ref [.var "A", .var "y", motive, dCase, .var "z", .var "r"])

#guard transAssocD.ok

/-! ## The fundamental groupoid (as a precategory)

Objects: points of `A`; morphisms: paths; identity: `refl`; composition:
`trans`; the laws are the squares just proven.  `Ob := A : U₀` is accepted
at `Ob : U₁` by universe subsumption. -/

def pathPrecatD : LibDef where
  name := "pathPrecat"
  ty := .pi "A" .univ (precatTy 0)
  tm := .lam "A"
    (.pair (.var "A")
      (.pair (lams ["x", "y"] (.path (.var "A") (.var "x") (.var "y")))
        (.pair (.lam "x" (apps reflD.ref [.var "A", .var "x"]))
          (.pair (lams ["x", "y", "z", "f", "g"]
            (apps transD.ref [.var "A", .var "x", .var "y", .var "z",
              .var "f", .var "g"]))
            (.pair (lams ["x", "y", "f"]
              (apps transReflLD.ref [.var "A", .var "x", .var "y", .var "f"]))
              (.pair (lams ["x", "y", "f"]
                (apps transReflRD.ref [.var "A", .var "x", .var "y", .var "f"]))
                (lams ["w", "x", "y", "z", "f", "g", "h"]
                  (apps transAssocD.ref [.var "A", .var "w", .var "x",
                    .var "y", .var "z", .var "f", .var "g", .var "h"]))))))))

#guard pathPrecatD.ok

/-! ## Commutativity of addition -/

/-- `(suc a) + b ≡ suc (a + b)`. -/
def addSucLD : LibDef where
  name := "addSucL"
  ty := .pi "a" .int (.pi "b" .int
    (.path .int
      (apps addD.ref [.app sucZD.ref (.var "a"), .var "b"])
      (.app sucZD.ref (apps addD.ref [.var "a", .var "b"]))))
  tm :=
    let sa := .app sucZD.ref (.var "a")
    lams ["a", "b"] (.intcase "k"
      (.path .int (apps addD.ref [sa, .var "k"])
        (.app sucZD.ref (apps addD.ref [.var "a", .var "k"])))
      (.lam "n" (.natrec "k2"
        (.path .int (apps addD.ref [sa, .ipos (.var "k2")])
          (.app sucZD.ref (apps addD.ref [.var "a", .ipos (.var "k2")])))
        (.plam "i" sa)
        (lams ["m", "ih"] (apps congD.ref [.int, .int, sucZD.ref,
          apps addD.ref [sa, .ipos (.var "m")],
          .app sucZD.ref (apps addD.ref [.var "a", .ipos (.var "m")]),
          .var "ih"]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path .int (apps addD.ref [sa, .inegsuc (.var "k2")])
          (.app sucZD.ref (apps addD.ref [.var "a", .inegsuc (.var "k2")])))
        (apps transD.ref [.int,
          .app predZD.ref sa, .var "a",
          .app sucZD.ref (.app predZD.ref (.var "a")),
          .app predSucZD.ref (.var "a"),
          apps symmD.ref [.int,
            .app sucZD.ref (.app predZD.ref (.var "a")), .var "a",
            .app sucPredZD.ref (.var "a")]])
        (lams ["m", "ih"]
          (apps transD.ref [.int,
            .app predZD.ref (apps addD.ref [sa, .inegsuc (.var "m")]),
            .app predZD.ref (.app sucZD.ref
              (apps addD.ref [.var "a", .inegsuc (.var "m")])),
            .app sucZD.ref (.app predZD.ref
              (apps addD.ref [.var "a", .inegsuc (.var "m")])),
            apps congD.ref [.int, .int, predZD.ref,
              apps addD.ref [sa, .inegsuc (.var "m")],
              .app sucZD.ref (apps addD.ref [.var "a", .inegsuc (.var "m")]),
              .var "ih"],
            apps transD.ref [.int,
              .app predZD.ref (.app sucZD.ref
                (apps addD.ref [.var "a", .inegsuc (.var "m")])),
              apps addD.ref [.var "a", .inegsuc (.var "m")],
              .app sucZD.ref (.app predZD.ref
                (apps addD.ref [.var "a", .inegsuc (.var "m")])),
              .app predSucZD.ref (apps addD.ref [.var "a", .inegsuc (.var "m")]),
              apps symmD.ref [.int,
                .app sucZD.ref (.app predZD.ref
                  (apps addD.ref [.var "a", .inegsuc (.var "m")])),
                apps addD.ref [.var "a", .inegsuc (.var "m")],
                .app sucPredZD.ref
                  (apps addD.ref [.var "a", .inegsuc (.var "m")])]]]))
        (.var "n")))
      (.var "b"))

/-- `(pred a) + b ≡ pred (a + b)`. -/
def addPredLD : LibDef where
  name := "addPredL"
  ty := .pi "a" .int (.pi "b" .int
    (.path .int
      (apps addD.ref [.app predZD.ref (.var "a"), .var "b"])
      (.app predZD.ref (apps addD.ref [.var "a", .var "b"]))))
  tm :=
    let pa := .app predZD.ref (.var "a")
    lams ["a", "b"] (.intcase "k"
      (.path .int (apps addD.ref [pa, .var "k"])
        (.app predZD.ref (apps addD.ref [.var "a", .var "k"])))
      (.lam "n" (.natrec "k2"
        (.path .int (apps addD.ref [pa, .ipos (.var "k2")])
          (.app predZD.ref (apps addD.ref [.var "a", .ipos (.var "k2")])))
        (.plam "i" pa)
        (lams ["m", "ih"]
          (apps transD.ref [.int,
            .app sucZD.ref (apps addD.ref [pa, .ipos (.var "m")]),
            .app sucZD.ref (.app predZD.ref
              (apps addD.ref [.var "a", .ipos (.var "m")])),
            .app predZD.ref (.app sucZD.ref
              (apps addD.ref [.var "a", .ipos (.var "m")])),
            apps congD.ref [.int, .int, sucZD.ref,
              apps addD.ref [pa, .ipos (.var "m")],
              .app predZD.ref (apps addD.ref [.var "a", .ipos (.var "m")]),
              .var "ih"],
            apps transD.ref [.int,
              .app sucZD.ref (.app predZD.ref
                (apps addD.ref [.var "a", .ipos (.var "m")])),
              apps addD.ref [.var "a", .ipos (.var "m")],
              .app predZD.ref (.app sucZD.ref
                (apps addD.ref [.var "a", .ipos (.var "m")])),
              .app sucPredZD.ref (apps addD.ref [.var "a", .ipos (.var "m")]),
              apps symmD.ref [.int,
                .app predZD.ref (.app sucZD.ref
                  (apps addD.ref [.var "a", .ipos (.var "m")])),
                apps addD.ref [.var "a", .ipos (.var "m")],
                .app predSucZD.ref
                  (apps addD.ref [.var "a", .ipos (.var "m")])]]]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path .int (apps addD.ref [pa, .inegsuc (.var "k2")])
          (.app predZD.ref (apps addD.ref [.var "a", .inegsuc (.var "k2")])))
        (.plam "i" (.app predZD.ref pa))
        (lams ["m", "ih"] (apps congD.ref [.int, .int, predZD.ref,
          apps addD.ref [pa, .inegsuc (.var "m")],
          .app predZD.ref (apps addD.ref [.var "a", .inegsuc (.var "m")]),
          .var "ih"]))
        (.var "n")))
      (.var "b"))

/-- Commutativity `a + b ≡ b + a`. -/
def addCommD : LibDef where
  name := "addComm"
  ty := .pi "a" .int (.pi "b" .int
    (.path .int (apps addD.ref [.var "a", .var "b"])
      (apps addD.ref [.var "b", .var "a"])))
  tm := lams ["a", "b"] (.intcase "k"
    (.path .int (apps addD.ref [.var "a", .var "k"])
      (apps addD.ref [.var "k", .var "a"]))
    (.lam "n" (.natrec "k2"
      (.path .int (apps addD.ref [.var "a", .ipos (.var "k2")])
        (apps addD.ref [.ipos (.var "k2"), .var "a"]))
      (apps symmD.ref [.int,
        apps addD.ref [posZ 0, .var "a"], .var "a",
        .app addZeroLD.ref (.var "a")])
      (lams ["m", "ih"]
        (apps transD.ref [.int,
          .app sucZD.ref (apps addD.ref [.var "a", .ipos (.var "m")]),
          .app sucZD.ref (apps addD.ref [.ipos (.var "m"), .var "a"]),
          apps addD.ref [.ipos (.succ (.var "m")), .var "a"],
          apps congD.ref [.int, .int, sucZD.ref,
            apps addD.ref [.var "a", .ipos (.var "m")],
            apps addD.ref [.ipos (.var "m"), .var "a"],
            .var "ih"],
          apps symmD.ref [.int,
            apps addD.ref [.ipos (.succ (.var "m")), .var "a"],
            .app sucZD.ref (apps addD.ref [.ipos (.var "m"), .var "a"]),
            apps addSucLD.ref [.ipos (.var "m"), .var "a"]]]))
      (.var "n")))
    (.lam "n" (.natrec "k2"
      (.path .int (apps addD.ref [.var "a", .inegsuc (.var "k2")])
        (apps addD.ref [.inegsuc (.var "k2"), .var "a"]))
      (apps symmD.ref [.int,
        apps addD.ref [.inegsuc .zero, .var "a"],
        .app predZD.ref (.var "a"),
        apps transD.ref [.int,
          apps addD.ref [.inegsuc .zero, .var "a"],
          .app predZD.ref (apps addD.ref [posZ 0, .var "a"]),
          .app predZD.ref (.var "a"),
          apps addPredLD.ref [posZ 0, .var "a"],
          apps congD.ref [.int, .int, predZD.ref,
            apps addD.ref [posZ 0, .var "a"], .var "a",
            .app addZeroLD.ref (.var "a")]]])
      (lams ["m", "ih"]
        (apps transD.ref [.int,
          .app predZD.ref (apps addD.ref [.var "a", .inegsuc (.var "m")]),
          .app predZD.ref (apps addD.ref [.inegsuc (.var "m"), .var "a"]),
          apps addD.ref [.inegsuc (.succ (.var "m")), .var "a"],
          apps congD.ref [.int, .int, predZD.ref,
            apps addD.ref [.var "a", .inegsuc (.var "m")],
            apps addD.ref [.inegsuc (.var "m"), .var "a"],
            .var "ih"],
          apps symmD.ref [.int,
            apps addD.ref [.inegsuc (.succ (.var "m")), .var "a"],
            .app predZD.ref (apps addD.ref [.inegsuc (.var "m"), .var "a"]),
            apps addPredLD.ref [.inegsuc (.var "m"), .var "a"]]]))
      (.var "n")))
    (.var "b"))

#guard addSucLD.ok
#guard addPredLD.ok
#guard addCommD.ok


/-! ## Natural transformations -/

def catIdl (c : Raw) : Raw := .fst (.snd (.snd (.snd (.snd c))))
def catIdr (c : Raw) : Raw := .fst (.snd (.snd (.snd (.snd (.snd c)))))

def funF0 (F : Raw) : Raw := .fst F
def funF1 (F : Raw) : Raw := .fst (.snd F)

/-- The naturality condition for a component family `eta`. -/
def natSquareTy (C D F G eta : Raw) : Raw :=
  .pi "x" (catOb C) (.pi "y" (catOb C)
    (.pi "f" (apps (catHom C) [.var "x", .var "y"])
      (.path (apps (catHom D) [.app (funF0 F) (.var "x"),
          .app (funF0 G) (.var "y")])
        (apps (catCmp D)
          [.app (funF0 F) (.var "x"), .app (funF0 F) (.var "y"),
           .app (funF0 G) (.var "y"),
           apps (funF1 F) [.var "x", .var "y", .var "f"],
           .app eta (.var "y")])
        (apps (catCmp D)
          [.app (funF0 F) (.var "x"), .app (funF0 G) (.var "x"),
           .app (funF0 G) (.var "y"),
           .app eta (.var "x"),
           apps (funF1 G) [.var "x", .var "y", .var "f"]]))))

/-- Natural transformations between functors `F G : C → D`. -/
def natTransTy (C D F G : Raw) : Raw :=
  .sigma "eta" (.pi "x" (catOb C)
    (apps (catHom D) [.app (funF0 F) (.var "x"), .app (funF0 G) (.var "x")]))
    (natSquareTy C D F G (.var "eta"))

/-- The identity natural transformation on any functor: naturality is
`idr ⬝ idl⁻¹` — an abstract proof using the category's law fields. -/
def idNatD : LibDef where
  name := "idNat"
  ty := .pi "C" (precatTy 0) (.pi "D" (precatTy 0)
    (.pi "F" (functorTy (.var "C") (.var "D"))
      (natTransTy (.var "C") (.var "D") (.var "F") (.var "F"))))
  tm :=
    let f0x := .app (funF0 (.var "F")) (.var "x")
    let f0y := .app (funF0 (.var "F")) (.var "y")
    let f1f := apps (funF1 (.var "F")) [.var "x", .var "y", .var "f"]
    let homD := apps (catHom (.var "D")) [f0x, f0y]
    let cmpFId := apps (catCmp (.var "D"))
      [f0x, f0y, f0y, f1f, .app (catId (.var "D")) f0y]
    let cmpIdF := apps (catCmp (.var "D"))
      [f0x, f0x, f0y, .app (catId (.var "D")) f0x, f1f]
    lams ["C", "D", "F"]
      (.pair
        (.lam "x" (.app (catId (.var "D")) (.app (funF0 (.var "F")) (.var "x"))))
        (lams ["x", "y", "f"]
          (apps transD.ref [homD, cmpFId, f1f, cmpIdF,
            apps (catIdr (.var "D")) [f0x, f0y, f1f],
            apps symmD.ref [homD, cmpIdF, f1f,
              apps (catIdl (.var "D")) [f0x, f0y, f1f]]])))

#guard idNatD.ok




/-! ## h-level theory -/

/-- Propositions are closed under Π (pointwise, by the funext shape). -/
def isPropPiD : LibDef where
  name := "isPropPi"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.arr (.pi "x" (.var "A") (isPropR (.app (.var "B") (.var "x"))))
      (.pi "f" (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
        (.pi "g" (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
          (.path (.pi "x" (.var "A") (.app (.var "B") (.var "x")))
            (.var "f") (.var "g"))))))
  tm := lams ["A", "B", "h", "f", "g"]
    (.plam "i" (.lam "x"
      (.papp (apps (.var "h") [.var "x", .app (.var "f") (.var "x"),
          .app (.var "g") (.var "x")])
        (.app (.var "f") (.var "x")) (.app (.var "g") (.var "x"))
        (.var "i"))))

/-- Contractible types are closed under Π (object-level weak funext). -/
def isContrPiD : LibDef where
  name := "isContrPi"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.arr (.pi "x" (.var "A") (isContrR (.app (.var "B") (.var "x"))))
      (isContrR (.pi "x" (.var "A") (.app (.var "B") (.var "x"))))))
  tm := lams ["A", "B", "h"]
    (.pair (.lam "x" (.fst (.app (.var "h") (.var "x"))))
      (.lam "f" (.plam "i" (.lam "x"
        (.papp (.app (.snd (.app (.var "h") (.var "x")))
            (.app (.var "f") (.var "x")))
          (.fst (.app (.var "h") (.var "x")))
          (.app (.var "f") (.var "x"))
          (.var "i"))))))

/-- **Propositions are sets** — the classic four-tube square: both `p` and
`q` are connected to the constant square through `h`, in one `hcomp`. -/
def isPropToIsSetD : LibDef where
  name := "isPropToIsSet"
  ty := .pi "A" .univ (.arr (isPropR (.var "A")) (isSetR (.var "A")))
  tm := lams ["A", "h", "a", "b", "p", "q"]
    (.plam "j" (.plam "i" (.hcomp "k" (.var "A")
      [([(.var "i", false)],
         .papp (apps (.var "h") [.var "a", .var "a"])
           (.var "a") (.var "a") (.var "k")),
       ([(.var "i", true)],
         .papp (apps (.var "h") [.var "a", .var "b"])
           (.var "a") (.var "b") (.var "k")),
       ([(.var "j", false)],
         .papp (apps (.var "h") [.var "a",
             .papp (.var "p") (.var "a") (.var "b") (.var "i")])
           (.var "a") (.papp (.var "p") (.var "a") (.var "b") (.var "i"))
           (.var "k")),
       ([(.var "j", true)],
         .papp (apps (.var "h") [.var "a",
             .papp (.var "q") (.var "a") (.var "b") (.var "i")])
           (.var "a") (.papp (.var "q") (.var "a") (.var "b") (.var "i"))
           (.var "k"))]
      (.var "a"))))

#guard isPropPiD.ok
#guard isContrPiD.ok
#guard isPropToIsSetD.ok

/-! ## `toPathP`: straightening a transport into a dependent path

Notable: the standard proof needs the φ-constrained `transp`; here the
`(i=0)` coherence holds *definitionally* because the interval smart
constructors collapse `A @ (0 ∧ j)` to a constant family. -/

def toPathPD : LibDef where
  name := "toPathP"
  ty := .pi "X" .univ (.pi "Y" .univ
    (.pi "A" (.path .univ (.var "X") (.var "Y"))
      (.pi "x" (.var "X") (.pi "y" (.var "Y")
        (.arr
          (.path (.var "Y")
            (apps transportD.ref [.var "X", .var "Y", .var "A", .var "x"])
            (.var "y"))
          (.pathP "i" (.papp (.var "A") (.var "X") (.var "Y") (.var "i"))
            (.var "x") (.var "y")))))))
  tm := lams ["X", "Y", "A", "x", "y", "h"]
    (.plam "i" (.hcomp "j"
      (.papp (.var "A") (.var "X") (.var "Y") (.var "i"))
      [([(.var "i", false)], .var "x"),
       ([(.var "i", true)],
         .papp (.var "h")
           (apps transportD.ref [.var "X", .var "Y", .var "A", .var "x"])
           (.var "y") (.var "j"))]
      (.transp "j2"
        (.papp (.var "A") (.var "X") (.var "Y")
          (.imin (.var "i") (.var "j2")))
        (.var "x"))))

#guard toPathPD.ok

/-- Squares in a set fill: `PathP (λ i. Path A x (r i)) α β` from `isSet A`. -/
def setFillD : LibDef where
  name := "setFill"
  ty := .pi "A" .univ (.pi "h" (isSetR (.var "A"))
    (.pi "x" (.var "A") (.pi "y0" (.var "A") (.pi "y1" (.var "A")
    (.pi "r" (.path (.var "A") (.var "y0") (.var "y1"))
    (.pi "al" (.path (.var "A") (.var "x") (.var "y0"))
    (.pi "be" (.path (.var "A") (.var "x") (.var "y1"))
      (.pathP "i" (.path (.var "A") (.var "x")
          (.papp (.var "r") (.var "y0") (.var "y1") (.var "i")))
        (.var "al") (.var "be")))))))))
  tm :=
    let PX0 := .path (.var "A") (.var "x") (.var "y0")
    let PX1 := .path (.var "A") (.var "x") (.var "y1")
    let famP := .plam "i" (.path (.var "A") (.var "x")
      (.papp (.var "r") (.var "y0") (.var "y1") (.var "i")))
    lams ["A", "h", "x", "y0", "y1", "r", "al", "be"]
      (apps toPathPD.ref [PX0, PX1, famP, .var "al", .var "be",
        apps (.var "h") [.var "x", .var "y1",
          apps transportD.ref [PX0, PX1, famP, .var "al"],
          .var "be"]])

#guard setFillD.ok

/-! ## Isomorphisms into sets are equivalences

The `setFill` technique behind `sucEquiv`, packaged as a reusable tool: for
*set-level* codomains, an isomorphism is an equivalence (a practical
replacement for the general `gradLemma`, which needs no h-level assumption
but a much harder square). -/

def setIsoToEquivD : LibDef where
  name := "setIsoToEquiv"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "B") (.var "A"))
    (.pi "sect" (.pi "b" (.var "B")
      (.path (.var "B") (.app (.var "f") (.app (.var "g") (.var "b")))
        (.var "b")))
    (.pi "retr" (.pi "a" (.var "A")
      (.path (.var "A") (.app (.var "g") (.app (.var "f") (.var "a")))
        (.var "a")))
    (.arr (isSetR (.var "B")) (equivR (.var "A") (.var "B"))))))))
  tm :=
    let gy := .app (.var "g") (.var "y")
    let fgy := .app (.var "f") gy
    let fibFst := .fst (.var "fib")
    let ffib := .app (.var "f") fibFst
    let alpha := apps symmD.ref [.var "B", fgy, .var "y",
      .app (.var "sect") (.var "y")]
    let q := apps transD.ref [.var "A",
      gy, .app (.var "g") ffib, fibFst,
      apps congD.ref [.var "B", .var "A", .var "g", .var "y", ffib,
        .snd (.var "fib")],
      .app (.var "retr") fibFst]
    let r := apps congD.ref [.var "A", .var "B", .var "f", gy, fibFst, q]
    let sq := apps setFillD.ref [.var "B", .var "hB", .var "y",
      fgy, ffib, r, alpha, .snd (.var "fib")]
    lams ["A", "B", "f", "g", "sect", "retr", "hB"]
      (.pair (.var "f")
        (.lam "y" (.pair
          (.pair gy alpha)
          (.lam "fib" (.plam "i" (.pair
            (.papp q gy fibFst (.var "i"))
            (.papp sq alpha (.snd (.var "fib")) (.var "i"))))))))

#guard setIsoToEquivD.ok

/-- **The successor equivalence, rebuilt**: fibers are contracted through
`predZ` and the cancellation *paths*, the coherence square coming from
`isSet ℤ` — no strict cancellation in the kernel required. -/
def sucEquivD : LibDef where
  name := "sucEquiv"
  ty := equivR .int .int
  tm :=
    let fibFst := .fst (.var "fib")
    let p := .snd (.var "fib")
    let sucFib := .app sucZD.ref fibFst
    let predY := .app predZD.ref (.var "y")
    let alpha := apps symmD.ref [.int, .app sucZD.ref predY, .var "y",
      .app sucPredZD.ref (.var "y")]
    let q := apps transD.ref [.int,
      predY, .app predZD.ref sucFib, fibFst,
      apps congD.ref [.int, .int, predZD.ref, .var "y", sucFib, p],
      .app predSucZD.ref fibFst]
    let r := apps congD.ref [.int, .int, sucZD.ref, predY, fibFst, q]
    let sq := apps setFillD.ref [.int, isSetZD.ref, .var "y",
      .app sucZD.ref predY, sucFib, r, alpha, p]
    .pair sucZD.ref
      (.lam "y" (.pair
        (.pair predY alpha)
        (.lam "fib" (.plam "i" (.pair
          (.papp q predY fibFst (.var "i"))
          (.papp sq alpha p (.var "i")))))))

#guard sucEquivD.ok

/-! ## The circle, integrated -/

/-- The universal cover of the circle. -/
def helixD : LibDef where
  name := "helix"
  ty := .arr .s1 .univ
  tm := .lam "x" (.s1elim "k" .univ .int
    (apps uaD.ref [.int, .int, sucEquivD.ref]) (.var "x"))

/-- The winding number: `encode` at `base`. -/
def windingD : LibDef where
  name := "winding"
  ty := .arr (.path .s1 .sbase .sbase) .int
  tm := .lam "p" (.transp "i"
    (.app helixD.ref (.papp (.var "p") .sbase .sbase (.var "i")))
    (.ipos .zero))

#guard helixD.ok
#guard windingD.ok

-- and it computes: winding loop ⟶ +1
#guard
  match normalize (.app windingD.ref (.plam "i" (.sloop (.var "i")))) .int with
  | .ok t => t == resolveClosed (posZ 1)
  | .error _ => false

end Cubical.Library

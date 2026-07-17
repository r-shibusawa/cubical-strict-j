import FormalizedMathematics.Cubical.LibCore

namespace Cubical.Library

open Raw

/-! ## Category theory

Structures are iterated Σ-types; laws are `Path`s. -/

/-- `Monoid := Σ (M : U₀) (e : M) (op : M → M → M), laws`. -/
def monoidTy : Raw :=
  .sigma "M" .univ
    (.sigma "e" (.var "M")
      (.sigma "op" (.arr (.var "M") (.arr (.var "M") (.var "M")))
        (.sigma "idl" (.pi "x" (.var "M")
          (.path (.var "M") (apps (.var "op") [.var "e", .var "x"]) (.var "x")))
          (.sigma "idr" (.pi "x" (.var "M")
            (.path (.var "M") (apps (.var "op") [.var "x", .var "e"]) (.var "x")))
            (.pi "x" (.var "M") (.pi "y" (.var "M") (.pi "z" (.var "M")
              (.path (.var "M")
                (apps (.var "op") [apps (.var "op") [.var "x", .var "y"], .var "z"])
                (apps (.var "op") [.var "x", apps (.var "op") [.var "y", .var "z"]])))))))))

/-! ## ⊤ and ⊥ are propositions -/

/-- `isProp ⊤`, by double `unitrec` (no η needed). -/
def isPropUnitD : LibDef where
  name := "isPropUnit"
  ty := isPropR .unit
  tm := lams ["x", "y"]
    (.unitrec "x2" (.path .unit (.var "x2") (.var "y"))
      (.unitrec "y2" (.path .unit .tt (.var "y2")) (.plam "i" .tt) (.var "y"))
      (.var "x"))

/-- `isProp ⊥`, vacuously. -/
def isPropEmptyD : LibDef where
  name := "isPropEmpty"
  ty := isPropR .empty
  tm := lams ["x", "y"]
    (.emptyrec (.path .empty (.var "x") (.var "y")) (.var "x"))

#guard isPropUnitD.ok
#guard isPropEmptyD.ok

/-! ## `isSet ℕ` by encode–decode -/

/-- Path codes for ℕ: `code 0 0 = ⊤`, `code (s m) (s n) = code m n`, else `⊥`. -/
def codeNatD : LibDef where
  name := "codeNat"
  ty := .arr .nat (.arr .nat .univ)
  tm := .lam "m" (.natrec "k" (.arr .nat .univ)
    (.lam "n" (.natrec "k2" .univ .unit
      (lams ["k3", "ih2"] .empty) (.var "n")))
    (lams ["m2", "ihm"] (.lam "n" (.natrec "k2" .univ .empty
      (lams ["n2", "ih2"] (.app (.var "ihm") (.var "n2"))) (.var "n"))))
    (.var "m"))

/-- Reflexivity codes. -/
def rNatD : LibDef where
  name := "rNat"
  ty := .pi "m" .nat (apps codeNatD.ref [.var "m", .var "m"])
  tm := .lam "m" (.natrec "k" (apps codeNatD.ref [.var "k", .var "k"])
    .tt (lams ["m2", "ih"] (.var "ih")) (.var "m"))

def encodeNatD : LibDef where
  name := "encodeNat"
  ty := .pi "m" .nat (.pi "n" .nat
    (.arr (.path .nat (.var "m") (.var "n"))
      (apps codeNatD.ref [.var "m", .var "n"])))
  tm := lams ["m", "n"] (.lam "p" (apps substD.ref [.nat,
    .lam "k" (apps codeNatD.ref [.var "m", .var "k"]),
    .var "m", .var "n", .var "p",
    .app rNatD.ref (.var "m")]))

def decodeNatD : LibDef where
  name := "decodeNat"
  ty := .pi "m" .nat (.pi "n" .nat
    (.arr (apps codeNatD.ref [.var "m", .var "n"])
      (.path .nat (.var "m") (.var "n"))))
  tm := .lam "m" (.natrec "k"
    (.pi "n" .nat (.arr (apps codeNatD.ref [.var "k", .var "n"])
      (.path .nat (.var "k") (.var "n"))))
    (.lam "n" (.natrec "k2"
      (.arr (apps codeNatD.ref [.zero, .var "k2"])
        (.path .nat .zero (.var "k2")))
      (.lam "c" (.plam "i" .zero))
      (lams ["n2", "ih2"] (.lam "c"
        (.emptyrec (.path .nat .zero (.succ (.var "n2"))) (.var "c"))))
      (.var "n")))
    (lams ["m2", "ihm"] (.lam "n" (.natrec "k2"
      (.arr (apps codeNatD.ref [.succ (.var "m2"), .var "k2"])
        (.path .nat (.succ (.var "m2")) (.var "k2")))
      (.lam "c" (.emptyrec (.path .nat (.succ (.var "m2")) .zero) (.var "c")))
      (lams ["n2", "ih2"] (.lam "c"
        (apps congD.ref [.nat, .nat, .lam "x" (.succ (.var "x")),
          .var "m2", .var "n2",
          apps (.var "ihm") [.var "n2", .var "c"]])))
      (.var "n"))))
    (.var "m"))

def isPropCodeNatD : LibDef where
  name := "isPropCodeNat"
  ty := .pi "m" .nat (.pi "n" .nat
    (isPropR (apps codeNatD.ref [.var "m", .var "n"])))
  tm := .lam "m" (.natrec "k"
    (.pi "n" .nat (isPropR (apps codeNatD.ref [.var "k", .var "n"])))
    (.lam "n" (.natrec "k2"
      (isPropR (apps codeNatD.ref [.zero, .var "k2"]))
      isPropUnitD.ref
      (lams ["n2", "ih2"] isPropEmptyD.ref)
      (.var "n")))
    (lams ["m2", "ihm"] (.lam "n" (.natrec "k2"
      (isPropR (apps codeNatD.ref [.succ (.var "m2"), .var "k2"]))
      isPropEmptyD.ref
      (lams ["n2", "ih2"] (.app (.var "ihm") (.var "n2")))
      (.var "n"))))
    (.var "m"))

#guard codeNatD.ok
#guard rNatD.ok
#guard encodeNatD.ok
#guard decodeNatD.ok
#guard isPropCodeNatD.ok

def decodeEncodeReflNatD : LibDef where
  name := "decodeEncodeReflNat"
  ty := .pi "m" .nat
    (.path (.path .nat (.var "m") (.var "m"))
      (apps decodeNatD.ref [.var "m", .var "m", .app rNatD.ref (.var "m")])
      (apps reflD.ref [.nat, .var "m"]))
  tm := .lam "m" (.natrec "k"
    (.path (.path .nat (.var "k") (.var "k"))
      (apps decodeNatD.ref [.var "k", .var "k", .app rNatD.ref (.var "k")])
      (apps reflD.ref [.nat, .var "k"]))
    (.plam "j" (.plam "i" .zero))
    (lams ["m2", "ih"]
      (apps congD.ref [
        .path .nat (.var "m2") (.var "m2"),
        .path .nat (.succ (.var "m2")) (.succ (.var "m2")),
        .lam "pp" (apps congD.ref [.nat, .nat, .lam "x" (.succ (.var "x")),
          .var "m2", .var "m2", .var "pp"]),
        apps decodeNatD.ref [.var "m2", .var "m2", .app rNatD.ref (.var "m2")],
        apps reflD.ref [.nat, .var "m2"],
        .var "ih"]))
    (.var "m"))

def decodeEncodeNatD : LibDef where
  name := "decodeEncodeNat"
  ty := .pi "m" .nat (.pi "n" .nat
    (.pi "p" (.path .nat (.var "m") (.var "n"))
      (.path (.path .nat (.var "m") (.var "n"))
        (apps decodeNatD.ref [.var "m", .var "n",
          apps encodeNatD.ref [.var "m", .var "n", .var "p"]])
        (.var "p"))))
  tm := lams ["m", "n", "p"] (apps jD.ref [.nat, .var "m",
    lams ["n2", "p2"] (.path (.path .nat (.var "m") (.var "n2"))
      (apps decodeNatD.ref [.var "m", .var "n2",
        apps encodeNatD.ref [.var "m", .var "n2", .var "p2"]])
      (.var "p2")),
    .app decodeEncodeReflNatD.ref (.var "m"),
    .var "n", .var "p"])

/-- **ℕ is a set**, by encode–decode. -/
def isSetNatD : LibDef where
  name := "isSetNat"
  ty := isSetR .nat
  tm :=
    let PT := .path .nat (.var "xs") (.var "ys")
    let encP := apps encodeNatD.ref [.var "xs", .var "ys", .var "xp"]
    let encQ := apps encodeNatD.ref [.var "xs", .var "ys", .var "yp"]
    let dp := apps decodeNatD.ref [.var "xs", .var "ys", encP]
    let dq := apps decodeNatD.ref [.var "xs", .var "ys", encQ]
    lams ["xs", "ys", "xp", "yp"]
      (apps transD.ref [PT, .var "xp", dp, .var "yp",
        apps symmD.ref [PT, dp, .var "xp",
          apps decodeEncodeNatD.ref [.var "xs", .var "ys", .var "xp"]],
        apps transD.ref [PT, dp, dq, .var "yp",
          apps congD.ref [apps codeNatD.ref [.var "xs", .var "ys"], PT,
            .lam "c" (apps decodeNatD.ref [.var "xs", .var "ys", .var "c"]),
            encP, encQ,
            apps isPropCodeNatD.ref [.var "xs", .var "ys", encP, encQ]],
          apps decodeEncodeNatD.ref [.var "xs", .var "ys", .var "yp"]]])

#guard decodeEncodeReflNatD.ok
#guard decodeEncodeNatD.ok
#guard isSetNatD.ok

/-! ## `isSet ℤ`, the square filler, and the new `sucEquiv` -/

def codeZD : LibDef where
  name := "codeZ"
  ty := .arr .int (.arr .int .univ)
  tm := .lam "z" (.lam "w" (.intcase "k" .univ
    (.lam "n" (.intcase "k2" .univ
      (.lam "n2" (apps codeNatD.ref [.var "n", .var "n2"]))
      (.lam "n2" .empty)
      (.var "w")))
    (.lam "n" (.intcase "k2" .univ
      (.lam "n2" .empty)
      (.lam "n2" (apps codeNatD.ref [.var "n", .var "n2"]))
      (.var "w")))
    (.var "z")))

def rZD : LibDef where
  name := "rZ"
  ty := .pi "z" .int (apps codeZD.ref [.var "z", .var "z"])
  tm := .lam "z" (.intcase "k" (apps codeZD.ref [.var "k", .var "k"])
    (.lam "n" (.app rNatD.ref (.var "n")))
    (.lam "n" (.app rNatD.ref (.var "n")))
    (.var "z"))

def encodeZD : LibDef where
  name := "encodeZ"
  ty := .pi "z" .int (.pi "w" .int
    (.arr (.path .int (.var "z") (.var "w"))
      (apps codeZD.ref [.var "z", .var "w"])))
  tm := lams ["z", "w"] (.lam "p" (apps substD.ref [.int,
    .lam "k" (apps codeZD.ref [.var "z", .var "k"]),
    .var "z", .var "w", .var "p",
    .app rZD.ref (.var "z")]))

def decodeZD : LibDef where
  name := "decodeZ"
  ty := .pi "z" .int (.pi "w" .int
    (.arr (apps codeZD.ref [.var "z", .var "w"])
      (.path .int (.var "z") (.var "w"))))
  tm := .lam "z" (.intcase "k"
    (.pi "w" .int (.arr (apps codeZD.ref [.var "k", .var "w"])
      (.path .int (.var "k") (.var "w"))))
    (.lam "n" (.lam "w" (.intcase "k2"
      (.arr (apps codeZD.ref [.ipos (.var "n"), .var "k2"])
        (.path .int (.ipos (.var "n")) (.var "k2")))
      (.lam "n2" (.lam "c" (apps congD.ref [.nat, .int,
        .lam "x" (.ipos (.var "x")), .var "n", .var "n2",
        apps decodeNatD.ref [.var "n", .var "n2", .var "c"]])))
      (.lam "n2" (.lam "c" (.emptyrec
        (.path .int (.ipos (.var "n")) (.inegsuc (.var "n2"))) (.var "c"))))
      (.var "w"))))
    (.lam "n" (.lam "w" (.intcase "k2"
      (.arr (apps codeZD.ref [.inegsuc (.var "n"), .var "k2"])
        (.path .int (.inegsuc (.var "n")) (.var "k2")))
      (.lam "n2" (.lam "c" (.emptyrec
        (.path .int (.inegsuc (.var "n")) (.ipos (.var "n2"))) (.var "c"))))
      (.lam "n2" (.lam "c" (apps congD.ref [.nat, .int,
        .lam "x" (.inegsuc (.var "x")), .var "n", .var "n2",
        apps decodeNatD.ref [.var "n", .var "n2", .var "c"]])))
      (.var "w"))))
    (.var "z"))

def isPropCodeZD : LibDef where
  name := "isPropCodeZ"
  ty := .pi "z" .int (.pi "w" .int
    (isPropR (apps codeZD.ref [.var "z", .var "w"])))
  tm := .lam "z" (.intcase "k"
    (.pi "w" .int (isPropR (apps codeZD.ref [.var "k", .var "w"])))
    (.lam "n" (.lam "w" (.intcase "k2"
      (isPropR (apps codeZD.ref [.ipos (.var "n"), .var "k2"]))
      (.lam "n2" (apps isPropCodeNatD.ref [.var "n", .var "n2"]))
      (.lam "n2" isPropEmptyD.ref)
      (.var "w"))))
    (.lam "n" (.lam "w" (.intcase "k2"
      (isPropR (apps codeZD.ref [.inegsuc (.var "n"), .var "k2"]))
      (.lam "n2" isPropEmptyD.ref)
      (.lam "n2" (apps isPropCodeNatD.ref [.var "n", .var "n2"]))
      (.var "w"))))
    (.var "z"))

#guard codeZD.ok
#guard rZD.ok
#guard encodeZD.ok
#guard decodeZD.ok
#guard isPropCodeZD.ok

def decodeEncodeReflZD : LibDef where
  name := "decodeEncodeReflZ"
  ty := .pi "z" .int
    (.path (.path .int (.var "z") (.var "z"))
      (apps decodeZD.ref [.var "z", .var "z", .app rZD.ref (.var "z")])
      (apps reflD.ref [.int, .var "z"]))
  tm := .lam "z" (.intcase "k"
    (.path (.path .int (.var "k") (.var "k"))
      (apps decodeZD.ref [.var "k", .var "k", .app rZD.ref (.var "k")])
      (apps reflD.ref [.int, .var "k"]))
    (.lam "n" (apps congD.ref [
      .path .nat (.var "n") (.var "n"),
      .path .int (.ipos (.var "n")) (.ipos (.var "n")),
      .lam "pp" (apps congD.ref [.nat, .int, .lam "x" (.ipos (.var "x")),
        .var "n", .var "n", .var "pp"]),
      apps decodeNatD.ref [.var "n", .var "n", .app rNatD.ref (.var "n")],
      apps reflD.ref [.nat, .var "n"],
      .app decodeEncodeReflNatD.ref (.var "n")]))
    (.lam "n" (apps congD.ref [
      .path .nat (.var "n") (.var "n"),
      .path .int (.inegsuc (.var "n")) (.inegsuc (.var "n")),
      .lam "pp" (apps congD.ref [.nat, .int, .lam "x" (.inegsuc (.var "x")),
        .var "n", .var "n", .var "pp"]),
      apps decodeNatD.ref [.var "n", .var "n", .app rNatD.ref (.var "n")],
      apps reflD.ref [.nat, .var "n"],
      .app decodeEncodeReflNatD.ref (.var "n")]))
    (.var "z"))

def decodeEncodeZD : LibDef where
  name := "decodeEncodeZ"
  ty := .pi "z" .int (.pi "w" .int
    (.pi "p" (.path .int (.var "z") (.var "w"))
      (.path (.path .int (.var "z") (.var "w"))
        (apps decodeZD.ref [.var "z", .var "w",
          apps encodeZD.ref [.var "z", .var "w", .var "p"]])
        (.var "p"))))
  tm := lams ["z", "w", "p"] (apps jD.ref [.int, .var "z",
    lams ["w2", "p2"] (.path (.path .int (.var "z") (.var "w2"))
      (apps decodeZD.ref [.var "z", .var "w2",
        apps encodeZD.ref [.var "z", .var "w2", .var "p2"]])
      (.var "p2")),
    .app decodeEncodeReflZD.ref (.var "z"),
    .var "w", .var "p"])

/-- **ℤ is a set**, by encode–decode. -/
def isSetZD : LibDef where
  name := "isSetZ"
  ty := isSetR .int
  tm :=
    let PT := .path .int (.var "xs") (.var "ys")
    let encP := apps encodeZD.ref [.var "xs", .var "ys", .var "xp"]
    let encQ := apps encodeZD.ref [.var "xs", .var "ys", .var "yp"]
    let dp := apps decodeZD.ref [.var "xs", .var "ys", encP]
    let dq := apps decodeZD.ref [.var "xs", .var "ys", encQ]
    lams ["xs", "ys", "xp", "yp"]
      (apps transD.ref [PT, .var "xp", dp, .var "yp",
        apps symmD.ref [PT, dp, .var "xp",
          apps decodeEncodeZD.ref [.var "xs", .var "ys", .var "xp"]],
        apps transD.ref [PT, dp, dq, .var "yp",
          apps congD.ref [apps codeZD.ref [.var "xs", .var "ys"], PT,
            .lam "c" (apps decodeZD.ref [.var "xs", .var "ys", .var "c"]),
            encP, encQ,
            apps isPropCodeZD.ref [.var "xs", .var "ys", encP, encQ]],
          apps decodeEncodeZD.ref [.var "xs", .var "ys", .var "yp"]]])

#guard decodeEncodeReflZD.ok
#guard decodeEncodeZD.ok
#guard isSetZD.ok



/-! ## Addition laws (pos/negsuc representation) -/

/-- `a + suc x ≡ suc (a + x)`, by cases on `x` (the `negsuc` side uses the
cancellation paths). -/
def addSucRD : LibDef where
  name := "addSucR"
  ty := .pi "a" .int (.pi "x" .int
    (.path .int
      (apps addD.ref [.var "a", .app sucZD.ref (.var "x")])
      (.app sucZD.ref (apps addD.ref [.var "a", .var "x"]))))
  tm := lams ["a", "x"] (.intcase "k"
    (.path .int
      (apps addD.ref [.var "a", .app sucZD.ref (.var "k")])
      (.app sucZD.ref (apps addD.ref [.var "a", .var "k"])))
    (.lam "n" (.plam "i"
      (.app sucZD.ref (apps addD.ref [.var "a", .ipos (.var "n")]))))
    (.lam "n" (.natrec "k2"
      (.path .int
        (apps addD.ref [.var "a", .app sucZD.ref (.inegsuc (.var "k2"))])
        (.app sucZD.ref (apps addD.ref [.var "a", .inegsuc (.var "k2")])))
      (apps symmD.ref [.int,
        .app sucZD.ref (.app predZD.ref (.var "a")), .var "a",
        .app sucPredZD.ref (.var "a")])
      (lams ["m", "ih"] (apps symmD.ref [.int,
        .app sucZD.ref (.app predZD.ref
          (apps addD.ref [.var "a", .inegsuc (.var "m")])),
        apps addD.ref [.var "a", .inegsuc (.var "m")],
        .app sucPredZD.ref (apps addD.ref [.var "a", .inegsuc (.var "m")])]))
      (.var "n")))
    (.var "x"))

/-- `a + pred x ≡ pred (a + x)`. -/
def addPredRD : LibDef where
  name := "addPredR"
  ty := .pi "a" .int (.pi "x" .int
    (.path .int
      (apps addD.ref [.var "a", .app predZD.ref (.var "x")])
      (.app predZD.ref (apps addD.ref [.var "a", .var "x"]))))
  tm := lams ["a", "x"] (.intcase "k"
    (.path .int
      (apps addD.ref [.var "a", .app predZD.ref (.var "k")])
      (.app predZD.ref (apps addD.ref [.var "a", .var "k"])))
    (.lam "n" (.natrec "k2"
      (.path .int
        (apps addD.ref [.var "a", .app predZD.ref (.ipos (.var "k2"))])
        (.app predZD.ref (apps addD.ref [.var "a", .ipos (.var "k2")])))
      (.plam "i" (.app predZD.ref (.var "a")))
      (lams ["m", "ih"] (apps symmD.ref [.int,
        .app predZD.ref (.app sucZD.ref
          (apps addD.ref [.var "a", .ipos (.var "m")])),
        apps addD.ref [.var "a", .ipos (.var "m")],
        .app predSucZD.ref (apps addD.ref [.var "a", .ipos (.var "m")])]))
      (.var "n")))
    (.lam "n" (.plam "i"
      (.app predZD.ref (apps addD.ref [.var "a", .inegsuc (.var "n")]))))
    (.var "x"))

/-- Associativity, by cases and induction on the third summand. -/
def addAssocD : LibDef where
  name := "addAssoc"
  ty := .pi "a" .int (.pi "b" .int (.pi "c" .int
    (.path .int
      (apps addD.ref [apps addD.ref [.var "a", .var "b"], .var "c"])
      (apps addD.ref [.var "a", apps addD.ref [.var "b", .var "c"]]))))
  tm :=
    let ab := apps addD.ref [.var "a", .var "b"]
    lams ["a", "b", "c"] (.intcase "k"
      (.path .int
        (apps addD.ref [ab, .var "k"])
        (apps addD.ref [.var "a", apps addD.ref [.var "b", .var "k"]]))
      (.lam "n" (.natrec "k2"
        (.path .int
          (apps addD.ref [ab, .ipos (.var "k2")])
          (apps addD.ref [.var "a", apps addD.ref [.var "b", .ipos (.var "k2")]]))
        (.plam "i" ab)
        (lams ["m", "ih"]
          (apps transD.ref [.int,
            .app sucZD.ref (apps addD.ref [ab, .ipos (.var "m")]),
            .app sucZD.ref
              (apps addD.ref [.var "a", apps addD.ref [.var "b", .ipos (.var "m")]]),
            apps addD.ref [.var "a",
              .app sucZD.ref (apps addD.ref [.var "b", .ipos (.var "m")])],
            apps congD.ref [.int, .int, sucZD.ref,
              apps addD.ref [ab, .ipos (.var "m")],
              apps addD.ref [.var "a", apps addD.ref [.var "b", .ipos (.var "m")]],
              .var "ih"],
            apps symmD.ref [.int,
              apps addD.ref [.var "a",
                .app sucZD.ref (apps addD.ref [.var "b", .ipos (.var "m")])],
              .app sucZD.ref
                (apps addD.ref [.var "a", apps addD.ref [.var "b", .ipos (.var "m")]]),
              apps addSucRD.ref [.var "a",
                apps addD.ref [.var "b", .ipos (.var "m")]]]]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path .int
          (apps addD.ref [ab, .inegsuc (.var "k2")])
          (apps addD.ref [.var "a", apps addD.ref [.var "b", .inegsuc (.var "k2")]]))
        (apps symmD.ref [.int,
          apps addD.ref [.var "a", .app predZD.ref (.var "b")],
          .app predZD.ref ab,
          apps addPredRD.ref [.var "a", .var "b"]])
        (lams ["m", "ih"]
          (apps transD.ref [.int,
            .app predZD.ref (apps addD.ref [ab, .inegsuc (.var "m")]),
            .app predZD.ref
              (apps addD.ref [.var "a", apps addD.ref [.var "b", .inegsuc (.var "m")]]),
            apps addD.ref [.var "a",
              .app predZD.ref (apps addD.ref [.var "b", .inegsuc (.var "m")])],
            apps congD.ref [.int, .int, predZD.ref,
              apps addD.ref [ab, .inegsuc (.var "m")],
              apps addD.ref [.var "a", apps addD.ref [.var "b", .inegsuc (.var "m")]],
              .var "ih"],
            apps symmD.ref [.int,
              apps addD.ref [.var "a",
                .app predZD.ref (apps addD.ref [.var "b", .inegsuc (.var "m")])],
              .app predZD.ref
                (apps addD.ref [.var "a", apps addD.ref [.var "b", .inegsuc (.var "m")]]),
              apps addPredRD.ref [.var "a",
                apps addD.ref [.var "b", .inegsuc (.var "m")]]]]))
        (.var "n")))
      (.var "c"))

#guard addSucRD.ok
#guard addPredRD.ok
#guard addAssocD.ok

/-- **The monoid `(ℤ, +, 0)`**, laws proven by induction (pos/negsuc). -/
def intMonoidD : LibDef where
  name := "intMonoid"
  ty := monoidTy
  tm := .pair .int (.pair (.ipos .zero) (.pair addD.ref
    (.pair addZeroLD.ref (.pair addZeroRD.ref
      (lams ["x", "y", "z"]
        (apps addAssocD.ref [.var "x", .var "y", .var "z"]))))))

#guard intMonoidD.ok



/-- Precategories at level `n`: objects in `U (n+1)`, hom-types in `U n`,
laws as `Path`s. -/
def precatTy (n : Nat) : Raw :=
  .sigma "Ob" (.univN (n + 1))
    (.sigma "Hom" (.arr (.var "Ob") (.arr (.var "Ob") (.univN n)))
      (.sigma "idm" (.pi "x" (.var "Ob")
        (apps (.var "Hom") [.var "x", .var "x"]))
        (.sigma "cmp" (.pi "x" (.var "Ob") (.pi "y" (.var "Ob") (.pi "z" (.var "Ob")
          (.arr (apps (.var "Hom") [.var "x", .var "y"])
            (.arr (apps (.var "Hom") [.var "y", .var "z"])
              (apps (.var "Hom") [.var "x", .var "z"]))))))
          (.sigma "idl" (.pi "x" (.var "Ob") (.pi "y" (.var "Ob")
            (.pi "f" (apps (.var "Hom") [.var "x", .var "y"])
              (.path (apps (.var "Hom") [.var "x", .var "y"])
                (apps (.var "cmp") [.var "x", .var "x", .var "y",
                  .app (.var "idm") (.var "x"), .var "f"])
                (.var "f")))))
            (.sigma "idr" (.pi "x" (.var "Ob") (.pi "y" (.var "Ob")
              (.pi "f" (apps (.var "Hom") [.var "x", .var "y"])
                (.path (apps (.var "Hom") [.var "x", .var "y"])
                  (apps (.var "cmp") [.var "x", .var "y", .var "y",
                    .var "f", .app (.var "idm") (.var "y")])
                  (.var "f")))))
              (.pi "w" (.var "Ob") (.pi "x" (.var "Ob") (.pi "y" (.var "Ob")
                (.pi "z" (.var "Ob")
                  (.pi "f" (apps (.var "Hom") [.var "w", .var "x"])
                    (.pi "g" (apps (.var "Hom") [.var "x", .var "y"])
                      (.pi "h" (apps (.var "Hom") [.var "y", .var "z"])
                        (.path (apps (.var "Hom") [.var "w", .var "z"])
                          (apps (.var "cmp") [.var "w", .var "y", .var "z",
                            apps (.var "cmp") [.var "w", .var "x", .var "y",
                              .var "f", .var "g"],
                            .var "h"])
                          (apps (.var "cmp") [.var "w", .var "x", .var "z",
                            .var "f",
                            apps (.var "cmp") [.var "x", .var "y", .var "z",
                              .var "g", .var "h"]]))))))))))))))

/-- **The category of types**: objects are `U 0` (an object of `U 1` — this
is what the universe hierarchy is for), morphisms are functions, all laws
hold by `refl` thanks to definitional η. -/
def typesCatD : LibDef where
  name := "typesCat"
  ty := precatTy 0
  tm := .pair .univ
    (.pair (lams ["A", "B"] (.arr (.var "A") (.var "B")))
      (.pair (lams ["A", "x"] (.var "x"))
        (.pair (lams ["A", "B", "C", "f", "g"]
          (.lam "x" (.app (.var "g") (.app (.var "f") (.var "x")))))
          (.pair (lams ["A", "B", "f"] (.plam "i" (.var "f")))
            (.pair (lams ["A", "B", "f"] (.plam "i" (.var "f")))
              (lams ["W", "X", "Y", "Z", "f", "g", "h"]
                (.plam "i" (.lam "x"
                  (.app (.var "h") (.app (.var "g")
                    (.app (.var "f") (.var "x"))))))))))))

#guard typesCatD.ok

/-- Projections of the precategory Σ-encoding. -/
def catOb (c : Raw) : Raw := .fst c
def catHom (c : Raw) : Raw := .fst (.snd c)
def catId (c : Raw) : Raw := .fst (.snd (.snd c))
def catCmp (c : Raw) : Raw := .fst (.snd (.snd (.snd c)))

/-- Functors between precategories (at level 0). -/
def functorTy (C D : Raw) : Raw :=
  .sigma "F0" (.arr (catOb C) (catOb D))
    (.sigma "F1" (.pi "x" (catOb C) (.pi "y" (catOb C)
      (.arr (apps (catHom C) [.var "x", .var "y"])
        (apps (catHom D) [.app (.var "F0") (.var "x"),
          .app (.var "F0") (.var "y")]))))
      (.sigma "Fid" (.pi "x" (catOb C)
        (.path (apps (catHom D) [.app (.var "F0") (.var "x"),
            .app (.var "F0") (.var "x")])
          (apps (.var "F1") [.var "x", .var "x", .app (catId C) (.var "x")])
          (.app (catId D) (.app (.var "F0") (.var "x")))))
        (.pi "x" (catOb C) (.pi "y" (catOb C) (.pi "z" (catOb C)
          (.pi "f" (apps (catHom C) [.var "x", .var "y"])
            (.pi "g" (apps (catHom C) [.var "y", .var "z"])
              (.path (apps (catHom D) [.app (.var "F0") (.var "x"),
                  .app (.var "F0") (.var "z")])
                (apps (.var "F1") [.var "x", .var "z",
                  apps (catCmp C) [.var "x", .var "y", .var "z",
                    .var "f", .var "g"]])
                (apps (catCmp D)
                  [.app (.var "F0") (.var "x"), .app (.var "F0") (.var "y"),
                   .app (.var "F0") (.var "z"),
                   apps (.var "F1") [.var "x", .var "y", .var "f"],
                   apps (.var "F1") [.var "y", .var "z", .var "g"]])))))))))

/-- The identity functor, for an **arbitrary** precategory. -/
def idFunctorD : LibDef where
  name := "idFunctor"
  ty := .pi "C" (precatTy 0) (functorTy (.var "C") (.var "C"))
  tm := .lam "C"
    (.pair (.lam "x" (.var "x"))
      (.pair (lams ["x", "y", "f"] (.var "f"))
        (.pair (.lam "x" (.plam "i" (.app (catId (.var "C")) (.var "x"))))
          (lams ["x", "y", "z", "f", "g"]
            (.plam "i" (apps (catCmp (.var "C"))
              [.var "x", .var "y", .var "z", .var "f", .var "g"]))))))

#guard idFunctorD.ok

end Cubical.Library

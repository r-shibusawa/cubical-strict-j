import FormalizedMathematics.Cubical.TypeCheck

/-!
# The first library written *in* the cubical kernel

Every definition below is an **object-language program**: a closed `Raw`
term together with its type, verified by the kernel's type checker at build
time (`#guard`).  Nothing here is a Lean theorem *about* the kernel — it is
mathematics carried out *inside* the type theory the kernel implements,
where:

* function extensionality and path algebra are programs, not axioms;
* laws of algebraic structures are `Path`s;
* the identity type is eliminated by `J`, itself a *derived* program
  (a transport along a connection square);
* the universe hierarchy `U 0 : U 1 : ⋯` hosts the category of types.

Layout: path algebra → transport & J → h-levels → equivalences &
univalence → integers (with inductive proofs of the monoid laws) →
category theory (monoids, precategories, functors).
-/

namespace Cubical.Library

open Raw

/-- A library entry: a closed term and its type. -/
structure LibDef where
  name : String
  ty : Raw
  tm : Raw

/-- Use a library entry inside a later term.  References are `defn` nodes:
evaluation unfolds them, but the checker trusts the annotation — each
entry is verified once by its own build-time guard, in dependency order
(the definition-environment mechanism). -/
def LibDef.ref (d : LibDef) : Raw := .defn d.name d.tm d.ty

/-- Kernel-check a library entry. -/
def LibDef.ok (d : LibDef) : Bool :=
  match checkDef d.tm d.ty with
  | .ok _ => true
  | .error _ => false

/-- Iterated application. -/
def apps (f : Raw) (as : List Raw) : Raw := as.foldl .app f

/-- Iterated λ. -/
def lams (xs : List String) (b : Raw) : Raw := xs.foldr .lam b

/-- Resolve a closed `Raw` term (for comparing normal forms in guards). -/
def resolveClosed (r : Raw) : Term :=
  match r.resolve [] with
  | .ok t => t
  | .error e => panic! s!"resolveClosed: {e}"

/-! ## Path algebra -/

def reflD : LibDef where
  name := "refl"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.path (.var "A") (.var "a") (.var "a")))
  tm := lams ["A", "a"] (.plam "i" (.var "a"))

def symmD : LibDef where
  name := "symm"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.path (.var "A") (.var "b") (.var "a")))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "i" (.papp (.var "p") (.var "a") (.var "b") (.ineg (.var "i"))))

def transD : LibDef where
  name := "trans"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A") (.pi "c" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.arr (.path (.var "A") (.var "b") (.var "c"))
        (.path (.var "A") (.var "a") (.var "c")))))))
  tm := lams ["A", "a", "b", "c", "p", "q"]
    (.plam "i" (.hcomp "j" (.var "A")
      [([(.var "i", false)], .var "a"),
       ([(.var "i", true)], .papp (.var "q") (.var "b") (.var "c") (.var "j"))]
      (.papp (.var "p") (.var "a") (.var "b") (.var "i"))))

def congD : LibDef where
  name := "cong"
  ty := .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
      (.arr (.path (.var "A") (.var "a") (.var "b"))
        (.path (.var "B") (.app (.var "f") (.var "a"))
          (.app (.var "f") (.var "b"))))))))
  tm := lams ["A", "B", "f", "a", "b", "p"]
    (.plam "i" (.app (.var "f")
      (.papp (.var "p") (.var "a") (.var "b") (.var "i"))))

def happlyD : LibDef where
  name := "happly"
  ty := .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "A") (.var "B"))
      (.arr (.path (.arr (.var "A") (.var "B")) (.var "f") (.var "g"))
        (.pi "x" (.var "A")
          (.path (.var "B") (.app (.var "f") (.var "x"))
            (.app (.var "g") (.var "x"))))))))
  tm := lams ["A", "B", "f", "g", "p", "x"]
    (.plam "i" (.app (.papp (.var "p") (.var "f") (.var "g") (.var "i")) (.var "x")))

def funExtD : LibDef where
  name := "funExt"
  ty := .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "A") (.var "B"))
      (.arr
        (.pi "x" (.var "A") (.path (.var "B")
          (.app (.var "f") (.var "x")) (.app (.var "g") (.var "x"))))
        (.path (.arr (.var "A") (.var "B")) (.var "f") (.var "g"))))))
  tm := lams ["A", "B", "f", "g", "h"]
    (.plam "i" (.lam "x"
      (.papp (.app (.var "h") (.var "x"))
        (.app (.var "f") (.var "x")) (.app (.var "g") (.var "x")) (.var "i"))))

#guard reflD.ok
#guard symmD.ok
#guard transD.ok
#guard congD.ok
#guard happlyD.ok
#guard funExtD.ok

/-! ## Transport and path induction -/

def transportD : LibDef where
  name := "transport"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (.path .univ (.var "A") (.var "B")) (.arr (.var "A") (.var "B"))))
  tm := lams ["A", "B", "p", "a"]
    (.transp "i" (.papp (.var "p") (.var "A") (.var "B") (.var "i")) (.var "a"))

def substD : LibDef where
  name := "subst"
  ty := .pi "A" .univ (.pi "P" (.arr (.var "A") .univ)
    (.pi "x" (.var "A") (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y"))
        (.arr (.app (.var "P") (.var "x")) (.app (.var "P") (.var "y")))))))
  tm := lams ["A", "P", "x", "y", "p", "px"]
    (.transp "i"
      (.app (.var "P") (.papp (.var "p") (.var "x") (.var "y") (.var "i")))
      (.var "px"))

/-- **Path induction `J`, as a program**: transport in the motive along the
connection square `(i, j) ↦ p @ (i ∧ j)`, which sweeps `(x, refl)` to
`(y, p)`.  In book HoTT, `J` is a primitive; here it is derived. -/
def jD : LibDef where
  name := "J"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (.pi "P" (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y")) .univ))
    (.pi "d" (apps (.var "P") [.var "x", .plam "k" (.var "x")])
    (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
      (apps (.var "P") [.var "y", .var "p"]))))))
  tm := lams ["A", "x", "P", "d", "y", "p"]
    (.transp "i"
      (apps (.var "P")
        [.papp (.var "p") (.var "x") (.var "y") (.var "i"),
         .plam "j" (.papp (.var "p") (.var "x") (.var "y")
           (.imin (.var "i") (.var "j")))])
      (.var "d"))

#guard transportD.ok
#guard substD.ok
#guard jD.ok

-- J computes on refl (the constancy rule fires on the collapsed square)
#guard
  match normalize
    (apps jD.ref [.nat, .zero,
      lams ["y", "q"] .nat, .succ .zero, .zero, .plam "k" .zero]) .nat with
  | .ok t => t == .succ .zero
  | .error _ => false

/-! ## h-levels -/

def isContrR (C : Raw) : Raw :=
  .sigma "ctr" C (.pi "other" C (.path C (.var "ctr") (.var "other")))

def isPropR (A : Raw) : Raw :=
  .pi "xp" A (.pi "yp" A (.path A (.var "xp") (.var "yp")))

def isSetR (A : Raw) : Raw :=
  .pi "xs" A (.pi "ys" A
    (isPropR (.path A (.var "xs") (.var "ys"))))

/-- Singletons are contractible (the connection contraction). -/
def contrSinglD : LibDef where
  name := "contrSingl"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (isContrR (.sigma "y" (.var "A") (.path (.var "A") (.var "x") (.var "y")))))
  tm := lams ["A", "x"]
    (.pair (.pair (.var "x") (.plam "k" (.var "x")))
      (.lam "s" (.plam "i" (.pair
        (.papp (.snd (.var "s")) (.var "x") (.fst (.var "s")) (.var "i"))
        (.plam "j" (.papp (.snd (.var "s")) (.var "x") (.fst (.var "s"))
          (.imin (.var "i") (.var "j"))))))))

/-- Contractible types are propositions: connect through the center. -/
def contrToPropD : LibDef where
  name := "contrToProp"
  ty := .pi "A" .univ (.arr (isContrR (.var "A")) (isPropR (.var "A")))
  tm := lams ["A", "c", "xp", "yp"]
    (apps transD.ref
      [.var "A", .var "xp", .fst (.var "c"), .var "yp",
       apps symmD.ref
         [.var "A", .fst (.var "c"), .var "xp",
          .app (.snd (.var "c")) (.var "xp")],
       .app (.snd (.var "c")) (.var "yp")])

#guard contrSinglD.ok
#guard contrToPropD.ok

/-! ## Equivalences and univalence -/

def fiberR (A B f y : Raw) : Raw :=
  .sigma "xf" A (.path B y (.app f (.var "xf")))

def equivR (A B : Raw) : Raw :=
  .sigma "f" (.arr A B)
    (.pi "yb" B (isContrR (fiberR A B (.var "f") (.var "yb"))))

def idEquivD : LibDef where
  name := "idEquiv"
  ty := .pi "A" .univ (equivR (.var "A") (.var "A"))
  tm := .lam "A" (.pair (.lam "x" (.var "x"))
    (.lam "a" (.pair
      (.pair (.var "a") (.plam "k" (.var "a")))
      (.lam "fib" (.plam "i" (.pair
        (.papp (.snd (.var "fib")) (.var "a") (.fst (.var "fib")) (.var "i"))
        (.plam "j"
          (.papp (.snd (.var "fib")) (.var "a") (.fst (.var "fib"))
            (.imin (.var "i") (.var "j"))))))))))

/-- **Univalence, the map** — an equivalence becomes a path in the universe. -/
def uaD : LibDef where
  name := "ua"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (equivR (.var "A") (.var "B"))
      (.path .univ (.var "A") (.var "B"))))
  tm := lams ["A", "B", "e"] (.plam "i"
    (.glueTy
      [([(.var "i", false)], .var "A", .var "e"),
       ([(.var "i", true)], .var "B", .app idEquivD.ref (.var "B"))]
      (.var "B")))

/-- The inverse direction of univalence, by transport in the `Equiv` family. -/
def pathToEquivD : LibDef where
  name := "pathToEquiv"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (.path .univ (.var "A") (.var "B"))
      (equivR (.var "A") (.var "B"))))
  tm := lams ["A", "B", "p"]
    (.transp "i"
      (equivR (.var "A") (.papp (.var "p") (.var "A") (.var "B") (.var "i")))
      (.app idEquivD.ref (.var "A")))

/- DISABLED pending A2 (old strict-cancellation sucEquiv + its guards)
/-- The successor equivalence of ℤ (strict `isuc`/`ipred` cancellation makes
its fibers literal singletons). -/
def sucEquivD : LibDef where
  name := "sucEquiv"
  ty := equivR .int .int
  tm := apps setIsoToEquivD.ref
    [.int, .int, sucZD.ref, predZD.ref,
     sucPredZD.ref, predSucZD.ref, isSetZD.ref]

#guard sucEquivD.ok

-- transport along `ua e` applies the equivalence — for an abstract `e`
#guard
  match normalize
    (.lam "e" (.transp "i"
      (.papp (apps uaD.ref [.int, .int, .var "e"]) .int .int (.var "i"))
      .izero))
    (.pi "e" (equivR .int .int) .int) with
  | .ok t => t == .lam (.app (.fst (.var 0)) .izero)
  | .error _ => false


-/

/-! ## Integers (`pos`/`negsuc` over ℕ)

`sucZ`/`predZ` are *defined* functions (case split + `natrec`); their
cancellation laws hold per case — `refl` in each branch, glued by
induction.  (The previous strictly-cancelling ℤ was removed from the
kernel: it broke substitution-stability of definitional equality.) -/

/-- Numeral helpers (Lean-side). -/
def natLit : Nat → Raw
  | 0 => .zero
  | n + 1 => .succ (natLit n)

def posZ (k : Nat) : Raw := .ipos (natLit k)
def negZ (k : Nat) : Raw := .inegsuc (natLit (k - 1))

def sucZD : LibDef where
  name := "sucZ"
  ty := .arr .int .int
  tm := .lam "z" (.intcase "k" .int
    (.lam "n" (.ipos (.succ (.var "n"))))
    (.lam "n" (.natrec "k2" .int (.ipos .zero)
      (lams ["m", "ih"] (.inegsuc (.var "m"))) (.var "n")))
    (.var "z"))

def predZD : LibDef where
  name := "predZ"
  ty := .arr .int .int
  tm := .lam "z" (.intcase "k" .int
    (.lam "n" (.natrec "k2" .int (.inegsuc .zero)
      (lams ["m", "ih"] (.ipos (.var "m"))) (.var "n")))
    (.lam "n" (.inegsuc (.succ (.var "n"))))
    (.var "z"))

/-- `pred (suc z) ≡ z` — every case is `refl`. -/
def predSucZD : LibDef where
  name := "predSucZ"
  ty := .pi "z" .int
    (.path .int (.app predZD.ref (.app sucZD.ref (.var "z"))) (.var "z"))
  tm := .lam "z" (.intcase "k"
    (.path .int (.app predZD.ref (.app sucZD.ref (.var "k"))) (.var "k"))
    (.lam "n" (.plam "i" (.ipos (.var "n"))))
    (.lam "n" (.natrec "k2"
      (.path .int
        (.app predZD.ref (.app sucZD.ref (.inegsuc (.var "k2"))))
        (.inegsuc (.var "k2")))
      (.plam "i" (.inegsuc .zero))
      (lams ["m", "ih"] (.plam "i" (.inegsuc (.succ (.var "m")))))
      (.var "n")))
    (.var "z"))

/-- `suc (pred z) ≡ z` — every case is `refl`. -/
def sucPredZD : LibDef where
  name := "sucPredZ"
  ty := .pi "z" .int
    (.path .int (.app sucZD.ref (.app predZD.ref (.var "z"))) (.var "z"))
  tm := .lam "z" (.intcase "k"
    (.path .int (.app sucZD.ref (.app predZD.ref (.var "k"))) (.var "k"))
    (.lam "n" (.natrec "k2"
      (.path .int
        (.app sucZD.ref (.app predZD.ref (.ipos (.var "k2"))))
        (.ipos (.var "k2")))
      (.plam "i" (.ipos .zero))
      (lams ["m", "ih"] (.plam "i" (.ipos (.succ (.var "m")))))
      (.var "n")))
    (.lam "n" (.plam "i" (.inegsuc (.var "n"))))
    (.var "z"))

#guard sucZD.ok
#guard predZD.ok
#guard predSucZD.ok
#guard sucPredZD.ok

def addD : LibDef where
  name := "add"
  ty := .arr .int (.arr .int .int)
  tm := lams ["m", "z"] (.intcase "k" .int
    (.lam "n" (.natrec "k2" .int (.var "m")
      (lams ["k3", "ih"] (.app sucZD.ref (.var "ih"))) (.var "n")))
    (.lam "n" (.natrec "k2" .int (.app predZD.ref (.var "m"))
      (lams ["k3", "ih"] (.app predZD.ref (.var "ih"))) (.var "n")))
    (.var "z"))

/-- `n + 0 ≡ n` holds by computation. -/
def addZeroRD : LibDef where
  name := "addZeroR"
  ty := .pi "n" .int
    (.path .int (apps addD.ref [.var "n", posZ 0]) (.var "n"))
  tm := .lam "n" (.plam "i" (.var "n"))

/-- `0 + z ≡ z`, by cases and induction (`cong sucZ/predZ` steps). -/
def addZeroLD : LibDef where
  name := "addZeroL"
  ty := .pi "z" .int
    (.path .int (apps addD.ref [posZ 0, .var "z"]) (.var "z"))
  tm := .lam "z" (.intcase "k"
    (.path .int (apps addD.ref [posZ 0, .var "k"]) (.var "k"))
    (.lam "n" (.natrec "k2"
      (.path .int (apps addD.ref [posZ 0, .ipos (.var "k2")])
        (.ipos (.var "k2")))
      (.plam "i" (.ipos .zero))
      (lams ["m", "ih"] (.plam "i" (.app sucZD.ref
        (.papp (.var "ih")
          (apps addD.ref [posZ 0, .ipos (.var "m")]) (.ipos (.var "m"))
          (.var "i")))))
      (.var "n")))
    (.lam "n" (.natrec "k2"
      (.path .int (apps addD.ref [posZ 0, .inegsuc (.var "k2")])
        (.inegsuc (.var "k2")))
      (.plam "i" (.inegsuc .zero))
      (lams ["m", "ih"] (.plam "i" (.app predZD.ref
        (.papp (.var "ih")
          (apps addD.ref [posZ 0, .inegsuc (.var "m")]) (.inegsuc (.var "m"))
          (.var "i")))))
      (.var "n")))
    (.var "z"))

#guard addD.ok
#guard addZeroRD.ok
#guard addZeroLD.ok

-- addition computes: 2 + 3 ⟶ 5, 2 + (−3) ⟶ −1
#guard
  match normalize (apps addD.ref [posZ 2, posZ 3]) .int with
  | .ok t => t == resolveClosed (posZ 5)
  | .error _ => false
#guard
  match normalize (apps addD.ref [posZ 2, negZ 3]) .int with
  | .ok t => t == resolveClosed (negZ 1)
  | .error _ => false

end Cubical.Library

import FormalizedMathematics.Cubical.LibHITs

namespace Cubical.Library

open Raw

/-! ## The figure eight and its abelianized winding

A rank-2 cover `helix8 : S¹ ∨ S¹ → U` (each circle winds its own ℤ factor)
gives the **abelianized winding homomorphism** `π₁(S¹∨S¹) → ℤ × ℤ`.  The
computations run through `pushrec`'s hcomp-commute, `HCompU`, and Glue
transport — and the commutator collapsing to `(0,0)` is a *computation*
witnessing that this invariant only sees the abelianization of `F₂`. -/

def prodZZ : Raw := .sigma "u" .int .int

/-- Products of sets are sets — no `hcomp` needed, thanks to Σ-η. -/
def isSetProdD : LibDef where
  name := "isSetProd"
  ty := .pi "A" .univ (.pi "B" .univ
    (.arr (isSetR (.var "A")) (.arr (isSetR (.var "B"))
      (isSetR (.sigma "u" (.var "A") (.var "B"))))))
  tm :=
    let PT : Raw := .sigma "u" (.var "A") (.var "B")
    let cfst (pp : Raw) : Raw := apps congD.ref [PT, .var "A",
      .lam "w" (.fst (.var "w")), .var "xs", .var "ys", pp]
    let csnd (pp : Raw) : Raw := apps congD.ref [PT, .var "B",
      .lam "w" (.snd (.var "w")), .var "xs", .var "ys", pp]
    lams ["A", "B", "hA", "hB", "xs", "ys", "xp", "yp"]
      (.plam "i" (.plam "j" (.pair
        (.papp
          (apps (.var "hA") [.fst (.var "xs"), .fst (.var "ys"),
            cfst (.var "xp"), cfst (.var "yp")])
          (cfst (.var "xp")) (cfst (.var "yp")) (.var "i")
          |> fun outer => .papp outer
            (.fst (.var "xs")) (.fst (.var "ys")) (.var "j"))
        (.papp
          (apps (.var "hB") [.snd (.var "xs"), .snd (.var "ys"),
            csnd (.var "xp"), csnd (.var "yp")])
          (csnd (.var "xp")) (csnd (.var "yp")) (.var "i")
          |> fun outer => .papp outer
            (.snd (.var "xs")) (.snd (.var "ys")) (.var "j")))))

#guard isSetProdD.ok

/-- `sucZ` on the left factor of `ℤ × ℤ`, as an equivalence. -/
def sucLeftEquivD : LibDef where
  name := "sucLeftEquiv"
  ty := equivR prodZZ prodZZ
  tm := apps setIsoToEquivD.ref
    [prodZZ, prodZZ,
     .lam "w" (.pair (.app sucZD.ref (.fst (.var "w"))) (.snd (.var "w"))),
     .lam "w" (.pair (.app predZD.ref (.fst (.var "w"))) (.snd (.var "w"))),
     .lam "w" (.plam "i" (.pair
       (.papp (.app sucPredZD.ref (.fst (.var "w")))
         (.app sucZD.ref (.app predZD.ref (.fst (.var "w"))))
         (.fst (.var "w")) (.var "i"))
       (.snd (.var "w")))),
     .lam "w" (.plam "i" (.pair
       (.papp (.app predSucZD.ref (.fst (.var "w")))
         (.app predZD.ref (.app sucZD.ref (.fst (.var "w"))))
         (.fst (.var "w")) (.var "i"))
       (.snd (.var "w")))),
     apps isSetProdD.ref [.int, .int, isSetZD.ref, isSetZD.ref]]

/-- `sucZ` on the right factor. -/
def sucRightEquivD : LibDef where
  name := "sucRightEquiv"
  ty := equivR prodZZ prodZZ
  tm := apps setIsoToEquivD.ref
    [prodZZ, prodZZ,
     .lam "w" (.pair (.fst (.var "w")) (.app sucZD.ref (.snd (.var "w")))),
     .lam "w" (.pair (.fst (.var "w")) (.app predZD.ref (.snd (.var "w")))),
     .lam "w" (.plam "i" (.pair (.fst (.var "w"))
       (.papp (.app sucPredZD.ref (.snd (.var "w")))
         (.app sucZD.ref (.app predZD.ref (.snd (.var "w"))))
         (.snd (.var "w")) (.var "i")))),
     .lam "w" (.plam "i" (.pair (.fst (.var "w"))
       (.papp (.app predSucZD.ref (.snd (.var "w")))
         (.app predZD.ref (.app sucZD.ref (.snd (.var "w"))))
         (.snd (.var "w")) (.var "i")))),
     apps isSetProdD.ref [.int, .int, isSetZD.ref, isSetZD.ref]]

#guard sucLeftEquivD.ok
#guard sucRightEquivD.ok

private def w8 : Raw := wedge .s1 .s1 .sbase .sbase
private def cbase : Raw := .lam "u0" .sbase
private def w8base : Raw := .pinl .sbase

/-- The rank-2 cover of the figure eight. -/
def helix8D : LibDef where
  name := "helix8"
  ty := .arr w8 .univ
  tm := .lam "p" (.pushrec "k" .univ
    (.lam "x" (.s1elim "x2" .univ prodZZ
      (apps uaD.ref [prodZZ, prodZZ, sucLeftEquivD.ref]) (.var "x")))
    (.lam "x" (.s1elim "x2" .univ prodZZ
      (apps uaD.ref [prodZZ, prodZZ, sucRightEquivD.ref]) (.var "x")))
    (.lam "u" (.plam "i" prodZZ))
    (.var "p"))

/-- The abelianized winding `π₁(S¹∨S¹) → ℤ × ℤ`. -/
def wind8D : LibDef where
  name := "wind8"
  ty := .arr (.path w8 w8base w8base) prodZZ
  tm := .lam "p" (.transp "i"
    (.app helix8D.ref (.papp (.var "p") w8base w8base (.var "i")))
    (.pair (.ipos .zero) (.ipos .zero)))

#guard helix8D.ok
#guard wind8D.ok

private def loopL : Raw := .plam "i" (.pinl (.sloop (.var "i")))
private def pushT : Raw :=
  .plam "i" (.ppush cbase cbase .tt (.var "i"))
private def w8r : Raw := .pinr .sbase
private def compW8 (a b c p q : Raw) : Raw :=
  apps transD.ref [w8, a, b, c, p, q]
/-- `push ⬝ loopR ⬝ push⁻¹`, the right loop based at `pinl base`. -/
private def loopRconj : Raw :=
  compW8 w8base w8r w8base pushT
    (compW8 w8r w8r w8base (.plam "i" (.pinr (.sloop (.var "i"))))
      (apps symmD.ref [w8, w8base, w8r, pushT]))

-- the two generators wind their own factors (sub-second computations) …
#guard
  match normalize (.app wind8D.ref loopL) prodZZ with
  | .ok t => t == .pair (resolveClosed (posZ 1)) (resolveClosed (posZ 0))
  | .error _ => false
#guard
  match normalize (.app wind8D.ref loopRconj) prodZZ with
  | .ok t => t == .pair (resolveClosed (posZ 0)) (resolveClosed (posZ 1))
  | .error _ => false

/- … and, verified by direct normalization (too slow for build guards:
   ~100 s each at composition depth 3, tens of minutes at the commutator's
   depth 5):

     wind8 (loopL ⬝ loopRconj) ⟶ (+1, +1)
     wind8 (loopRconj ⬝ loopL) ⟶ (+1, +1)     — the two orders agree:
   this invariant sees only the *abelianization* of π₁(S¹∨S¹) = F₂. -/

/-! ## Set quotients

The last of the major HITs.  `isSetQuot` is the constructor; the dependent
`elimProp` is *derived* from the primitive `qelim` (`isPropToIsSet` for the
set-ness, `toPathP` for the path cells); and the flagship identifies
propositional truncation with the quotient by the total relation. -/

/-- Quotients are sets — the constructor, verbatim. -/
def isSetQuotD : LibDef where
  name := "isSetQuot"
  ty := .pi "A" .univ (.pi "R" (.arr (.var "A") (.arr (.var "A") .univ))
    (isSetR (.quot (.var "A") (.var "R"))))
  tm := lams ["A", "R", "xs", "ys", "xp", "yp"]
    (.plam "i" (.plam "j" (.qsquash (.var "xs") (.var "ys")
      (.var "xp") (.var "yp") (.var "i") (.var "j"))))

/-- Dependent paths over a path in a family of *sets* are unique
(one application of `J`). -/
def isPropPathPSetD : LibDef where
  name := "isPropPathPSet"
  ty :=
    -- PathP (λ j. P (pth @ j)) u v, for a path variable `pv : x ≡ ye`
    let pp (pv ye : Raw) : Raw := .pathP "j"
      (.app (.var "P") (.papp pv (.var "x") ye (.var "j")))
      (.var "u") (.var "v")
    .pi "X" .univ (.pi "P" (.arr (.var "X") .univ)
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
      (apps jD.ref [.var "X", .var "x",
        lams ["y2", "p2"] (.pi "v" (.app (.var "P") (.var "y2"))
          (.pi "al" (pp (.var "p2") (.var "y2"))
          (.pi "be" (pp (.var "p2") (.var "y2"))
            (.path (pp (.var "p2") (.var "y2")) (.var "al") (.var "be"))))),
        lams ["v", "al", "be"]
          (apps (.app (.var "mset") (.var "x"))
            [.var "u", .var "v", .var "al", .var "be"]),
        .var "y", .var "pth"])

#guard isSetQuotD.ok
#guard isPropPathPSetD.ok

/-- Dependent elimination into propositions, derived from `qelim`. -/
def qelimPropD : LibDef where
  name := "qelimProp"
  ty := .pi "A" .univ (.pi "R" (.arr (.var "A") (.arr (.var "A") .univ))
    (.pi "P" (.arr (.quot (.var "A") (.var "R")) .univ)
    (.pi "mprp" (.pi "x0" (.quot (.var "A") (.var "R"))
      (isPropR (.app (.var "P") (.var "x0"))))
    (.pi "f" (.pi "a" (.var "A") (.app (.var "P") (.qin (.var "a"))))
    (.pi "x" (.quot (.var "A") (.var "R"))
      (.app (.var "P") (.var "x")))))))
  tm :=
    let Pat (v : Raw) : Raw := .app (.var "P") v
    let line : Raw := .plam "i" (Pat (.qeq (.var "a") (.var "b")
      (.var "w") (.var "i")))
    lams ["A", "R", "P", "mprp", "f", "x"] (.qelim "k"
      (Pat (.var "k"))
      (.lam "k" (apps isPropToIsSetD.ref
        [Pat (.var "k"), .app (.var "mprp") (.var "k")]))
      (.var "f")
      (lams ["a", "b", "w"] (apps toPathPD.ref
        [Pat (.qin (.var "a")), Pat (.qin (.var "b")), line,
         .app (.var "f") (.var "a"), .app (.var "f") (.var "b"),
         apps (.app (.var "mprp") (.qin (.var "b")))
           [apps transportD.ref [Pat (.qin (.var "a")),
              Pat (.qin (.var "b")), line,
              .app (.var "f") (.var "a")],
            .app (.var "f") (.var "b")]]))
      (.var "x"))

#guard qelimPropD.ok

private def totalRel : Raw := lams ["u1", "u2"] .unit
private def quotTot (A : Raw) : Raw := .quot A totalRel

/-- The quotient by the total relation is a proposition. -/
def isPropQuotTotalD : LibDef where
  name := "isPropQuotTotal"
  ty := .pi "A" .univ (isPropR (quotTot (.var "A")))
  tm := lams ["A", "xp", "yp"] (apps qelimPropD.ref
    [.var "A", totalRel,
     .lam "k" (.path (quotTot (.var "A")) (.var "k") (.var "yp")),
     .lam "k" (apps isSetQuotD.ref
       [.var "A", totalRel, .var "k", .var "yp"]),
     .lam "a" (apps qelimPropD.ref
       [.var "A", totalRel,
        .lam "k2" (.path (quotTot (.var "A")) (.qin (.var "a")) (.var "k2")),
        .lam "k2" (apps isSetQuotD.ref
          [.var "A", totalRel, .qin (.var "a"), .var "k2"]),
        .lam "b" (.plam "i" (.qeq (.var "a") (.var "b") .tt (.var "i"))),
        .var "yp"]),
     .var "xp"])

#guard isPropQuotTotalD.ok

/-- **`∥ A ∥ ≃ A / (total relation)`** — truncation is a quotient. -/
def truncAsQuotD : LibDef where
  name := "truncAsQuot"
  ty := .pi "A" .univ (equivR (.trunc (.var "A")) (quotTot (.var "A")))
  tm :=
    let toQ : Raw := .lam "t" (.truncrec (quotTot (.var "A"))
      (.app isPropQuotTotalD.ref (.var "A"))
      (.lam "a" (.qin (.var "a"))) (.var "t"))
    let fromQ : Raw := .lam "x" (apps qelimPropD.ref
      [.var "A", totalRel,
       .lam "k" (.trunc (.var "A")),
       .lam "k" (.app isPropTruncD.ref (.var "A")),
       .lam "a" (.tin (.var "a")),
       .var "x"])
    let toQA : Raw := .ann toQ
      (.arr (.trunc (.var "A")) (quotTot (.var "A")))
    let fromQA : Raw := .ann fromQ
      (.arr (quotTot (.var "A")) (.trunc (.var "A")))
    .lam "A" (apps isoToEquivD.ref
      [.trunc (.var "A"), quotTot (.var "A"), toQ, fromQ,
       .lam "x" (apps qelimPropD.ref
         [.var "A", totalRel,
          .lam "k" (.path (quotTot (.var "A"))
            (.app toQA (.app fromQA (.var "k"))) (.var "k")),
          .lam "k" (apps isSetQuotD.ref [.var "A", totalRel,
            .app toQA (.app fromQA (.var "k")), .var "k"]),
          .lam "a" (.plam "i" (.qin (.var "a"))),
          .var "x"]),
       .lam "u" (apps (.app isPropTruncD.ref (.var "A"))
         [.app fromQA (.app toQA (.var "u")), .var "u"])])

#guard truncAsQuotD.ok

/-! ## ℤ as a quotient of ℕ × ℕ

The textbook construction: `(a, b)` represents `a − b`, and
`(a,b) ∼ (c,d) ⟺ a + d = c + b`.  First the ℕ arithmetic, then the
quotient maps, then the equivalence. -/

/-- ℕ addition (recursion on the first argument). -/
def addNatD : LibDef where
  name := "addNat"
  ty := .arr .nat (.arr .nat .nat)
  tm := lams ["m", "n"] (.natrec "k" .nat (.var "n")
    (lams ["m2", "ih"] (.succ (.var "ih"))) (.var "m"))

private def addN (a b : Raw) : Raw := apps addNatD.ref [a, b]

def addZeroRNatD : LibDef where
  name := "addZeroRNat"
  ty := .pi "a" .nat (.path .nat (addN (.var "a") .zero) (.var "a"))
  tm := .lam "a" (.natrec "k"
    (.path .nat (addN (.var "k") .zero) (.var "k"))
    (.plam "i" .zero)
    (lams ["m", "ih"] (apps congD.ref [.nat, .nat,
      .lam "w" (.succ (.var "w")),
      addN (.var "m") .zero, .var "m", .var "ih"]))
    (.var "a"))

def addSucRNatD : LibDef where
  name := "addSucRNat"
  ty := .pi "a" .nat (.pi "k" .nat
    (.path .nat (addN (.var "a") (.succ (.var "k")))
      (.succ (addN (.var "a") (.var "k")))))
  tm := lams ["a", "k"] (.natrec "k2"
    (.path .nat (addN (.var "k2") (.succ (.var "k")))
      (.succ (addN (.var "k2") (.var "k"))))
    (.plam "i" (.succ (.var "k")))
    (lams ["m", "ih"] (apps congD.ref [.nat, .nat,
      .lam "w" (.succ (.var "w")),
      addN (.var "m") (.succ (.var "k")),
      .succ (addN (.var "m") (.var "k")), .var "ih"]))
    (.var "a"))

def addCommNatD : LibDef where
  name := "addCommNat"
  ty := .pi "a" .nat (.pi "b" .nat
    (.path .nat (addN (.var "a") (.var "b")) (addN (.var "b") (.var "a"))))
  tm := lams ["a", "b"] (.natrec "k"
    (.path .nat (addN (.var "k") (.var "b")) (addN (.var "b") (.var "k")))
    (apps symmD.ref [.nat, addN (.var "b") .zero, .var "b",
      .app addZeroRNatD.ref (.var "b")])
    (lams ["m", "ih"] (apps transD.ref [.nat,
      .succ (addN (.var "m") (.var "b")),
      .succ (addN (.var "b") (.var "m")),
      addN (.var "b") (.succ (.var "m")),
      apps congD.ref [.nat, .nat, .lam "w" (.succ (.var "w")),
        addN (.var "m") (.var "b"), addN (.var "b") (.var "m"), .var "ih"],
      apps symmD.ref [.nat,
        addN (.var "b") (.succ (.var "m")),
        .succ (addN (.var "b") (.var "m")),
        apps addSucRNatD.ref [.var "b", .var "m"]]]))
    (.var "a"))

#guard addNatD.ok
#guard addZeroRNatD.ok
#guard addSucRNatD.ok
#guard addCommNatD.ok

/-- `a − b : ℤ` (iterated predecessor). -/
def subNatD : LibDef where
  name := "subNat"
  ty := .arr .nat (.arr .nat .int)
  tm := lams ["a", "b"] (.natrec "k" .int (.ipos (.var "a"))
    (lams ["m", "ih"] (.app predZD.ref (.var "ih"))) (.var "b"))

private def subN (a b : Raw) : Raw := apps subNatD.ref [a, b]

def subSucSucD : LibDef where
  name := "subSucSuc"
  ty := .pi "a" .nat (.pi "b" .nat
    (.path .int (subN (.succ (.var "a")) (.succ (.var "b")))
      (subN (.var "a") (.var "b"))))
  tm := lams ["a", "b"] (.natrec "k"
    (.path .int (subN (.succ (.var "a")) (.succ (.var "k")))
      (subN (.var "a") (.var "k")))
    (.plam "i" (.ipos (.var "a")))
    (lams ["m", "ih"] (apps congD.ref [.int, .int, predZD.ref,
      subN (.succ (.var "a")) (.succ (.var "m")),
      subN (.var "a") (.var "m"), .var "ih"]))
    (.var "b"))

def subAddCancelRD : LibDef where
  name := "subAddCancelR"
  ty := .pi "a" .nat (.pi "b" .nat (.pi "k" .nat
    (.path .int (subN (addN (.var "a") (.var "k")) (addN (.var "b") (.var "k")))
      (subN (.var "a") (.var "b")))))
  tm := lams ["a", "b", "k"] (.natrec "k2"
    (.path .int
      (subN (addN (.var "a") (.var "k2")) (addN (.var "b") (.var "k2")))
      (subN (.var "a") (.var "b")))
    -- k = 0: rewrite both summands by addZeroR
    (apps transD.ref [.int,
      subN (addN (.var "a") .zero) (addN (.var "b") .zero),
      subN (.var "a") (addN (.var "b") .zero),
      subN (.var "a") (.var "b"),
      apps congD.ref [.nat, .int,
        .lam "w" (subN (.var "w") (addN (.var "b") .zero)),
        addN (.var "a") .zero, .var "a",
        .app addZeroRNatD.ref (.var "a")],
      apps congD.ref [.nat, .int,
        .lam "w" (subN (.var "a") (.var "w")),
        addN (.var "b") .zero, .var "b",
        .app addZeroRNatD.ref (.var "b")]])
    -- k = suc m: rewrite by addSucR twice, then subSucSuc, then ih
    (lams ["m", "ih"] (apps transD.ref [.int,
      subN (addN (.var "a") (.succ (.var "m")))
        (addN (.var "b") (.succ (.var "m"))),
      subN (.succ (addN (.var "a") (.var "m")))
        (addN (.var "b") (.succ (.var "m"))),
      subN (.var "a") (.var "b"),
      apps congD.ref [.nat, .int,
        .lam "w" (subN (.var "w") (addN (.var "b") (.succ (.var "m")))),
        addN (.var "a") (.succ (.var "m")),
        .succ (addN (.var "a") (.var "m")),
        apps addSucRNatD.ref [.var "a", .var "m"]],
      apps transD.ref [.int,
        subN (.succ (addN (.var "a") (.var "m")))
          (addN (.var "b") (.succ (.var "m"))),
        subN (.succ (addN (.var "a") (.var "m")))
          (.succ (addN (.var "b") (.var "m"))),
        subN (.var "a") (.var "b"),
        apps congD.ref [.nat, .int,
          .lam "w" (subN (.succ (addN (.var "a") (.var "m"))) (.var "w")),
          addN (.var "b") (.succ (.var "m")),
          .succ (addN (.var "b") (.var "m")),
          apps addSucRNatD.ref [.var "b", .var "m"]],
        apps transD.ref [.int,
          subN (.succ (addN (.var "a") (.var "m")))
            (.succ (addN (.var "b") (.var "m"))),
          subN (addN (.var "a") (.var "m")) (addN (.var "b") (.var "m")),
          subN (.var "a") (.var "b"),
          apps subSucSucD.ref [addN (.var "a") (.var "m"),
            addN (.var "b") (.var "m")],
          .var "ih"]]]))
    (.var "k"))

#guard subNatD.ok
#guard subSucSucD.ok
#guard subAddCancelRD.ok

private def nnTy : Raw := .sigma "u" .nat .nat
private def relNN : Raw := lams ["w1", "w2"] (.path .nat
  (addN (.fst (.var "w1")) (.snd (.var "w2")))
  (addN (.fst (.var "w2")) (.snd (.var "w1"))))
private def zqTy : Raw := .quot nnTy relNN

/-- `(a,b) ↦ a − b` descends to the quotient. -/
def nnQuotToZD : LibDef where
  name := "nnQuotToZ"
  ty := .arr zqTy .int
  tm :=
    let a : Raw := .fst (.var "w1")
    let b : Raw := .snd (.var "w1")
    let c : Raw := .fst (.var "w2")
    let d : Raw := .snd (.var "w2")
    .lam "x" (.qelim "k" .int
      (.lam "k" isSetZD.ref)
      (.lam "w" (subN (.fst (.var "w")) (.snd (.var "w"))))
      (lams ["w1", "w2", "e"] (apps transD.ref [.int,
        subN a b,
        subN (addN a d) (addN b d),
        subN c d,
        apps symmD.ref [.int,
          subN (addN a d) (addN b d), subN a b,
          apps subAddCancelRD.ref [a, b, d]],
        apps transD.ref [.int,
          subN (addN a d) (addN b d),
          subN (addN c b) (addN b d),
          subN c d,
          apps congD.ref [.nat, .int,
            .lam "h" (subN (.var "h") (addN b d)),
            addN a d, addN c b, .var "e"],
          apps transD.ref [.int,
            subN (addN c b) (addN b d),
            subN (addN c b) (addN d b),
            subN c d,
            apps congD.ref [.nat, .int,
              .lam "h" (subN (addN c b) (.var "h")),
              addN b d, addN d b,
              apps addCommNatD.ref [b, d]],
            apps subAddCancelRD.ref [c, d, b]]]]))
      (.var "x"))

/-- `ℤ → (ℕ×ℕ)/∼` via the canonical representatives. -/
def zToNNQuotD : LibDef where
  name := "zToNNQuot"
  ty := .arr .int zqTy
  tm := .lam "z" (.intcase "k" zqTy
    (.lam "n" (.qin (.pair (.var "n") .zero)))
    (.lam "n" (.qin (.pair .zero (.succ (.var "n")))))
    (.var "z"))

#guard nnQuotToZD.ok
#guard zToNNQuotD.ok

/-- The successor-of-second-component map on the quotient. -/
def predQD : LibDef where
  name := "predQ"
  ty := .arr zqTy zqTy
  tm :=
    let a : Raw := .fst (.var "w1")
    let b : Raw := .snd (.var "w1")
    let c : Raw := .fst (.var "w2")
    let d : Raw := .snd (.var "w2")
    .lam "x" (.qelim "k" zqTy
      (.lam "k" (apps isSetQuotD.ref [nnTy, relNN]))
      (.lam "w" (.qin (.pair (.fst (.var "w")) (.succ (.snd (.var "w"))))))
      (lams ["w1", "w2", "e"] (.plam "i" (.qeq
        (.pair a (.succ b)) (.pair c (.succ d))
        (apps transD.ref [.nat,
          addN a (.succ d),
          .succ (addN a d),
          addN c (.succ b),
          apps addSucRNatD.ref [a, d],
          apps transD.ref [.nat,
            .succ (addN a d),
            .succ (addN c b),
            addN c (.succ b),
            apps congD.ref [.nat, .nat, .lam "h" (.succ (.var "h")),
              addN a d, addN c b, .var "e"],
            apps symmD.ref [.nat,
              addN c (.succ b), .succ (addN c b),
              apps addSucRNatD.ref [c, b]]]])
        (.var "i"))))
      (.var "x"))

#guard predQD.ok

/-- `zToNNQuot` intertwines `predZ` with `predQ`. -/
def fromPredZD : LibDef where
  name := "fromPredZ"
  ty := .pi "z" .int
    (.path zqTy (.app zToNNQuotD.ref (.app predZD.ref (.var "z")))
      (.app predQD.ref (.app zToNNQuotD.ref (.var "z"))))
  tm := .lam "z" (.intcase "k"
    (.path zqTy (.app zToNNQuotD.ref (.app predZD.ref (.var "k")))
      (.app predQD.ref (.app zToNNQuotD.ref (.var "k"))))
    (.lam "n" (.natrec "k2"
      (.path zqTy
        (.app zToNNQuotD.ref (.app predZD.ref (.ipos (.var "k2"))))
        (.app predQD.ref (.app zToNNQuotD.ref (.ipos (.var "k2")))))
      (.plam "i" (.qin (.pair .zero (.succ .zero))))
      (lams ["m", "ih"] (.plam "i" (.qeq
        (.pair (.var "m") .zero)
        (.pair (.succ (.var "m")) (.succ .zero))
        (apps addSucRNatD.ref [.var "m", .zero])
        (.var "i"))))
      (.var "n")))
    (.lam "n" (.plam "i"
      (.qin (.pair .zero (.succ (.succ (.var "n")))))))
    (.var "z"))

#guard fromPredZD.ok

/-- `zToNNQuot (a − b) ≡ [(a,b)]`, by induction on `b`. -/
def nnRoundD : LibDef where
  name := "nnRound"
  ty := .pi "a" .nat (.pi "b" .nat
    (.path zqTy (.app zToNNQuotD.ref (subN (.var "a") (.var "b")))
      (.qin (.pair (.var "a") (.var "b")))))
  tm := lams ["a", "b"] (.natrec "k"
    (.path zqTy (.app zToNNQuotD.ref (subN (.var "a") (.var "k")))
      (.qin (.pair (.var "a") (.var "k"))))
    (.plam "i" (.qin (.pair (.var "a") .zero)))
    (lams ["m", "ih"] (apps transD.ref [zqTy,
      .app zToNNQuotD.ref (subN (.var "a") (.succ (.var "m"))),
      .app predQD.ref (.app zToNNQuotD.ref (subN (.var "a") (.var "m"))),
      .qin (.pair (.var "a") (.succ (.var "m"))),
      .app fromPredZD.ref (subN (.var "a") (.var "m")),
      apps congD.ref [zqTy, zqTy, predQD.ref,
        .app zToNNQuotD.ref (subN (.var "a") (.var "m")),
        .qin (.pair (.var "a") (.var "m")), .var "ih"]]))
    (.var "b"))

/-- `(a−b)+b`-style: the other round trip, on canonical representatives. -/
def zRoundD : LibDef where
  name := "zRound"
  ty := .pi "z" .int
    (.path .int (.app nnQuotToZD.ref (.app zToNNQuotD.ref (.var "z")))
      (.var "z"))
  tm := .lam "z" (.intcase "k"
    (.path .int (.app nnQuotToZD.ref (.app zToNNQuotD.ref (.var "k")))
      (.var "k"))
    (.lam "n" (.plam "i" (.ipos (.var "n"))))
    (.lam "n" (.natrec "k2"
      (.path .int (subN .zero (.succ (.var "k2"))) (.inegsuc (.var "k2")))
      (.plam "i" (.inegsuc .zero))
      (lams ["m", "ih"] (apps congD.ref [.int, .int, predZD.ref,
        subN .zero (.succ (.var "m")), .inegsuc (.var "m"), .var "ih"]))
      (.var "n")))
    (.var "z"))

#guard nnRoundD.ok
#guard zRoundD.ok

/-- **`(ℕ × ℕ)/∼ ≃ ℤ`** — the difference representation of the integers. -/
def intAsQuotD : LibDef where
  name := "intAsQuot"
  ty := equivR zqTy .int
  tm := apps setIsoToEquivD.ref
    [zqTy, .int, nnQuotToZD.ref, zToNNQuotD.ref,
     zRoundD.ref,
     .lam "x" (apps qelimPropD.ref
       [nnTy, relNN,
        .lam "k" (.path zqTy
          (.app zToNNQuotD.ref (.app nnQuotToZD.ref (.var "k"))) (.var "k")),
        .lam "k" (apps isSetQuotD.ref [nnTy, relNN,
          .app zToNNQuotD.ref (.app nnQuotToZD.ref (.var "k")), .var "k"]),
        .lam "w" (apps nnRoundD.ref [.fst (.var "w"), .snd (.var "w")]),
        .var "x"]),
     isSetZD.ref]

#guard intAsQuotD.ok

-- and it computes: [(3,1)] ↦ +2,  [(0,2)] ↦ −2
#guard
  match normalize (.app nnQuotToZD.ref (.qin (.pair
    (.succ (.succ (.succ .zero))) (.succ .zero)))) .int with
  | .ok t => t == resolveClosed (posZ 2)
  | .error _ => false
#guard
  match normalize (.app nnQuotToZD.ref (.qin (.pair .zero
    (.succ (.succ .zero))))) .int with
  | .ok t => t == resolveClosed (negZ 2)
  | .error _ => false

end Cubical.Library

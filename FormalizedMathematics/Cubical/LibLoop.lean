import FormalizedMathematics.Cubical.LibGroupoid

namespace Cubical.Library

open Raw

/-! ## Towards the quantified `π₁(S¹) ≅ ℤ`: the decode square -/

/-! ## `intLoop`: decode at the base point -/

private def loopT : Raw := .plam "li" (.sloop (.var "li"))
private def loopInvT : Raw := .plam "li" (.sloop (.ineg (.var "li")))
private def pathS1 : Raw := .path .s1 .sbase .sbase
private def compS1 (p q : Raw) : Raw :=
  apps transD.ref [.s1, .sbase, .sbase, .sbase, p, q]

/-- `intLoop (pos n) = loopⁿ`, `intLoop (negsuc n) = (loop⁻¹)ⁿ⁺¹`. -/
def intLoopD : LibDef where
  name := "intLoop"
  ty := .arr .int pathS1
  tm := .lam "z" (.intcase "k" pathS1
    (.lam "n" (.natrec "k2" pathS1
      (.plam "i0" .sbase)
      (lams ["m", "ih"] (compS1 (.var "ih") loopT))
      (.var "n")))
    (.lam "n" (.natrec "k2" pathS1
      (compS1 (.plam "i0" .sbase) loopInvT)
      (lams ["m", "ih"] (compS1 (.var "ih") loopInvT))
      (.var "n")))
    (.var "z"))

#guard intLoopD.ok



/-! ## Level-1 path algebra

The core lemmas restated one universe up (`A : U₁`), needed to reason about
paths *between types* — e.g. `cong helix p : Path U₁?? — no: a path in `U₀`
viewed inside the ambient `U₁`.  Mixed-level `cong` and `J` follow. -/

def refl1D : LibDef where
  name := "refl@1"
  ty := .pi "A" (.univN 1) (.pi "a" (.var "A")
    (.path (.var "A") (.var "a") (.var "a")))
  tm := reflD.tm

def symm1D : LibDef where
  name := "symm@1"
  ty := .pi "A" (.univN 1) (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.path (.var "A") (.var "b") (.var "a")))))
  tm := symmD.tm

def trans1D : LibDef where
  name := "trans@1"
  ty := .pi "A" (.univN 1) (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "c" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.arr (.path (.var "A") (.var "b") (.var "c"))
        (.path (.var "A") (.var "a") (.var "c")))))))
  tm := transD.tm

def transReflR1D : LibDef where
  name := "transReflR@1"
  ty := .pi "A" (.univN 1) (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (apps trans1D.ref [.var "A", .var "a", .var "b", .var "b", .var "p",
          apps refl1D.ref [.var "A", .var "b"]])
        (.var "p")))))
  tm := transReflRD.tm

/-- `cong` from a level-0 domain into a level-1 codomain (e.g. `f = helix`). -/
def cong01D : LibDef where
  name := "cong@01"
  ty := .pi "A" .univ (.pi "B" (.univN 1) (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
      (.arr (.path (.var "A") (.var "a") (.var "b"))
        (.path (.var "B") (.app (.var "f") (.var "a"))
          (.app (.var "f") (.var "b"))))))))
  tm := congD.tm

/-- `cong` from a level-1 domain into a level-0 codomain
(e.g. `f = λ R. transport R 0`). -/
def cong10D : LibDef where
  name := "cong@10"
  ty := .pi "A" (.univN 1) (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
      (.arr (.path (.var "A") (.var "a") (.var "b"))
        (.path (.var "B") (.app (.var "f") (.var "a"))
          (.app (.var "f") (.var "b"))))))))
  tm := congD.tm

/-- `J` over a level-0 type with a level-1 motive (for 2-path statements
about paths between types). -/
def j01D : LibDef where
  name := "J@01"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (.pi "P" (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y")) (.univN 1)))
    (.pi "d" (apps (.var "P") [.var "x", .plam "k" (.var "x")])
    (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
      (apps (.var "P") [.var "y", .var "p"]))))))
  tm := jD.tm

/-- `J` over a level-1 type (e.g. eliminating a path in the universe). -/
def j10D : LibDef where
  name := "J@10"
  ty := .pi "A" (.univN 1) (.pi "x" (.var "A")
    (.pi "P" (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y")) .univ))
    (.pi "d" (apps (.var "P") [.var "x", .plam "k" (.var "x")])
    (.pi "y" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
      (apps (.var "P") [.var "y", .var "p"]))))))
  tm := jD.tm

#guard refl1D.ok
#guard symm1D.ok
#guard trans1D.ok
#guard transReflR1D.ok
#guard cong01D.ok
#guard cong10D.ok
#guard j01D.ok
#guard j10D.ok

/-! ## Path algebra over the universe (unblocked by the constancy-check
optimization: this `J` application took 54 minutes before, 0.2s after) -/

private def fx : Raw := .app (.var "f") (.var "x")
private def fy : Raw := .app (.var "f") (.var "y")

/-- `cong f (p ⬝ q) ≡ cong f p ⬝ cong f q` (codomain one level up),
by `J`; the `refl` case is the right-unit square pushed through `cong`. -/
def congTrans01D : LibDef where
  name := "congTrans@01"
  ty := .pi "A" .univ (.pi "B" (.univN 1) (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "x" (.var "A") (.pi "y" (.var "A") (.pi "z" (.var "A")
    (.pi "p" (.path (.var "A") (.var "x") (.var "y"))
    (.pi "q" (.path (.var "A") (.var "y") (.var "z"))
      (.path (.path (.var "B") fx (.app (.var "f") (.var "z")))
        (apps cong01D.ref [.var "A", .var "B", .var "f", .var "x", .var "z",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z",
            .var "p", .var "q"]])
        (apps trans1D.ref [.var "B", fx, fy, .app (.var "f") (.var "z"),
          apps cong01D.ref [.var "A", .var "B", .var "f", .var "x", .var "y",
            .var "p"],
          apps cong01D.ref [.var "A", .var "B", .var "f", .var "y", .var "z",
            .var "q"]])))))))))
  tm :=
    let congP := apps cong01D.ref
      [.var "A", .var "B", .var "f", .var "x", .var "y", .var "p"]
    let pRefl := apps transD.ref [.var "A", .var "x", .var "y", .var "y",
      .var "p", apps reflD.ref [.var "A", .var "y"]]
    let pathBxy : Raw := .path (.var "B") fx fy
    let x1 := apps cong01D.ref
      [.var "A", .var "B", .var "f", .var "x", .var "y", pRefl]
    let x3 := apps trans1D.ref [.var "B", fx, fy, fy, congP,
      apps cong01D.ref [.var "A", .var "B", .var "f", .var "y", .var "y",
        apps reflD.ref [.var "A", .var "y"]]]
    let leg1 := apps cong01D.ref
      [.path (.var "A") (.var "x") (.var "y"), pathBxy,
       .lam "r" (apps cong01D.ref
         [.var "A", .var "B", .var "f", .var "x", .var "y", .var "r"]),
       pRefl, .var "p",
       apps transReflRD.ref [.var "A", .var "x", .var "y", .var "p"]]
    let leg2 := apps symm1D.ref [pathBxy, x3, congP,
      apps transReflR1D.ref [.var "B", fx, fy, congP]]
    let dCase := apps trans1D.ref [pathBxy, x1, congP, x3, leg1, leg2]
    let motive := .lam "z2" (.lam "q2"
      (.path (.path (.var "B") fx (.app (.var "f") (.var "z2")))
        (apps cong01D.ref [.var "A", .var "B", .var "f", .var "x", .var "z2",
          apps transD.ref [.var "A", .var "x", .var "y", .var "z2",
            .var "p", .var "q2"]])
        (apps trans1D.ref [.var "B", fx, fy, .app (.var "f") (.var "z2"),
          congP,
          apps cong01D.ref [.var "A", .var "B", .var "f", .var "y", .var "z2",
            .var "q2"]])))
    lams ["A", "B", "f", "x", "y", "z", "p", "q"]
      (apps j01D.ref [.var "A", .var "y", motive, dCase, .var "z", .var "q"])

/-- `transport (P ⬝ Q) x ≡ transport Q (transport P x)`, by `J` on `Q`. -/
def transpTransD : LibDef where
  name := "transpTrans"
  ty := .pi "X" .univ (.pi "Y" .univ (.pi "Z" .univ
    (.pi "P" (.path .univ (.var "X") (.var "Y"))
    (.pi "Q" (.path .univ (.var "Y") (.var "Z"))
    (.pi "x" (.var "X")
      (.path (.var "Z")
        (apps transportD.ref [.var "X", .var "Z",
          apps trans1D.ref [.univ, .var "X", .var "Y", .var "Z",
            .var "P", .var "Q"],
          .var "x"])
        (apps transportD.ref [.var "Y", .var "Z", .var "Q",
          apps transportD.ref [.var "X", .var "Y", .var "P", .var "x"]])))))))
  tm :=
    let motive := .lam "Z2" (.lam "Q2"
      (.path (.var "Z2")
        (apps transportD.ref [.var "X", .var "Z2",
          apps trans1D.ref [.univ, .var "X", .var "Y", .var "Z2",
            .var "P", .var "Q2"],
          .var "x"])
        (apps transportD.ref [.var "Y", .var "Z2", .var "Q2",
          apps transportD.ref [.var "X", .var "Y", .var "P", .var "x"]])))
    let dCase := apps cong10D.ref
      [.path .univ (.var "X") (.var "Y"), .var "Y",
       .lam "R" (apps transportD.ref [.var "X", .var "Y", .var "R", .var "x"]),
       apps trans1D.ref [.univ, .var "X", .var "Y", .var "Y", .var "P",
         apps refl1D.ref [.univ, .var "Y"]],
       .var "P",
       apps transReflR1D.ref [.univ, .var "X", .var "Y", .var "P"]]
    lams ["X", "Y", "Z", "P", "Q", "x"]
      (apps j10D.ref [.univ, .var "Y", motive, dCase, .var "Z", .var "Q"])

#guard congTrans01D.ok
#guard transpTransD.ok

/-! ## The quantified round trip, `pos`/`negsuc` edition

The composite laws are still **`refl`** (the eliminator-commute + HCompU +
Glue-transport chain computes them judgementally, for the rebuilt
`sucEquiv` as well), so the induction closes with bare `cong` steps —
now via `intcase` + `natrec`. -/

/-- `winding (p ⬝ loop) ≡ sucZ (winding p)` — by `refl`. -/
def windingCompLoopD : LibDef where
  name := "windingCompLoop"
  ty := .pi "p" pathS1
    (.path .int
      (.app windingD.ref (compS1 (.var "p") loopT))
      (.app sucZD.ref (.app windingD.ref (.var "p"))))
  tm := .lam "p" (.plam "wi"
    (.app sucZD.ref (.app windingD.ref (.var "p"))))

/-- `winding (p ⬝ loop⁻¹) ≡ predZ (winding p)` — by `refl`. -/
def windingCompLoopInvD : LibDef where
  name := "windingCompLoopInv"
  ty := .pi "p" pathS1
    (.path .int
      (.app windingD.ref (compS1 (.var "p") loopInvT))
      (.app predZD.ref (.app windingD.ref (.var "p"))))
  tm := .lam "p" (.plam "wi"
    (.app predZD.ref (.app windingD.ref (.var "p"))))

/-- **`encode ∘ decode = id`, quantified over all of ℤ**:
`Π (z : ℤ). winding (intLoop z) ≡ z`, by case split and ℕ-induction. -/
def encodeDecodeD : LibDef where
  name := "encodeDecode"
  ty := .pi "z" .int
    (.path .int (.app windingD.ref (.app intLoopD.ref (.var "z"))) (.var "z"))
  tm :=
    let wil (k : Raw) : Raw := .app windingD.ref (.app intLoopD.ref k)
    .lam "z" (.intcase "k"
      (.path .int (wil (.var "k")) (.var "k"))
      (.lam "n" (.natrec "k2"
        (.path .int (wil (.ipos (.var "k2"))) (.ipos (.var "k2")))
        (.plam "zi" (.ipos .zero))
        (lams ["m", "ih"]
          (apps congD.ref [.int, .int, sucZD.ref,
            wil (.ipos (.var "m")), .ipos (.var "m"), .var "ih"]))
        (.var "n")))
      (.lam "n" (.natrec "k2"
        (.path .int (wil (.inegsuc (.var "k2"))) (.inegsuc (.var "k2")))
        (.plam "zi" (.inegsuc .zero))
        (lams ["m", "ih"]
          (apps congD.ref [.int, .int, predZD.ref,
            wil (.inegsuc (.var "m")), .inegsuc (.var "m"), .var "ih"]))
        (.var "n")))
      (.var "z"))

#guard windingCompLoopD.ok
#guard windingCompLoopInvD.ok
#guard encodeDecodeD.ok



/-! ## A4: the full `π₁(S¹) ≅ ℤ`

`decodeSquare` is the dependent square connecting `intLoop (pred z)` to
`intLoop z` over `λ i. base ≡ loop i`; `decode` extends `intLoop` over the
whole circle by ungluing and correcting with the cancellation *path*
(`cong intLoop (predSucZ y)`) — the price of substitution-stable ℤ;
`decodeEncode` is `J`; the two round trips assemble into an `Iso`. -/

/-- `PathP (λ i. base ≡ loop i) (intLoop (pred z)) (intLoop z)`. -/
def decodeSquareD : LibDef where
  name := "decodeSquare"
  ty := .pi "z" .int
    (.pathP "i" (.path .s1 .sbase (.sloop (.var "i")))
      (.app intLoopD.ref (.app predZD.ref (.var "z")))
      (.app intLoopD.ref (.var "z")))
  tm := .lam "z" (.intcase "k"
    (.pathP "i" (.path .s1 .sbase (.sloop (.var "i")))
      (.app intLoopD.ref (.app predZD.ref (.var "k")))
      (.app intLoopD.ref (.var "k")))
    (.lam "n" (.natrec "k2"
      (.pathP "i" (.path .s1 .sbase (.sloop (.var "i")))
        (.app intLoopD.ref (.app predZD.ref (.ipos (.var "k2"))))
        (.app intLoopD.ref (.ipos (.var "k2"))))
      -- pos 0: left edge refl ⬝ loop⁻¹, right edge refl
      (.plam "i" (.plam "j" (.hcomp "k3" .s1
        [([(.var "j", false)], .sbase),
         ([(.var "j", true)], .sloop (.imax (.ineg (.var "k3")) (.var "i"))),
         ([(.var "i", true)], .sbase)]
        .sbase)))
      -- pos (s m): the composition filler, lid intLoop (pos m) ⬝ loop
      (lams ["m", "ihn"] (.plam "i" (.plam "j" (.hcomp "k3" .s1
        [([(.var "j", false)], .sbase),
         ([(.var "j", true)], .sloop (.imin (.var "i") (.var "k3"))),
         ([(.var "i", false)],
           .papp (.app intLoopD.ref (.ipos (.var "m"))) .sbase .sbase
             (.var "j"))]
        (.papp (.app intLoopD.ref (.ipos (.var "m"))) .sbase .sbase
          (.var "j"))))))
      (.var "n")))
    -- negsuc n (uniformly): left edge q ⬝ loop⁻¹, right edge q
    (.lam "n" (.plam "i" (.plam "j" (.hcomp "k3" .s1
      [([(.var "j", false)], .sbase),
       ([(.var "j", true)], .sloop (.imax (.ineg (.var "k3")) (.var "i"))),
       ([(.var "i", true)],
         .papp (.app intLoopD.ref (.inegsuc (.var "n"))) .sbase .sbase
           (.var "j"))]
      (.papp (.app intLoopD.ref (.inegsuc (.var "n"))) .sbase .sbase
        (.var "j"))))))
    (.var "z"))

#guard decodeSquareD.ok

/-- `encode : Π (x : S¹). (base ≡ x) → helix x`. -/
def encodeD : LibDef where
  name := "encode"
  ty := .pi "x" .s1
    (.arr (.path .s1 .sbase (.var "x")) (.app helixD.ref (.var "x")))
  tm := lams ["x", "p"] (.transp "i"
    (.app helixD.ref (.papp (.var "p") .sbase (.var "x") (.var "i")))
    (.ipos .zero))

/-- **`decode : Π (x : S¹). helix x → (base ≡ x)`** — `intLoop` extended over
the circle.  The loop cell unglues, applies `decodeSquare`, and corrects the
`i = 0` face by the cancellation path. -/
def decodeD : LibDef where
  name := "decode"
  ty := .pi "x" .s1
    (.arr (.app helixD.ref (.var "x")) (.path .s1 .sbase (.var "x")))
  tm :=
    let u : Raw := .unglue (.app helixD.ref (.sloop (.var "i"))) (.var "y")
    let dsAt : Raw := .papp (.app decodeSquareD.ref u)
      (.app intLoopD.ref (.app predZD.ref u))
      (.app intLoopD.ref u)
      (.var "i")
    let corr : Raw := apps congD.ref [.int, .path .s1 .sbase .sbase,
      intLoopD.ref,
      .app predZD.ref (.app sucZD.ref (.var "y")), .var "y",
      .app predSucZD.ref (.var "y")]
    .lam "x" (.s1elim "x2"
      (.arr (.app helixD.ref (.var "x2")) (.path .s1 .sbase (.var "x2")))
      intLoopD.ref
      -- the loop cell: an hcomp at the *function* type, so that the tube
      -- binders `y` are introduced under the face restriction (their Glue
      -- type then collapses to ℤ)
      (.plam "i" (.hcomp "k3"
        (.arr (.app helixD.ref (.sloop (.var "i")))
          (.path .s1 .sbase (.sloop (.var "i"))))
        [([(.var "i", false)],
           .lam "y" (.papp corr
             (.app intLoopD.ref (.app predZD.ref (.app sucZD.ref (.var "y"))))
             (.app intLoopD.ref (.var "y"))
             (.var "k3"))),
         ([(.var "i", true)],
           .lam "y" (.app intLoopD.ref (.var "y")))]
        (.lam "y" dsAt)))
      (.var "x"))

#guard encodeD.ok
#guard decodeD.ok

/-- **`decode ∘ encode = id`, quantified over all points and loops** — by
`J`, the `refl` case being definitional. -/
def decodeEncodeD2 : LibDef where
  name := "decodeEncode"
  ty := .pi "x" .s1 (.pi "p" (.path .s1 .sbase (.var "x"))
    (.path (.path .s1 .sbase (.var "x"))
      (apps decodeD.ref [.var "x", apps encodeD.ref [.var "x", .var "p"]])
      (.var "p")))
  tm := lams ["x", "p"] (apps jD.ref [.s1, .sbase,
    lams ["x2", "p2"] (.path (.path .s1 .sbase (.var "x2"))
      (apps decodeD.ref [.var "x2", apps encodeD.ref [.var "x2", .var "p2"]])
      (.var "p2")),
    .plam "k3" (.plam "i0" .sbase),
    .var "x", .var "p"])

#guard decodeEncodeD2.ok

/-- Isomorphisms of types. -/
def isoTy (A B : Raw) : Raw :=
  .sigma "f" (.arr A B)
    (.sigma "g" (.arr B A)
      (.sigma "sect" (.pi "b" B
        (.path B (.app (.var "f") (.app (.var "g") (.var "b"))) (.var "b")))
        (.pi "a" A
          (.path A (.app (.var "g") (.app (.var "f") (.var "a"))) (.var "a")))))

/-- **THE THEOREM: `π₁(S¹) ≅ ℤ`** — winding and `intLoop` are mutually
inverse, both round trips quantified. -/
def pi1S1IsoIntD : LibDef where
  name := "pi1S1IsoInt"
  ty := isoTy (.path .s1 .sbase .sbase) .int
  tm := .pair windingD.ref (.pair intLoopD.ref
    (.pair encodeDecodeD.ref
      (.lam "a" (apps decodeEncodeD2.ref [.sbase, .var "a"]))))

#guard pi1S1IsoIntD.ok

/-! ## The circle is not a set

The first *negative* homotopy-theoretic result: `loop ≢ refl`.  If they
were equal, `cong winding` would give `pos 1 ≡ pos 0` in ℤ, and the ℤ-codes
turn that into an element of `⊥`. -/

private def reflS1 : Raw := .plam "i0" .sbase

/-- `loop ≡ refl → ⊥`. -/
def loopNeqReflD : LibDef where
  name := "loopNeqRefl"
  ty := .arr (.path pathS1 loopT reflS1) .empty
  tm := .lam "h" (apps encodeZD.ref [posZ 1, posZ 0,
    apps congD.ref [pathS1, .int, windingD.ref, loopT, reflS1, .var "h"]])

/-- Hence the circle is not a set. -/
def s1NotSetD : LibDef where
  name := "s1NotSet"
  ty := .arr (isSetR .s1) .empty
  tm := .lam "h" (.app loopNeqReflD.ref
    (apps (.var "h") [.sbase, .sbase, loopT, reflS1]))

#guard loopNeqReflD.ok
#guard s1NotSetD.ok

end Cubical.Library

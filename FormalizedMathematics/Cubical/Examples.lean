import FormalizedMathematics.Cubical.TypeCheck
import FormalizedMathematics.Cubical.Library

/-!
# The kernel at work

In Lean itself `funext` needs the quotient axiom machinery and `Eq.symm` a
`Prop`-valued eliminator; univalence is outright inconsistent.  In this
cubical kernel, `funext`, `symm` and `cong` are *programs* — they type-check
against their path-type specifications and *compute*.

All claims below are verified at build time by `#guard`.
-/

namespace Cubical.Examples

open Raw

private def ok? : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- Does `tm : ty` normalize to exactly `expect`? -/
private def nf? (tm ty : Raw) (expect : Term) : Bool :=
  match normalize tm ty with
  | .ok t => t == expect
  | .error _ => false

/-! ## Interval algebra sanity (free De Morgan algebra) -/

-- De Morgan law: ¬(i ∧ j) = ¬i ∨ ¬j
#guard IVal.equiv (.neg (.min (.var 0) (.var 1)))
  (.max (.neg (.var 0)) (.neg (.var 1)))
-- the interval is NOT Boolean: i ∧ ¬i ≠ 0 (no excluded middle on I)
#guard !IVal.equiv (.min (.var 0) (.neg (.var 0))) .zero
-- but absorption holds: i ∨ (i ∧ j) = i
#guard IVal.equiv (.max (.var 0) (.min (.var 0) (.var 1))) (.var 0)

/-! ## refl, symm, cong, funext, transport -/

/-- `refl : Π (A : U) (a : A), Path A a a  :=  λ A a, ⟨i⟩ a` -/
def reflTy : Raw := .pi "A" .univ (.pi "a" (.var "A")
  (.path (.var "A") (.var "a") (.var "a")))
def reflTm : Raw := .lam "A" (.lam "a" (.plam "i" (.var "a")))

#guard ok? (checkDef reflTm reflTy)

/-- `symm : Π A a b, Path A a b → Path A b a  :=  λ A a b p, ⟨i⟩ p @ ¬i`

In Lean, `Eq.symm` needs the `Eq` eliminator; here it is just De Morgan
reparametrization of the interval — and it computes. -/
def symmTy : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.path (.var "A") (.var "b") (.var "a")))))
def symmTm : Raw :=
  .lam "A" (.lam "a" (.lam "b" (.lam "p"
    (.plam "i" (.papp (.var "p") (.var "a") (.var "b") (.ineg (.var "i")))))))

#guard ok? (checkDef symmTm symmTy)

/-- `cong : Π A B (f : A → B) a b, Path A a b → Path B (f a) (f b)` -/
def congTy : Raw :=
  .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A")
      (.arr (.path (.var "A") (.var "a") (.var "b"))
        (.path (.var "B") (.app (.var "f") (.var "a"))
          (.app (.var "f") (.var "b"))))))))
def congTm : Raw :=
  .lam "A" (.lam "B" (.lam "f" (.lam "a" (.lam "b" (.lam "p"
    (.plam "i" (.app (.var "f")
      (.papp (.var "p") (.var "a") (.var "b") (.var "i")))))))))

#guard ok? (checkDef congTm congTy)

/-- **Function extensionality is a one-line program**:

`funext : Π A B (f g : A → B), (Π x, Path B (f x) (g x)) → Path (A→B) f g`
`       := λ A B f g h, ⟨i⟩ λ x, h x @ i`

The boundary conditions `(λ x, h x @ 0) ≡ f` and `(λ x, h x @ 1) ≡ g` are
checked by the kernel (they hold by the path boundary rules + η). -/
def funextTy : Raw :=
  .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "g" (.arr (.var "A") (.var "B"))
      (.arr
        (.pi "x" (.var "A") (.path (.var "B")
          (.app (.var "f") (.var "x")) (.app (.var "g") (.var "x"))))
        (.path (.arr (.var "A") (.var "B")) (.var "f") (.var "g"))))))
def funextTm : Raw :=
  .lam "A" (.lam "B" (.lam "f" (.lam "g" (.lam "h"
    (.plam "i" (.lam "x"
      (.papp (.app (.var "h") (.var "x"))
        (.app (.var "f") (.var "x")) (.app (.var "g") (.var "x"))
        (.var "i"))))))))

#guard ok? (checkDef funextTm funextTy)

/-- `transport : Π (A B : U), Path U A B → A → B  :=  λ A B p a, transp (p @ i) a`

Type checks because the path boundary rules compute `p @ 0 ≡ A`, `p @ 1 ≡ B`
even for a *variable* `p` — types are being transported along a path in the
universe, the computational heart of what univalence will provide. -/
def transportTy : Raw :=
  .pi "A" .univ (.pi "B" .univ
    (.arr (.path .univ (.var "A") (.var "B"))
      (.arr (.var "A") (.var "B"))))
def transportTm : Raw :=
  .lam "A" (.lam "B" (.lam "p" (.lam "a"
    (.transp "i" (.papp (.var "p") (.var "A") (.var "B") (.var "i")) (.var "a")))))

#guard ok? (checkDef transportTm transportTy)

/-! ## Computation -/

-- transp along a constant family is the identity: `transp (λ i, ℕ) 0 ⟶ 0`
#guard nf? (.transp "i" .nat .zero) .nat .zero

-- funext COMPUTES: (funext ℕ ℕ succ succ (λ x, refl) @ 0) ⟶ λ x, succ x
def sucF : Raw := .lam "x" (.succ (.var "x"))
def funextApplied : Raw :=
  .papp
    (.app (.app (.app (.app (.app (.ann funextTm funextTy) .nat) .nat) sucF) sucF)
      (.lam "x" (.plam "j" (.succ (.var "x")))))
    sucF sucF .i0
#guard nf? funextApplied (.arr .nat .nat) (.lam (.succ (.var 0)))

-- symm computes: (symm ℕ 0 0 refl) @ i ⟶ ⟨i⟩ 0
#guard nf?
  (.app (.app (.app (.app (.ann symmTm symmTy) .nat) .zero) .zero) (.plam "j" .zero))
  (.path .nat .zero .zero) (.plam .zero)

/-- The Kan Π-rule at work on a family that genuinely varies: transporting a
function along a line of *domains* inserts the backward fill on the argument.
`λ p f, transp (λ i, (p@i) → ℕ) f  ⟶  λ p f x, f (transp (λ j, p@¬j) x)` -/
def transpPiDemo : Raw :=
  .lam "p" (.lam "f"
    (.transp "i" (.arr (.papp (.var "p") .nat .nat (.var "i")) .nat) (.var "f")))
def transpPiDemoTy : Raw :=
  .pi "p" (.path .univ .nat .nat)
    (.arr (.arr .nat .nat) (.arr .nat .nat))

#guard ok? (checkDef transpPiDemo transpPiDemoTy)

/-! ## Phase 2a: homogeneous composition (`hcomp`) and path composition -/

/-- **Path composition (transitivity)** — impossible with `plam`/`papp` alone,
this is what `hcomp` is *for*:

`trans := λ A a b c p q, ⟨i⟩ hcomp {A} [(i=0) ↦ (λ j, a), (i=1) ↦ (λ j, q @ j)] (p @ i)`

Geometrically: the square with `p` at the bottom, `a` on the left wall,
`q` on the right wall, composed to its lid. -/
def transTy : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A") (.pi "c" (.var "A")
    (.arr (.path (.var "A") (.var "a") (.var "b"))
      (.arr (.path (.var "A") (.var "b") (.var "c"))
        (.path (.var "A") (.var "a") (.var "c")))))))
def transTm : Raw :=
  .lam "A" (.lam "a" (.lam "b" (.lam "c" (.lam "p" (.lam "q"
    (.plam "i"
      (.hcomp "j" (.var "A")
        [([(.var "i", false)], .var "a"),
         ([(.var "i", true)],
           .papp (.var "q") (.var "b") (.var "c") (.var "j"))]
        (.papp (.var "p") (.var "a") (.var "b") (.var "i")))))))))

#guard ok? (checkDef transTm transTy)

-- trans COMPUTES on ℕ: refl ⬝ refl ⟶ refl (the ℕ-hcomp rule fires)
def transApplied : Raw :=
  .app (.app (.app (.app (.app (.app (.ann transTm transTy)
    .nat) .zero) .zero) .zero) (.plam "k" .zero)) (.plam "k" .zero)
#guard nf? transApplied (.path .nat .zero .zero) (.plam .zero)

-- hcomp computes structurally on Σ-types (via the filler + heterogeneous comp)
#guard nf? (.hcomp "i" (.sigma "x" .nat .nat) [] (.pair .zero .zero))
  (.sigma "x" .nat .nat) (.pair .zero .zero)

/-- `transp` on a `PathP`-family (stuck in v0, computes in 2a): transporting
`refl` along the family `λ i, Path ℕ (q@i) (q@i)` for an abstract `q`. -/
def transpPathPDemo : Raw :=
  .lam "q"
    (.transp "i"
      (.path .nat (.papp (.var "q") .zero .zero (.var "i"))
        (.papp (.var "q") .zero .zero (.var "i")))
      (.plam "j" .zero))
def transpPathPDemoTy : Raw :=
  .arr (.path .nat .zero .zero) (.path .nat .zero .zero)

#guard ok? (checkDef transpPathPDemo transpPathPDemoTy)

-- ... and when `q` is in fact refl, the whole composite COMPUTES to refl:
#guard nf? (.app (.ann transpPathPDemo transpPathPDemoTy) (.plam "k" .zero))
  (.path .nat .zero .zero) (.plam .zero)

/-! ## Phase 2b: Glue types and computing univalence -/

/-- `isContr C := Σ (c : C), Π (c' : C), Path C c c'` -/
def isContrR (C : Raw) : Raw :=
  .sigma "ctr" C (.pi "other" C (.path C (.var "ctr") (.var "other")))

/-- `fiber f y := Σ (x : A), Path B y (f x)` -/
def fiberR (A B f y : Raw) : Raw :=
  .sigma "x" A (.path B y (.app f (.var "x")))

/-- `Equiv A B := Σ (f : A → B), Π (y : B), isContr (fiber f y)` —
the contractible-fibers formulation the kernel's `Glue` rules consume. -/
def equivR (A B : Raw) : Raw :=
  .sigma "f" (.arr A B)
    (.pi "y" B (isContrR (fiberR A B (.var "f") (.var "y"))))

/-- The identity equivalence.  The fiber of `id` over `a` is the singleton
`Σ x, Path A a x`, contracted by the De Morgan connection `p @ (i ∧ j)` —
this is where 2a's interval algebra earns its keep.  (The term does not
mention the type, but we keep the parameter for readability at use sites.) -/
def idEquivR (_A : Raw) : Raw :=
  .pair (.lam "x" (.var "x"))
    (.lam "a" (.pair
      (.pair (.var "a") (.plam "k" (.var "a")))
      (.lam "fib" (.plam "i" (.pair
        (.papp (.snd (.var "fib")) (.var "a") (.fst (.var "fib")) (.var "i"))
        (.plam "j"
          (.papp (.snd (.var "fib")) (.var "a") (.fst (.var "fib"))
            (.imin (.var "i") (.var "j")))))))))

#guard ok? (checkDef (idEquivR .nat) (equivR .nat .nat))

/-- **Univalence, the map**: an equivalence becomes a path in the universe.

`ua := λ A B e, ⟨i⟩ Glue [(i=0) ↦ (A, e), (i=1) ↦ (B, idEquiv B)] B`

The path boundary conditions hold *definitionally*: on `i=0` the face of the
first branch is true and the `Glue` collapses to `A`; on `i=1` to `B`. -/
def uaTy : Raw :=
  .pi "A" .univ (.pi "B" .univ
    (.arr (equivR (.var "A") (.var "B"))
      (.path .univ (.var "A") (.var "B"))))
def uaTm : Raw :=
  .lam "A" (.lam "B" (.lam "e" (.plam "i"
    (.glueTy
      [([(.var "i", false)], .var "A", .var "e"),
       ([(.var "i", true)], .var "B",
         .ann (idEquivR (.var "B")) (equivR (.var "B") (.var "B")))]
      (.var "B")))))

#guard ok? (checkDef uaTm uaTy)

-- ua e is a genuine path: its endpoints compute to A and B
def uaIdNat : Raw :=
  .app (.app (.app (.ann uaTm uaTy) .nat) .nat)
    (.ann (idEquivR .nat) (equivR .nat .nat))
#guard nf? (.papp uaIdNat .nat .nat .i0) .univ .nat
#guard nf? (.papp uaIdNat .nat .nat .i1) .univ .nat

-- **transport along ua computes**: transp (ua (idEquiv ℕ)) 0 ⟶ 0
#guard nf? (.transp "i" (.papp uaIdNat .nat .nat (.var "i")) .zero) .nat .zero

/-- **The computation rule of univalence**, for an *abstract* equivalence:
`λ e, transport (ua e) 0` normalizes to `λ e, e.fst 0` — transporting along
`ua e` *is* applying the equivalence.  In book HoTT this is an axiom with no
computational content; here it is a definitional equality produced by the
`Glue` transport rule. -/
def transportUaE : Raw :=
  .lam "e"
    (.transp "i"
      (.papp (.app (.app (.app (.ann uaTm uaTy) .nat) .nat) (.var "e"))
        .nat .nat (.var "i"))
      .zero)
def transportUaETy : Raw := .pi "e" (equivR .nat .nat) .nat

#guard nf? transportUaE transportUaETy (.lam (.app (.fst (.var 0)) .zero))

-- Glue soundness: a bare function is not an equivalence — rejected
#guard !ok? (checkDef
  (.plam "i" (.glueTy [([(.var "i", false)], .nat, sucF)] .nat))
  (.path .univ .nat .nat))

/-! ## Phase 2d: the circle S¹, the integers, and winding numbers

The classical first computation of synthetic homotopy theory:
`π₁(S¹) ≅ ℤ`, computed by transporting in the "helix" family
`helix := S¹-elim U ℤ (ua sucEquiv)` — the universal cover of the circle,
whose monodromy around `loop` is the successor equivalence. -/

/-- The successor equivalence `ℤ ≃ ℤ`.  Because `isuc`/`ipred` cancel
*strictly* in this kernel, its fibers are literally singletons and the same
connection trick as `idEquivR` contracts them. -/
def sucEquivR : Raw := Library.sucEquivD.tm

#guard ok? (checkDef sucEquivR (equivR .int .int))

-- the circle eliminator computes on the point constructor
#guard nf? (.s1elim "x" .nat .zero (.plam "k" .zero) .sbase) .nat .zero

/-- `winding p := transp (λ i, helix (p @ i)) 0` -/
def windingR : Raw := Library.windingD.tm
def windingTy : Raw := .arr (.path .s1 .sbase .sbase) .int

#guard ok? (checkDef windingR windingTy)

def loopR : Raw := .plam "i" (.sloop (.var "i"))
def loopInvR : Raw := .plam "i" (.sloop (.ineg (.var "i")))

-- **π₁(S¹) winding numbers COMPUTE**:
--   winding loop  ⟶  +1        winding loop⁻¹  ⟶  -1
#guard nf? (.app (.ann windingR windingTy) loopR) .int ((.ipos (.succ .zero)))
#guard nf? (.app (.ann windingR windingTy) loopInvR) .int ((.inegsuc .zero))

-- refl winds zero times
#guard nf? (.app (.ann windingR windingTy) (.plam "i" .sbase)) .int (.ipos .zero)

/-! ## Phase 2b': HCompU and the general Glue transport

`hcomp` at the universe is a `Glue` along the branch lines, glued by
`lineEquiv` — "transport along a line is an equivalence" — a closed
object-language program the kernel evaluates (and which the checker itself
verifies below).  Together with the general `∀i.φ` Glue transport this makes
winding numbers of *composite* loops compute. -/

-- the kernel-trusted `lineEquiv` program is itself well-typed
#guard ok? (checkDef lineEquivRaw
  (.pi "X" .univ (.pi "Y" .univ
    (.arr (.path .univ (.var "X") (.var "Y"))
      (equivR (.var "Y") (.var "X"))))))

/-- The composite `loop ⬝ loop` (an `hcomp` cell on S¹). -/
def loop2R : Raw :=
  .plam "i" (.hcomp "j" .s1
    [([(.var "i", false)], .sbase),
     ([(.var "i", true)], .sloop (.var "j"))]
    (.sloop (.var "i")))

#guard ok? (checkDef loop2R (.path .s1 .sbase .sbase))

-- **winding of composite loops COMPUTES** (needs HCompU + general transpGlue):
--   winding (loop ⬝ loop)   ⟶  +2
#guard nf? (.app (.ann windingR windingTy) loop2R) .int ((.ipos (.succ (.succ .zero))))

-- composing with the inverse cancels: winding (loop ⬝ loop⁻¹) ⟶ 0
def loopLoopInvR : Raw :=
  .plam "i" (.hcomp "j" .s1
    [([(.var "i", false)], .sbase),
     ([(.var "i", true)], .sloop (.ineg (.var "j")))]
    (.sloop (.var "i")))
#guard nf? (.app (.ann windingR windingTy) loopLoopInvR) .int (.ipos .zero)

-- and the same composite built with the generic `trans` program
def transLoopLoop : Raw :=
  .app (.app (.app (.app (.app (.app (.ann transTm transTy)
    .s1) .sbase) .sbase) .sbase) loopR) loopR
#guard nf? (.app (.ann windingR windingTy) transLoopLoop) .int
  ((.ipos (.succ (.succ .zero))))

/-! ## Phase 2c: the universe hierarchy

`univ n : univ (n+1)` with subsumption `univ m ≤ univ n` (m ≤ n) at the
checking judgement.  In particular **type-in-type is gone**: `U₀ : U₀` is
rejected, closing the Girard-paradox door of the earlier prototype. -/

-- U₀ : U₁, and U₀ : U₅ by cumulativity
#guard ok? (check [] [] (.univ 0) (.vuniv 1))
#guard ok? (check [] [] (.univ 0) (.vuniv 5))
-- but NOT U₀ : U₀ (no type-in-type), and not downwards
#guard !ok? (check [] [] (.univ 0) (.vuniv 0))
#guard !ok? (check [] [] (.univ 3) (.vuniv 2))
-- levels propagate through formers: Π (A : U₀), A → A lives in U₁, not U₀
#guard ok? (check [] [] (.pi (.univ 0) (.pi (.var 0) (.var 1))) (.vuniv 1))
#guard !ok? (check [] [] (.pi (.univ 0) (.pi (.var 0) (.var 1))) (.vuniv 0))
-- Path U₀ A B lives in U₁
#guard ok? (check [] [] (.pathP (.univ 0) .nat .int) (.vuniv 1))
#guard !ok? (check [] [] (.pathP (.univ 0) .nat .int) (.vuniv 0))

/-! ## encode–decode: `intLoop` (decode at `base`) and the round trip

`decode base := intLoop : ℤ → Path S¹ base base`, `loopⁿ` by ℤ-recursion
(the eliminator `intrec` is well-defined because ℤ values are kept in
`isuc`/`ipred`-cancelled canonical form).  The composite
`encode ∘ decode = winding ∘ intLoop` is verified *by computation* on
concrete integers.  The universally quantified isomorphism
`π₁(S¹) ≅ ℤ` (decodeSquare, `toPathP`, J-machinery in the object language)
remains future work — see the README roadmap. -/

def pathS1 : Raw := .path .s1 .sbase .sbase

def compS1 (p q : Raw) : Raw :=
  .app (.app (.app (.app (.app (.app (.ann transTm transTy)
    .s1) .sbase) .sbase) .sbase) p) q

/-- `intLoop n = loopⁿ`: 0 ↦ refl, n+1 ↦ intLoop n ⬝ loop, n−1 ↦ intLoop n ⬝ loop⁻¹. -/
def intLoopR : Raw := Library.intLoopD.tm
def intLoopTy : Raw := .arr .int pathS1

#guard ok? (checkDef intLoopR intLoopTy)

-- intrec computes: intLoop 0 ⟶ refl
#guard nf? (.app (.ann intLoopR intLoopTy) (.ipos .zero)) pathS1 (.plam .sbase)

-- **the round trip computes**: winding (intLoop n) ⟶ n
#guard nf? (.app (.ann windingR windingTy)
    (.app (.ann intLoopR intLoopTy) ((.ipos (.succ (.succ .zero))))))
  .int ((.ipos (.succ (.succ .zero))))
#guard nf? (.app (.ann windingR windingTy)
    (.app (.ann intLoopR intLoopTy) ((.inegsuc .zero))))
  .int ((.inegsuc .zero))

/-! ## Soundness: hcomp side conditions are enforced -/

-- base/tube adjacency violation: tube (λ j, 1) does not meet base 0 at j=0
#guard !ok? (checkDef
  (.plam "i" (.hcomp "j" .nat [([(.var "i", false)], .succ .zero)] .zero))
  (.path .nat .zero .zero))

-- incompatible overlapping branches are rejected: both tubes agree with the
-- base at j=0, but on the overlap (i=0)∧(i'=0) the tubes `λ j, r @ j` and
-- `λ j, 0` disagree for an abstract `r : Path ℕ 0 0`
#guard !ok? (checkDef
  (.lam "r" (.plam "i" (.plam "i'"
    (.hcomp "j" .nat
      [([(.var "i", false)], .papp (.var "r") .zero .zero (.var "j")),
       ([(.var "i'", false)], .zero)]
      .zero))))
  (.arr (.path .nat .zero .zero)
    (.path (.path .nat .zero .zero) (.plam "k" .zero) (.plam "k" .zero))))

-- since the DNF face generalization (2026-07-13), arbitrary interval
-- expressions are legal faces: `(i∧i = 0)` normalizes to `(i = 0)` and the
-- branch checks — this is now a POSITIVE test
#guard ok? (checkDef
  (.plam "i" (.hcomp "j" .nat [([(.imin (.var "i") (.var "i"), false)], .zero)] .zero))
  (.path .nat .zero .zero))
-- but a face constraining a term-level (non-interval) variable is rejected
#guard !ok? (checkDef
  (.lam "n" (.plam "i" (.hcomp "j" .nat [([(.var "n", false)], .zero)] .zero)))
  (.arr .nat (.path .nat .zero .zero)))

/-! ## Soundness: ill-typed programs are rejected -/

-- wrong boundary: ⟨i⟩ 0 is NOT a path from 0 to 1
#guard !ok? (checkDef (.plam "i" .zero) (.path .nat .zero (.succ .zero)))

-- interval variables are not terms
#guard !ok? (checkDef (.plam "i" (.var "i")) (.path .nat .zero .zero))

-- lying endpoint annotations on papp are caught
#guard !ok? (checkDef
  (.lam "p" (.papp (.var "p") (.succ .zero) .zero .i0))
  (.arr (.path .nat .zero .zero) .nat))

/-! ## Show some normal forms at build time -/

def transpPiApplied : Raw :=
  .app (.app (.ann transpPiDemo transpPiDemoTy) (.plam "j" .nat)) sucF

#eval do
  let fx := normalize funextApplied (.arr .nat .nat)
  let px := normalize transpPiApplied (.arr .nat .nat)
  let tx := normalize transApplied (.path .nat .zero .zero)
  let ux := normalize transportUaE transportUaETy
  let wPos := normalize (.app (.ann windingR windingTy) loopR) .int
  let wNeg := normalize (.app (.ann windingR windingTy) loopInvR) .int
  let w2 := normalize (.app (.ann windingR windingTy) loop2R) .int
  IO.println "cubical kernel (phase 2c + encode–decode) — all #guard tests passed at elaboration time"
  IO.println "universes: U n : U (n+1), no type-in-type; winding (intLoop n) ⟶ n for n = +2, −1, 0"
  IO.println s!"funext example nf:          {repr fx}"
  IO.println s!"transp Π-rule nf:           {repr px}"
  IO.println s!"trans refl refl nf:         {repr tx}"
  IO.println s!"λ e, transport (ua e) 0 nf: {repr ux}"
  IO.println s!"winding loop nf:            {repr wPos}"
  IO.println s!"winding loop⁻¹ nf:          {repr wNeg}"
  IO.println s!"winding (loop ⬝ loop) nf:   {repr w2}"

end Cubical.Examples
-- perf-check rebuild marker

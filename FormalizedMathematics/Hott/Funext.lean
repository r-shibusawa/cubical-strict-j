import FormalizedMathematics.Hott.Univalence

/-!
# Voevodsky's theorem: univalence implies function extensionality

This is Theorem 4.9.5 of the HoTT book, formalized fully and *axiom-free*
(univalence is a hypothesis, not an `axiom`; check with
`#print axioms Hott.funextOfUnivalence`).

The proof pipeline:
1. For any *path* `p : Path A B` of types, post-composition with
   `idtoeqv p` has contractible fibers (by path induction, the fibers become
   singleton path spaces).  Univalence upgrades this from paths to arbitrary
   equivalences (`fiberPostcompContr`).
2. *Weak funext*: a product of contractible types is contractible
   (`weakFunext`).  Given pointwise contractible `P`, the projection
   `(Σ x, P x) → A` is an equivalence, so by (1) the fiber over `id` of
   post-composition with it is contractible, and `∀ x, P x` is a definitional
   retract of that fiber.
3. *Funext* (`funext`): the total space `Σ g, ∀ x, Path (f x) (g x)` is a
   definitional retract of `∀ x, Σ y, Path (f x) y`, which is contractible by
   weak funext; connecting `⟨f, refl⟩` and `⟨g, H⟩` through the center and
   projecting to the first component yields `Path f g`.
-/

namespace Hott

universe u

/-- Step 1a: along a *path* of types, post-composition fibers are singletons. -/
def fiberPostcompPathContr {X A B : Type u} (p : Path A B) (k : X → B) :
    Contr (Σ γ : X → A, Path (fun x => (idtoeqv p).map (γ x)) k) :=
  match B, p with
  | _, .refl => singletonContr' k

/-- Step 1b: univalence transports Step 1a to an arbitrary equivalence `e`. -/
def fiberPostcompContr (uni : Univalence.{u}) {X A B : Type u}
    (e : Equiv A B) (k : X → B) :
    Contr (Σ γ : X → A, Path (fun x => e.map (γ x)) k) :=
  Path.transport
    (fun m : A → B => Contr (Σ γ : X → A, Path (fun x => m (γ x)) k))
    (Path.ap Equiv.map (uni.uaBeta e))
    (fiberPostcompPathContr (uni.ua e) k)

/-- The projection of a pointwise-contractible family is an equivalence. -/
def projEquiv {A : Type u} {P : A → Type u} (c : (x : A) → Contr (P x)) :
    Equiv (Σ x : A, P x) A where
  map := Sigma.fst
  isEquiv :=
    { inv := fun x => ⟨x, (c x).center⟩
      rightInv := fun _ => .refl
      leftInv := fun w => Path.ap (Sigma.mk w.1) ((c w.1).contr w.2) }

/-- Step 2 (weak funext): a product of contractible types is contractible. -/
def weakFunext (uni : Univalence.{u}) {A : Type u} {P : A → Type u}
    (c : (x : A) → Contr (P x)) : Contr ((x : A) → P x) :=
  Contr.retract
    (fun w => fun x => Path.transport P (happly w.2 x) (w.1 x).2)
    (fun f => ⟨fun x => ⟨x, f x⟩, .refl⟩)
    (fun _ => .refl)
    (fiberPostcompContr uni (projEquiv c) (fun x => x))

/-- **Voevodsky's theorem**: univalence implies function extensionality,
for dependent functions. -/
def funextOfUnivalence (uni : Univalence.{u}) {A : Type u} {P : A → Type u}
    {f g : (x : A) → P x} (H : (x : A) → Path (f x) (g x)) : Path f g :=
  let cT : Contr (Σ g' : (x : A) → P x, (x : A) → Path (f x) (g' x)) :=
    Contr.retract
      (fun c => ⟨fun x => (c x).1, fun x => (c x).2⟩)
      (fun w => fun x => ⟨w.1 x, w.2 x⟩)
      (fun _ => .refl)
      (weakFunext uni (fun x => singletonContr (f x)))
  Path.ap Sigma.fst ((cT.contr ⟨f, fun _ => .refl⟩).symm.trans (cT.contr ⟨g, H⟩))

end Hott

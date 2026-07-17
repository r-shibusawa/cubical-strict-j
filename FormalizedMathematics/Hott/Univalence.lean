import FormalizedMathematics.Hott.Basic

/-!
# Equivalences and the univalence axiom

We package equivalences via quasi-inverses (sufficient here, since we only
ever *construct* equivalences and transport along paths between their
underlying maps; we never need `IsEquiv` to be a proposition).

Univalence cannot be postulated as a global `axiom` for Lean's `Eq`
(proof irrelevance refutes it), and even for our `Type`-valued `Path` a
global axiom would still be refutable using `Eq`-reasoning from outside the
fragment.  We therefore state univalence as a *structure* (`Univalence`) and
prove theorems `Univalence → ...`, which keeps every result axiom-free:
the implication itself is the mathematical content.
-/

namespace Hott

universe u v

/-- Quasi-inverse data for `f`. -/
structure IsEquiv {A : Type u} {B : Type v} (f : A → B) : Type (max u v) where
  inv : B → A
  rightInv : (b : B) → Path (f (inv b)) b
  leftInv : (a : A) → Path (inv (f a)) a

/-- An equivalence of types (in a single universe, as univalence requires). -/
structure Equiv (A B : Type u) : Type u where
  map : A → B
  isEquiv : IsEquiv map

/-- The identity equivalence. -/
def Equiv.rfl (A : Type u) : Equiv A A where
  map := fun a => a
  isEquiv := ⟨fun a => a, fun _ => .refl, fun _ => .refl⟩

/-- Every path between types induces an equivalence. -/
def idtoeqv {A B : Type u} : Path A B → Equiv A B
  | .refl => Equiv.rfl A

/-- The univalence "axiom", packaged as a hypothesis: `idtoeqv` has a section.
`uaBeta` is the computation rule; together they say every equivalence is of
the form `idtoeqv p`, which is all the funext proof needs. -/
structure Univalence : Type (u + 1) where
  ua : {A B : Type u} → Equiv A B → Path A B
  uaBeta : {A B : Type u} → (e : Equiv A B) → Path (idtoeqv (ua e)) e

end Hott

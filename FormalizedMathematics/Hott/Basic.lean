/-!
# HoTT core: Type-valued path types

Lean 4's built-in equality `Eq` lives in `Prop` and enjoys definitional proof
irrelevance, which is *inconsistent* with the univalence axiom.  To do homotopy
type theory inside Lean we therefore introduce our own identity type `Path`
living in `Type`, and use *only* its induction principle (J).  No `Eq`-based
reasoning is ever imported into this fragment (doing so would let one prove
UIP for `Path` and destroy the homotopical interpretation).
-/

namespace Hott

universe u v w

/-- The identity type ("path type") of HoTT, valued in `Type`, not `Prop`. -/
inductive Path {A : Type u} (a : A) : A → Type u
  | refl : Path a a

namespace Path

/-- Path inversion. -/
def symm {A : Type u} {a b : A} : Path a b → Path b a
  | .refl => .refl

/-- Path composition. -/
def trans {A : Type u} {a b c : A} : Path a b → Path b c → Path a c
  | .refl, q => q

/-- Action of a function on paths. -/
def ap {A : Type u} {B : Type v} (f : A → B) {a b : A} : Path a b → Path (f a) (f b)
  | .refl => .refl

/-- Transport in a type family along a path. -/
def transport {A : Type u} (P : A → Type v) {a b : A} : Path a b → P a → P b
  | .refl => fun x => x

end Path

/-- Pointwise application of a path between (dependent) functions.
Note this direction needs no function extensionality. -/
def happly {A : Type u} {P : A → Type v} {f g : (x : A) → P x}
    (p : Path f g) (x : A) : Path (f x) (g x) :=
  Path.ap (fun h => h x) p

/-- Contractibility: a center together with a path to every point. -/
structure Contr (A : Type u) : Type u where
  center : A
  contr : (a : A) → Path center a

/-- A retract of a contractible type is contractible. -/
def Contr.retract {A : Type u} {B : Type v} (r : A → B) (s : B → A)
    (hrs : (b : B) → Path (r (s b)) b) (cA : Contr A) : Contr B where
  center := r cA.center
  contr b := (Path.ap r (cA.contr (s b))).trans (hrs b)

private def singletonContrAux {A : Type u} {a b : A} (p : Path a b) :
    Path (⟨a, .refl⟩ : Σ x : A, Path a x) ⟨b, p⟩ :=
  match b, p with
  | _, .refl => .refl

/-- Based path spaces (singletons) are contractible. -/
def singletonContr {A : Type u} (a : A) : Contr (Σ b : A, Path a b) where
  center := ⟨a, .refl⟩
  contr w := singletonContrAux w.2

private def singletonContrAux' {A : Type u} {k b : A} (p : Path b k) :
    Path (⟨k, .refl⟩ : Σ x : A, Path x k) ⟨b, p⟩ :=
  match k, p with
  | _, .refl => .refl

/-- Singletons based at the right endpoint are contractible. -/
def singletonContr' {A : Type u} (k : A) : Contr (Σ b : A, Path b k) where
  center := ⟨k, .refl⟩
  contr w := singletonContrAux' w.2

end Hott

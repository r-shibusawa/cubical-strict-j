/-!
# Lawvere's fixed point theorem

Self-contained: we define cartesian closed structure from scratch and prove
Lawvere's fixed point theorem (1969) — if some `φ : A ⟶ Bᴬ` is
point-surjective, then every endomorphism of `B` has a fixed point.

The theorem is stated at an arbitrary "stage" `Γ` (generalized points), so
no terminal object is even required; the classical statement is the case
`Γ = 1`.  Cantor's theorem drops out by instantiating in the category of
types (`typesCCC`) with `B = Bool`.

Diagonal arguments throughout logic — Cantor, Russell, Gödel, Tarski,
Turing — are instances of this single categorical fact (Lawvere 1969;
Yanofsky, *A universal approach to self-referential paradoxes*, 2003).
-/

namespace CategoryTheory

universe u v

/-- A cartesian closed category, bundled: composition is in diagrammatic
order (`comp f g` is "`f` then `g`").  Products and exponentials are chosen
structure; only the β-law is required of `curry` (no uniqueness). -/
structure CCC : Type (max (u + 1) (v + 1)) where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)
  /-- Chosen binary products. -/
  prod : Obj → Obj → Obj
  fst : {X Y : Obj} → Hom (prod X Y) X
  snd : {X Y : Obj} → Hom (prod X Y) Y
  pair : {Z X Y : Obj} → Hom Z X → Hom Z Y → Hom Z (prod X Y)
  pair_fst : ∀ {Z X Y} (f : Hom Z X) (g : Hom Z Y), comp (pair f g) fst = f
  pair_snd : ∀ {Z X Y} (f : Hom Z X) (g : Hom Z Y), comp (pair f g) snd = g
  comp_pair : ∀ {W Z X Y} (h : Hom W Z) (f : Hom Z X) (g : Hom Z Y),
    comp h (pair f g) = pair (comp h f) (comp h g)
  /-- Chosen exponentials: `exp X Y` is the object of maps `X ⟶ Y`. -/
  exp : Obj → Obj → Obj
  eval : {X Y : Obj} → Hom (prod (exp X Y) X) Y
  curry : {Z X Y : Obj} → Hom (prod Z X) Y → Hom Z (exp X Y)
  curry_beta : ∀ {Z X Y} (g : Hom (prod Z X) Y),
    comp (pair (comp fst (curry g)) snd) eval = g

namespace CCC

variable (C : CCC.{u, v})

/-- β-reduction at a generalized point: evaluating `curry g` at `x`. -/
theorem curry_beta_point {Γ A B : C.Obj} (g : C.Hom (C.prod Γ A) B)
    (x : C.Hom Γ A) :
    C.comp (C.pair (C.curry g) x) C.eval = C.comp (C.pair (C.id Γ) x) g := by
  have key : C.pair (C.curry g) x
      = C.comp (C.pair (C.id Γ) x) (C.pair (C.comp C.fst (C.curry g)) C.snd) := by
    rw [C.comp_pair, ← C.assoc, C.pair_fst, C.id_comp, C.pair_snd]
  rw [key, C.assoc, C.curry_beta]

/-- `φ : A ⟶ Bᴬ` is point-surjective at stage `Γ` if every point
`Γ ⟶ Bᴬ` factors through it. -/
def PointSurjective (Γ : C.Obj) {A B : C.Obj} (φ : C.Hom A (C.exp A B)) : Prop :=
  ∀ p : C.Hom Γ (C.exp A B), ∃ x : C.Hom Γ A, C.comp x φ = p

/-- **Lawvere's fixed point theorem**: if `φ : A ⟶ Bᴬ` is point-surjective
at stage `Γ`, then every `t : B ⟶ B` has a fixed point `b : Γ ⟶ B`. -/
theorem lawvere_fixed_point {Γ A B : C.Obj} (φ : C.Hom A (C.exp A B))
    (hφ : C.PointSurjective Γ φ) (t : C.Hom B B) :
    ∃ b : C.Hom Γ B, C.comp b t = b := by
  -- `d : A ⟶ B` is the self-application map `⟨φ, 1⟩ ; eval`;
  -- take `x : Γ ⟶ A` hitting the name of `a ↦ t (d a)`.
  obtain ⟨x, hx⟩ :=
    hφ (C.curry (C.comp C.snd (C.comp (C.comp (C.pair φ (C.id A)) C.eval) t)))
  refine ⟨C.comp x (C.comp (C.pair φ (C.id A)) C.eval), Eq.symm ?_⟩
  calc C.comp x (C.comp (C.pair φ (C.id A)) C.eval)
      = C.comp (C.pair (C.comp x φ) x) C.eval := by
        rw [← C.assoc, C.comp_pair, C.comp_id]
    _ = C.comp (C.pair (C.curry (C.comp C.snd
          (C.comp (C.comp (C.pair φ (C.id A)) C.eval) t))) x) C.eval := by
        rw [hx]
    _ = C.comp (C.pair (C.id Γ) x) (C.comp C.snd
          (C.comp (C.comp (C.pair φ (C.id A)) C.eval) t)) :=
        C.curry_beta_point _ x
    _ = C.comp x (C.comp (C.comp (C.pair φ (C.id A)) C.eval) t) := by
        rw [← C.assoc, C.pair_snd]
    _ = C.comp (C.comp x (C.comp (C.pair φ (C.id A)) C.eval)) t := by
        rw [← C.assoc]

/-- Contrapositive form: if `B` has a fixed-point-free endomorphism, no
`φ : A ⟶ Bᴬ` is point-surjective. -/
theorem no_point_surjective {Γ A B : C.Obj} (t : C.Hom B B)
    (ht : ∀ b : C.Hom Γ B, C.comp b t ≠ b) (φ : C.Hom A (C.exp A B)) :
    ¬ C.PointSurjective Γ φ := fun hφ =>
  let ⟨b, hb⟩ := C.lawvere_fixed_point φ hφ t
  ht b hb

end CCC

/-- The category of types is cartesian closed (all laws are definitional). -/
def typesCCC : CCC.{u + 1, u} where
  Obj := Type u
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  prod A B := A × B
  fst := Prod.fst
  snd := Prod.snd
  pair f g := fun z => (f z, g z)
  pair_fst _ _ := rfl
  pair_snd _ _ := rfl
  comp_pair _ _ _ := rfl
  exp A B := A → B
  eval := fun p => p.1 p.2
  curry g := fun z x => g (z, x)
  curry_beta _ := rfl

/-- **Cantor's theorem** (via Lawvere): no map `f : A → (A → Bool)` is
surjective. -/
theorem cantor {A : Type} (f : A → (A → Bool)) :
    ¬ ∀ g : A → Bool, ∃ a : A, f a = g := by
  intro hsurj
  have hφ : typesCCC.PointSurjective PUnit (A := A) (B := Bool) f := by
    intro p
    obtain ⟨a, ha⟩ := hsurj (p PUnit.unit)
    exact ⟨fun _ => a, funext fun u => by cases u; exact ha⟩
  obtain ⟨b, hb⟩ := typesCCC.lawvere_fixed_point f hφ Bool.not
  have : Bool.not (b PUnit.unit) = b PUnit.unit := congrFun hb PUnit.unit
  cases h : b PUnit.unit <;> rw [h] at this <;> exact Bool.noConfusion this

end CategoryTheory

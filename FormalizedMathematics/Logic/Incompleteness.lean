/-!
# Abstract incompleteness: Löb's theorem and Gödel's theorems

We axiomatize a theory `T` by the Hilbert–Bernays–Löb derivability
conditions over a minimal implicational language (implication + falsum +
an internal provability operator `box`), together with modus ponens and
the two standard implicational axiom schemes.  Any recursively enumerable
theory interpreting enough arithmetic (PA, ZFC, ...) satisfies these
conditions, with `box φ = Pr⌜φ⌝` and the diagonal lemma providing
`Diagonal` instances.

From this we derive, purely formally:
* `loeb`      : Löb's theorem — if `T ⊢ □θ → θ` then `T ⊢ θ`.
* `goedel1`   : the Gödel sentence of a consistent `T` is unprovable.
* `goedel2`   : a consistent `T` never proves its own consistency.
-/

namespace Logic

universe u

/-- A theory satisfying the Hilbert–Bernays–Löb derivability conditions. -/
structure ProvabilityTheory : Type (u + 1) where
  /-- Sentences of the language. -/
  Sentence : Type u
  /-- External provability: `Prov φ` means `T ⊢ φ`. -/
  Prov : Sentence → Prop
  /-- Implication connective. -/
  imp : Sentence → Sentence → Sentence
  /-- Falsum. -/
  falsum : Sentence
  /-- Internalized provability predicate: `box φ` is `Pr⌜φ⌝`. -/
  box : Sentence → Sentence
  /-- Modus ponens. -/
  mp : ∀ {φ ψ}, Prov (imp φ ψ) → Prov φ → Prov ψ
  /-- Axiom scheme K: `φ → (ψ → φ)`. -/
  a1 : ∀ {φ ψ}, Prov (imp φ (imp ψ φ))
  /-- Axiom scheme S: `(φ → ψ → χ) → (φ → ψ) → (φ → χ)`. -/
  a2 : ∀ {φ ψ χ}, Prov (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  /-- HBL condition D1: provable sentences are provably provable. -/
  d1 : ∀ {φ}, Prov φ → Prov (box φ)
  /-- HBL condition D2: internal provability distributes over implication. -/
  d2 : ∀ {φ ψ}, Prov (imp (box (imp φ ψ)) (imp (box φ) (box ψ)))
  /-- HBL condition D3: internal formalization of D1. -/
  d3 : ∀ {φ}, Prov (imp (box φ) (box (box φ)))

namespace ProvabilityTheory

variable (T : ProvabilityTheory.{u})

/-- Negation, defined as `φ → ⊥`. -/
def neg (φ : T.Sentence) : T.Sentence := T.imp φ T.falsum

/-- Consistency of `T` (an external, meta-level statement). -/
def Con : Prop := ¬ T.Prov T.falsum

/-- The consistency of `T` expressed *inside* `T`: `¬ Pr⌜⊥⌝`. -/
def con : T.Sentence := T.neg (T.box T.falsum)

/-- Hypothetical syllogism, derived from `a1`, `a2`, `mp`. -/
theorem impTrans {φ ψ χ : T.Sentence}
    (h₁ : T.Prov (T.imp φ ψ)) (h₂ : T.Prov (T.imp ψ χ)) :
    T.Prov (T.imp φ χ) :=
  T.mp (T.mp T.a2 (T.mp T.a1 h₂)) h₁

/-- Modus ponens under a common antecedent. -/
theorem mpUnder {φ ψ χ : T.Sentence}
    (h : T.Prov (T.imp φ (T.imp ψ χ))) (h' : T.Prov (T.imp φ ψ)) :
    T.Prov (T.imp φ χ) :=
  T.mp (T.mp T.a2 h) h'

/-- A fixed point of `ψ ↦ (□ψ → θ)`, as produced by the diagonal lemma.
For `θ = ⊥` the fixed point `φ` is the Gödel sentence ("I am unprovable"). -/
structure Diagonal (θ : T.Sentence) : Type u where
  φ : T.Sentence
  fix₁ : T.Prov (T.imp φ (T.imp (T.box φ) θ))
  fix₂ : T.Prov (T.imp (T.imp (T.box φ) θ) φ)

/-- **Löb's theorem**: if `T ⊢ □θ → θ` then `T ⊢ θ`. -/
theorem loeb {θ : T.Sentence} (dg : T.Diagonal θ)
    (h : T.Prov (T.imp (T.box θ) θ)) : T.Prov θ := by
  -- □φ → □(□φ → θ)
  have s₁ : T.Prov (T.imp (T.box dg.φ) (T.box (T.imp (T.box dg.φ) θ))) :=
    T.mp T.d2 (T.d1 dg.fix₁)
  -- □φ → (□□φ → □θ)
  have s₂ : T.Prov (T.imp (T.box dg.φ) (T.imp (T.box (T.box dg.φ)) (T.box θ))) :=
    T.impTrans s₁ T.d2
  -- □φ → □θ   (using D3: □φ → □□φ)
  have s₃ : T.Prov (T.imp (T.box dg.φ) (T.box θ)) := T.mpUnder s₂ T.d3
  -- □φ → θ    (using the hypothesis □θ → θ)
  have s₄ : T.Prov (T.imp (T.box dg.φ) θ) := T.impTrans s₃ h
  -- hence φ, hence □φ, hence θ
  have s₅ : T.Prov dg.φ := T.mp dg.fix₂ s₄
  exact T.mp s₄ (T.d1 s₅)

/-- **Gödel's first incompleteness theorem** (unprovability half):
if `T` is consistent, its Gödel sentence is unprovable. -/
theorem goedel1 (dg : T.Diagonal T.falsum) (hcon : T.Con) :
    ¬ T.Prov dg.φ := fun h =>
  hcon (T.mp (T.mp dg.fix₁ h) (T.d1 h))

/-- **Gödel's second incompleteness theorem**:
if `T` is consistent, `T` does not prove its own consistency. -/
theorem goedel2 (dg : T.Diagonal T.falsum) (hcon : T.Con) :
    ¬ T.Prov T.con := fun h =>
  hcon (T.loeb dg h)

end ProvabilityTheory

/-- Sanity check: the axioms are satisfiable (by the inconsistent theory
over a one-sentence language — this only shows the *structure* is coherent). -/
def trivialTheory : ProvabilityTheory where
  Sentence := PUnit
  Prov _ := True
  imp _ _ := PUnit.unit
  falsum := PUnit.unit
  box _ := PUnit.unit
  mp _ _ := trivial
  a1 := trivial
  a2 := trivial
  d1 _ := trivial
  d2 := trivial
  d3 := trivial

end Logic

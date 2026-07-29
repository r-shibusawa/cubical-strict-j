import FormalizedMathematics.Cubical.LibMixed

/-! # Word problems over cellular contexts, I: the relator mechanism

Program (docs/WordProblem.md): over cellular contexts, the *strict*
word problem is always decidable (the realization theorem plus the
decidability of the algorithmic equality), and the *propositional*
word problem splits along dimension: decidable for free graph
computads (reduced words; separations by circle instantiation and
computed winding invariants), undecidable from 2-computads on
(finitely presented groups embed as relator cells).

This file machine-demonstrates the mechanism behind the second half:
over the presentation computad of ℤ/2 — one vertex `a`, one loop
`x`, one relator 2-cell `R : x·x ⇒ refl` — relator applications are
path *constructions*.  We derive the group-theoretic consequence
`x⁴ = 1` as an explicit propositional identification:

  `x⁴ = (x·x)·(x·x) ⇝[cong (·(x·x)) R] refl·(x·x)
        ⇝[transReflL] x·x ⇝[R] refl`,

a composite of two groupoid laws and two relator uses, type-checked
over the generic presentation context.  (Over the *free* loop
context, the same word pair is separated: winding computes `+2` for
`loop·loop` after instantiating at the circle, and `0` for `refl` —
the machine values recorded in the artifact library.) -/

namespace Cubical.Library

open Raw

private def A : Raw := .var "A"
private def a : Raw := .var "a"
private def x : Raw := .var "x"
private def R : Raw := .var "R"

/-- The loop type `Path A a a`. -/
private def LT : Raw := .path A a a

private def rfl0 : Raw := apps reflD.ref [A, a]
/-- `x·x`. -/
private def xx : Raw := apps transD.ref [A, a, a, a, x, x]
/-- `(x·x)·(x·x)` — the word `x⁴`. -/
private def x4 : Raw := apps transD.ref [A, a, a, a, xx, xx]
/-- `refl·(x·x)`. -/
private def rxx : Raw := apps transD.ref [A, a, a, a, rfl0, xx]

/-- The presentation context of `⟨x ∣ x² = 1⟩`:
`A : U, a : A, x : Path A a a, R : Path (Path A a a) (x·x) refl`. -/
private def ctxW (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" A (.pi "x" LT
    (.pi "R" (.path LT xx rfl0) body)))

private def lamsW (body : Raw) : Raw :=
  lams ["A", "a", "x", "R"] body

/-- **Relator-derived identification**: `x⁴ ≡prop refl` over the
presentation computad of ℤ/2 — two relator uses composed with the
groupoid laws.  This is the ⟸ direction of the undecidability
transfer in miniature: group-theoretic consequences of the relators
become explicit path constructions. -/
def wordX4D : LibDef where
  name := "wordX4"
  ty := ctxW (.path LT x4 rfl0)
  tm :=
    -- cong (λw. w·(x·x)) R : x⁴ ≡ refl·(x·x)
    let f : Raw := .lam "w" (apps transD.ref [A, a, a, a, .var "w", xx])
    let step1 : Raw := apps congD.ref [LT, LT, f, xx, rfl0, R]
    -- transReflL : refl·(x·x) ≡ x·x
    let step2 : Raw := apps transReflLD.ref [A, a, a, xx]
    -- assemble: step1 ⬝ (step2 ⬝ R) at the loop type
    let inner : Raw := apps transD.ref [LT, rxx, xx, rfl0, step2, R]
    lamsW (apps transD.ref [LT, x4, rxx, rfl0, step1, inner])

#guard wordX4D.ok

/-- Control: over the presentation context the relator gives
`x·x ≡prop refl` directly (the variable itself is the witness). -/
def wordRelD : LibDef where
  name := "wordRel"
  ty := ctxW (.path LT xx rfl0)
  tm := lamsW R

#guard wordRelD.ok

end Cubical.Library

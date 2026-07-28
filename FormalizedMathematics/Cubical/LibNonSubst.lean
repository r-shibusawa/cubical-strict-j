import FormalizedMathematics.Cubical.LibSwitchover

/-! # Substitution (in)stability of the typed algorithmic equality

Take the non-constant path family `C(i) := Path A a (p i)` over
`Γ = (A, a, b, p : Path A a b, q : Path A a a)`, and let

* `t := transp^i C q`  — a transport redex whose family is
  *non-constant at the generic environment* (the check cannot fire), and
* `u := ⟨j⟩ hcomp^ii A [j=0 ↦ a, j=1 ↦ p ii] (q j)` — the structural
  contractum of `t` (the transp components along the constant line `A`
  collapse by rule (R) during evaluation).

Substituting `σ := [refl/p, a/b]` makes the family *constant*, so `tσ`
takes the positive branch and collapses to `q`, while `uσ` freezes into
a constant-tube `hcomp` — the (†)-residue of the paper's no-go theorem.

The three probes below ask the kernel:

* P1: `Γ ⊢ t ≡ u`?            (is the structural instance in ≡alg?)
* P2: `Δ ⊢ tσ ≡ q`?           (does the collapse fire after σ?)
* P3: `Δ ⊢ uσ ≡ q`?           (is the substituted equation still in ≡alg?)

If P1 and P2 hold but P3 fails, then the typed algorithmic equality is
**not closed under substitution** — the no-go theorem materializes
inside the algorithmic layer itself, one substitution instance at a
time.  (Consequences: the erratum to the paper's admissibility claim,
and the proof that no substitution-closed presentation of the
algorithmic equality exists; see the paper's non-substitutivity
section.) -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

private def A : Raw := .var "A"
private def a : Raw := .var "a"
private def b : Raw := .var "b"
private def p : Raw := .var "p"
private def q : Raw := .var "q"
private def vi : Raw := .var "i"
private def vj : Raw := .var "j"
private def vii : Raw := .var "ii"
private def rfla : Raw := apps reflD.ref [A, a]

/-- `Γ = (A : U, a b : A, p : Path A a b, q : Path A a a)`. -/
private def ctxG (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path A a b) (.pi "q" (.path A a a) body))))

/-- `Δ = (A : U, a : A, q : Path A a a)` — the target of `σ`. -/
private def ctxD (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "q" (.path A a a) body))

/-- `t = transp^i (Path A a (p i)) q`. -/
private def t : Raw := .transp "i" (.path A a (.papp p a b vi)) q

/-- `u = ⟨j⟩ hcomp^ii A [j=0 ↦ a, j=1 ↦ p ii] (q j)` —
the structural contractum of `t`. -/
private def u : Raw :=
  .plam "j" (.hcomp "ii" A
    [([(vj, false)], a), ([(vj, true)], .papp p a b vii)]
    (.papp q a a vj))

/-- `tσ` (σ = [refl/p, a/b]). -/
private def tS : Raw := .transp "i" (.path A a (.papp rfla a a vi)) q

/-- `uσ`. -/
private def uS : Raw :=
  .plam "j" (.hcomp "ii" A
    [([(vj, false)], a), ([(vj, true)], .papp rfla a a vii)]
    (.papp q a a vj))

/-! ## P1: the structural instance is in ≡alg -/

/-- `Γ ⊢ t ≡ u : Path A a b` — the transport redex over the
*non-constant* family is convertible with its structural contractum
(the evaluator's negative branch *is* the structural rule). -/
def nsStructuralD : LibDef where
  name := "nsStructural"
  ty := ctxG (.path (.path A a b) t u)
  tm := lams ["A", "a", "b", "p", "q"] (.plam "k" u)

#guard nsStructuralD.ok

/-! ## P2: after σ, the redex collapses -/

/-- `Δ ⊢ tσ ≡ q : Path A a a` — the substituted family has constant
*value*, so rule (R) fires. -/
def nsCollapseD : LibDef where
  name := "nsCollapse"
  ty := ctxD (.path (.path A a a) tS q)
  tm := lams ["A", "a", "q"] (.plam "k" q)

#guard nsCollapseD.ok

/-! ## P3: the substituted structural equation is NOT in ≡alg -/

-- Control: `uσ` is well-typed at `Path A a a`.
def nsResidueCtrlD : LibDef where
  name := "nsResidueCtrl"
  ty := ctxD (.path A a a)
  tm := lams ["A", "a", "q"] uS

#guard nsResidueCtrlD.ok

-- `Δ ⊢ uσ ≢ q` — the substituted contractum is a stuck constant-tube
-- hcomp (the (†)-residue), separated from `q` by path separation.
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" q))
  (ctxD (.path (.path A a a) uS q)))

-- Corollary witness: `Δ ⊢ tσ ≢ uσ` — the *same equation* `t ≡ u`,
-- instantiated along σ, leaves ≡alg.
#guard !(okD
  (lams ["A", "a", "q"] (.plam "k" uS))
  (ctxD (.path (.path A a a) tS uS)))

end Cubical.Library

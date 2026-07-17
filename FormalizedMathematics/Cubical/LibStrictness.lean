import FormalizedMathematics.Cubical.LibTower

/-! # The definitional-strictness catalogue

A systematic, machine-checked record of which path-algebra laws hold
*definitionally* in this CCHM kernel — the empirical basis for the two
research targets recorded in `docs/PaperNotes.md` §8–9:

1. the cubical-specific "types are weak ω-groupoids" theorem (which
   directions/dimensions are *strict*), and
2. a Mac Lane-style coherence theorem for the connection algebra.

Positive probes are `LibDef`s whose term is an inline `refl`; the guard
passes iff the two sides are convertible.  **Negative probes are
first-class**: `#guard !(okD ...)` records that a law is *not*
definitional — the essential-weakness data.  -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

/-! ## Ambient contexts -/

private def ctxP (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b")) body)))

private def ctxPQ (body : Raw) : Raw :=
  .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "c" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
    (.pi "q" (.path (.var "A") (.var "b") (.var "c")) body)))))

private def A : Raw := .var "A"
private def a : Raw := .var "a"
private def b : Raw := .var "b"
private def c : Raw := .var "c"
private def p : Raw := .var "p"
private def q : Raw := .var "q"
private def rfla : Raw := apps reflD.ref [A, a]
private def PT (x y : Raw) : Raw := .path A x y

/-! ## 1. Interval / connection layer (De Morgan normal forms) -/

/-- `⟨i⟩ p (i ∧ i) ≐ p` (idempotence absorbed by the DNF). -/
def strictConnIdemD : LibDef where
  name := "strictConnIdem"
  ty := ctxP (.path (PT a b)
    (.plam "i" (.papp p a b (.imin (.var "i") (.var "i")))) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictConnIdemD.ok

/-- `⟨i⟩ p (¬¬i) ≐ p` (involution). -/
def strictConnInvolD : LibDef where
  name := "strictConnInvol"
  ty := ctxP (.path (PT a b)
    (.plam "i" (.papp p a b (.ineg (.ineg (.var "i"))))) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictConnInvolD.ok

/-- Absorption: the squares `⟨i⟩⟨j⟩ p (i ∧ (i ∨ j))` and
`⟨i⟩⟨j⟩ p i` coincide. -/
def strictConnAbsorbD : LibDef where
  name := "strictConnAbsorb"
  ty :=
    let sqTy : Raw := .pathP "i"
      (.path A (.papp p a b (.var "i")) (.papp p a b (.var "i")))
      (apps reflD.ref [A, a]) (apps reflD.ref [A, b])
    ctxP (.path sqTy
      (.plam "i" (.plam "j" (.papp p a b
        (.imin (.var "i") (.imax (.var "i") (.var "j"))))))
      (.plam "i" (.plam "j" (.papp p a b (.var "i")))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "k" (.plam "i" (.plam "j" (.papp p a b (.var "i")))))

#guard strictConnAbsorbD.ok

/-- `⟨i⟩ p (i ∧ 0) ≐ refl a`. -/
def strictConnZeroD : LibDef where
  name := "strictConnZero"
  ty := ctxP (.path (PT a a)
    (.plam "i" (.papp p a b (.imin (.var "i") .i0))) rfla)
  tm := lams ["A", "a", "b", "p"] (.plam "j" rfla)

#guard strictConnZeroD.ok

/-! ## 2. Path-former layer: symm / η -/

/-- Path η: `⟨i⟩ (p @ i) ≐ p`. -/
def strictPathEtaD : LibDef where
  name := "strictPathEta"
  ty := ctxP (.path (PT a b) (.plam "i" (.papp p a b (.var "i"))) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictPathEtaD.ok

/-- `symm refl ≐ refl`. -/
def strictSymmReflD : LibDef where
  name := "strictSymmRefl"
  ty := .pi "A" .univ (.pi "a" (.var "A")
    (.path (PT a a) (apps symmD.ref [A, a, a, rfla]) rfla))
  tm := lams ["A", "a"] (.plam "j" rfla)

#guard strictSymmReflD.ok

/-- `symm (symm p) ≐ p` (known: the `symmInvol` proof is `⟨j⟩ p`). -/
def strictSymmSymmD : LibDef where
  name := "strictSymmSymm"
  ty := ctxP (.path (PT a b)
    (apps symmD.ref [A, b, a, apps symmD.ref [A, a, b, p]]) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictSymmSymmD.ok

/-! ## 3. cong layer -/

/-- `cong f refl ≐ refl`. -/
def strictCongReflD : LibDef where
  name := "strictCongRefl"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B")) (.pi "a" (.var "A")
      (.path (.path (.var "B") (.app (.var "f") a) (.app (.var "f") a))
        (apps congD.ref [A, .var "B", .var "f", a, a,
          apps reflD.ref [A, a]])
        (apps reflD.ref [.var "B", .app (.var "f") a])))))
  tm := lams ["A", "B", "f", "a"]
    (.plam "j" (apps reflD.ref [.var "B", .app (.var "f") a]))

#guard strictCongReflD.ok

/-- `cong id p ≐ p`. -/
def strictCongIdD : LibDef where
  name := "strictCongId"
  ty := ctxP (.path (PT a b)
    (apps congD.ref [A, A, .lam "t" (.var "t"), a, b, p]) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictCongIdD.ok

/-- `cong f (symm p) ≐ symm (cong f p)`. -/
def strictCongSymmD : LibDef where
  name := "strictCongSymm"
  ty :=
    let B : Raw := .var "B"
    let f : Raw := .var "f"
    let fa : Raw := .app f a
    let fb : Raw := .app f b
    .pi "A" .univ (.pi "B" .univ (.pi "f" (.arr A B)
      (.pi "a" A (.pi "b" A (.pi "p" (PT a b)
        (.path (.path B fb fa)
          (apps congD.ref [A, B, f, b, a, apps symmD.ref [A, a, b, p]])
          (apps symmD.ref [B, fa, fb,
            apps congD.ref [A, B, f, a, b, p]])))))))
  tm := lams ["A", "B", "f", "a", "b", "p"]
    (.plam "j" (apps symmD.ref [.var "B", .app (.var "f") a,
      .app (.var "f") b, apps congD.ref [A, .var "B", .var "f", a, b, p]]))

#guard strictCongSymmD.ok

/-! ## 4. Transport layer (regularity-flavoured rules) -/

/-- Constant-family transport is the identity (the constancy rule). -/
def strictTranspConstD : LibDef where
  name := "strictTranspConst"
  ty := .pi "A" .univ (.pi "a" (.var "A")
    (.path A (.transp "i" A a) a))
  tm := lams ["A", "a"] (.plam "j" a)

#guard strictTranspConstD.ok

/-- **`J` computes on `refl` definitionally** — value-level regularity.
(Notable: NOT definitional in cubical Agda; the model-theoretic status
of regularity is delicate — see PaperNotes §9.) -/
def strictJReflD : LibDef where
  name := "strictJRefl"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (.pi "P" (.pi "y" (.var "A")
      (.arr (.path (.var "A") (.var "x") (.var "y")) .univ))
    (.pi "d" (apps (.var "P") [.var "x", .plam "k" (.var "x")])
      (.path (apps (.var "P") [.var "x", .plam "k" (.var "x")])
        (apps jD.ref [.var "A", .var "x", .var "P", .var "d",
          .var "x", .plam "k" (.var "x")])
        (.var "d")))))
  tm := lams ["A", "x", "P", "d"] (.plam "j" (.var "d"))

#guard strictJReflD.ok

/-! ## 5. Negative probes: the essentially weak laws -/

-- `trans refl refl ≐ refl` FAILS (composition is a stuck hcomp).
#guard !(okD
  (lams ["A", "a"] (.plam "j" (.plam "k" (.var "a"))))
  (.pi "A" .univ (.pi "a" (.var "A")
    (.path (.path (.var "A") (.var "a") (.var "a"))
      (apps transD.ref [.var "A", .var "a", .var "a", .var "a",
        .plam "i" (.var "a"), .plam "i" (.var "a")])
      (.plam "i" (.var "a"))))))

-- `cong f (p ⬝ q) ≐ cong f p ⬝ cong f q` FAILS (needs `congTrans`, by J).
#guard !(okD
  (lams ["A", "B", "f", "a", "b", "c", "p", "q"]
    (.plam "j" (apps transD.ref [.var "B",
      .app (.var "f") (.var "a"), .app (.var "f") (.var "b"),
      .app (.var "f") (.var "c"),
      apps congD.ref [.var "A", .var "B", .var "f", .var "a", .var "b",
        .var "p"],
      apps congD.ref [.var "A", .var "B", .var "f", .var "b", .var "c",
        .var "q"]])))
  (.pi "A" .univ (.pi "B" .univ (.pi "f" (.arr (.var "A") (.var "B"))
    (.pi "a" (.var "A") (.pi "b" (.var "A") (.pi "c" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
    (.pi "q" (.path (.var "A") (.var "b") (.var "c"))
      (.path (.path (.var "B")
          (.app (.var "f") (.var "a")) (.app (.var "f") (.var "c")))
        (apps congD.ref [.var "A", .var "B", .var "f", .var "a", .var "c",
          apps transD.ref [.var "A", .var "a", .var "b", .var "c",
            .var "p", .var "q"]])
        (apps transD.ref [.var "B",
          .app (.var "f") (.var "a"), .app (.var "f") (.var "b"),
          .app (.var "f") (.var "c"),
          apps congD.ref [.var "A", .var "B", .var "f", .var "a", .var "b",
            .var "p"],
          apps congD.ref [.var "A", .var "B", .var "f", .var "b", .var "c",
            .var "q"]])))))))))))

-- `symm (p ⬝ q) ≐ symm q ⬝ symm p` FAILS (different hcomp shapes).
#guard !(okD
  (lams ["A", "a", "b", "c", "p", "q"]
    (.plam "j" (apps transD.ref [.var "A", .var "c", .var "b", .var "a",
      apps symmD.ref [.var "A", .var "b", .var "c", .var "q"],
      apps symmD.ref [.var "A", .var "a", .var "b", .var "p"]])))
  (ctxPQ (.path (.path (.var "A") (.var "c") (.var "a"))
    (apps symmD.ref [.var "A", .var "a", .var "c",
      apps transD.ref [.var "A", .var "a", .var "b", .var "c",
        .var "p", .var "q"]])
    (apps transD.ref [.var "A", .var "c", .var "b", .var "a",
      apps symmD.ref [.var "A", .var "b", .var "c", .var "q"],
      apps symmD.ref [.var "A", .var "a", .var "b", .var "p"]]))))

/-! ## 6. The regularity frontier (danger-zone probes)

The constancy rule is *value-level*: it fires whenever the family's
evaluated form does not mention the transport dimension.  These probes
map exactly where it fires — the data for the soundness analysis in
`docs/RegularityNotes.md`. -/

/-- Transport along the constant universe family is the identity —
the constancy rule fires at `U` itself. -/
def strictTranspUD : LibDef where
  name := "strictTranspU"
  ty := .pi "X" .univ (.path .univ (.transp "i" .univ (.var "X"))
    (.var "X"))
  tm := .lam "X" (.plam "j" (.var "X"))

#guard strictTranspUD.ok

/-- Transport along a *constant path-type* family is the identity. -/
def strictTranspPathFamD : LibDef where
  name := "strictTranspPathFam"
  ty := ctxP (.path (PT a b)
    (.transp "i" (.path A a b) p) p)
  tm := lams ["A", "a", "b", "p"] (.plam "j" p)

#guard strictTranspPathFamD.ok

/-- `transport (ua idEquiv) x ≐ x`?  The `ua` line *does* mention the
dimension (a `Glue`), so the constancy rule does NOT fire; this probes
whether `transpGlue` computation alone closes it. -/
def strictTranspUaIdD : LibDef where
  name := "strictTranspUaId"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (.path (.var "A")
      (apps transportD.ref [.var "A", .var "A",
        apps uaD.ref [.var "A", .var "A", .app idEquivD.ref (.var "A")],
        .var "x"])
      (.var "x")))
  tm := lams ["A", "x"] (.plam "j" (.var "x"))

-- RESULT (2026-07-16): POSITIVE — `transpGlue` computation alone
-- closes it; no constancy rule involved.
#guard strictTranspUaIdD.ok

-- Is `hcomp` with an identically-constant tube over `refl` reduced?
-- `trans p refl ≐ p` would be hcomp-regularity — expected NOT to hold
-- (the kernel has no hcomp-regularity rule; `transReflR` is a proof).
#guard !(okD
  (lams ["A", "a", "b", "p"] (.plam "j" p))
  (ctxP (.path (PT a b)
    (apps transD.ref [A, a, b, b, p, apps reflD.ref [A, b]]) p)))

/-- Value-constancy beats syntax: a family that *mentions* the dimension
but whose value reduces it away (`p @ (i ∧ 0)`) still fires the rule. -/
def strictTranspValueConstD : LibDef where
  name := "strictTranspValueConst"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
    (.pi "u" (.app (.var "B") (.var "a"))
      (.path (.app (.var "B") (.var "a"))
        (.transp "i" (.app (.var "B")
          (.papp (.var "p") (.var "a") (.var "b")
            (.imin (.var "i") .i0)))
          (.var "u"))
        (.var "u")))))))
  tm := lams ["A", "B", "a", "b", "p", "u"] (.plam "j" (.var "u"))

#guard strictTranspValueConstD.ok

/-! ## 7. η-inventory (needed for the admissibility proof: rule (R)
together with the structural transp clauses *derives* the η laws, so
the algorithmic equality must already contain them) -/

/-- Function η: `(λ x. f x) ≐ f`. -/
def strictFunEtaD : LibDef where
  name := "strictFunEta"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "f" (.arr (.var "A") (.var "B"))
      (.path (.arr (.var "A") (.var "B"))
        (.lam "x" (.app (.var "f") (.var "x"))) (.var "f"))))
  tm := lams ["A", "B", "f"] (.plam "j" (.var "f"))

#guard strictFunEtaD.ok

/-- Σ η (surjective pairing): `(fst u, snd u) ≐ u`. -/
def strictSigEtaD : LibDef where
  name := "strictSigEta"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.pi "u" (.sigma "x" (.var "A") (.app (.var "B") (.var "x")))
      (.path (.sigma "x" (.var "A") (.app (.var "B") (.var "x")))
        (.pair (.fst (.var "u")) (.snd (.var "u"))) (.var "u"))))
  tm := lams ["A", "B", "u"] (.plam "j" (.var "u"))

#guard strictSigEtaD.ok

/-! ## 8. Reparametrization coherence (theorem C): completeness probes

The free De Morgan algebra on one generator has six elements
`0, 1, i, ¬i, i∧¬i, i∨¬i`; in particular `i∧¬i ≠ 0` and `i∨¬i ≠ 1`
(no excluded middle).  Completeness of the coherence theorem predicts
the corresponding reparametrizations of a generic path are NOT
convertible, even though their endpoints agree. -/

-- `⟨i⟩ p(i∧¬i) ≢ refl a` (both are paths a → a).
#guard !(okD
  (lams ["A", "a", "b", "p"] (.plam "j" (.plam "i" (.var "a"))))
  (ctxP (.path (.path A a a)
    (.plam "i" (.papp p a b (.imin (.var "i") (.ineg (.var "i")))))
    (.plam "i" a))))

-- `⟨i⟩ p(i∨¬i) ≢ refl b`.
#guard !(okD
  (lams ["A", "a", "b", "p"] (.plam "j" (.plam "i" (.var "b"))))
  (ctxP (.path (.path A b b)
    (.plam "i" (.papp p a b (.imax (.var "i") (.ineg (.var "i")))))
    (.plam "i" b))))

/-- De Morgan duality is definitional: `⟨i⟩⟨j⟩ p(¬(i∧j)) ≐
⟨i⟩⟨j⟩ p(¬i ∨ ¬j)` (soundness direction, 2 generators). -/
def strictDeMorganD : LibDef where
  name := "strictDeMorgan"
  ty :=
    let sq (e : Raw) : Raw := .plam "i" (.plam "j" (.papp p a b e))
    let f1 : Raw := .ineg (.imin (.var "i") (.var "j"))
    let f2 : Raw := .imax (.ineg (.var "i")) (.ineg (.var "j"))
    ctxP (.path
      (.pathP "i" (.path A b (.papp p a b (.ineg (.var "i"))))
        (.plam "j" b) (.plam "j" (.papp p a b (.ineg (.var "j")))))
      (sq f1) (sq f2))
  tm :=
    let f1 : Raw := .ineg (.imin (.var "i") (.var "j"))
    lams ["A", "a", "b", "p"]
      (.plam "k" (.plam "i" (.plam "j" (.papp p a b f1))))

#guard strictDeMorganD.ok

end Cubical.Library

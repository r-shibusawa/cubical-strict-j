import FormalizedMathematics.Cubical.LibStrictness

/-! # Switchover coherence probes

**Question** (raised by external review of the paper, 2026-07-17): when a
transport family is *constant*, both rule (R) (constancy collapse,
`transp A u ≡ u`) and the *structural* transport rule for the head
former apply.  Does the structural contractum, hand-written as an
object term and specialized to the constant family, evaluate to
something convertible with `u`?

If YES for a former, the two rules commute there and prioritization is
harmless for that former.  If NO, the unrestricted equational theory
T₀+(R) would prove an equation the algorithm refutes — prioritized /
operational treatment is *forced* at that former.

**Machine verdict recorded below**:
- Π, Σ (incl. dependent), HIT constructors: CONVERGE (positive probes).
- PathP: **FAILS** — the structural contractum carries the endpoint
  correction `⟨j⟩ hcomp [j=0 ↦ a, j=1 ↦ b] (p @ j)`, whose tubes are
  constant in the fill dimension; the kernel (correctly — no
  hcomp-regularity, cf. the `trans refl refl` negative probe in
  LibStrictness) does not collapse constant-tube hcomps, so the
  contractum is a stuck hcomp, not `p`.
- Glue: the `transpGlue` contractum embeds the same mechanism (the
  base-correction `comp` with δ-tubes degenerates, at a constant
  family, to exactly such a constant-tube hcomp), so the Path failure
  already witnesses the residual; a full hand-written `transpGlue`
  probe is future work.

Consequence for the metatheory (docs/RegularityProof.md §7): the
judgmental equality of the extended theory must be *defined as* the
algorithmic (NbE) equality; its substitution stability is the NbE
substitution lemma (the constancy check happens on values, after
environments are applied), NOT a rule-restriction argument. -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

/-! ## 1. Π: structural contractum at a constant family converges

`λx. transp^i B (u (transp^i A x))  ≐  u` — inner transports collapse
by (R), then function η. -/

def swPiD : LibDef where
  name := "swPi"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "u" (.arr (.var "A") (.var "B"))
      (.path (.arr (.var "A") (.var "B"))
        (.lam "x" (.transp "i" (.var "B")
          (.app (.var "u") (.transp "i" (.var "A") (.var "x")))))
        (.var "u"))))
  tm := lams ["A", "B", "u"] (.plam "j" (.var "u"))

#guard swPiD.ok

/-! ## 2. Σ (non-dependent and dependent): converges

`(transp^i A (fst u), transp^i B (snd u))  ≐  u` — (R) on both
components, then Σ η.  In the dependent case the second family is
`B (transp^k A (fst u))`, itself constant after the inner collapse. -/

def swSigD : LibDef where
  name := "swSig"
  ty := .pi "A" .univ (.pi "B" .univ
    (.pi "u" (.sigma "x" (.var "A") (.var "B"))
      (.path (.sigma "x" (.var "A") (.var "B"))
        (.pair (.transp "i" (.var "A") (.fst (.var "u")))
               (.transp "i" (.var "B") (.snd (.var "u"))))
        (.var "u"))))
  tm := lams ["A", "B", "u"] (.plam "j" (.var "u"))

#guard swSigD.ok

def swSigDepD : LibDef where
  name := "swSigDep"
  ty := .pi "A" .univ (.pi "B" (.arr (.var "A") .univ)
    (.pi "u" (.sigma "x" (.var "A") (.app (.var "B") (.var "x")))
      (.path (.sigma "x" (.var "A") (.app (.var "B") (.var "x")))
        (.pair (.transp "i" (.var "A") (.fst (.var "u")))
               (.transp "i"
                 (.app (.var "B") (.transp "k" (.var "A") (.fst (.var "u"))))
                 (.snd (.var "u"))))
        (.var "u"))))
  tm := lams ["A", "B", "u"] (.plam "j" (.var "u"))

#guard swSigDepD.ok

/-! ## 3. HIT constructor case (list cons): converges

Constructor-wise structural transport at a constant family collapses
by (R) on each argument line; no η needed, no hcomp generated. -/

def swListD : LibDef where
  name := "swList"
  ty := .pi "A" .univ (.pi "h" (.var "A")
    (.pi "t" (.list (.var "A"))
      (.path (.list (.var "A"))
        (.lcons (.transp "i" (.var "A") (.var "h"))
                (.transp "i" (.list (.var "A")) (.var "t")))
        (.lcons (.var "h") (.var "t")))))
  tm := lams ["A", "h", "t"] (.plam "j" (.lcons (.var "h") (.var "t")))

#guard swListD.ok

/-! ## 3b. HIT *path* constructor (susp merid): converges

The kernel's structural transport acts on path constructors
argument-wise, carrying the interval argument along unchanged
(`vmerid x r ↦ vmerid (transp x) r`); at a constant family (R)
collapses the argument transport and the constructor form is literal.
NOTE (signature caveat recorded for the paper): the quotient path
constructor `qeq` has NO structural transport clause in this kernel
(non-constructor transports at quotients go neutral), so there is no
critical pair to converge there — the switchover question is vacuous
for such signatures. -/

def swSuspMeridD : LibDef where
  name := "swSuspMerid"
  ty := .pi "A" .univ (.pi "x" (.var "A")
    (.path (.path (.susp (.var "A")) .north .south)
      (.plam "r" (.merid (.transp "i" (.var "A") (.var "x")) (.var "r")))
      (.plam "r" (.merid (.var "x") (.var "r")))))
  tm := lams ["A", "x"]
    (.plam "j" (.plam "r" (.merid (.var "x") (.var "r"))))

#guard swSuspMeridD.ok

/-! ## 4. PathP: the structural contractum does NOT converge

The structural rule for path types is
`transp^i (Path A a b) p ≡ ⟨j⟩ comp^i A [j=0 ↦ a, j=1 ↦ b] (p @ j)`;
at a constant family the transp part of `comp` collapses and the
residue is an hcomp whose tubes are constant in the fill dimension.
The kernel has no hcomp-regularity (by design and by model-theoretic
necessity, Swan/Sattler), so the residue is stuck and NOT convertible
with `p`.  **This is the machine witness that prioritization is forced
already at path types, not only at Glue.** -/

-- `⟨j⟩ hcomp^i A [j=0 ↦ a, j=1 ↦ b] (p @ j)  ≢  p`
#guard !(okD
  (lams ["A", "a", "b", "p"] (.plam "k" (.var "p")))
  (.pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.path (.var "A") (.var "a") (.var "b"))
        (.plam "jj" (.hcomp "ii" (.var "A")
          [([(.var "jj", false)], .var "a"),
           ([(.var "jj", true)], .var "b")]
          (.papp (.var "p") (.var "a") (.var "b") (.var "jj"))))
        (.var "p")))))))

-- Control: the well-typedness of the contractum itself (as a plain
-- definition, no equation asserted) — confirms the failure above is a
-- conversion failure, not a typing artifact.
def swPathContractumD : LibDef where
  name := "swPathContractum"
  ty := .pi "A" .univ (.pi "a" (.var "A") (.pi "b" (.var "A")
    (.pi "p" (.path (.var "A") (.var "a") (.var "b"))
      (.path (.var "A") (.var "a") (.var "b")))))
  tm := lams ["A", "a", "b", "p"]
    (.plam "jj" (.hcomp "ii" (.var "A")
      [([(.var "jj", false)], .var "a"),
       ([(.var "jj", true)], .var "b")]
      (.papp (.var "p") (.var "a") (.var "b") (.var "jj"))))

#guard swPathContractumD.ok

end Cubical.Library

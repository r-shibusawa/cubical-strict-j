# Artifact: Evaluation-Time Constancy Inference for Transport in Cubical Type Theory

This repository is the artifact accompanying the paper
*Evaluation-Time Constancy Inference for Transport in Cubical Type Theory*
(`docs/paper/jrefl.tex`).

- Repository: <https://github.com/r-shibusawa/cubical-strict-j>
- Submission snapshot: release `v1.0.0`, commit `6c5904be3f9bf8ec9138cda5bcb961b6a67f4feb`
- Archived DOI: [10.5281/zenodo.21405962](https://doi.org/10.5281/zenodo.21405962)
- Typical full `lake build` time: ~10–20 min cold (first build of the
  toolchain-pinned project), a few minutes warm.

## Requirements

- Lean 4 toolchain **4.31.0** (pinned in `lean-toolchain`)
- No external dependencies (no mathlib); the cubical kernel is self-contained
  and independent of Lean's own definitional equality.

## Build

```sh
lake build                                                    # full library (~300 definitions)
lake build FormalizedMathematics.Cubical.LibStrictness        # strictness catalogue only
```

Every `#guard` / `def … := checkD …` in the library is checked at
elaboration time; a successful build **is** the verification run.

## Layout (kernel core, ~5,200 lines)

| file | contents |
|---|---|
| `FormalizedMathematics/Cubical/Interval.lean` | free De Morgan algebra, antichain-DNF decision procedure (`IVal.dnf`, `IVal.equiv`) |
| `FormalizedMathematics/Cubical/Syntax.lean` | terms, raw terms, substitution/shifting |
| `FormalizedMathematics/Cubical/Semantics.lean` | NbE evaluator (defunctionalized closures), **rule (R) = the transport constancy check in `vtransp`** (fresh-dimension instantiation + occurs check `usesLvl` — **read-back-exact**: mirrors `quote` clause by clause, so `usesLvl ℓ v = (ℓ ∈ FV(quote v))`; the paper's specified checker and the implemented checker are one and the same, see the paper's Checker-exactness theorem; a legacy non-instantiating closure walk was found unreachable and removed 2026-07-17), conversion `conv`/`convNe` with η for Π/Σ/Path |
| `FormalizedMathematics/Cubical/TypeCheck.lean` | bidirectional checker, Glue/`transpGlue`, HIT rules |

## Paper ↔ probe correspondence (`LibStrictness.lean`)

| paper (catalogue row / theorem) | probe(s) |
|---|---|
| connection reparametrizations (idem/invol/absorb/zero) | `strictConnIdemD`, `strictConnInvolD`, `strictConnAbsorbD`, `strictConnZeroD` |
| De Morgan duality | `strictDeMorganD` |
| path η / function η / Σ η | `strictPathEtaD`, `strictFunEtaD`, `strictSigEtaD` |
| `symm refl ≡ refl`, `symm ∘ symm ≡ id` | `strictSymmReflD`, `strictSymmSymmD` |
| `cong` laws (refl, id, ∘ symm) | `strictCongReflD`, `strictCongIdD`, `strictCongSymmD` |
| transport along constant families (incl. value-level constancy, at 𝒰, path families) | `strictTranspConstD`, `strictTranspValueConstD`, `strictTranspUD`, `strictTranspPathFamD` |
| **J d refl ≡ d (main)** | `strictJReflD` |
| `transport (ua idEquiv) ≡ id` | `strictTranspUaIdD` |
| NEGATIVE: `trans refl refl ≢ refl` (no hcomp-regularity) | `#guard !(okD …)`, LibStrictness.lean:198 |
| NEGATIVE: cong/symm over trans | `#guard !(okD …)`, lines 207, 234, 293 |
| NEGATIVE: `⟨i⟩p(i∧¬i) ≢ refl`, `⟨i⟩p(i∨¬i) ≢ refl` (reparametrization coherence, ⇒) | `#guard !(okD …)`, lines 351, 358 |
| switchover convergence at Π / Σ / dependent Σ / argument-wise HIT constructors incl. the path constructor `merid` (Lemma, paper §Switchover) | `swPiD`, `swSigD`, `swSigDepD`, `swListD`, `swSuspMeridD` (LibSwitchover.lean) |
| **NEGATIVE: path switchover contractum `⟨j⟩hcomp[j=0↦a,j=1↦b](p@j) ≢ p` (No-go Theorem, machine witness)** | `#guard !(okD …)` in LibSwitchover.lean §4; control probe `swPathContractumD` |

Positive rows: the probe is a `refl`-witness (`.plam`) at the stated path
type, accepted by the checker ⟺ the equation is *algorithmic* (definitional);
the build enforces acceptance via `#guard probe.ok`. Negative rows: the
analogous witness is *rejected*, enforced via `#guard !(okD tm ty)`.

The transport-heavy library (`LibTower.lean`, `LibCoherence.lean`,
`LibCircleEM.lean`, …) exercises rule (R) throughout: untruncated
Eckmann–Hilton, Mac Lane pentagon, `π₁(S¹) ≅ ℤ` (winding), the groupoid
classifying-space HIT `BGpd` and its classification theorem.

## Differential testing

`Test/Golden.lean` + `FormalizedMathematics/Cubical/golden.txt`:
name-keyed fingerprints of the normal forms of every library definition
(~300). `golden check` validates a kernel change against the frozen
fingerprints; `golden gen` regenerates them.

## Scope statement

A kernel passing its test suite is *evidence*, not a proof, of its own
soundness. The metatheoretic claims are those of the paper
(Sections *Metatheory*, *Canonicity and decidability*); this artifact
witnesses the algorithmic behaviour (all catalogue rows, and
`J d refl ≡ d` end-to-end).

## Author

Ryota Shibusawa, Daiichi Institute of Technology —
r-shibusawa@daiichi-koudai.ac.jp

# cubical-strict-j

**A cubical type theory kernel in Lean 4 in which `J d refl ≡ d` holds definitionally** — the artifact for the paper *Evaluation-Time Constancy Inference for Transport in Cubical Type Theory*.

## 📄 The paper

- **[Paper PDF (`docs/paper/jrefl.pdf`)](docs/paper/jrefl.pdf)** — 38 pages, LMCS format
- LaTeX source: [`docs/paper/jrefl.tex`](docs/paper/jrefl.tex)
- Archived artifact snapshot: release `v1.0.0`, commit `6c5904b` — DOI [10.5281/zenodo.21405962](https://doi.org/10.5281/zenodo.21405962)
- Paper-to-probe correspondence table and artifact guide: [`ARTIFACT.md`](ARTIFACT.md)

## 📚 The paper series

Seventeen self-contained papers have been developed on this artifact; each is independently readable, with all machine-checked claims anchored in this repository.

| # | paper (PDF) | one line |
|---|---|---|
| 1 | [Evaluation-time constancy inference for transport](docs/paper/jrefl.pdf) *(superseded — see the consolidated manuscripts below)* | definitional `J d refl ≡ d` in a CCHM kernel: a no-go theorem, an admissible operational rule, canonicity on the core |
| 2 | [The strict layer of generic cells is a wedge of De Morgan spheres](docs/paperC/strictlayer.pdf) *(superseded — see the consolidated manuscripts below)* | classification of the judgmental layer of cubical computads |
| 3 | [Generic cellular contexts realize their cube presheaves on the nose](docs/paperD/realization.pdf) *(superseded — see the consolidated manuscripts below)* | attachment equations are definitional; the kernel decides presheaf equality |
| 4 | [De Morgan convexity and the strict–weak comparison](docs/paperE/convexity.pdf) *(superseded — see the consolidated manuscripts below)* | strict fillers are non-unique but strictly contractible; the third median term is the price of no-LEM |
| 5 | [Word problems across the strict–weak boundary](docs/paperF/wordproblems.pdf) *(superseded — see the consolidated manuscripts below)* | the strict/weak boundary **is** the decidable/undecidable boundary; Sanov invariant at <1 ms per letter; RP² realized faithfully |
| 6 | [Boundary fibers in free De Morgan algebras](docs/paperG/dmfibers.pdf) *(superseded — see the consolidated manuscripts below)* | fibers are Boolean intervals over antichains of diagonal points; Sperner-extremal; census new to OEIS |
| 7 | [The strict layer of De Morgan cubical sets](docs/paperH/strictdm.pdf) *(algebraic part superseded — see below)* | the Karoubi envelope via projective De Morgan algebras; the defect formula; a coherence dichotomy |
| 8 | [The Kleene interpolation](docs/paperI/kleene.pdf) *(superseded — see the consolidated manuscripts below)* | boundary fibers across the subvarieties of De Morgan algebras: Kleene has exactly two non-singleton fibers in every dimension |
| 9 | [Natural strict fillers do not exist](docs/paperJ/nogo.pdf) *(superseded — see the consolidated manuscripts below)* | a three-line no-go theorem: no filler choice is substitution-natural; the median correction system is strictly contractible — the weak layer is categorically necessary |
| 10 | [Cubical models with reversal do not present spaces](docs/paperK/reversal.pdf) *(superseded — see the consolidated manuscript below)* | first complete proof of the 2018 folklore (De Morgan/Boolean) and first resolution of the Kleene case; the interval quotient by reversal is a K(ℤ/2,1) |
| 11 | [Reversal is unrepairable](docs/paperL/unrepairable.pdf) *(superseded — see the consolidated manuscript below)* | the hyperoctahedral-equivariant model structure exists but overshoots the test structure; no relatively elegant embedding exists; the folklore witness against the test comparison is void — "does CCHM present spaces?" is re-opened |
| 12 | [The join of two projective spaces](docs/paperM/isotropy.pdf) *(superseded — see the consolidated manuscript below)* | the upper bound W_type ⊆ W_test on any totally aspherical cube category; the element category of the Klein quotient of the square is RP^∞ ⋆ RP^∞; both structures agree on every isotropy quotient of the square — no quotient witness separates the localizers |
| 13 | [An explicit separation of the type and test model structures on De Morgan cubical sets](docs/consolidated/separation.pdf) *(superseded — merged into paper 15 below)* | **W_type ⊊ W_test**: an explicit map in W_test ∖ W_type, from a Klein quotient of the join □¹⋆□¹ to the Klein quotient of the square, built from the De Morgan median interpolation; the folklore expectation gets its first published proof, by a necessarily map-level witness |
| 14 | [The isotropy classification of the type and test model structures on De Morgan cubical sets in dimensions up to three](docs/consolidated/classification.pdf) | complete classification of all 98 subgroups H ≤ B₃: the two structures assign the same homotopy type to □³/H in 78 cases (coverings, contractions, median retractions, products) and are separated by an explicit map in 20 (collage certificates, block transfer, a homological obstruction) — including the full symmetric quotient □³/B₃ |
| 15 | [An explicit separation of the type and test model structures on De Morgan cubical sets, and their different contractible objects](docs/consolidated/sepobjects.pdf) | merges and supersedes paper 13, extended to the object level: the two natural homotopy theories on the site of cubical type theory disagree already about **which finite objects are contractible** — an explicit finite subdivided mapping cone is test-contractible but not type-contractible; self-contained (equivariant descent, sector pasting, first-exit induction; the collage formula is the only external ingredient) |
| 16 | [The phase diagram of cubical sites: connections, reversals, and the separation of the type and test model structures](docs/consolidated/phasediagram.pdf) | which interval operations produce separation: on every site with connections and no reversal, ALL isotropy quotients are contractible in both structures (no witness can exist — why the Dedekind question resists); on every standard site with reversal (De Morgan, Kleene, Boolean) the median-collage separation transfers uniformly, at maps and at finite objects — the site-dependence of the proofs is concentrated in two evaluations at unmixed points |
| 17 | [The isotropy landscape across cubical sites with reversal: rigidity, character realizability, and covering descent](docs/consolidated/landscape.pdf) | how the isotropy classification's proofs deform across the De Morgan, Kleene, and Boolean sites: a rigidity discriminant (twisted cells slide iff the strata-swap character vanishes; genuinely twisted cells are permanent, detected by test-side covering theory), a realizability divide (De Morgan is the exceptional site — its parity obstructions live on the mixed points that the Kleene inequality removes and Boolean XOR destroys), and a covering theory for uniform Kan replacements that descends separations along free towers — completing the Boolean and Kleene classifications in dimensions ≤ 3 with the same conclusions and provably different proofs |

Papers 2–12 cite paper 1 as the platform; papers 13–15 build on the consolidated test-comparison manuscript below (paper 15 is self-contained up to the standard collage formula); release-by-release DOIs are listed in [`ARTIFACT.md`](ARTIFACT.md).

**Consolidated manuscripts.** The papers of the series have been consolidated, in four groups (1+5; 2+3+4+9; 6+8 with the algebraic part of 7; 10–12), into substantially revised and corrected journal manuscripts — not concatenations: proofs were restructured, several were completed or corrected, and the papers' claims are reconciled inside each document:

- **[The test comparison for De Morgan cubical sets: reversal, equivariance, and the join of two projective spaces](docs/consolidated/testcomparison.pdf)** (27 pages; supersedes papers 10–12)
- **[Boundary fibers of free De Morgan and Kleene algebras: Boolean intervals, Sperner extremality, and Kalman's three grades](docs/consolidated/fibers.pdf)** (19 pages; supersedes papers 6 and 8, and the algebraic part of paper 7)
- **[Definitional transport in cubical type theory: constancy inference, canonicity, and the decidable–undecidable boundary](docs/consolidated/transport.pdf)** (47 pages; supersedes papers 1 and 5)
- **[The strict layer of cubical type theory: cellular realization, De Morgan convexity, and the impossibility of natural strict fillers](docs/consolidated/strictlayer.pdf)** (32 pages; supersedes papers 2, 3, 4, and 9)

The repository versions remain available as the archived machine-verification record and are **superseded** by the consolidated manuscripts; none of them is separately published or under journal review.

## What the paper shows

In cubical type theories the eliminator `J` does not compute definitionally on `refl`, because the transport primitive's constancy formula is fixed when a term is written. Re-detecting constancy at evaluation time is an old informal idea; the paper gives it a metatheory:

1. **A no-go theorem.** Adding the evaluation-time constancy rule *equationally* to the structural transport rules derives a constant-system `hcomp`-regularity principle — already at *path types*, before `Glue`. Naive equational formulations cannot work, and restricting the structural rules is not substitution-stable.
2. **An operational system that works.** Judgmental equality is defined as the algorithmic equality of a prioritized NbE strategy whose constancy check is specified representation-independently (the fresh dimension must not occur in the *read-back* of the family's value) — and implemented exactly by this kernel's `usesLvl`. The typed algorithmic equality is proved an admissible conversion relation, with termination and canonicity.
3. **An unconditional core.** For the `Glue`-free, universe-free fragment `Π, Σ, Path, ℕ` — enough to define `J` — the base normalization component is discharged in the paper, so **strict `J` is unconditional** there.

All concrete positive and negative conversion claims in the paper are machine-checked here: a successful build **is** the verification run (every claim is an elaboration-time `#guard`).

## Quick start

Requires the pinned Lean toolchain (`lean-toolchain`: 4.31.0); no external dependencies (no mathlib).

```sh
lake build                                                    # full library (~300 definitions)
lake build FormalizedMathematics.Cubical.LibStrictness        # strictness catalogue only
lake build FormalizedMathematics.Cubical.LibSwitchover        # switchover experiments only
```

## Layout

| path | contents |
|---|---|
| `FormalizedMathematics/Cubical/Interval.lean` | free De Morgan algebra, antichain-DNF decision procedure |
| `FormalizedMathematics/Cubical/Syntax.lean` | terms, raw surface syntax, substitution |
| `FormalizedMathematics/Cubical/Semantics.lean` | NbE evaluator; **rule (R) = the read-back-exact transport constancy check** (`vtransp` + `usesLvl`); conversion with η for Π/Σ/Path |
| `FormalizedMathematics/Cubical/TypeCheck.lean` | bidirectional type checker, `Glue`/`transpGlue`, HIT rules |
| `FormalizedMathematics/Cubical/LibStrictness.lean` | the strictness catalogue (incl. the `J d refl ≡ d` witness `strictJReflD`) |
| `FormalizedMathematics/Cubical/LibSwitchover.lean` | the switchover experiments behind the no-go theorem |
| `FormalizedMathematics/Cubical/Lib*.lean` | object-language library: `π₁(S¹) ≅ ℤ` with computing winding numbers, untruncated Eckmann–Hilton and Mac Lane coherence, K(G,1), a groupoid classifying-space HIT, … |
| `Test/Golden.lean` + `Cubical/golden.txt` | differential-testing harness (normal-form fingerprints of the full library) |
| `docs/` | the paper and the supporting proof documents |

The kernel is self-contained and independent of Lean's own definitional equality: univalence *computes* (`transport (ua e) x ⟶ e.fst x`), and `π₁(S¹) ≅ ℤ` is proved inside the object language with winding numbers that actually evaluate.

## Also in this repository

Companion Lean 4 formalizations, all axiom-free (`#print axioms` verifiable): Voevodsky's univalence ⇒ function extensionality (`FormalizedMathematics/Hott/`), abstract incompleteness via Hilbert–Bernays–Löb (`Logic/`), and Lawvere's fixed-point theorem in a from-scratch CCC (`CategoryTheory/`).

## Citation

```bibtex
@software{shibusawa_cubical_strict_j_2026,
  author    = {Shibusawa, Ryota},
  title     = {cubical-strict-j: Evaluation-Time Constancy Inference for
               Transport in Cubical Type Theory (Lean 4 artifact)},
  year      = {2026},
  publisher = {Zenodo},
  version   = {v1.0.0},
  doi       = {10.5281/zenodo.21405962},
  url       = {https://github.com/r-shibusawa/cubical-strict-j}
}
```

## License

[Apache-2.0](LICENSE). Author: Ryota Shibusawa (Daiichi Institute of Technology).

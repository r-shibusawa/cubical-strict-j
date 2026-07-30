# cubical-strict-j

**A cubical type theory kernel in Lean 4 in which `J d refl ≡ d` holds definitionally** — the artifact for the paper *Evaluation-Time Constancy Inference for Transport in Cubical Type Theory*.

## 📄 The paper

- **[Paper PDF (`docs/paper/jrefl.pdf`)](docs/paper/jrefl.pdf)** — 38 pages, LMCS format
- LaTeX source: [`docs/paper/jrefl.tex`](docs/paper/jrefl.tex)
- Archived artifact snapshot: release `v1.0.0`, commit `6c5904b` — DOI [10.5281/zenodo.21405962](https://doi.org/10.5281/zenodo.21405962)
- Paper-to-probe correspondence table and artifact guide: [`ARTIFACT.md`](ARTIFACT.md)

## 📚 The paper series

Seven self-contained papers have been developed on this artifact; each is independently readable, with all machine-checked claims anchored in this repository.

| # | paper (PDF) | one line |
|---|---|---|
| 1 | [Evaluation-time constancy inference for transport](docs/paper/jrefl.pdf) | definitional `J d refl ≡ d` in a CCHM kernel: a no-go theorem, an admissible operational rule, canonicity on the core |
| 2 | [The strict layer of generic cells is a wedge of De Morgan spheres](docs/paperC/strictlayer.pdf) | classification of the judgmental layer of cubical computads |
| 3 | [Generic cellular contexts realize their cube presheaves on the nose](docs/paperD/realization.pdf) | attachment equations are definitional; the kernel decides presheaf equality |
| 4 | [De Morgan convexity and the strict–weak comparison](docs/paperE/convexity.pdf) | strict fillers are non-unique but strictly contractible; the third median term is the price of no-LEM |
| 5 | [Word problems across the strict–weak boundary](docs/paperF/wordproblems.pdf) | the strict/weak boundary **is** the decidable/undecidable boundary; Sanov invariant at <1 ms per letter; RP² realized faithfully |
| 6 | [Boundary fibers in free De Morgan algebras](docs/paperG/dmfibers.pdf) | fibers are Boolean intervals over antichains of diagonal points; Sperner-extremal; census new to OEIS |
| 7 | [The strict layer of De Morgan cubical sets](docs/paperH/strictdm.pdf) | the Karoubi envelope via projective De Morgan algebras; the defect formula; a coherence dichotomy |

Papers 2–7 cite paper 1 as the platform; release-by-release DOIs are listed in [`ARTIFACT.md`](ARTIFACT.md).

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

# Artifact: Evaluation-Time Constancy Inference for Transport in Cubical Type Theory

This repository is the artifact accompanying the paper
*Evaluation-Time Constancy Inference for Transport in Cubical Type Theory*
(`docs/paper/jrefl.tex`).

- Repository: <https://github.com/r-shibusawa/cubical-strict-j>
- Current snapshot: release `v1.10.0` (adds the paper
  `docs/paperK/reversal.{tex,pdf}` — cubical models with reversal
  do not present spaces: the interval quotient is a K(ℤ/2,1) —
  with the note `docs/ReversalQuotient.md` and the record
  `scripts/reversal.py`), archived at DOI
  [10.5281/zenodo.21704342](https://doi.org/10.5281/zenodo.21704342)
- Previous: release `v1.9.0` (the no-go paper), DOI
  [10.5281/zenodo.21697938](https://doi.org/10.5281/zenodo.21697938)
- Previous: release `v1.8.1` (Kleene paper revision), DOI
  [10.5281/zenodo.21695917](https://doi.org/10.5281/zenodo.21695917)
- Previous: release `v1.8.0` (the Kleene interpolation paper), DOI
  [10.5281/zenodo.21695778](https://doi.org/10.5281/zenodo.21695778)
- Previous: release `v1.7.0` (strict-layer paper), DOI
  [10.5281/zenodo.21695641](https://doi.org/10.5281/zenodo.21695641)
- Previous: release `v1.6.0` (De Morgan fiber paper + census), DOI
  [10.5281/zenodo.21695307](https://doi.org/10.5281/zenodo.21695307)
- Previous: release `v1.5.0` (word-problem suites + paper F), DOI
  [10.5281/zenodo.21669939](https://doi.org/10.5281/zenodo.21669939)
- Previous: release `v1.4.0` (De Morgan convexity suite + paper E),
  DOI
  [10.5281/zenodo.21639454](https://doi.org/10.5281/zenodo.21639454)
- Previous: release `v1.3.0` (generic-boundary and shared-edge
  suites + papers C/D), DOI
  [10.5281/zenodo.21638976](https://doi.org/10.5281/zenodo.21638976)
- Previous: release `v1.2.0` (dimension-2 reparametrization suite),
  DOI [10.5281/zenodo.21638543](https://doi.org/10.5281/zenodo.21638543)
- Paper snapshot: release `v1.1.0` (paper v14: non-substitutivity
  theorem, presentation impossibility, canonicity regained on the
  core), archived at DOI
  [10.5281/zenodo.21637898](https://doi.org/10.5281/zenodo.21637898)
- Pre-erratum snapshot: release `v1.0.0`, commit
  `6c5904be3f9bf8ec9138cda5bcb961b6a67f4feb`, archived at DOI
  [10.5281/zenodo.21405962](https://doi.org/10.5281/zenodo.21405962);
  `v1.1.0` is archived as a new version under the same Zenodo record
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
| **Non-substitutivity (second no-go): `t ≡ u` (structural instance), `tσ ≡ q` (collapse), yet `uσ ≢ q` and `tσ ≢ uσ`** | `nsStructuralD`, `nsCollapseD`, `nsResidueCtrlD` + two `#guard !(okD …)` (LibNonSubst.lean) |
| Dimension-2 reparametrization: DM² laws strict per coordinate (idem/invol/cross-absorption/De Morgan) | `sq2IdemD`, `sq2InvolD`, `sq2AbsorbD`, `sq2DeMorganD` (LibSquares.lean; proofs in `docs/ReparamCoherence2.md`) |
| Degenerate collapse: any endpoint coordinate (in the free DM algebra) kills the square; the degenerate class is one point | `sq2DegFstD`, `sq2DegSndD`, `sq2DegCrossD` |
| NEGATIVE: transposition `q(j)(i) ≢ q(i)(j)` (definitional shadow of weak Eckmann–Hilton); diagonal pair separated; dim-2 no-LEM `q(i∧¬i)(j) ≢ const` | `#guard !(okD …)` + controls (`sq2TransposeCtrlD`, `sq2DiagCtrlD`, `sq2LEMCtrlD`) |
| Multi-cell wedge: cross-cell degenerate collapse; head and spine-depth separation | `sqxDegD`, `sqxDepthCtrlD` + `#guard` negatives |
| De Morgan cube-category action is strictly functorial: unit (nested path η) and composition (= formula substitution) | `sqEtaD`, `sqCloneCompD`, `sqDiagCtrlD` |
| Generic-boundary square: attachment equations (faces ≡ prescribed edges, corners ≡ vertices, edge squares); De Morgan laws strict at dependent square types | `gbAttPD/QD/RD/SD`, `gbCornerD`, `gbEdgeSqD`, `gbEtaD`, `gbAbsorbD`, `gbAbsorbPerturbD` (LibGenBoundary.lean; notes in `docs/GenericBoundary.md`) |
| **Non-uniqueness of strict fillers: two distinct squares with the same boundary** | `gbFill1D`, `gbFill2D` + separation `#guard`; transposition as a cross-type operation: `gbTransposeCtrlD` |
| Shared-edge gluing: cross-cell face identification definitional; boundary-collapsed interiors of distinct cells pairwise separated | `seAttM1D/M2D`, `seGlueD`, `seS1CtrlD/S2CtrlD/SmCtrlD` + three `#guard` negatives (LibSharedEdge.lean) |
| **De Morgan interpolation: strict homotopy rel boundary between the two non-convertible fillers; naive interpolant FAILS (no-LEM)** | `mixInterpD`, `mixInterpCtrlD` + separation and naive-failure `#guard`s (LibMixed.lean; notes in `docs/DeMorganConvexity.md`, `docs/MixedLayer.md`) |
| Cross-cell zig-zag: both interiors deform strictly onto the shared-edge square | `mixDeformQ1D`, `mixDeformQ2D` |
| **(†) is propositional: the canonical filler connects the constant-tube composite to its base, rel boundary** | `mixFillD` + definitional-separation `#guard` |
| Relator compilation over the presentation context of ⟨x∣x²⟩: `x⁴ ≡prop refl` from two relator uses + a unit law | `wordX4D`, `wordRelD` (LibWord.lean; notes in `docs/WordProblem.md`) |
| **Sanov invariant (proof-free carrier): right-multiplication equivalences of ℤ⁴, the SL₂(ℤ) cover of the figure eight, matrix winding** | `addCancelD`, `addCancelND`, `sanovLD/RD`, `helixSLD`, `windSLD` (LibSanov.lean); timings + machine-compared matrix values: `lake exe sanov` (generators 8 ms; iterated per-letter transport < 1 ms; L·R vs R·L separated; commutator ≠ I) |
| **Internal presentation complex: RP² = cofib(deg2); the relator cell realized; generic derivations transfer by instantiation** | `deg2D`, `deg2LoopD`, `rp2D`, `rp2AttachD`, `rp2RelSqD`, `rp2RelD`, `wordX4RP2D`, `wordRelRP2D` + two definitional-separation `#guard`s (LibPresent.lean) |
| ua-coherence for the double cover: `ua not ⬝ ua not ≡prop refl` | `uaNotNotD` (LibPresent.lean; heavy guard, ~110 s) |
| **Double cover of RP²: winding computes (refl ↦ true, x ↦ false); the presentation ⟨x∣x²⟩ realized faithfully (x² = 1, x ≠ 1)** | `covS1D`, `covRP2D`, `windRP2D`, `rp2LoopNontrivD`, `rp2NotSetD` (LibCover.lean) |
| Boundary fibers in free De Morgan algebras (paper `docs/paperG`): Boolean-interval structure, Sperner-extremal fibers, sphere filling, boundary↔antichain classification, median cylinder — full census n ≤ 3, construction check n = 4 | `scripts/dmfiber.py`, `scripts/dmfiber3.py`, `scripts/dmfiber_boundaries.py` (Python; notes in `docs/DMFiber.md`; the type-theoretic counterparts are `mixInterpD`/`mixFillD` and the strictness suites) |
| The strict layer of De Morgan cubical sets (paper `docs/paperH`): non-idempotent-completeness, Karoubi envelope via projective De Morgan algebras (Bova–Cabrer), the defect antichain formula, the coherence dichotomy — verified on all 7,828,354 elements of DM(3) | `scripts/dmdefect.py` (record; notes in `docs/StrictLayer.md`) |
| The Kleene interpolation (paper `docs/paperI`): KL(n) = monotone functions on the unmixed poset (counts 6, 84, 43918 = Berman–Mukaidono); fibers ≤ 2 with exactly two non-singleton fibers at every n; B_K(n) = FK(n) − 2 (= OEIS A007154, newly interpreted); defect/coherence ported with polar exceptional locus | `scripts/kleene.py` (record; notes in `docs/Kleene.md`) |
| The no-go theorem (paper `docs/paperJ`): no natural section of the boundary-fiber correspondence (three-line proof from m = ¬x∧y∧¬y; 142 forced conflicts; exhaustive 2^38·4^16 search); the median correction system is strictly contractible (fiber-coordinate formula; iterated median cylinder with exact faces) | `scripts/nogo.py` (record; notes in `docs/NoGo.md`) |
| The reversal quotient (paper `docs/paperK`): freeness of the reversal action (0 self-dual cells, m ≤ 3, DM and KL); no symmetric rescue terms; reachability census (60/32/8 symmetric squares, [x]-component isolated in all three theories); sheet-transport fibration — L is a K(ℤ/2,1) with contractible realization | `scripts/reversal.py` (record; notes in `docs/ReversalQuotient.md`) |

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

Ryota Shibusawa, Daiichi Institute of Technology.
(Contact: see the paper, `docs/paper/jrefl.pdf`.)

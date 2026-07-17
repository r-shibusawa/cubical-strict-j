# 投稿手順と記入内容(コピー&ペースト用)

## A. arXiv 投稿

### A-1. アカウント作成(初回のみ)
1. https://arxiv.org/user/register を開く
2. **メール: r-shibusawa@daiichi-koudai.ac.jp**(大学メール — 学術所属の
   確認が円滑になります)で登録し、確認メールのリンクをクリック
3. 所属: Daiichi Institute of Technology

### A-2. 投稿(https://arxiv.org/submit)
- **Archive/Category**: Computer Science → **cs.LO** (Logic in Computer
  Science)。cross-list に **math.LO** を追加(任意・推奨)
- 初回投稿では cs.LO の **endorsement** を求められる場合があります。
  その場合は表示される指示に従ってください(大学メールなら自動承認の
  ことも多い; 必要なら分野の知人研究者に endorsement を依頼)
- **License**: 「CC BY 4.0」を選択(LMCS はダイアモンド OA / CC-BY 系
  なので互換で、最も無難)
- **Files**: `docs/paper/jrefl-arxiv.tar.gz` をアップロード
  (jrefl.tex + lmcs.cls のみ。arXiv 側で自動コンパイルされます —
  processing 画面で PDF が 38 頁で生成されることを確認)

### A-3. メタデータ(コピー&ペースト)

**Title**:
```
Evaluation-Time Constancy Inference for Transport in Cubical Type Theory
```

**Authors**:
```
Ryota Shibusawa (Daiichi Institute of Technology)
```

**Abstract**(arXiv 用プレーンテキスト版):
```
The eliminator J of cubical type theories does not compute
definitionally on refl: the transport primitive's constancy formula is
fixed when a term is written, so constancy arising later by
substitution is never used. Re-detecting it at evaluation time is an
old informal idea; this paper gives it a metatheory. First, a no-go
theorem: combining the evaluation-time rule equationally with the
structural transport rules derives a constant-system
hcomp-regularity principle -- closely related to regularity principles
known to fail in standard cubical-sets models -- already at path
types, before Glue; and restricting the structural rules to
non-constant families is not substitution-stable. Second, the positive
system: judgmental equality is defined as the algorithmic equality of
a prioritized normalization-by-evaluation strategy whose constancy
check is specified representation-independently (the fresh dimension
must not occur in the read-back of the family's value) and implemented
exactly; we prove the check semantically sound and the typed
algorithmic equality an admissible conversion relation -- equivalence,
congruence, weakening, substitution, context conversion, type
preservation -- with termination and canonicity relative to an
explicitly delimited base component, which we discharge for a
Glue-free, universe-free core fragment: there, including for
J d refl = d itself, the results are unconditional. All concrete
positive and negative object-language conversion witnesses, including
the switchover experiments behind the no-go theorem, are
machine-checked in a self-contained Lean 4 kernel; the metatheory
itself is pen-and-paper.
```

**Comments**:
```
38 pages. Artifact: https://github.com/r-shibusawa/cubical-strict-j
(release v1.0.0, commit 6c5904b), archived at
https://doi.org/10.5281/zenodo.21405962
```

- Submit を押すと通常 **1–2 営業日**で announce され、arXiv ID
  (例: 2607.XXXXX)が確定します。

## B. LMCS 投稿(arXiv announce 後)

1. https://lmcs.episciences.org → 右上 Log in(ORCID または
   episciences アカウントを作成; メールは大学メール推奨)
2. 「Submit an article」→ **arXiv ID を入力**(LMCS は arXiv 上の版を
   査読する方式。episciences が自動でメタデータを取得します)
3. Sections: 「Type theory and constructive mathematics」系の
   セクションを選択(表示される選択肢から最も近いもの)
4. カバーレター(下記をコピー&ペースト):

```
Dear Editors,

Please consider the enclosed submission "Evaluation-Time Constancy
Inference for Transport in Cubical Type Theory" for publication in
Logical Methods in Computer Science.

The paper studies a long-standing informal idea: making the cubical
eliminator J compute definitionally on refl by re-detecting transport
constancy at evaluation time. Its two main contributions are (1) a
no-go theorem showing that any equational combination of the
evaluation-time rule with the structural transport rules derives a
constant-system hcomp-regularity principle -- locating the obstruction
at path types, before Glue, and explaining why naive formulations
cannot work -- and (2) the metatheory of an operational formulation
that does work: a prioritized normalization-by-evaluation strategy
with a representation-independent constancy-check specification, for
which we prove admissibility of the induced typed algorithmic
equality, termination, and canonicity. For a Glue-free, universe-free
core fragment sufficient to define J, the base normalization component
is discharged in the paper, making strict J unconditional there; for
the full univalent calculus the results are stated relative to an
explicitly delimited base component. All object-language conversion
claims are machine-checked in a self-contained Lean 4 kernel, publicly
archived (GitHub: r-shibusawa/cubical-strict-j, v1.0.0; DOI:
10.5281/zenodo.21405962).

The paper is not under consideration elsewhere. Given the subject, we
would welcome reviewers with expertise in cubical type theory and the
metatheory of normalization by evaluation.

Sincerely,
Ryota Shibusawa
Daiichi Institute of Technology
r-shibusawa@daiichi-koudai.ac.jp
```

5. 投稿後、editorial board による査読者割当 → 査読(通常数か月)。

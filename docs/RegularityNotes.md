# Regularity ノート — 値レベル constancy 規則の研究課題

作成: 2026-07-16。厳密性カタログ(LibStrictness.lean)から浮上した
**論文級候補の発見**の精密な記録と、定理化までの分析計画。

## 1. 発見(機械検証済みの事実)

本カーネルの transp 規則は「族の**評価後の値**が輸送次元を含まなければ
恒等」(値レベル constancy = 標準的な構文的側条件 `i ∉ A` の
**conversion 閉包**)。この帰結として、以下が**定義的に**成立する:

| 事実 | cubical Agda |
|---|---|
| `J d refl ≐ d` | **不成立**(transportRefl は命題的) |
| `transport (⟨i⟩A) x ≐ x`(定数族、φ=i0 相当) | 不成立 |
| `transp (⟨i⟩U) X ≐ X` | 不成立 |
| 構文的に i を含むが値が定数の族(`p@(i∧0)`)でも発火 | 不成立 |
| `transport (ua idEquiv) x ≐ x`(transpGlue 計算による) | 不成立(命題的) |

「cubical 型理論では J が refl 上で計算しない」は分野の有名な難点であり、
これを**定義的に回復する規則の健全性が立てば、論文級の結果**になる。

## 2. 定理候補

**候補定理 R**: 「CCHM + 正規形-regularity transp 規則は健全
(モデルを持つ/canonicity を保つ)であり、J-refl を定義的に検証する」

**候補定理 C**(独立・より安全): 再パラメータ化コヒーレンス —
`⟨i⟩ p(φ(i)) ≐ ⟨i⟩ p(ψ(i)) ⟺ φ ≡ ψ`(自由 De Morgan 代数)。
papp-η + DNF 決定手続きから紙上証明が届く射程。カタログの
区間層 probe 群(冪等・対合・吸収・零)が実証。

## 3. 危険地帯(候補 R の生死を分ける論点)

- **CCHM regularity バグの先行事例**: CCHM は当初 composition の
  regularity を主張したが、Sattler が宇宙(Glue)の合成で誤りを発見。
  Swan の結果により、**path-equal-to-constant** な族への regularity は
  標準 cubical 集合モデルで不成立。
- **本規則との差分(希望の根拠)**: 本規則は path-equality ではなく
  **判断的(正規形)定数性**にのみ発火する。構文的側条件
  `i ∉ A ⟹ transp^i A a = a` は CCHM の transp の型別定義から
  各節で成立するはず(要・節ごと検証)であり、本規則はその
  conversion 閉包に過ぎない可能性が高い。
- **要検証の急所**: Glue/宇宙の節。値レベルで i-自由な Glue 族に対し
  transpGlue が恒等に簡約するか(実装では unglue∘glue の往復)。
  モデル側: 判断的定数な Glue 線に沿う transp がモデルで恒等か。
  **hcomp には本規則は無い**(trans p refl ≐ p は否 — カタログ済み)
  ため、Sattler の反例(composition/filling の regularity)とは
  当たる場所が異なる可能性が高い。

## 4. 分析計画(定理化まで)

1. **節ごと検証(紙上)**: CCHM 論文の transp 定義(Π/Σ/Path/Glue/U/
   自然数/HIT)各節について「A が i-自由 ⟹ transp = id」を確認。
   本カーネルの vtransp 実装と突き合わせ。
2. **canonicity 論証の下書き**: 値レベル規則が簡約として合流的・
   正規化を壊さないこと(NbE 実装がその実証)。
3. **モデル論**: 判断的 regularity(transp のみ、hcomp なし)が
   cubical 集合で成立するかの文献確認(Swan の反例の正確な主張の
   再読が必須)+ 成立しない場合の代替モデル(regular な変種:
   Orton–Pitts 系、または syntactic model)。
4. **主張の最終形の調整**: モデルが立たない場合でも
   「J-refl を定義的に持つ cubical 型理論の変種の提示 + 一貫性の
   syntactic 論証 + 実装」で論文は成立し得る(主張を弱める)。

## 5. 文献(要精読)

- Swan, "Separating Path and Identity Types in Presheaf Models" /
  regularity 関連の note
- Sattler の CCHM regularity 指摘(CCHM 論文の後日談)
- Orton–Pitts, "Axioms for Modelling Cubical Type Theory in a Topos"
- Cavallo–Harper 系(ABCFHL)の transp φ 側条件の扱い
- Coquand らの variations(regularity を持つ変種の有無)

## 6. 現状の位置づけ(誠実な要約)

- **発見 = 論文級候補**: 「正規形 regularity で J-refl が定義的」は
  鋭く定式化された新規のメタ理論的主張で、機械的実証(カタログ)と
  作動する実装を伴う。
- **未達 = 定理**: 健全性分析(§4)が完了するまで定理ではない。
  先行の regularity バグが示す通り、ここは慎重さが本体。
- 候補 C(再パラメータ化コヒーレンス)は先に小定理として
  紙上証明を完成できる見込みが高い。

---

## 7. vtransp 節ごと監査(2026-07-16 実施)— 規則が「追加公理」となる場所の特定

| 型形成子(族の generic 値) | i-自由族での恒等性の由来 |
|---|---|
| nat / int / unit / empty / S¹ / torus / U | **無条件に恒等**(節が `a` を返す)— 自明に regular |
| Π / Σ / PathP | 構造的再帰(派生閉包の副族も i-自由)→ 再帰的に恒等 + 関数 η。**再帰の葉が下の行に落ちる** |
| Glue | transpGlue は計算する(ua idEquiv の probe が実証)が、i-自由 Glue はトップの constancy が先に発火 |
| pushout / em1 / list / quot / trunc / susp / sum | 点・セル別に副族へ再帰(同上) |
| **中立型族(`.vne`)** | **計算では stuck** — `vneAt (.transp fam a)`。恒等は constancy ショートカット**のみ**から来る。**ここが規則の本体** |

**結論**: 本規則が真に追加しているのは「**中立(および再帰の途中で中立に遭遇する)i-自由族に対する transp = id**」。

## 8. 決定的な再定式化: 「評価時 φ-推論」

ABCFHL/cubical Agda の transp は明示的な定数性式 φ を持ち、
**`transp A i1 u = u` は既に標準理論の健全な規則**である。J-refl が
Agda で計算しない理由は、**φ が定義時に固定される**(J の定義内の
transp は φ = i0 のまま)ため — refl を代入しても φ は再推論されない。

**本カーネルの規則の正体**: φ を**評価時に再推論**する —
「族の正規形が i-自由なら φ := i1 とみなす」。

したがって候補定理 R は**モデル構築問題ではなく可容性(admissibility)
問題**に帰着する:

> **候補定理 R'(鋭化)**: 簡約規則
> 「`transpⁱ A u ⟶ u` if `i ∉ nf(A)`」
> は cubical 型理論(ABCFHL 型の提示)において可容である
> (subject reduction・合流・canonicity を保つ)。系: J-refl が定義的。

**証明戦略の心臓 — 代入安定性補題**:
`i` は transp に束縛されるため、外側文脈の代入 σ の値は `i` を含み得ない
(捕獲なし)。よって `nf(A)` が i-自由なら `nf(Aσ) = nf(nf(A)σ)` も
i-自由 — 側条件は代入で安定。等式自体は φ=i1 規則の instance で健全。
型付けも整合(i-自由なら A(0) = A(1))。

**Swan/Sattler との非衝突(明確化)**: 彼らの否定的結果は
(a) hcomp/filling の regularity、(b) **path-equal**-to-constant
(命題的)regularity に関するもの。本規則は (a) を含まず
(`trans p refl ≐ p` は否 — probe 済み)、(b) でなく**判断的**
(正規形)定数性のみ。衝突する場所がない。

## 9. 現状評価の更新

- 候補 R → **R'**: 「モデル論的に危険な主張」から
  「**明確な証明戦略を持つ可容性定理**」へ格上げ。
  残る作業: (1) 代入安定性補題の精密な紙上証明(de Bruijn/表示的の
  どちらかで)、(2) 合流(constancy 発火と通常簡約の可換性)、
  (3) canonicity(本 NbE 実装がその構成的証拠 — quote∘eval の
  正規形が規則を吸収済み)、(4) hcomp との相互作用の無害性
  (hcomp 側に規則が無いことの確認 = 済み)。
- 実装的裏付け: 300 定義 + 全ガードが本規則込みで一貫して稼働
  (矛盾の兆候なし)、golden により回帰も監視下。
- **論文の主張形(案)**: "Evaluation-time constancy inference gives
  cubical type theory a definitional J-refl" — 有名な難点への
  直接の回答 + 実装 + 機械検証されたカタログ。

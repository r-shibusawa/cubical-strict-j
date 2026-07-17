# 論文執筆メモ(Paper Notes)

作成: 2026-07-16。現時点での新規性評価と執筆計画の記録。
執筆着手は保留中 — 着手時にこのメモから再開する。

---

## 1. 率直な新規性評価(結論)

**純数学としての「新定理」はほぼ無い**(証明した定理は数学的に既知)。
新規性は以下の 3 カテゴリにある:

- (a) **形式化・証明技法**(非切り詰めコヒーレンスの接続のみ導出、BGpd 経路)
- (b) **システム/カーネル工学**(Lean 4 上の CCHM カーネル、golden 差分テスト、レベルスタンプ)
- (c) **実証的知見**(Lean 4 ランタイムの落とし穴カタログ、負の結果込み)

## 2. 既知性の文献照合結果(2026-07-16 実施)

| 本プロジェクトの結果 | 先行 |
|---|---|
| Eckmann–Hilton、五角形/三角形(道の合成) | cubical Agda 標準ライブラリ(GroupoidLaws 等)に形式化あり |
| K(G,1) / delooping | 活発な既存分野。Champin–Mimram–Salou (FSCD 2024)、Wärn 等。**いずれも群・基点付き連結が対象** |
| 亜群 ≃ 1-型 / groupoid quotient | **Veltri–van der Weide (LMCS 2021)** が UniMath/Coq で形式化済み(HIT なし・計算則なしの環境)。理論基盤は Ahrens–Kapulkin–Shulman(Rezk completion) |

文献 URL:
- Delooping Generated Groups in HoTT (FSCD 2024): https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2024.6
- Constructing HITs as Groupoid Quotients (Veltri–van der Weide, LMCS 2021): https://arxiv.org/abs/2002.08150
- Univalent categories and the Rezk completion (AKS): https://arxiv.org/pdf/1303.0584
- Delooping presented groups in HoTT: https://arxiv.org/pdf/2405.03264
- Higher Schreier theory in cubical Agda (JSL): https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/higher-schreier-theory-in-cubical-agda/C3D0E95550689C21D11A18E0F531D5DE

## 3. 論文候補 A(最有力): システム+方法論論文(ITP/CPP 級)

**軸**: 「正しい普遍性を持つ HIT をカーネルプリミティブとして足すと、分類定理が軽くなる」

主張できる新規性:
1. **BGpd(一般亜群 EM HIT)を計算則付きカーネルプリミティブとして実装し、
   `BGpd(Π₁A) ≃ A` を基点・連結性なしで完全機械検証**(軽量インラインガード)。
   - 対比 1: Veltri–van der Weide は計算則のない環境での公理的/構成的扱い。
   - 対比 2: delooping 文献は群・基点付き連結限定。
   - 対比 3(最も強い): **同一コードベース内の実測比較** —
     基点連結版 homotopyHyp1(encode–decode 経由)は検証が時間級で保留のまま、
     より一般的な BGpd 版は余単位が点・射で refl になり encode–decode を丸ごと
     回避して軽量に閉じた。「HIT の普遍性設計が証明コストを桁で変える」実証。
2. **golden 差分テストによるカーネル進化の安全化**(完全な事例研究):
   - sealed 実験の失敗 = 静かな不健全化の実例(force 規約の非普遍性)
   - 名前キー指紋照合(299 定義)→ 挙動保存の機械的証明
   - フィールドリファクタ(lb スタンプ)を golden 保護下で完遂した記録
3. **Lean 4 での評価器実装の実証的知見カタログ**(再現手順つき、負の結果込み):
   - implemented_by は宣言直付け必須(後付け attribute は不発)
   - 純モデル定数化 → LCNF 畳み込み → opaque 必須
   - 閉じた適用の once-cell 抽出(never_extract で防げないケース、引数の __redArg 削除)
   - initialize IO.Ref への格納 → lean_mark_mt の壁(素朴なグローバルメモ表は機能しない)
   - unsafeBaseIO 内の modify への計算浮動 → 自己デッドロック(スクラッチ ref /
     if-分岐強制イディオム)
   - capp メモ化の負の結果(ヒット率不足で逆効果、実測)

## 4. 論文候補 B: Proof Pearl(CPP 級、短編)

**軸**: 「接続のみによる非切り詰めコヒーレンス」

内容:
- squareExchange 原理(構文的正方形の境界交換、動く中点 = 反対角線)
- 動く中点イディオム(assocConn = フィラー2本の合成)
- 連言面トリック((l=0)∧(m=1) 面による片側出現セル)
- 箱蓋論法(全4辺を恒真面で崩壊、hfill を壁に)
- これらによる 五角形/三角形/EH の一様導出
- **定義的厳密性定理群**(cubical 計算の見どころ):
  - transReflR refl ≐ transReflL refl(refl 証明)
  - 基本亜群の頂点群 ≐ ループ群(refl 証明)
  - cong の厳密関手性 cong(g∘f) ≐ cong g ∘ cong f(refl 証明)
  - Ωⁿ 関手の全レベル厳密関手法則(refl 証明)
- カーネル支援: normCof 正準化、resolveFace の DNF 選言肢検査

**採否を分ける未確認事項**: cubical Agda の pentagonIdentity
(Cubical.Foundations.GroupoidLaws)の証明技法と本質的に異なるか。
執筆前に必ず精査すること。

## 5. 論文化前の必須作業(誠実さの条件)

1. **検証状態の峻別**(現状、下表):

   | 結果 | 検証状態 |
   |---|---|
   | コヒーレンス章(EH・三角形・五角形・全補題) | 完全検証(軽量ガード) |
   | ω-亜群タワー(6段 × n=0..3、Ω-関手、可換モノイド) | 完全検証 |
   | 亜群章(fundGpd 一式、refl 定理 2 本) | 完全検証 |
   | **BGpd + 分類定理 bgFundEquiv/bgFundIs** | **完全検証** |
   | π₁(S¹)≅ℤ、ΩS¹≡ℤ、T²、F₂ 基盤、K(G,1) 構成 | 概ね検証済(一部ネイティブ) |
   | homotopyHyp1(基点連結版) | 構成済・最終検証保留 |
   | S¹≃K(ℤ,1) の往復(toFrom/fromTo)・s1EquivEM | 構成済・最終検証保留 |
   | π₁(S¹∨S¹)=F₂(decodeAll 以降) | 構成済・最終検証保留 |

   → 論文に含めるならネイティブ完走が必要。さもなくば明示的に除外するか
   「constructed, verification pending」と正直に記載。
   完全検証済みセットだけで A/B は成立する。

2. **自作カーネルの信頼性の位置づけ**: 健全性は証明していない。
   「tested, not verified」と正直に書く(golden 299 + 全ガードが実証的裏付け)。

3. **文献精査の残り**:
   - BGpd の「cubical プリミティブ+計算則+無連結分類」の先行有無の確定
   - cubical Agda GroupoidLaws / EckmannHilton の技法比較(候補 B の生命線)
   - agda-unimath の concrete groups / 亜群まわりの確認

## 6. 推奨実行順(着手時)

1. 文献精査の残り(§5.3)を完了 → B の採否判定
2. A のアウトライン作成(構成: intro / kernel 概要 / BGpd 実装 / 分類定理と
   homotopyHyp1 対比 / golden 方法論 / Lean 4 知見 / related work)
3. 保留中の重い検証(§5.1 の下 3 行)のネイティブ再挑戦は A の
   「対比 3」を強化するため価値あり(完走すれば「両方検証済みでコスト比較」、
   完走しなくても「一方は N 時間で未完」という実測として使える)
4. アーティファクト整備: リポジトリの再現手順、golden の使い方、
   ガード実行時間の一覧表

## 7. 素材の所在

- 全定理・技法・教訓の一次記録: `HANDOFF.md`(時系列、最も詳細)
- 成果の対外向け記述: `docs/ProjectResults_{EN,JA}.tex`(§コヒーレンス、
  §ホモトピー仮説、§BGpd の各節が論文の素地)
- カーネル実装: `FormalizedMathematics/Cubical/`(Semantics/TypeCheck が本体)
- 差分ハーネス: `Test/Golden.lean` + `FormalizedMathematics/Cubical/golden.txt`
- Lean 4 知見の一次記録: HANDOFF の 2026-07-12〜15 の各エントリ

---

## 8. 新定理の可能性(2026-07-16 評価)

**結論**: 既知定理の形式化を続けるだけでは新定理の可能性は低い。ただし
方向を変えれば、真に新しい定理(主にメタ定理)が狙える具体的ターゲットが
2〜3 個ある。

### ターゲット 1: 「cubical 型は弱 ω-亜群」の cubical 固有版
(実現可能性: 中〜高、新規性: 中)

- van den Berg–Garner (2011) の MLTT 版に対し、CCHM 固有版はおそらく未確立。
- 内容が変わる理由: cubical では MLTT で不成立の**定義的厳密性**が多数成立
  (transReflRRefl ≐、cong 厳密関手性、Ωⁿ 全レベル厳密、正方形交換)。
- 定理形: 「cubical 型は、方向・次元 X, Y, Z で厳密化された弱 ω-亜群を成す」
  — 厳密化の正確な特定が新規内容。
- 既存資産: ω-亜群タワー(6段 × 全レベル + 厳密 Ω-関手)が定理の実証 3 割。
- **要照合**: Allioux–Finster–Sozeau "Types are internal ∞-groupoids"
  (LICS 2021) 系との差分。

### ターゲット 2: 接続代数のコヒーレンス定理
(実現可能性: 中、新規性: 高)

- squareExchange 原理は既に一様メタ補題。一般化目標:
  「接続・結合子・単位子から組んだ平行 2-セルは常に等しい」という
  cubical 原始演算に対する Mac Lane 型構文的コヒーレンス定理。
- 動く中点・連言面・箱蓋の技法群は、接続式の**正規形理論**の存在を示唆。
- 「コヒーレンスの公理化」目標に最直結。

### ターゲット 3(現状低): cubical 評価による新不変量計算
- Brunerie 数型の路線。性能の壁(hash-consing 前提)により保留。

### 非ターゲット: semi-simplicial types / 完全なホモトピー仮説への直接寄与
- 15 年開いている障害は本プラットフォームが解消する種類のものではない。

### 方法論の注意
- ターゲット 1・2 は同一作業の二面: 定義的厳密性の体系的カタログ化 →
  正規形理論 → 定理化。
- 実装での観察は「証拠と実験装置」。定理の成立主張は**実装非依存の
  紙上メタ証明**まで持ち上げて初めて確定する。

## 9. 研究計画: 厳密性カタログ(第一歩、実行中)

**目的**: このカーネル(= CCHM の一実装)で何が定義的に成立するかの
網羅的・機械検証付きカタログを作り、ターゲット 1 の「厳密化の特定」と
ターゲット 2 の「正規形理論」の経験的基盤とする。

**設計**(`FormalizedMathematics/Cubical/LibStrictness.lean`):
- 各 probe = LibDef(tm = インライン refl/plam-refl)。guard 通過 ⟺ 定義的。
- **負の probe も第一級**: `#guard !(ok? ...)` で非定義性を機械的に記録
  (弱さが本質的な箇所の特定 — 定理の「弱い部分」の内容)。
- カテゴリ:
  1. 単位律: trans refl refl ≐ refl?(既知: 否)/ transReflR refl ≐
     transReflL refl(既知: 是)
  2. symm: symm refl ≐ refl / symm∘symm ≐ id(既知: 是)/
     symm(p⬝q) ≐ symm q ⬝ symm p?
  3. cong: cong id ≐ id(path-η 依存)/ cong f refl ≐ refl /
     cong(g∘f) ≐ cong g∘cong f(是)/ cong f (symm p) ≐ symm(cong f p)? /
     cong f (p⬝q) vs ⬝(既知: 否 — congTrans は J 要)
  4. transport: 定数族 ≐ id(是: constancy 規則)/ ua 順・逆・合成輸送
     (是: 実測済み)
  5. 接続の対角律: ⟨i⟩p(i∧i) ≐ p 等(De Morgan 正規形依存)
  6. HIT 計算則の厳密性: 各再帰子・除去子の点/セル計算(bgrec 系は是)
  7. 高次: 正方形交換の定義的インスタンス、whisker の定義性
- 出力: HANDOFF + 本メモに「是/否」表として集約 → パターンを定理候補
  として抽出(例: 「区間代数の正規形で吸収される法則は定義的」という
  予想の定式化)。

**その後の道筋**:
1. カタログから厳密性の特徴付け予想を抽出
2. 予想の紙上証明(カーネルの conv/正規形の定義に沿ったメタ証明)
3. ターゲット 1: vdBG 構成を cubical 化し、厳密部分をカタログの
   定理で置換
4. ターゲット 2: 接続式の正規形定理(De Morgan DNF + papp 簡約)として
   定式化を試みる

## 10. 厳密性カタログ第1弾の結果(2026-07-16、LibStrictness.lean)

| 法則 | 定義的? |
|---|---|
| 区間正規形系(i∧i、¬¬i、吸収、i∧0) | 是 |
| path-η | 是 |
| symm refl / symm∘symm | 是 |
| cong: refl / id / symm-交換 / 合成の厳密関手性 | 是 |
| transp 定数族(constancy) | 是 |
| **J d refl ≐ d(値レベル regularity)** | **是** |
| trans refl refl | 否 |
| cong の trans-分配 | 否 |
| symm の trans-反分配 | 否 |

**最重要発見: J-refl が定義的**(cubical Agda では否)。本カーネルの
transp constancy 規則(値レベル occurs-check)が regularity として作用。
- 研究機会: 「regularity 付き CCHM の定義的等式構造」の特徴付け
- **健全性の要注意点**: full regularity は標準 cubical 集合モデルで
  不成立(Swan/Sattler)。値レベル版のモデル論的地位は要調査 —
  論文 A の "tested, not verified" で明記必須。最悪 constancy 規則の
  適用条件を狭める必要が生じ得る。

**第一予想(ターゲット2の種)**: 区間 De Morgan 正規形で吸収される法則
+ hcomp/transp を生成しない再インデックス(symm/cong/η)は定義的;
hcomp を生成する法則(trans 系)は本質的に弱い。
→ 精密化: 「⟨i⟩ p(φ(i)) ≐ ⟨i⟩ p(ψ(i)) ⟺ φ ≡ ψ in 自由 De Morgan 代数」
という**再パラメータ化コヒーレンス定理**として定式化できる見込み
(papp-eta と DNF 決定手続きから紙上証明が届く射程)。

**次の作業**: カタログ拡張(HIT 計算則、whisker/正方形交換の定義的
インスタンス、transpGlue 系)→ 予想の精密化 → regularity モデル論調査。

## 11. 外部批評レビューへの対応と論文全面改訂(2026-07-17)

ユーザー提供の外部レビュー(ChatGPT による詳細批評)を受領。指摘は
大部分が妥当と判断し、`docs/paper/jrefl.tex` を全面改訂した
(旧版は `jrefl_v1_backup.tex` として保存)。

### レビューの主要指摘と対応

1. **(R) の導出可能性問題(§3.1、最重要・形式的正しさ)**:
   φ を省いた提示では (R) は congruence + (S) から導出可能
   (A ≡ A₀, i∉FV(A₀) ⟹ transp A u ≡ transp A₀ u ≡ u)。
   → **対応**: 基礎理論を φ 明示構文(ABCFHL 流 `transp^i A φ u`、
   規則 S_i1: transp A i1 u ≡ u)に変更。Remark "Why the formula must
   be explicit" で二重の読みを明記: φ 明示計算では (R) は判断的等式の
   真の拡張(congruence は φ を変えられない)、φ 非明示計算では等式は
   導出可能だが決定アルゴリズムが存在しなかった(貢献はアルゴリズム)。

2. **T^≺ の定義循環(§3.2)**: 「判断的定数性」が定義対象の判断的
   等式に言及。→ **対応**: (R) の側条件を **T₀ の**正規形・判断的
   等式で層化定義(Remark "Stratification")。T₀ のメタ理論は文献
   (Huber, Sterling–Angiuli)から明示的な形 (i)–(iii) で引用。
   実装の値レベル検査は層化定義に対し保守的(発火は常に健全側)と
   別 Remark で明記。新 §"The algorithm" で eval/const?/conv の相互
   再帰を提示し、Lemma (well-foundedness): const? は transp ノードの
   真部分項を評価するだけで新たな呼び出し閉路を作らない。

3. **canonicity ⇏ decidability(§3.3)**: → **対応**: 定理を分離。
   Theorem (Canonicity): Huber 拡張、基底から使う結果を列挙
   ((i) 評価停止、(ii) 正規形の非可換性、(iii) 述語の等式閉包)、
   3 つの大域的再検査点 (well-definedness / termination / substitution)
   を明記。Theorem (Decidability): アルゴリズム的等式の停止性+健全性
   のみ主張。**Remark (Completeness)**: 完全性は未証明と明示し、
   カタログの負例は「アルゴリズムが受理しない」という主張であって
   「T^≺ で導出不能」への格上げは完全性経由と明記。これが
   by-extension の正確な意味であり、完全性証明が主要な残タスク。

4. **先行アイデア(2021 Arend 公開議論)**: → **対応**: イントロに
   "Prior art" 段落新設。アイデア自体は 2021 年から公知、真の障害は
   構造規則(特に Glue)との相互作用と専門家が指摘済み — 本論文の
   貢献は「その相互作用のメタ理論的分析」と再位置付け。タイトルを
   "Evaluation-Time Constancy Inference for Transport in Cubical Type
   Theory" に変更("Gives ... a Definitional J" の主張形を降格)。
   アブストラクトはレビュー提案の "first metatheoretic treatment
   (to our knowledge)" 型に書き換え。「full regularity を与えたとは
   主張しない」段落をイントロ末尾に追加。

5. **アーティファクト不在**: → **対応**: §Implementation に Artifact
   段落(Lean 4.31.0、ビルドコマンド、公開予定の明記、カーネル健全性
   の境界声明)。リポジトリに `ARTIFACT.md` 新規作成(ビルド手順、
   カーネル構成表、**論文カタログ行 ↔ probe 名対応表**(実名 `...D`
   サフィックス+負例の #guard 行番号)、golden 差分テスト、スコープ
   声明、著者連絡先)。**残**: リポジトリの公開(URL 確定)は
   ユーザーの操作が必要。

6. **関連研究の薄さ**: → **対応**: Arend/Isaev、Sterling–Angiuli
   (LICS 2021 normalization)を文献追加し、Related work を 4 段落構成
   (constancy formulas / regularity / systems with regular coercion /
   normalization)に拡充。XTT は「等式を大域的に強める(univalent
   宇宙を犠牲)」対比として正確化。

7. **焦点(定理 C の位置)**: → **対応**: §Reparametrization coherence
   を「補完的・自己完結的結果」と明示し、カタログの境界を下から画定
   する役割として位置付け(本文には保持 — LMCS は長さ制約が緩い)。
   負方向はアルゴリズムについての主張である旨も Remark (Completeness)
   参照で明記。

### 改訂後の論文の主張構造(誠実版)

- 主定理: T^≺ は consistent + 停止する健全な決定戦略を持ち、
  J d refl ≡ d が定義的に成立(canonicity は Huber 拡張で証明、
  完全性は open)。
- Open problems(結論、重要度順): (1) T^≺ アルゴリズム的等式の
  完全性、(2) 非優先化提示の保存性(手書き transpGlue インスタンス)、
  (3) 判断的 transport-regularity のモデル論的地位。
- 9 ページ、0 エラー、0 未定義参照。

### 投稿前の残作業

1. リポジトリ公開(GitHub 等)+ jrefl.tex の "public repository upon
   publication" を実 URL に差し替え(ユーザー操作待ち)
2. Arend 2021 公開議論の一次ソース特定と正確な引用(現在は
   Arend 本体サイトの引用のみ — 議論スレッドの URL を脚注に追加すべき)
3. (推奨)完全性証明の少なくともプランを付録に — 採択確度を大きく
   上げる(レビュー採点「証明の充実度 2/5」への最終回答)
4. arXiv 投稿 → LMCS (episciences) 投稿

## 12. 第2次外部レビューと開発再開(2026-07-17)

改訂版(v2)への第2次レビューを受領。判定:「新規性・重要性は認める
が、正しさ・完全性が不足 — 現状では reject または major revision」。
ユーザー指示: **指摘された開発を先に進め、その後に論文を再執筆**。

### 最重要指摘 3.1(¬Const の置換非安定)の帰結 — 本日の主要な進展

レビューの通り Definition 4.6(構造規則の非定数族への制限)は置換に
閉じない。さらに機械実験(`LibSwitchover.lean` 新設、全 guard 通過)
により、切替時整合性の証明による修復は **Path 型で不可能** と判明:
構造 Path contractum の端点補正 comp は定数族で「定数チューブ hcomp」
として残留し、u と非 convertible(hcomp-regularity の不在と同機構)。

**新知見(論文の物語を強化する)**: 優先化は実装の便宜ではなく理論的
必然であり、それは Glue 以前に Path 型で強制される。「なぜ誰も
やらなかったか」への定理級の回答: 無制限 T₀+(R) は hcomp-regularity
型等式を導出してしまう(不可能性定理として定式化予定)。

### 採用した解決アーキテクチャ(docs/RegularityProof.md §8)

- 判断的等式 = **アルゴリズム的(NbE)等式として定義**(規則制限の
  等式理論は破棄)。置換安定性 = NbE 置換補題(constancy 検査は値
  レベルなので transp 節も構造的に通る — レビュー要求の coherence
  補題そのもの)。3.1 と 3.2(二重定義の不一致)を同時に解消。
- canonicity は操作的(環境ベース computability、Huber 再利用目録
  §8.4)。「decision procedure」→「sound conversion checker」(3.4)。
- 基底メタ理論は Assumption パッケージに相対化(3.3; De Morgan 版の
  文献ギャップに正直に対応、Cartesian なら Sterling–Angiuli で履行)。
- critical-pair 表は機械判定表(§8.1)に置換 — U は Glue バケツへ、
  HIT は列挙した署名に限定(3.5)。

### 開発フェーズ計画(論文再執筆は D6)

- **D1 ✅(2026-07-17)**: switchover 機械実験(LibSwitchover.lean;
  Π/Σ/依存Σ/HIT 収束、Path 不収束、contractum well-typedness 対照)
- **D2 ✅(2026-07-17)**: アーキテクチャ再設計文書(RegularityProof §8)
- **D3(次)**: 不可能性定理の正確な定式化と証明(Path 非収束の
  完全性への依存を精査 — アルゴリズム拒否から理論的非導出への格上げ
  条件、または「アルゴリズム的に区別される」形での無条件定式化)、
  Glue の switchover 残滓の書き下し(transpGlue の a1'-補正が定数族で
  定数チューブ hcomp に退化することの明示計算)
- **D4**: canonicity 証明の全面展開(Huber 補題の再利用/再証明目録、
  NbE 置換補題の完全証明、評価器停止、conv 健全性 — 論文の付録級)
- **D5**: Arend 2021 公開議論の一次ソース特定・引用整備;
  リポジトリ公開(ユーザー操作)+ commit 固定 + (可能なら Zenodo DOI)
- **D6**: 論文再執筆 — LMCS 25–35 頁構成(本文 15–20、形式的規則
  5–10、critical pair 計算、canonicity 詳細、artifact、付録)。
  操作的主定理+不可能性定理を物語の中心に。

### D5 文献調査メモ(2026-07-17)

- **Arend**: 公式文書 Prelude(`coe` の仕様と正則性)+ Isaev らの
  言語論文(arend-lang.github.io/assets/lang-paper.pdf)を正式引用に
  使用。2021 年の「公開議論」の一次ソース(スレッド URL)は未特定 —
  レビュー側の記憶による可能性もあるため、v3 では「Arend の coe は
  正則; 評価時検出のアイデアは以前から知られている」という検証可能な
  形に弱めて引用し、特定スレッドへの言及は確たるソースが見つかった
  場合のみ脚注化する。
- **Towards Computational UIP in Cubical Agda**(arXiv:2511.21209,
  2025): regularity 不在が UIP/計算に及ぼす影響を扱う近年の仕事 —
  Related work の「regularity の現在」段落に追加。
- **Normal forms in cubical type theory**(Xu Huang, arXiv:2603.24923,
  2026-03): Sterling–Angiuli 証明内の正規形仕様の明示的再定式化。
  競合ではない(regularity/constancy 推論への言及なし)。Assumption
  パッケージ(正規形の仕様)の引用先として有用。

### D6 完了(2026-07-17): 論文 v3

`docs/paper/jrefl.tex` を v3 に全面改稿(v2 は `jrefl_v2_backup.tex`)。
12 頁、0 エラー、0 未定義参照。構成:
- 物語の中心 = **No-go 定理**(Theorem: 無制限 T₀+(R) は定数チューブ
  hcomp-regularity を導出、衝突は Glue 以前に Path で発生;制限版は
  置換非閉 — レビュー 3.1 を定理の一部として肯定的に取り込んだ)
  +**操作的定式化**(判断的等式 = 優先化 NbE のアルゴリズム的等式)。
- switchover 解析節(機械検証つき収束補題 Π/Σ/依存Σ/HIT、Path 非収束
  の機械証人、Glue 残滓の明示計算)。
- NbE 置換補題(transp 節を完全証明 — レビュー要求の coherence)、
  停止性、決定性。
- Soundness 定理 + 「completeness は No-go により原理的に不可能」を
  明示(「decision procedure」の語を全廃 — レビュー 3.4)。
- canonicity は (A1)–(A4) 仮定パッケージに相対化(レビュー 3.3)、
  環境ベース fundamental lemma、継承目録(再利用/再証明/仮定)。
- 文献: UIP (arXiv:2511.21209)、Huang NF (arXiv:2603.24923)、
  Arend(言語論文+Prelude、「2021 スレッド」への言及は検証可能な
  形に弱めた)を追加。謝辞に匿名レビュー 2 巡の寄与を明記。
- 頁数は 12(LMCS 推奨 25–35 への拡張余地 = 付録: 規則の完全列挙、
  canonicity 全展開(RegularityProof §10.6 の TODO)、critical pair
  全計算。**投稿判断前にこの付録拡張を行うか要検討**)。

### 投稿前チェックリスト(残)

1. **リポジトリ公開**(ユーザー操作)→ 論文 Artifact 節に URL・
   commit・(可能なら Zenodo DOI)を記入
2. 付録拡張(規則列挙+canonicity 詳細)で 20 頁級にするか判断
3. arXiv (CoRR) 投稿 → episciences 経由 LMCS

## 13. 第3次レビューと E フェーズ(操作的メタ理論の正式化、2026-07-17)

第3次レビュー受領(判定: 新規性・重要性・LMCS 適合は高いが、操作的
体系の基礎メタ理論が未証明 — 現状採択確度 20–30%、完全証明後
45–60%)。ユーザー指示: **§5–7 を正式な operational dependent type
theory のメタ理論として完成させる開発を先に行い、完了後に論文改訂**。

### 指摘の妥当性判断(全面的に妥当)

- 3.2 が最も鋭い: defunctionalized NbE では eval(Aσ,ρ) と
  eval(A,eval(σ,ρ)) はクロージャ表現まで同一にならず、旧補題 5.1 の
  「same value」は構造的等号としては**偽**。表現同値 ≈(双模倣)への
  格上げが必須で、さらに constancy 検査が ≈ の両辺で一致する保証は
  実装レベルでは無い(チューブ閉包の構造走査は表現依存)。
- 3.3: usesLvl=false ⟹ 意味論的定数性、の健全性定理が必要 — 正しい。
- 3.1/3.4/5: admissibility 群・停止性・canonicity の正式化要求 — 標準
  かつ正当。

### 実施した開発(docs/OperationalMetatheory.md 新設)

1. **表現同値 ≈**(クロージャ差を吸収する双模倣; readback 不変性
   補題)と**型指標付き Kripke PER ≡val**(conv の正当性で対称・推移を
   導出)— レビュー 3.2 の解消。
2. **constancy 検査の仕様/実装分離**(本フェーズの中心的設計判断):
   体系の定義は const?_spec(F,ℓ) := ℓ ∉ FV(quote F)(表現非依存)で
   行い、**健全性定理 3.2.1**(spec ⟹ ∀r,s: F⟨r/ℓ⟩ ≡val F⟨s/ℓ⟩;
   quote/作用可換+NbE 冪等性で証明)を置く。実装 usesLvl は
   **仕様への健全な近似**(lb カットは正確、チューブ走査の過大報告は
   (R) の発火を減らす方向のみ=安全; 定理 3.3.1)。正例 probe は
   仕様体系の証人を兼ねる — レビュー 3.3 の解消。
3. **意味論的置換補題**(定理 4.1: eval(tσ,ρ) ≈ eval(t,eval(σ,ρ));
   transp 節は仕様検査が ≈ で不変だから分岐一致 — 「検査を仕様で
   定義する」ことが置換補題成立の決定的理由であることを明示)。
4. **admissibility 一括**: 論理関係の基本定理(5.2.2)を一度証明し、
   同値関係・former 別合同・弱化・置換・文脈変換・型保存・型検査
   整合をすべて系として導出(定理 5.3.1)— レビュー 3.1 の解消。
5. **停止性の畳み込み**(Tait 流: Γ ⊨ t : A の定義に停止を含め基本
   定理で拡張; 「call graph に新閉路なし」表現は全廃; transp 負分岐の
   内部再帰は型値帰納との二重帰納と明示 — 循環疑義解消)— 3.4/5。
6. **No-go の補強**: 完全導出木(型付け前提付き)+意味論的主張は
   方法 B(「closely related to … excluded in standard models」に
   弱め、countermodel 構築は Open Problem/強化路線)— レビュー 4。
7. **主定理二層化**: Theorem A(Cartesian、S–A から基底 component、
   無条件を目指す)/ Theorem B(De Morgan、仮定パッケージ相対化、
   Lean 実装はこちら)— レビュー 6。
8. **HIT 署名クラス**(argument-wise transport 署名の定義+実装署名の
   分類表; qeq 系は構造規則なし=臨界対が空虚; 新 probe
   swSuspMeridD ✅ でパス構成子の収束も機械検証)— レビュー 7。

### 残作業(v4 執筆の前提; OperationalMetatheory §11)

機械的な分量作業(操作両立補題群の個別化、基底節の環境版転写の
全列挙、導出木の LaTeX 化)+ S–A 対応表(文献精読)+ リポジトリ公開
(ユーザー操作)。数学的な穴は残っていない認識(新規の本質的補題は
3.2.1/3.3.1/4.1 で、いずれも証明骨格まで完成)。

### v4 執筆方針(開発完了後)

25–35 頁+付録(レビュー 9 の頁配分に準拠)。§5–7 は本文書 §2–7 の
転写。coherence 定理(旧 Theorem 8.1)は付録へ移動を検討(レビュー
C.10)。artifact に URL・commit・(可能なら Zenodo DOI)。

### v4 完成(2026-07-17)

E フェーズの開発(OperationalMetatheory.md)完了を受け、論文を v4 に
改訂(v3 は `jrefl_v3_backup.tex`)。**16 頁、0 エラー、0 未定義参照**。
v3 からの主変更:
- §5–7 を全面差し替え: 意味領域の正式定義、表現同値 ≈+readback
  不変性、Kripke PER ≡val+conv 正当性(対称・推移の出所)、
  **constancy 検査の仕様/実装分離**+健全性定理+実装近似補題、
  置換補題(≈ レベル、仕様が load-bearing である旨の Remark)、
  基本定理(二重帰納明示)、停止性は論理関係の系(構文的測度の
  主張なし)、**Admissibility 定理**(同値・合同・弱化・置換・文脈
  変換・型保存・検査整合 — 「judgmental と呼ぶ資格」の定理)。
- No-go 節: 完全導出木 (d1)–(†) を型付き前提・各段検証付きで収載、
  スコープ 4 注記(PathP/Cartesian/η_Path/定数性の次元)、意味論的
  主張は方法 B の言い回しに統一(countermodel は Open Problem (2))。
- HIT: argument-wise 署名クラス定義+分類表(merid 機械証人
  swSuspMeridD、qeq 系は臨界対空虚)。
- Theorem A(Cartesian、S–A で基底 component 放電、橋渡しの限界を
  明記)/ Theorem B(De Morgan、(B) 相対、実装対応)の二層化。
- coherence 定理を付録 A へ移動(レビュー C.10)。付録 B に補題・
  ケース目録(L1–L15、基底/新規のマーク付き)。
- artifact 節: witnesses / regression tests / (機械検証されていない)
  メタ理論、の三区分を明示。abstract から強い意味論的主張を除去。

残(投稿前): リポジトリ公開+URL/commit 記入(ユーザー操作)、
付録の routine 帰納の書き下しでさらに 20 頁台へ伸ばすか判断、
S–A 橋渡し対応表の精密化(文献精読)、arXiv → LMCS。

### 付録拡張+S–A 橋渡し完了(2026-07-17、ユーザー指示「2と3を実施」)

論文を 24 頁に拡張(v4 直前版は `jrefl_v4_backup.tex`)。0 エラー・
0 未定義参照・overfull 最大 15pt(軽微)。追加内容:

1. **付録 "Lemmas: statements and proofs"** — 構造的注記
   「(R) は評価器を変えるがドメインを変えない ⟹ 値についての基底補題
   (L10–L13, L15)は逐語的に移送、監査対象は評価器節と検査のみ」を
   冒頭に置き、L1(深さ不変量)/L2(深さ決定性)/L3–L8(≈ 両立、
   同時余帰納)/L14(readback/作用可換)を完全証明、(B) 印の
   L10–L13/L15 は proof shape 明示。conv に新節が無い事実
   (transp は評価器側)も L12 で明文化。
2. **付録 "The fundamental theorem, case by case"** — 環境形式の
   基底節を全列挙(変数、Π/Σ/Path の導入・除去、宇宙、ℕ、hcomp
   全前者(transport redex 不参照の確認込み)、Glue、HIT、構造
   transport dispatch)。dispatch 節では「内側帰納(型値)が評価器の
   線構造再帰を鏡映し、外側帰納(型付け導出)は前提のみ」という
   分業を Π 線で明示的に書き下し(第3次レビューの循環疑義への
   最終回答)。正分岐(new)と合同補題の非自明インスタンスも収載。
3. **付録 "The Sterling–Angiuli bridge"** — arXiv:2101.11479v2 を
   精読して確定した事実に基づく: S–A は Cartesian、Π/Σ/path/glue/S¹、
   **宇宙なし**、手法は STC(stabilized neutrals)で**非評価的**、
   De Morgan は「mutatis mutandis」主張のみ。項目別対応表:
   (B) の judgmental-theory 部(正規形全単射 Thm 42、単射性 Thm 43、
   決定可能性 Cor 47)= **provided** / evaluator-level 部(環境形式
   基本定理・readback 正当性・停止)= **not literal**(標準的 NbE
   正当性転写の証明義務)/ 宇宙・HIT 拡張・De Morgan = **gap**。
   coe の境界条件 r=s↪a は (S_i1) の Cartesian 版という翻訳段落、
   No-go 導出が Cartesian 署名でもそのまま通る旨も明記。
   **Theorem A の正確な最終文言**を quote 環境で固定(「fragment 上、
   evaluator-level 転写を modulo として、それ以上は主張しない」)。
   本文 §2.2 の Theorem A も同内容に更新。
4. **付録 "The base calculus in full"** — 文法・判断・構造コア規則・
   Kan 操作(hcomp の typing+side conditions、comp の定義)・Glue・
   変換規則(conversion rule のアルゴリズム的等式が Theorem
   (Admissibility) により正当、の明記)。

投稿前の残り: リポジトリ公開(ユーザー操作)→ artifact 節へ URL/
commit/(Zenodo DOI)、arXiv (CoRR) → LMCS (episciences)。
任意: pushout probe 追加、overfull 最終研磨。

## 14. 第4次レビュー対応(2026-07-17): 検査器「実装=仕様」の確立と論文 v5

第4次レビュー(採択確度 25–40%、最重要指摘 3.1 = 仕様検査器と実装
検査器が異なる分岐を選び得る)。**指摘の論理は正当**だが、カーネル
精査により前提事実が覆った:

### 主要な開発成果 — usesLvl は既に readback-正確だった(死コード発見)

旧 Lemma 6.3 の「チューブ閉包の構造走査による過大近似」は、usesLvl の
入口から**到達不能な死コード**(usesLvlClosure/usesLvlSys、204 行)と
古い doc コメントに基づく誤記述だった。到達可能な全経路は quote を
節ごとに正確に鏡映(binder 閉包は generic 実体化、中立 hcomp の
チューブも usesLvlIBinder で実体化 = quoteSys と同型)。よって
**usesLvl(ℓ,F) = (ℓ ∈ FV(quote F)) が成立(検査器正確性定理)**。
レビューの修正方法 1「実装も readback ベースの仕様を正確に実行」が
既に真であり、実装体系=仕様体系。開発: 死コード 204 行削除
(lake build 成功・golden 299 一致・全 probe 通過=到達不能の実証)、
usesLvl に正確性 doc コメント追加、OperationalMetatheory §12 に記録。

### 論文 v5(25 頁、0 エラー、0 未定義参照; v4+付録版は jrefl_v5pre_backup.tex)

1. **§6.3 全面書換**: 「sound approximation」を撤廃し
   **Theorem (Checker exactness)** に置換。Remark (An instructive
   archaeology): 旧構造走査設計がまさにレビューの懸念する分裂
   (仕様=正分岐/実装=構造分岐、Path で非可換)を開き得たこと、
   到達不能と判明し除去したことを明記 —「検査器の readback からの
   逸脱は近似ではなく判断的等式の変更」というスローガンに昇華。
2. **T_eq / T_alg の分離**(3.2): T_eq = 無制限等式理論(No-go と
   soundness 専用、型付けには不使用)、T_alg = ≡alg を conversion に
   使う記録の体系(Definition、双方向検査器と一致)。fundamental
   theorem は T_alg の導出について述べ、**conversion 規則の節を証明に
   追加**(conv 正当性+≡val 型不変性で閉じる; T_eq conversion なら
   (†) 型等式への不変性が要求され定理が偽になる、という説明込み)。
   admissibility/canonicity も T_alg に統一。
3. **Canonicity の表現修正**(3.3): 「unconditionally in the
   Cartesian layer」を撤回し「Relative to (B), in both presentations;
   Cartesian fragment では judgmental-theory 部が S–A から従い、
   evaluator-level bridge は open」に。
4. **部分性の形式化**(3.4/3.5): 新 §"Partiality" — 5 関数は一つの
   相互再帰部分関数族、グラフを big-step 導出として帰納的に定義、
   eval→const?→quote→inst→eval の循環は帰納的グラフ定義ゆえ無害、
   全域性は基本定理の結論。≈ の閉包節は Kleene 読み+guardedness、
   置換補題も Kleene 形に修正。
5. **Abstract 短縮**(約半分、4 論点)+「excluded」→「closely
   related to regularity principles known to fail」(4)。

### 残作業(前回から不変)

リポジトリ公開(ユーザー操作)→ URL/commit/DOI 記入 → arXiv → LMCS。

# HANDOFF — 開発引き継ぎ資料

**常設ドキュメント(コードと並走して保守すること)**: `docs/` 配下の
4文書 — ProjectResults_{EN,JA}.tex(成果・意義・未解決問題への関わり)、
StudyGuide_{EN,JA}.tex(前提知識・文献・最短学習経路)。
**実質的マイルストーン(新定理・新カーネル機構・大きな方針転換)ごとに、
HANDOFF と併せてこれらの .tex を更新し PDF を再コンパイルする**
(EN: pdflatex ×2、JA: lualatex ×2)。日付行(Last updated / 最終更新)も更新。


最終更新: 2026-07-08。このドキュメントは、任意の開発者(人間・AI を問わず)が
このプロジェクトを引き継ぐための自己完結の資料である。README は「何ができたか」、
本書は「どう作られているか・何に気をつけるか・次に何をするか」を扱う。

---

## 2026-07-17 (31): アーティファクト公開完了 — GitHub + Zenodo DOI(投稿前ブロッカー解消)

公開チェーン完成: **リポジトリ** https://github.com/r-shibusawa/cubical-strict-j(公開、Apache-2.0; 共著トレーラーを除いた履歴で再構築し、セッション関連ファイル・個人メモは .git/info/exclude によるローカル専用除外)、**スナップショット** = release v1.0.0 @ commit 6c5904be3f9bf8ec9138cda5bcb961b6a67f4feb、**DOI** = 10.5281/zenodo.21405962(Zenodo 自動アーカイブ; トグルがリリース作成より後だったため webhook 未発火 → リリース再作成で解決、という顛末)。旧リポジトリ FormalizedMathematics はユーザーが削除済み(Zenodo 未アーカイブを API で確認済み)。論文 Artifact 節と ARTIFACT.md に URL・commit・DOI 記入済み(38 頁・0 エラー)。main = de51b6a。**残: 投稿手続きのみ** — ドラフト版マーカー除去 → arXiv (CoRR) 投稿 → episciences 経由 LMCS 投稿。

## 2026-07-17 (30): 最終整理 — 論文 v12(38 頁)、レビュー判定「投稿可能水準」到達

第11次レビュー(70–80%、「これ以上大定理を追加するより最終整理して投稿を; 現実的経路は一度の revision 経由で採択」)の 3 点を実施: §2.2 見出しを three-layer に、Abstract の機械検証範囲を「object-language conversion witnesses は機械検証・metatheory は pen-and-paper」と精密化、版マーカー v12。38 頁・0 エラー・0 未定義参照。**投稿前の残作業 = リポジトリ公開(ユーザー: URL/commit/Zenodo DOI)のみ**。公開後: Artifact 節記入 → マーカー除去 → arXiv → LMCS。バックアップ jrefl_v11_backup.tex。

## 2026-07-17 (29): 層切替の明示+Path 分離の紙上証明 — 論文 v11(38 頁)

第10次レビュー(「採択可能性が高い」段階)の 2 点に対応。(1) 本文 Lemma 5.4 直後に **Remark (Where clause (iii) is proved, per layer)**: 相対層=(B) 継承/無条件 core=readback 特徴付け+型レベル健全性+完全性で置換(項レベル健全性は不使用)、「別経路の共存」を明記し矛盾誤認を遮断。(2) **Path 分離の紙上証明**: Lemma (hcomp/spine separation)(core 型の構造帰納; ℕ で文法生成規則の相違に着地、Π/Σ/PathP は構造規則で部分型に帰着、face は generic で未決定のまま)+ Proposition (Path separation in the core, on paper)(任意 core 型 A のスキーマで (†) 左辺 ≢alg p を無条件証明)→ No-go の両半分が無条件層内で紙上確立、機械 probe は full calculus(A: 宇宙変数)の証人に降格。本文 Lemma 4.5 改名+前方参照。版マーカー v11。38 頁・0 エラー・0 未定義参照。バックアップ jrefl_v10_backup.tex。残: リポジトリ公開(ユーザー; URL/commit/DOI)→ arXiv → LMCS。

## 2026-07-17 (28): idempotence/変換健全性の型レベル再構成 — 論文 v10(37 頁)

第9次レビュー(60–75%; ①NbE idempotence 独立補題化 ②generic→arbitrary 明示 ③sorted worlds)に全対応。素朴な項レベル対応は NbE 正当性の既知の難所に入るため、**負荷点=型値レベル**の再構成で根本解決: (1) **conv 受理 ⟺ readback 等式**(純構文的; ≡alg の PER・合同性がここから無害に出る)。(2) **型レベル idempotence 補題**(型値反転→構文型の構造帰納; Π codomain の generic→arbitrary は構文帰納で閉じる)— 検査健全性が使うのは型のみ。(3) **PathP reindexing 補題**(world 射=次元代入で証明、項置換補題は不要と明記 — 循環疑義遮断)。(4) **型変換健全性補題**(基本定理 conversion 節用)。(5) **Remark**: 項レベル意味論的健全性はどの証明も不使用と明示(型では構文帰納、項では不要 — ギャップの正確な解消)。(6) sorted context shape の一文。(7) 引用張替(checksound step3 / coretransp 正分岐 / 基本定理 conversion 節)。v10・37 頁・0 エラー・0 未定義参照。バックアップ jrefl_v9_backup.tex。残: リポジトリ公開(ユーザー; レビューも supplementary artifact の URL/commit/DOI を指摘)→ arXiv → LMCS。

## 2026-07-17 (27): face-indexed world 構造の正式化 — 論文 v9(37 頁)

第8次レビュー(評価「比較的高い」へ到達; 最重要 = 付録 F の face/cofibration 文脈)に全対応。**World 構造を正式化**: world = (深さ, cofibration)、射 = 次元代入(ψ′ ⊨ ψ⟨ξ⟩)、意味論的文脈充足(区間変数は両側同一値、restriction は ψ ⊨ φ[ρ])、不条理 world では全値関連(空交差条件の真の自明化)。論理関係を world 指標付き Kripke に書き換え、**Related systems の正式定義**(チューブは制限 world で関連+対整合+base adapted 条件)、**face restriction/weakening 補題**(world 関手性; forcing との可換+L14)、**Boundary preservation 補題**(合成は各制限 world でチューブ top と関連)を追加、hcomp 補題群の仮定・結論を同期。本文 §5 に world 構造の所在注記。他: No-go (3) に明示的 substitution witness(C(i)=Path A a (p i)、σ=[refl_a/p])、Proposition J の schema 注記、「terms are never typed in T_eq」表現修正。37 頁・0 エラー・0 未定義参照。バックアップ jrefl_v8_backup.tex。残: リポジトリ公開(ユーザー)→ arXiv → LMCS。

## 2026-07-17 (26): 付録 F 難所の完全仕上げ+文献追跡可能化 — 論文 v8(34 頁)

第7次レビュー(55–70%; 焦点 = 付録 F の難 case を査読者が補完なしで追跡できる形へ)に全対応。(1) reflect/reify を**前者別 8 補題**に分割(相互帰納規律を明文化)、conversion correctness を健全性/完全性の 2 補題に分割(generic→任意引数の転送を置換補題で明示)。(2) **従属 Σ-hcomp**: c・filler c̄(ι)・第2成分の異種合成を型注釈付き完全式で表示+境界前提の継承。(3) **PathP transport**: 前提 (P1)–(P3) と端点 coherence (E0)(E1) を番号付き導出形式で表示。(4) Kan 補題群(hcomp/transport)の**同時構造帰納宣言**(相互参照は真部分項のみ — 循環疑義の先回り遮断)。(5) 結論に「full univalent system の無条件 strict J は主張しない;三層区分が主張のすべて」を明記。(6) 文献: 「public discussion」→「folklore assessment (informal)」、Sattler 項を「unpublished observation, commonly attributed + 公刊 account への指針」に、Arend 項に Prelude URL+accessed 日付。34 頁・0 エラー・0 未定義参照。バックアップ jrefl_v7_backup.tex。残: リポジトリ公開(ユーザー)→ arXiv → LMCS; 強化 = (†) countermodel。

## 2026-07-17 (25): 無条件 core の全面展開 — 最小 core(S¹ 除外)+付録 F 増補+Step soundness+Strict J 命題(論文 v7、32 頁)

第6次レビュー(45–60%; 「無条件 core を査読者が補完なしに検証できる密度へ」)に全対応。(1) **S¹ を core から除外**し最小 core = Π,Σ,PathP,ℕ+transp+hcomp に(S¹ は proof sketch 明示の Proposition+artifact evidence に分離)。(2) 付録 F を前者別補題に全面増補(~8 頁): **論理関係を構文型への構造再帰で再定義**(帰納順序の疑義を根本解消 — 順序 = 部分項関係のみ)、正規形 BNF、reflect/reify 全ケース、conversion correctness、hcomp(ℕ の中立 base stuck ケースを正しく記述+閉 cofibration は決定される注記、PathP 端点 coherence)、transport(Σ codomain typing 詳細、ℕ 線は正分岐必発)、基本定理+系。(3) **Lemma (Step soundness)** 新設+Theorem 8.1 完全証明(正 transp 分岐: A₀:=quote(F) ℓ-自由+IH ⟹ (R) 前提成立; T_alg ⊊ T_eq なのに各ステップ T_eq-健全という非対称性を明文化)。(4) **Proposition (Strict J)**: J_C の定義から d への計算まで独立命題として完全証明(接続吸収の機械証人 strictConnZeroD 引用)。(5) イントロに三層段落(Unconditional/Relative/Artifact evidence)+univalence の住所明示。32 頁・0 エラー・0 未定義参照。バックアップ jrefl_v6_backup.tex。残: リポジトリ公開(ユーザー)→ arXiv → LMCS。

## 2026-07-17 (24): ★ 無条件 core の確立(base component を論文内で放電)+ 論文 v6(28 頁)★

第5次レビュー(35–50%; 最有効修正 = exactness 完全化/小断片での (B) 放電/Cartesian 表現弱化)に全対応。**最大の追加 = 無条件 core**: T^core = Π,Σ,PathP,ℕ,S¹+transp+hcomp(Glue・宇宙なし)について (B) を新付録で完全放電(型値の素構造帰納+transpGlue 不在が鍵; 論理関係全節・reflect/reify・hcomp/transp 計算可能性・基本定理)→ **Theorem A′: core 上で admissibility・canonicity・J d refl ≡ d が無条件**(J は Path+transp のみで定義されるため看板等式は core 内)。exactness は Kleene 形+全節対応表付録(definedness transfer、lb カット完全性、memo 透明性)。≈ は Φ の gfp として形式化(単調性・guardedness・依存順序=部分導出関係)。結論の「Cartesian layer already inherits」撤回、abstract に core の一文追加。28 頁・0 エラー・0 未定義参照。詳細 OperationalMetatheory §13、バックアップ jrefl_v5_backup.tex。残: リポジトリ公開(ユーザー)→ arXiv → LMCS; 強化路線 = (†) の semantic countermodel。

## 2026-07-17 (23): ★ 検査器「実装=仕様」の確立(死コード 204 行発見・削除)+ 論文 v5(25 頁)★

第4次レビューの最重要指摘 3.1(仕様/実装検査器の分岐分裂)を検証した結果、**旧記述の方が誤りで実装は既に readback-正確**と判明: 「チューブ閉包の構造走査(過大近似)」は usesLvl 入口から到達不能な死コード(usesLvlClosure/usesLvlSys、204 行)+古い doc コメントに基づくものだった。到達可能経路は quote を節ごとに鏡映(binder=generic 実体化、中立 hcomp チューブ=usesLvlIBinder=quoteSys 同型)。開発: 死コード削除(build ✅ golden 299 ✅ = 到達不能の実証)、usesLvl に正確性 doc コメント、OperationalMetatheory §12。論文 v5: §6.3 を **Checker exactness 定理**に書換+Remark (archaeology)(旧設計がレビューの懸念そのものを開き得た事実を教訓として収載)、**T_eq/T_alg 分離**(fundamental theorem に conversion 節追加 — T_eq conversion では定理が偽になる説明込み)、canonicity の「unconditional Cartesian」撤回、**Partiality 節新設**(big-step グラフ、Kleene ≈、循環 eval→const?→quote→inst→eval の無害性、全域性=基本定理の結論)、Abstract 半減+「excluded」緩和。25 頁・0 エラー・0 未定義参照・overfull 4 件(≤15pt)。ARTIFACT.md 同期。残: リポジトリ公開(ユーザー)→ arXiv → LMCS。

## 2026-07-17 (22): 付録全面展開+Sterling–Angiuli 橋渡し表 — 論文 24 頁(投稿可能水準の完成度へ)

ユーザー指示「2と3を実施」を完遂。(2) 付録 routine 帰納の書き下し: "Lemmas: statements and proofs"(ドメイン不変の構造的注記+L1–L15 全て statement+証明/proof shape; L3–L8 は同時余帰納)と "The fundamental theorem, case by case"(環境形式の基底節全列挙+構造 dispatch の内側帰納/外側帰納の分業明示+正分岐+合同補題)を新設、"The base calculus in full"(文法・判断・全規則)も追加。(3) S–A 橋渡し: arXiv:2101.11479v2 を精読(Thm 42 正規形全単射・Thm 43 単射性・Cor 47 決定可能性; 宇宙なし・HIT は S¹ のみ・STC は非評価的・De Morgan は mutatis mutandis 主張のみ)し、付録 "The Sterling–Angiuli bridge" に項目別対応表(provided / not literal / gap)+ coe 境界条件=(S_i1) の Cartesian 版という翻訳+ Theorem A の正確な最終文言(quote 固定)を収載、本文 §2.2 も同期。24 頁・0 エラー・0 未定義参照・overfull 最大 15pt。OperationalMetatheory §11 チェックリスト 4 項目消化。残: リポジトリ公開(ユーザー)→ URL/commit/DOI 記入 → arXiv → LMCS。任意: pushout probe、最終研磨。

## 2026-07-17 (21): 論文 v4 完成 — 操作的メタ理論を本文化(16 頁エラーゼロ)

E フェーズ完了を受け v4 改訂(v3 は jrefl_v3_backup.tex)。§5–7 を OperationalMetatheory.md から転写・拡張: 表現同値 ≈、Kripke PER ≡val、constancy 検査の仕様/実装分離+健全性定理 3.2.1 相当(paper では Thm 6.2)+実装近似、置換補題(≈ レベル)、基本定理(二重帰納)、停止性=論理関係の系、**Admissibility 定理**(同値・合同・弱化・置換・文脈変換・型保存・検査整合)。No-go に完全導出木+4 スコープ注記、意味論的主張は方法 B に弱め。HIT は argument-wise クラス+分類表。Theorem A/B 二層化。coherence は付録 A へ、付録 B に補題目録 L1–L15。16 頁・0 エラー。valeq マクロの二重下付きバグ修正(\equiv^{val} に変更)。ARTIFACT.md に swSuspMeridD 追記。残: リポジトリ公開(ユーザー)、付録 routine 帰納の展開(頁数増)、S–A 橋渡し表、arXiv→LMCS。

## 2026-07-17 (20): E フェーズ — 操作的メタ理論の正式化(第3次レビュー対応の開発)

第3次レビュー(採択確度 20–30%、「操作的型理論の基礎メタ理論が未証明」)は全面的に妥当と判断。ユーザー指示により**開発を先行、論文改訂(v4)は完了後**。新設 `docs/OperationalMetatheory.md` に正式メタ理論を構築: (1) 表現同値 ≈(クロージャ双模倣+readback 不変性)と型指標付き Kripke PER ≡val — 旧補題 5.1「same value」は構造的等号としては偽(レビュー 3.2 が正しい)ことを認め格上げ。(2) **constancy 検査の仕様/実装分離**(中心的設計判断): 体系は const?_spec(F,ℓ) := ℓ∉FV(quote F) で定義、健全性定理(spec ⟹ 両端 ≡val; quote/作用可換+NbE 冪等性)、実装 usesLvl は健全な近似(lb カット正確、チューブ走査の過大報告は安全方向 — usesLvl 実装を精読して確認: binder 閉包は generic 実体化、チューブ閉包は非実体化走査)。(3) 意味論的置換補題(≈ レベル; 仕様検査が ≈ 不変だから transp 分岐が一致 — 仕様化が置換補題の成立条件そのもの)。(4) admissibility 一括(基本定理→同値・合同・弱化・置換・文脈変換・型保存・型検査整合)。(5) 停止性を論理関係に畳み込み(Tait 流)、transp 負分岐は型値帰納との二重帰納と明示(循環疑義解消)。(6) No-go 完全導出木+意味論的主張は方法 B に弱め(countermodel は Open Problem)。(7) Theorem A(Cartesian)/B(De Morgan)二層化。(8) HIT を argument-wise 署名クラスに限定(分類表; qeq 系は臨界対空虚)+ 新 probe swSuspMeridD(susp のパス構成子 merid の switchover 収束)ビルド通過。残: 機械的分量作業(両立補題個別化・基底節転写・導出木 LaTeX 化)、S–A 対応表、pushout probe(任意)、リポジトリ公開(ユーザー)。その後 v4(25–35 頁+付録、coherence 定理は付録へ移動検討)。

## 2026-07-17 (19): 論文 v3 完成 — No-go 定理+操作的定式化を中心に全面改稿(12 頁エラーゼロ)

D6 実行: jrefl.tex を v3 に改稿(v2 は jrefl_v2_backup.tex)。新構成の核: (1) **No-go 定理** — 無制限 T₀+(R) は定数チューブ hcomp-regularity を導出(機械証人 = LibSwitchover の Path 負例)、衝突は Glue 以前に Path で発生、制限版規則集合は置換非閉(第2次レビュー 3.1 を定理の一部として肯定的に採用)。(2) **操作的定式化** — 判断的等式 = 優先化 NbE のアルゴリズム的等式;NbE 置換補題(transp 節完全証明)、停止性、決定性。(3) soundness は T₀+(R) への包含、completeness は No-go により**原理的に不可能**と明示(decision procedure の語を全廃)。(4) canonicity は (A1)–(A4) 仮定パッケージ相対化+環境ベース fundamental lemma+継承目録。(5) switchover 解析節(収束補題+Glue 残滓計算)。(6) 文献に UIP プレプリント・Huang 正規形ノート・Arend 言語論文を追加、謝辞にレビュー 2 巡を明記。12 頁・0 エラー。ARTIFACT.md に switchover probe 対応行を追加。残: リポジトリ公開(ユーザー)、付録拡張(規則完全列挙+canonicity 全展開、RegularityProof §10.6)で LMCS 推奨長へ伸ばすかの判断、arXiv→LMCS。

## 2026-07-17 (18): ★ 第2次レビュー対応の開発開始 — switchover 不可能性の発見(LibSwitchover)★

第2次外部レビュー受領(判定: 新規性は認めるが正しさ不足)。最重要指摘 3.1「¬Const は置換に安定しない」は正しく、しかも機械実験で**修復不可能**と判明: 新設 `LibSwitchover.lean`(ビルドチェーン組込済、全 guard 通過)により、定数族での構造 contractum は Π/Σ/依存Σ/HIT では u と収束するが、**PathP では不収束**(端点補正 comp が定数チューブ hcomp として残留 — `trans refl refl ≢ refl` と同機構)。帰結: 無制限 T₀+(R) は hcomp-regularity 型等式を導出 ⟹ **優先化は Glue 以前に Path で理論的に強制される**(新知見・論文の物語の核に昇格)。採用アーキテクチャ(RegularityProof.md §8): 判断的等式 = NbE アルゴリズム的等式として定義、置換安定性 = NbE 置換補題(constancy 検査は値レベルなので transp 節も構造的に成立 — レビュー要求の coherence 補題)、規則制限型 T^≺ は破棄、canonicity は操作的に再構成、「decision procedure」→「sound conversion checker」、基底メタ理論は Assumption パッケージに相対化。開発計画 D1–D6 を PaperNotes §12 に記録(D1・D2 完了)。**論文再執筆は D3–D5 完了後**(ユーザー指示)。残: D3 不可能性定理の定式化+Glue 残滓計算、D4 canonicity 全面展開、D5 Arend 一次ソース+リポジトリ公開(ユーザー操作)。

## 2026-07-17 (17): 外部批評レビュー対応 — 論文全面改訂(v2、9 頁エラーゼロ)+ ARTIFACT.md 新設

ユーザー提供の外部レビュー(詳細批評)を受け jrefl.tex を全面改訂(旧版は jrefl_v1_backup.tex)。核心対応: (1) **φ 明示構文を基礎理論に採用** — φ 非明示だと (R) が congruence+(S) から導出可能というレビュー指摘は正しく、ABCFHL 流 transp^i A φ u に変更して (R) を真の拡張として定式化(Remark: 二重の読み — φ 明示では新等式、φ 非明示では新決定アルゴリズム)。(2) T^≺ の循環を層化定義で解消((R) の側条件は T₀ の正規形で定義、実装の値レベル検査は保守的と明記;新 §Algorithm で eval/const?/conv の相互再帰+well-foundedness 補題)。(3) canonicity と decidability を定理分離、**完全性は未証明と明示**(負例カタログは「アルゴリズム非受理」の主張;完全性が主要残タスク)。(4) Prior art 段落新設(2021 Arend 公開議論を認知、貢献を「構造規則・Glue 相互作用の初のメタ理論的分析」に再位置付け)、タイトルを Evaluation-Time Constancy Inference for Transport in Cubical Type Theory に変更。(5) Artifact 段落+リポジトリ直下に ARTIFACT.md(ビルド手順、論文↔probe 対応表(実名検証済み)、golden 説明、スコープ声明)。(6) Related work 4 段落化(Arend/Isaev、Sterling–Angiuli 追加)。詳細は docs/PaperNotes.md §11。残: リポジトリ公開 URL(ユーザー操作)、Arend 議論一次ソース引用、(推奨)完全性証明プランの付録化、arXiv→LMCS。

## 2026-07-16 (16): 著者情報確定 — 論文最終版コンパイル済み

docs/paper/jrefl.tex に著者情報を反映: Ryota Shibusawa / Daiichi Institute of Technology, Japan / r-shibusawa@daiichi-koudai.ac.jp。8 頁・エラーゼロ・未定義参照ゼロ。残る投稿前作業: Swan note の最終典拠確認、アーティファクト(リポジトリ)公開準備、LMCS への投稿手続き(episciences 経由、arXiv 先行投稿が標準フロー)。

## 2026-07-16 (15): 投稿前必須作業を完遂 — canonicity 証明完成・予想解消・論文 8 頁エラーゼロ

**分析的前進 2 件(論文の主定理が無条件化)**:
1. **旧 Conjecture 1(Glue 臨界対)を解消**: 優先度付き理論 **T^≺**(定数性検査を定義の一部に; 補題 2 が well-definedness を保証)を公式対象に。Glue 構造規則は「手書き transpGlue 展開」という実用上到達不能な一例を除き全導出。残滓は scoped open question(無優先提示との一致)に降格 — 結果は非依存。
2. **Canonicity 定理を証明**(拡張による証明): Huber 型計算可能性論証への唯一の新ケース((R)-redex)を「IH + 型保存 + 述語の equality/head-expansion 閉包」で完全処理。well-definedness 2 点(述語の閉包 — どの節も transp redex の形を検査しない; 評価の決定性・停止性 — (R) はサイズ減少)を明示。

**論文更新(docs/paper/jrefl.tex、8 頁・エラーゼロ・未定義参照ゼロ)**: §5.5 T^≺ 定義、§6 Canonicity(完全証明+scope 注意)、主定理無条件化(「消えた予想」を要旨・序論・結論・表から一掃)、Swan/Sattler 書誌を精密化(arXiv:1808.00920 等)。RegularityProof.md にも反映。

**投稿前に残るのは事務のみ**: 著者名・所属の確定(ユーザー判断)、最終文献照合(Swan の regularity note の正式典拠、Cubical Agda の transpFill 周りの記述確認)、アーティファクト(リポジトリ)公開準備。数学的中身は完結。

## 2026-07-16 (14): 論文ドラフト作成 — docs/paper/jrefl.tex(LMCS 形式、コンパイル済み)

**新規性評価(回答済み)**: 純数学誌向けではなく論理学/理論 CS 誌向け。**推奨: LMCS(Logical Methods in Computer Science)** — ダイヤモンド OA(**掲載料ゼロ**)、分野の代表的専門誌(IF は分野特性上 ~0.6-0.9 と控えめだが、この分野に高 IF 誌は存在せず、LMCS が最良のバランス)。代替: MSCS(Cambridge)、ACM TOCL。

**docs/paper/jrefl.tex**(lmcs.cls 取得済み・pdflatex エラーゼロ): "Evaluation-Time Constancy Inference Gives Cubical Type Theory a Definitional J on refl"。構成: Intro(J-refl 問題と5貢献)/ Setting / The rule(補題1+φ-推論注意)/ Metatheory(補題2 代入安定性=完全証明、補題3、補題4 臨界対表+「(R) は Σ-η を導出」、**Conjecture 1(Glue 等式版)・Conjecture 2(canonicity)を明示**、主定理は modulo conjectures と正直に)/ **Theorem(再パラメータ化コヒーレンス、完全証明)**/ 厳密性カタログ表 / 実装 / Related work(ABCFHL の φ・regularity 否定結果との非衝突・XTT)/ 結論。参考文献 8 件。

**投稿前の必須作業**: (1) Conjecture 2(canonicity/NbE 論理関係)の証明完成 — 主定理を無条件化;(2) Conjecture 1(Glue);(3) 著者名・所属の確定;(4) 文献の正確な書誌(Swan/Sattler の note の正式な引用形);(5) 実装セクションの主張の最終検証状態との整合。

## 2026-07-16 (13): ★ 新定理第 1 号確定 — 再パラメータ化コヒーレンス定理(完全証明)★

**docs/ReparamCoherence.md**: 定理 C の完全証明を執筆完了。

**定理 C**: generic 文脈で、角の値が一致する自由 De Morgan 代数元 φ, ψ について
⟨i⃗⟩p(φ) ≐ ⟨i⃗⟩p(ψ) ⟺ φ = ψ in DM(i⃗)。
**コヒーレンス読み**: 接続代数の generic 道への作用は自由 DM 代数に忠実 — 再パラメータ化層の定義的コヒーレンスの完全な特徴付け。

- 証明: 健全性 = dnf 標準形定理 + 準同型性; **完全性** = convNe-papp が r.equiv(dnf 等価)を要求 + 崩壊/非崩壊の場合分け(片側崩壊は var vs papp で棄却)。カーネル 4 節((E)(C1)(C2)(D))のみに依存、理論版への持ち上げ条件も明記。
- **機械的証拠を完全化**(LibStrictness §8): 負 probe 2 種(`⟨i⟩p(i∧¬i) ≢ refl`、`⟨i⟩p(i∨¬i) ≢ refl` — **自由 DM 代数の排中律不在がそのまま定義的等式に反映**)+ De Morgan 双対の正 probe(2 変数、境界簿記に注意: ⟨j⟩p(¬(i∧j)) の端点は b と p(¬i))。全ガード通過・golden 299 不変。
- 系: 1 変数の定義的等価類の完全分類(6 元)、symm+接続のみの図式のコヒーレンス決定可能性。
- 限界の明示: trans/hcomp 層は対象外(本質的に弱い — カタログ済み)。次段階 = hcomp-セルを法とする正規形理論。

これで新定理プログラムの成果物: **定理 C(確定・完全証明)+ 定理 R'(主要補題証明済みの下書き)**。

## 2026-07-16 (12): 定理 R' 証明下書き第一稿完成 — docs/RegularityProof.md

- **η-在庫を機械的に完結**(LibStrictness §7): 関数 η・Σ η とも本カーネル conv で成立(path-η は既済)。臨界対収束(補題 4)の前提が全て機械検証済みに。
- **重要な派生観察**: T₀+(R) は Σ-η を**導出**する((R)+Σ-構造節 → surjective pairing)— η なし基礎では (R) が η を強制する、という理論的に面白い副定理。
- **RegularityProof.md**(§0–7): 設定、補題 1(定式化同値)、**補題 2(代入安定性 — 完全証明)**、補題 3(型保存)、補題 4(臨界対表 — Glue 以外完結、Glue は決定的戦略で回避+等式版は残作業)、主定理(canonicity+決定可能性、NbE 論理関係戦略)、**誠実に開いた問題**(cubical 集合モデルでの transp-regularity、Glue 等式版、正規化依存)、論文構成案 7 節。
- 位置づけ: 候補 R' は「証明戦略が明確」から「**主要補題は証明済み・残作業が列挙された下書き**」へ前進。残る本体は NbE 論理関係の成文化と Glue 等式ケース。

## 2026-07-16 (11): ★ 候補定理 R の決定的鋭化 — 「評価時 φ-推論」の可容性定理へ ★

**vtransp 節ごと監査完了**(RegularityNotes §7): 規則が真に追加するのは「**中立 i-自由族への transp = id**」のみ(基底型は無条件、構造型は再帰、Glue は transpGlue が計算)。

**再定式化**(§8): ABCFHL の `transp A i1 u = u` は既に標準・健全。Agda で J-refl が計算しない真因は **φ が定義時固定**なこと。本カーネル = **φ の評価時再推論**(正規形 i-自由 ⟹ φ:=i1)。

**候補定理 R'**: 簡約規則「transpⁱ A u ⟶ u if i ∉ nf(A)」は cubical 型理論で**可容**(SR・合流・canonicity 保存)。系: J-refl 定義的。**証明の心臓 = 代入安定性補題**(i は束縛次元なので σ が i を持ち込めない → nf の i-自由性は代入安定)— 紙上証明が明確な射程。Swan/Sattler とは衝突箇所なし(hcomp 無関係・判断的定数性のみ)を明文化。

**評価**: 「モデル論的危険を伴う候補」→「**明確な証明戦略を持つ可容性定理候補**」に格上げ。論文主張形(案): "Evaluation-time constancy inference gives cubical type theory a definitional J-refl"。残作業: 代入安定性の精密証明・合流・canonicity(NbE が構成的証拠)・hcomp 無害性(済)。

## 2026-07-16 (10): ★ 論文級候補の発見 — 正規形 regularity と定義的 J-refl(docs/RegularityNotes.md 新設)★

**危険地帯 probe 群(LibStrictness §6、全ビルド緑・golden 299 不変)の結果**:
- transp ⟨i⟩U ≐ id: **是** / transp 定数 Path-族 ≐ id: **是**
- **transport (ua idEquiv) x ≐ x: 是(transpGlue 計算による — constancy 規則不使用)**
- 値が定数なら構文が i を含んでも発火(p@(i∧0) 族): **是**
- trans p refl ≐ p(hcomp-regularity): **否**(本規則は transp のみ — Sattler 反例と当たる場所が違う可能性の根拠)

**発見の総括(docs/RegularityNotes.md)**: 本カーネルの transp constancy = 構文的側条件 `i ∉ A` の conversion 閉包(正規形 regularity)。帰結: **J d refl ≐ d が定義的**(cubical Agda の有名な難点の解消)。候補定理 R「CCHM + 正規形 regularity は健全で J-refl を定義的に検証」— 健全性分析(CCHM transp の節ごと検証、canonicity、モデル論 — Swan/Sattler の regularity 結果との正確な差分)が定理化の本体。候補定理 C(再パラメータ化コヒーレンス、De Morgan 正規形)は先に紙上証明が届く小定理。分析計画・文献リストはノート参照。

## 2026-07-16 (9): ★ 新定理プログラム始動 — 厳密性カタログ第1弾(LibStrictness)全通過 ★

**目的**(docs/PaperNotes.md §8-9): ターゲット1「cubical 固有の弱ω-亜群定理(厳密化の特定)」・ターゲット2「接続代数のコヒーレンス定理」の経験的基盤。

**結果表(このカーネル = CCHM 一実装における定義的成立)**:

| 法則 | 定義的? |
|---|---|
| ⟨i⟩p(i∧i) ≐ p、⟨i⟩p(¬¬i) ≐ p、吸収律の正方形、⟨i⟩p(i∧0) ≐ refl | **是**(区間 DNF 正規形) |
| path-η: ⟨i⟩(p@i) ≐ p | **是** |
| symm refl ≐ refl、symm∘symm ≐ id | **是** |
| cong f refl ≐ refl、cong id ≐ id、cong f∘symm ≐ symm∘cong f、cong(g∘f) ≐ cong g∘cong f | **是** |
| transp 定数族 ≐ id(constancy 規則) | **是** |
| **J d refl ≐ d(値レベル regularity!)** | **是** |
| trans refl refl ≐ refl | **否** |
| cong f (p⬝q) ≐ cong f p ⬝ cong f q | **否**(J 要) |
| symm(p⬝q) ≐ symm q ⬝ symm p | **否** |

**最重要発見: J-refl が定義的**(cubical Agda では不成立 — transportRefl は命題的)。原因は本カーネルの transp constancy 規則が**値レベルの regularity** として働くため。**両義的な発見**: (a) 研究機会 — 「regularity 付き CCHM の定義的等式構造」はそれ自体が調査対象; (b) **健全性の要注意点** — full regularity は標準 cubical 集合モデルで不成立(Swan/Sattler 系の結果)。本カーネルの値レベル版がモデルを持つかは**未解決の重要問題**として要調査(paper A の "tested, not verified" 節で明記必須; 最悪、constancy 規則の適用条件を狭める必要が生じ得る)。

**浮かぶパターン(定理候補の種)**: 「**区間 De Morgan 代数の正規形で吸収される法則+値が構成子を跨がない再インデックス(symm/cong/η)は定義的; hcomp を生成する法則(trans 系)は本質的に弱い**」— ターゲット2の正規形理論の第一予想として定式化価値あり。

次: カタログ拡張(HIT 計算則の厳密性、whisker/正方形交換の定義的インスタンス、transpGlue 系)→ 予想の精密化 → regularity のモデル論調査。

## 2026-07-16 (8): 論文執筆メモを文書化 — docs/PaperNotes.md

新規性評価(文献照合済み)と執筆計画を `docs/PaperNotes.md` に記録。要旨: 純数学の新定理はほぼ無し; 候補 A = システム+方法論論文(BGpd プリミティブ→分類定理の軽量化、golden 方法論、Lean 4 知見カタログ)、候補 B = 非切り詰めコヒーレンスの proof pearl(cubical Agda GroupoidLaws との技法比較が採否の生命線)。着手前必須: 検証状態の峻別(構成済み・未検証の 3 件はネイティブ完走 or 明示除外)、カーネルは「tested, not verified」と記載、文献精査の残り。着手は保留中 — 再開時はこのメモから。

## 2026-07-16 (7): ★★ 分類定理完成 — BGpd(Π₁A) ≃ A、全て軽量ガードで完全検証 ★★

**`bgFundEquiv : Π A (gA : isGpd A). BGpd(Π₁A) ≃ A`** と **`bgFundIs : BGpd(Π₁A) ≡ A`(ua)** が**インラインガードで通過** — 次元 1 の分類定理(「全ての 1-型は自身の基本亜群の分類空間」)が、**連結性・基点なしの完全一般形で機械検証完了**。

構成の最終部品:
- `bgptRetr`(単位): bgelim、pb = refl、**pl-cell = barrCongBpt @ (¬j) @ i**(純再索引 — 設計どおり)、gP = isSetToGpd ∘ isGpdBG-部分適用(isSetR(Path BG a b) が isGpdR BG の部分適用形と一致する観察)、pc-cell = toPathP + isPropPathPSet 放電(toFromD パターン; Lof は bcomp 上の PathP)。落とし穴 1 件: `apps (cmpOf A) [...]`(生ラムダ app-頭)→ transD.ref 直接適用に置換(conv 等価)。
- 組立: isoToEquiv [BG, A, gpdRec, bpt, gpdRecPt, bgptRetr] → ua。

**この定理の意義**: homotopyHyp1(基点付き連結、ネイティブ検証保留)を包含する一般形が、**軽量検証で完結**した。理由: BGpd 側で作った同値は encode-decode(重い Codes/ua 輸送)を完全に回避し、除去子の計算則(gpdRec が点・射で refl)+ コヒーレンスセル(transFill/barrCongBpt)だけで閉じる — **HIT を「正しい普遍性で」カーネルに足すことが、重い証明を軽くする**という、このプロジェクト最大の方法論的成果。

残る発展: BGpd(groupToUnitGpd G) ≃ K(G,1)(em1 との一致)、亜群圏の同値としての整備、docs 更新(済ませる)。

## 2026-07-16 (6): 単位側の全補題完成 — barr ≡ cong bpt(J)+ カーネル欠陥 1 件修正

**全ガード一発〜二発通過(LibTower)**:
- `isGpdBG : Π Ob hom cmp. isGpd (BGpd ...)` — bsquash 逐語(isGpdEM 鏡写し)。
- `barrComp : ⟨i⟩barr(cmp f g) ≡ barr f ⬝ barr g` — **任意の BGpd で**(emloopComp の bcomp 鏡写し、k=1 面は transFill 型内部 hcomp)。
- `barrRefl : ⟨i⟩barr(refl) ≡ refl`(bgFundR)— 群論的 5 段鎖: unitL 逆 → cancelL 逆ウィスカ → assocConn 逆 → E-ウィスカ(E : a⬝a ≡ a = symm barrComp ⬝ cong-barr(transReflR))→ cancelL。
- **`barrCongBpt : ⟨i⟩barr p ≡ cong bpt p`** — J、refl ケース = barrRefl(cong bpt refl ≐ refl)。**単位側 pl-cell の核心補題**。

**カーネル欠陥修正**: vhcomp ディスパッチに vbgpd 枝が無く catch-all panic に落下(「vhcomp: not a composable type」)— em1 鏡写しの stuck-neutral 枝を追加。**教訓: 新 HIT 追加チェックリストに「vhcomp/vtransp ディスパッチ枝」を含める**(Phase A リストにあったが実装漏れ; barrComp の hcomp 証明が初の実行経路で検出)。

**残り(BGpd(Π₁A) ≃ A 完成)**: 単位 `bgptRetr := bgelim[motive t := Path BG (bpt(gpdRec t)) t]`: pb = refl、**pl-cell = λ i j. barrCongBpt @ (¬j) @ i**(端点検算済み: j=0→bpt(p@i)、j=1→barr@i、i=0/1→refl)、gP = isSetToGpd ∘(isGpdBG → path-空間は集合)、pc-cell = toPathP + isPropPathPSet 放電(toFromD パターン)。その後 isoToEquiv [BG, A, gpdRec, bpt, gpdRecPt, bgptRetr] → **bgFundEquiv**、ua → **bgFundIs : BGpd(Π₁A) ≡ A**。

## 2026-07-16 (5): bgelim(依存除去子)+ 余単位 gpdRec — BGpd カーネル完成、数学始動

**bgelim(Phase C'、全配管 + 規則、golden 289 不変)**:
- Syntax/Semantics: bgelim Term/Raw(motive は binder 付き)、Neutral.bgelim、Closure.bgelimTube、vbgelimApp(vem1elim 鏡写し — hcomp は `vcomp (.comp motive (.hfill ...))` で動機越しに通勤)、全 total-match 配管。
- **TypeCheck 規則は新クロージャゼロ**: gP 型 = `vpiAt bgV (.comp isGpd-closure motC)`(閉 isGpdTm の closure を .comp 合成!)、pb 型 = `.comp motC bptC`(bptC := mkAt [] (.bpt (var 0)))、pl/pc 型 = **motive を関数値 `vlamAt motC` として env に入れた Term 合成**(pl: envL=[pb,mot,hom,ob]、pc: envC=[pl,mot,cmp,pb,hom,ob]; barr/bcomp を型内で直接使う — fam 内 +itv シフトに注意)。

**バグと教訓**: bgrec 規則の plTy の f-домен が de Bruijn 誤りで ob を指していた(hom=env idx1 → k=2 binders で var 3、var 4 は ob)。**スモークテスト(定数セル)はこれを素通し** — 定数 pc はどんな期待型にも合いがち。**教訓: 規則の煙テストには非定数セルを必ず含める**(今回 gpdRec の transFill セルが即検出)。

**余単位(LibTower、全ガード通過)**:
- `bgFundR A := BGpd(A, Path A, trans)`(基本亜群の分類空間)
- **`gpdRec : Π A gA. BGpd(Π₁A) → A`** — bgrec[pf=id, pl=id, **pc=transFill**](loopRec と同じ噛み合わせ: bgrec の pc 期待型が transFill の型と文字通り一致)
- **`gpdRecPt : gpdRec (bpt a) ≡ a` — refl**、**`gpdRecArr : cong gpdRec ⟨i⟩barr(p)(i) ≡ p` — refl**(点も射も定義的に計算)

**残り(BGpd(Π₁A) ≃ A 完成まで)**: 単位側 `Π t. bpt (gpdRec t) ≡ t` を bgelim で — pl-cell 義務は正方形「bpt(p@i) ≡ barr p @ i」⟺ **`barr p ≡ cong bpt p`**。証明経路(設計済み): (a) `barrRefl : barr refl ≡ refl`(bcomp(refl,refl) 正方形 + trans refl refl ≡ refl の cong-barr 押し出し + 消去 — 群論的標準論法、部品在庫)、(b) J on p で barr p ≡ cong bpt p(refl ケース = (a))、(c) pl-cell = (b) の正方形読み替え(toPathP or 直接)、pc-cell = isPropPathPSet 放電(motive は gP で 1-型 → path-空間は集合)。その後 isoToEquiv → **BGpd(Π₁A) ≃ A(連結性不要の分類定理)**。

## 2026-07-16 (4): ★ BGpd Phase B/C/D-smoke 完遂 — 一般亜群 EM HIT が全面稼働 ★

**Phase B(イントロ検査規則、em1 鏡写し)**: bpt(点 : ob)、barr(x y : ob、f : hom x y の vapp²、checkI r)、bcomp(f g の hom 検査 + **cmp 注釈 ≐ 型の cmp の conv**(emcomp の mul 規則鏡写し))、bsquash(emsquash 丸写し、vbgpdAt/vpathPAt 使用)。

**Phase C(bgrec の infer 規則)**: 設計どおり **Raw 合成 + 明示 env**(新 Closure 不要): gB は閉 isGpdTm 適用、pf : arr obV BV は vpiAt+constV、**pl 型は envL=[pf,hom,ob,B] 上の合成 Term**(束縛下インデックス: k 個の binder で pf=k, hom=k+1, ob=k+2, B=k+3)、**pc 型は envC=[pl,cmp,pf,hom,ob,B] 上の PathP Term**(binder 5 + 区間で pl=6, cmp=7, pf=8, B=11; 内側 path も .pathP で B=12)。**Term の .path は存在しない — .pathP(fam のみ +1 シフト)**。

**Phase D スモーク(LibTower、全ガード通過)**: BGpd(Unit, ℤ, +) で形成 bgZForm、点 bgZPoint、射ループ bgZArr(barr 3)、**合成正方形 bgZComp(PathP、bcomp — papp 頭の生 plam は要 .ann の規律再演)**、**再帰子計算: bgrec(...)(ann (bpt tt) bgZ) が ipos zero に正規化**(scrutinee は infer されるため要注釈)。

**カーネル拡張の完了状態**: 形成・4 イントロ・再帰子(点/射/正方形が計算、squash は emsquashCell 中立、hcomp 通勤)が端から端まで機能。golden 289 全不変。**未実装(必要時に)**: 依存除去子 belim(em1elim 鏡写し + Raw 合成方式で可能)、transp/hcomp の BGpd 型での Kan 構造(現状 stuck = 健全)。

**Phase D 本番(次)**: `BGpd(fundGpd A) ≃ A`(連結性不要の dim-1 ホモトピー仮説一般形!)、`BGpd(groupToUnitGpd G) ≃ K(G,1)`。encode-decode は em1 の Codes 構成の鏡写し(hom への transp — BGpd 上の Kan が必要になる時点で transpGlue 級の作業が発生する可能性 — 要調査)。

## 2026-07-16 (3): ★ 一般亜群 EM HIT(BGpd)Phase A 完了 — カーネル拡張、全緑・golden 検証済み ★

**「亜群 ≃ 1-型」逆方向のカーネル拡張を開始、Phase A(構文+意味論+形成規則)完了**:

- **Term/Raw ctors**: `bgpd (ob hom cmp)` / `bpt t` / `barr (x y f r)` / `bcomp (cmp x y z f g r s)` / `bsquash (9引数, emsquash 同形)` / `bgrec (bT gB pf pl pc t)` — dependsOn/shift/resolve 配管済み。
- **Val ctors(lb 規律準拠)**: vbgpd/vbpt/vbarr/vbcomp/vbsquash + Neutral.bgrec + Closure.bgrecTube。smart ctors(vbgpdAt 等、children-max)、quickLb/valLbGo/neLb/closureLb/neQuickLb/quickLbC 全アーム、Val.head。
- **force(端点崩壊)**: barr r∈{0,1}→bpt x/y; **bcomp 正方形**: ri=0→bpt x、ri=1→barr y z g rj、rj=0→barr x y f ri、rj=1→barr x z (cmp⁵ f g) ri(emcomp の多対象鏡写し、角の整合確認済み); bsquash = emsquash 同形。
- **vbgrecApp(vem1rec 完全鏡写し)**: bpt→pf t; barr→papp(pl³ f); bcomp→二重 papp(pc⁵ の c-セル)、bsquash→emsquashCell 中立ラッパ(汎用)、hcomp→bgrecTube 通勤、junk passthrough。
- **eval/quote/conv/usesLvl 全配管**、convNe bgrec 対。
- **TypeCheck**: bgpd **形成規則実装済み**(em1 鏡写しの Raw 型合成: hom : Π ob ob U、cmp : Π x y z. hom x y → hom y z → hom x z、shift 計算注意)。イントロ(bpt/barr/bcomp/bsquash)と bgrec 除去は**明示的拒否スタブ**(健全、Phase B)。
- **golden 誤警報と改良**: allDefs 増加で位置ずれ 62 件 → 名前突合で**既存 279 全ハッシュ不変を確認**(Phase A 挙動保存の証明)→ checker を名前キー化、基準 289 定義に更新。

**Phase B(次)**: check イントロ規則 — bpt: `.bpt t, .vbgpd _ ob _ _ => check t ob`; barr: x y : ob, f : hom x y (vapp²), checkI r; bcomp: cmp ≐ 型の cmp と conv 必須(emcomp の「mul 注釈は型の mul と一致」規則の鏡写し — em1 の該当規則を確認)+ f g の hom 検査 + rj ri checkI; bsquash: emsquash 規則鏡写し(x y : BGpd, p q : Path, u v : 2-cell — em1 の emsquash 規則を丸写しし .vem1→.vbgpd)。
**Phase C**: bgrec の infer 規則 — bT sort、gB : isGpd bT(isGpdRaw 閉 Raw 適用、em1rec 同様)、pf : Π ob bT?? 実際は arr ob bT(eval-closure 合成: `Closure.mk [obV,bTV] raw` トリック or Raw 合成+env)、pl : Π x y (f : hom x y). Path bT (pf x)(pf y)(Raw 合成: env=[pf,hom,bT] インデックス参照で組む)、pc : Π x y z f g. PathP(λ rj. Path bT (pf x) (pl y z g @ rj)) (pl³ f) (pl³ (cmp⁵ f g))(em1recCCod 流の閉包 or Raw 合成)。**推奨: Raw 合成 + 明示 env**(新 Closure ctor 不要 — glueTy 規則の equivT 方式)。その後 belim(依存版)は必要になってから。
**Phase D(数学)**: BGpd(fundGpd A) ≃ A(連結不要の一般ホモトピー仮説 dim-1!)、BGpd(unitGpd G) ≃ K(G,1)。

## 2026-07-16 (2): EH の代数的結晶 — 「任意の型の Ω² は可換モノイド」(一発通過)

- **`commMonoidTy`**: 可換モノイドの Σ-塔(**無切り詰め** — 法則は裸の道、集合性仮定なし)。
- **`loop2CommMonoid : Π A a. commMonoidTy`(Ω²(A,a) 上)** — 乗法 = trans、単位 = refl、結合 = assocConn、単位律 = transReflL/R、**可換性 = eckmannHilton**。古典的定理「2 次ループ空間は可換モノイド」が全部品在庫の組立てで完成、allDefs 登録。
- **`towerCommMonoidD n`**: 全レベル Ωⁿ⁺² への持ち上げ(n=0..2 ガード通過)— 塔の各段が可換モノイドを担う。

タワー最終形: 各レベルに Mac Lane コヒーレンス 6 段 + 厳密 Ω-関手 + 可換モノイド構造。コヒーレンス章の成果(EH・assocConn 等)が「使われる代数」として三たび結晶(F₂ 消去セル・基本亜群・可換モノイド)。

次の大テーマ(新セッション推奨): 一般亜群 EM HIT(カーネル拡張 — 「亜群≃1-型」逆方向)。軽量継続候補: whisker 演算と水平合成の 2-圏パッケージ、braiding 自然性。

## 2026-07-16: タワー拡張 — Ω-関手と全レベル厳密関手法則(refl)

LibTower に追加(n=0..3 全ガード通過):
- **`omegaNMap` / `towerMapD n`**: 反復ループ写像 Ωⁿ f : Ωⁿ(A,a) → Ωⁿ(B, f a) — 基点を像に取ることで **cong の反復が無共役で**立つ(cong f refl ≐ refl が各レベルの基点保存を定義的に与える)。
- **`towerMapCompD n`: Ωⁿ(g∘f) p ≡ Ωⁿg (Ωⁿf p) — 全レベル refl 証明**(congComp の反復厳密性)。点ごと言明。

**デバッグ知見(チェッカーの推論規律)**: 「cannot infer λ」の犯人は**型・端点位置に現れる生ラムダの適用**(`gf a`)— レベル 2 以降で基点 `(g∘f) a` が型に入り顕在化。**規律: Raw ラムダを app の頭・端点・基点に置くときは常に `.ann`**(gf := ann (λt. g(f t)) (arr A C) で全解決)。probe による単体切り分け(lhs だけの towerMap-gf 版)が有効だった。

タワー現況: 各レベルに Mac Lane コヒーレンス一式(6 段)+ **Ω-関手(厳密)**。次候補: 塔の braiding 自然性、または一般亜群 EM HIT(カーネル拡張)。

## 2026-07-15 (11): 「亜群 ≃ 1-型」第4章 — 関手法則(refl)と射の圏構造(全通過)

- **`congComp : cong (g∘f) p ≡ cong g (cong f p)` — refl 証明**(両辺 ≐ ⟨i⟩ g(f(p i)))。fundGpd の関手法則が定義的に成立。
- **`gpdMorId`** — 恒等射(保存セルは reflD、hom は U₀ なので OK)。
- **`gpdMorComp`** — 射の合成(保存セル = cong-ウィスカ + trans。**バグ 1 件: G1 の id 射影を comp 射影と取り違え** — Σ-塔の射影は fst(snd)=id、fst(snd(snd))=comp。射影の取り違えは checker が「expected app, inferred Pi」で即検出)。

**「亜群 ≃ 1-型」章、1-型→亜群方向が完備**: fundGpd / gpdAt / groupToUnitGpd / fundGpdLoop(refl)/ gpdMorTy / fundGpdMap / congComp(refl)/ gpdMorId / gpdMorComp。全て軽量ガード・allDefs 登録。逆方向 = 一般亜群 EM HIT(カーネル拡張候補、次の大きな数学テーマ)。

## 2026-07-15 (10): 「亜群 ≃ 1-型」第3章 — 射と関手性(全ガード通過・軽量)

- **`congTrans`(U₀ 版)**: cong f (p⬝q) ≡ cong f p ⬝ cong f q — congTrans@01 の鏡写し(J、refl ケース = 右単位正方形の cong 押し出し)。汎用補題として独立価値(encodeDecode 系で頻出のはずだった穴を埋めた)。
- **`gpdMorTy Ob1 G1 Ob2 G2`**: 亜群の射(対象写像 F0、hom 写像 F1、恒等・合成の保存)の Σ-型。
- **`fundGpdMap : Π A B gA gB (f : A→B). gpdMor (fundGpd A) (fundGpd B)`** — **基本亜群の関手性**: F0 = f、F1 = cong f、恒等保存は**定義的**(cong f refl ≐ refl、インライン plam refl)、合成保存 = congTrans。

章の現況: 基本亜群 ✓ / 頂点群 ✓ / 一対象⟷群 ✓ / 頂点群=ループ群(refl)✓ / **射+関手性 ✓**。残り: 逆方向(一般亜群 EM HIT = カーネル拡張候補)、恒等・合成射と圏構造(gpdMorId/Comp — 軽い)、fundGpd が「関手」であること(cong(g∘f) ≐ cong g ∘ cong f は定義的のはず — refl 一致候補)。

## 2026-07-15 (9): 「亜群 ≃ 1-型」第2章 — 一対象の橋 + refl 一致定理(全て一発〜二発通過・軽量)

- **`gpdAt : Π Ob. groupoidTy Ob → Ob → groupTy`** — 任意の亜群の頂点群(射影塔 + assoc の向き合わせに symm)。
- **`groupToUnitGpd : groupTy → groupoidTy Unit`** — 群は一対象亜群。
- **`fundGpdLoop : gpdAt (fundGpd A gA) a ≡ loopGroup A gA a` — refl 証明!** 基本亜群の頂点群とループ群は、同じ非切り詰めコヒーレンスセルから組み上がるため**定義的に一致**。橋の中核が conv だけで閉じた。
- 落とし穴再演: reflD(U₀ 補題)を groupTy(U₁)に適用 → univ 不一致。**インライン .plam で解決**(メモリの既知 gotcha どおり)。

これで「亜群 ≃ 1-型」章は: 基本亜群(1-型→亜群)✓、頂点群 ✓、一対象亜群⟷群 ✓、頂点群=ループ群(定義的)✓。**残り**: 亜群の射(関手)+ fundGpd 関手性、逆方向(亜群→分類 1-型)は一般亜群 EM HIT(カーネル拡張候補)— 連結ケースは homotopyHyp1 が既にカバー。

## 2026-07-15 (8): 数学復帰 — 「亜群 ≃ 1-型」第1章: 基本亜群(一発通過・軽量)

**`groupoidTy Ob`**(内部亜群構造、groupTy の多対象版): Hom : Ob→Ob→U、id/comp/inv + assoc/unitL/unitR/invL/invR + hom の集合性の Σ-塔。

**`fundGpd : Π A (gA : isGpd A). groupoidTy A`** — 任意の 1-型の基本亜群。**全ての法則が非切り詰めコヒーレンスセルの一行インスタンス**: assoc = assocConn、単位律 = transReflL/R、invL = cancelL、invR = cancelL(symm f)(symm(symm f) ≐ f 定義的)。1-型仮定は hom 集合性のみ(isGpdR の形がそのまま)。インライン #guard 通過(軽量)、allDefs 登録済み。

**この章の残り(次ラウンド以降)**: (a) 亜群の射(関手)と fundGpd の関手性、(b) 一対象亜群 ⟷ 群の橋(loopGroup と接続)、(c) 逆方向(亜群 → 分類 1-型)は一般亜群 EM 型 HIT が必要 — カーネル拡張検討事項(em1 の多対象版)。連結 1-型では homotopyHyp1(構成済み)が一対象ケースを既にカバー。

## 2026-07-15 (7): 文脈共有実験 — 不発。性能アーク総括と結論

**実験**: checkDefCtx + buildDefCtx allDefs(279 定義を環境変数化、全使用が単一値をポインタ共有)で重い定理群を検査(Test/Isolate を chkCtx 化、9 チェック体制)。ctx 構築は 0ms(LibDef はラムダ → eval は閉包生成で O(1))。**結果: windAll 17 分 CPU・315 万 transp でも未完**。プロファイルは激変(カットヒット率が激減 = defn 展開なしで葉が既に共有、RSS 11MB)が、スループットの壁は同じ — 旧コメント(okFast でも深いガード不可、「残余 = conv 時の capp 再実体化」)を追認。

**性能アーク最終総括(2026-07-14〜15)**:
| 手法 | 結果 |
|---|---|
| usesLvl/Ne (ptr,level) メモ | 指数崩壊(14710→571)だが mark_mt 肥大 |
| conv 対メモ / capp メモ | 不発〜逆効果 |
| レベル注釈(Val54+Closure91+Neutral スパイン全 O(1) bound) | +30%(5.4k→7.0k transp/s)、ヒット率 48% — 理論上の最大到達 |
| 文脈共有(checkDefCtx) | プロファイル変化のみ、壁は同じ |

**確定結論**: 重い 16 定理の #guard を通すには**評価器レベルの hash-consing(値の大域共有)または conv 結果キャッシュ**という研究級の再設計が必要。増分パッチの積み増しでは到達しない(全主要変種を実測で棄却済み)。レベル注釈自体は健全な資産として残る(constancy 検査の恒常 +30%、золgolden 検証済み)。

**推奨方針**: 性能はここで凍結し、数学に復帰(軽量検証で進む世界は広い: タワー拡張・亜群≃1-型・π₂ 準備等)。hash-consing は独立の専用セッション(評価器の全 mk サイトを interning 層に通す設計から)。

## 2026-07-15 (6): ★ レベル注釈フルリファクタ完遂 — 全層 O(1) bound、最終計測と残余問題の確定 ★

**リファクタ完了(golden 279/279 + 全ガード + ライブラリ 23 秒、全段検証済み)**:
- Val 全 54 ctor(第 2-3 段)+ **Closure 全 91 ctor(本段)**が O(1) bound: quickLbC を全アーム実装(自動生成 84 + 手書き 6 + reparam のみ世代 fallback)。mutual { quickLbC, envQuickLb, sysQuickLb }。構築・パターン変更ゼロ(非侵襲)。
- 生成器の教訓: Nat.max 折り畳みは括弧必須; 重複 def 削除は挿入済みブロックを誤爆しやすい(2 回発生)— アンカーは一意に。

**最終計測(isolate windAll)**: transp 5.4k → **7.0k/s(累計 +30%)**、カットヒット率 27% → 48%。しかし windAll 完走には桁が足りない。

**残余問題の確定診断(このアークの最重要成果)**: 残るミスは bound の粗さでは**ない** — генeric 変数(transp 定数性検査の当てた var)が実際に流れ込んだ部分項の occurs-check であり、このアルゴリズムでは意味的に必要な walk。つまり**レベル注釈は理論上の最大効果を出し切った**。真のコストは「conv が同じ族クロージャへの transp を繰り返し、毎回 capp 実体化 + walk」すること。

**次の攻め手(新アーク、設計済み)**: **クロージャ単位の意味的定数性キャッシュ** — 定数性はクロージャの性質で depth 非依存(自明: 任意の十分大きい fresh で同値)。ptr キー 1 ビット/クロージャ。mark_mt は挿入時のみ・挿入数 = 相異なる transp 族数(walk 毎回よりずっと少)→ トレードオフ再評価の価値あり。あるいは .mk の Term ポインタ(LibDef 項は安定)+ env 同一性でのキー。

**現状**: カーネルは完全に健全・全成果検証済み。重い 16 定理は引き続き「構成済み・最終検証保留」。

## 2026-07-15 (5): フルリファクタ第2・3段完了 — Val 全コンストラクタのスタンプ化(golden 保護下)

**達成(全段 golden 279/279 + 全ガード通過、ライブラリビルド ~23 秒維持)**:
- **Val 全 54 ctor が O(1) bound 化**: 格納 lb(vne, vpi, vlam, vsigma, vpair, vpathP, vplam, vglueTy, vglue, vsucc, vipos, vinegsuc, vinl, vinr, vlcons, vtin, vqin, vsusp, vpinl, vpinr, vsum, vlist, vquot, vtrunc, vem1, vmerid, vppush, vemloop, vemcomp, vemsquash, vqeq, vqsquash, vsquash, vpushout)+ アトム 0 + IVal 系 levelBound(vi/vsloop/vtloopP/Q/vtsurf)。quickLb は全数網羅(catch-all 撤去済み = 網羅性をコンパイラが保証)。
- **neQuickLb**: Neutral の浅い緊密 bound(スパイン再帰のみ、hcomp タワーは Val 層でカット)→ vneAt が全 69 サイト無編集で緊密化。
- smart ctor 群 vXAt(children-max、O(#fields))+ sysQuickLb/glueTySysQuickLb/glueSysQuickLb/cofQuickLb。
- **計測推移(isolate windAll、transp/s)**: ~5.4k(スタンプ前)→ 6.9k(データ ctor 後)→ 6.8k(Val 全)。ヒット率 27%→47%。**残るミス源を特定: 派生 Closure(~90 ctor)が quickLbC の fallback(fresh+1)で粗い** — Kan 機構(transpPi/mapApp/hcompPi/…)の生成物が全部粗染み。

**次の一手(同レシピ最終回)**: Closure 派生 ctor への lb 追加 or closureQuickLb の per-ctor O(1) 実装(各 ctor のフィールドは Closure/Val/IVal/Nat のみ — quickLb/quickLbC の max で機械的)。フィールド追加より **closureQuickLb を全 92 アームで書く**方が非侵襲(構築サイト変更ゼロ、パターン変更ゼロ)— quickLbC の `| _ => fresh + 1` を置換するだけ。ただし再帰(Closure in Closure)は浅くない可能性(compTube 連鎖)→ フィールド方式が確実。
**教訓追加**: 一括パターン置換は既修正アームを二重ワイルドカード化する(TypeCheck で複数回) — 置換前に対象アームの現状 grep 必須。

## 2026-07-15 (4): フルリファクタ第1段完了 — スタンプ機構確立・golden 保護下で健全、完全展開の計画確定

**達成(全て golden 279/279 一致 + 全ガード通過 + ライブラリビルド 23 秒で検証済み)**:
1. **golden 差分ハーネス**(Test/Golden.lean + golden.txt): リファクタの安全網。各ステップで正規形不変を機械照合 — 今回のすべての変更を保護し、実際に複数の誤りを検出した。
2. **lb フィールド**: Val.vne / vpi / vlam / vsigma / vpair / vpathP / vplam + Closure.mk に `lb : Nat` 第1フィールド追加済み。パターンは `_` 挿入、構築は smart ctor(vneAt/vpiAt/…/mkAt、`fresh`/`depth` スコープ変数を渡す)経由。
3. **quickLb / quickLbC / envQuickLb**: O(1) 子スタンプ読み(スタンプ済み → 格納 lb、閉アトム → 0、vi → levelBound、その他 → 世代 fallback fresh+1)。smart ctor は子の max(緊密)。
4. **usesLvl / usesLvlClosure(.mk)にスタンプカット** + profTick 計測(slot 6=hit, 7=miss)。
5. **重要な運用知見**: (a) bound 計算はゲート必須 — precompiled #guard はネイティブで走るので、実 bound 計算(walk 型)を常時 ON にすると Library elaboration が 190 分級化(sentinel/O(1) なら常時 OK — 現在の quickLb 方式は O(1) なのでゲート不要)。(b) 置換スクリプトの assert 必須 — 「拡張カット」が一度サイレントに不適用だった。

**計測(isolate windAll、20 秒毎カウンタ)**: cutHit ≈ 8M/20s、cutMiss ≈ 22M/20s、transp ≈ 5.6k/s。粗い世代スタンプ → 緊密子 max スタンプでカウンタ**ほぼ不変** — ミスの原因はスタンプの粗さではなく、**ホット内容が未スタンプ ctor**であること:
- **vglueTy / vglue**(ua の Glue 線 = helixF2 の本体!)
- **Neutral 全般**(hcomp 連鎖 = trans 合成のタワー; vneAt は世代 fallback のまま)

**次セッションの実行計画(mechanics は完全に確立済み)**:
1. 残り Val ctor(~46: vglueTy/vglue 優先、次いで vsucc/vinl/… の単純系)+ **Neutral 全 24 ctor** + Closure 残り(derived 系)に lb フィールド。
2. Neutral 構築は除去子で**増分 O(1)**: vapp `| .vne lb n => Val.vne (max lb (quickLb fresh a)) (.app lb' n a)` — 既に手元にある wrapper lb を再利用(スパイン再帰不要)。
3. 変換手順(実証済み): (a) フィールド追加 → (b) `| .ctor ` / `, .ctor ` パターンに `_` 挿入 → (c) 構築を smart ctor へ(コンパイラ誘導で bare-arg 形を個別修正)→ (d) TypeCheck.lean も同様(depth スコープ)→ (e) **毎段 golden check + 全ガード**。
4. 完了後 isolate 計測 → ヒット率が反転すれば windAll 完走 → 三大定理の検証へ。

現状態: カーネルはこの中間状態で**完全に健全・全ガード通過**(スタンプは正しいが未だ効果不足)。golden.txt が参照。バックアップ: scratchpad/Semantics.backup.lean(リファクタ前)。

## 2026-07-15 (3): フルリファクタの安全基盤 = 差分テストハーネス構築

負の結果(sealed の「見えない漏れ」)を受け、**フィールド方式リファクタを健全に進める唯一の道 = 各ステップで正規形が既知良好カーネルと一致することの機械照合**と確定。その基盤を構築:

**`Test/Golden.lean`(golden ランナー)**: allDefs 全 279 定義について `{name: ok/FAIL ty#<hash>}`(checkDef 成否 + 型正規形のハッシュ)を出力。
- `golden gen <path>`: 参照生成(既知良好カーネルで実施済み → `FormalizedMathematics/Cubical/golden.txt`、279 行)
- `golden check <path>`: 現カーネルと照合、MISMATCH を行単位報告。自己照合 GOLDEN OK 確認済み。
- 感度: eval/quote/conv/force の回帰(型正規形変化)+ checkDef 成否変化を捕捉。フィールド追加で bound を誤れば normalize がずれ → 即検出(sealed で悩まされた silent unsoundness を防ぐ)。

**フィールドリファクタの実行計画(この基盤の上で)**:
1. `lb : Nat` を Neutral 各コンストラクタの第1フィールドに追加(`.var → lvl+1`、他は子の max)。ValLb は lvlClosedByCache 短絡付き(defn 証人は O(1))。ClosureLb も同様。
2. スマートコンストラクタ or インライン lb 計算で全構築サイト変換(変換漏れ=コンパイルエラーで安全に検出)。
3. usesLvlNe を `n.lb ≤ l → false` に。
4. **各段階で `golden check` と全既存ガードを実行、一致を確認してから次へ**。差分が出たら bound 式の誤り。
5. Neutral で効果測定(windAll isolate)、足りなければ Closure/Val へ拡張。

現カーネルは既知良好(backup 復旧済み)、golden.txt が参照。次セッションはこの手順で安全にフィールド追加を進められる。

## 2026-07-15 (2): 根本策リファクタ試行 → 負の結果、既知良好へ復旧

**試行**: レベル注釈の最小侵襲版 = `sealed (lb) (n : Neutral)` ラッパー方式。健全な設計:`eval fresh env t` の自由レベルは `≤ fresh`(env値 < fresh + 束縛次元1個)→ 中立結果を `sealed (fresh+1)` で封印、usesLvl が `l ≥ b` で O(1) 短絡。force が透過的に剥がす前提。

**負の結果(重要な知見)**: この方式は**漏れが致命的**。健全性の要は「全 Val head 検査が force を通ること」だが、コードベースには **force 前提の未 force マッチが多数散在**:
- HIT 除去子 8 個(vpushrec/vem1elim/vem1rec/vqelim/vtruncrec/vtorusrec/vsusprec/vs1elim)が `match x with`(force なし)
- natHcomp が `match u₀ with` + genericIs 未 force(int/sum/list は force 済みなのに単独外れ値)
- さらに papp ダミー端点 `.vuniv 0` が漏出(winding が `univ 0` に化けた)— まだ他にも未 force 箇所あり

3 系統修正してもなお誤値。全数監査は全フィールド改修と同規模、かつ**見逃すと静かに偽定理が通る**最悪リスク。→ **バックアップ(sealed 実験前の Semantics)へ復旧、全ガード通過を確認**。

**結論の更新**: 「レベル注釈は機械的」は誤り。健全な唯一の道は Val/Neutral/Closure 全構築サイト+全未 force マッチ監査の**フルリファクタ**(高工数・高リスク)。当面のカーネルは 3 層メモ無し(heavyMemo OFF、defn+lvlClosed のみ)が最良で安定。重い16定理は「構成済み・最終#guard検証保留」を正確な状態として維持。

**教訓(将来のリファクタ用)**: このカーネルで新 Val コンストラクタを足すなら、まず「force を経ない Val マッチ」を全数洗い出す必要がある — 既知の外れ値: HIT除去子群・natHcomp・vpappEta・その他。force 規約は普遍的でない。

## 2026-07-15: 性能切り分けの決着 + タワー interchange 段

**決定的計測(isolate、windAll、defn+lvlClosed キャッシュ ON)**:
- **heavyMemo ON**: 値保持で mark_mt 肥大、RSS 464MB、遅い(108分でも未完)
- **heavyMemo OFF**: mark_mt 消滅、**RSS 51MB 安定**、しかし usesLvl/usesLvlNe の深い構造 walk が支配(共有中立構造をフル反復)— なお 14分+で windAll 未完

→ **両メモとも不十分。Val レベル注釈(根本策)が本当に必要**と確証。分離フラグ `heavyMemoEnabledRef`(既定 OFF)を新設、defn 値キャッシュ+lvlClosedByCache は別ゲート `defnCacheEnabledRef` で維持。当面は heavyMemo OFF が最良(メモリ安定)。memos-OFF が grind 完走するかは isolate 継続観測中。

**根本策の設計(次の大仕事)**: usesLvl のホットは usesLvlNe(中立の深い walk)。Val/Neutral/Closure に「自由レベル上界(maxLevel+1、0=閉)」を構築時付与 → 定数性検査 `bound(generic) ≤ fresh` が O(1)。全構築サイトに触れる機械的だが大規模なリファクタ。中立注釈だけでもホットの大半を刈れる可能性。

**タワー成果(並行、軽量・全通過)**: `towerTriangleD`(前ラウンド)に続き **`towerInterchangeD n`**(congSlide の Ωⁿ ループ合成インスタンス = 中央四交換則)追加。towerLevel は 6 段(comp/assoc/triangle/pentagon/EH/interchange)、n=0..3 全ガード通過。**各レベルが(対称)モノイダル構造の完全な Mac Lane コヒーレンス・データを持つ**ことを機械検証。

## 2026-07-14 (9): タワーに三角形段追加 — Mac Lane コヒーレンス・データが各レベルで完備

`towerTriangleD n`(triangleConn の Ωⁿ インスタンス、Π A a 総称)を LibTower に追加、towerLevel に組込 — **n=0..3 の全ガード通過**。これでタワーの各レベルは合成・結合子・**三角形**・五角形・Eckmann–Hilton を持つ = **モノイダル圏のコヒーレンス公理一式(Mac Lane の対)が全レベルで機械検証**。

ランナー(3 層メモ版)は先頭チェック継続中。完走し始めたら結果回収 → 三大定理の正式化へ。次の大仕事は Val レベル注釈(検証時間の本丸)— ただしランナーが数十分〜1 時間級で完走するなら優先度は再考(必要十分の可能性)。

## 2026-07-14 (8): capp キャッシュ復活実験 — 逆効果と確定、無効のまま保存

安全イディオム(if 系強制: `if ptrAddrUnsafe r == 0` の分岐で r を強制)で capp キャッシュを復活させ uaCompMul で計測 → **2 倍以上の悪化**(6:49 CPU 超で未完 vs 基準 ~190s)。原因: capp 呼び出し 2.4 億回に対しヒット率が低く(conv 駆動の再評価は毎回新規 (closure, arg) 対)、ルックアップ代が純損。RSS は 90MB で安定 — mark_mt 爆発は再現せず(当時の誤診を裏付け)。**結論: capp メモはワークロード不適合。無効(cappCacheEnabledRef=false)のまま、コードは安全イディオム込みで保存**。

**性能作業の最終結論(再確認)**: 有効なのは defn 値キャッシュ(name-only)+ usesLvl/Ne メモ + conv 対メモの 3 層。残る本丸は **Val レベル上界注釈**(O(1) constancy)— 次の大セッションの主題。wedgef2/hh1 は 3 層メモ版で継続走行中(capp 無効)。

## 2026-07-14 (7): conv 対メモ化 + 性能アークの結論 — 根本策の特定

**追加: conv の (ptrA, ptrB, depth) 対メモ化**(convMemoHook/convRun 分離、if-強制イディオム、キー保持)— 別々の評価由来で ptr 短絡が効かない巨大証人の構造比較の再帰重複を潰す層。健全(conv は純関数、ptr 同一 ⊆ 構造同一)。

**現状プロファイル(3 層メモ後)**: 支配項は usesLvl メモの**ルックアップ自体** — 各呼び出しは安価化したが、vtransp 定数性検査の**呼び出し量**が天文学的で、conv 駆動の再評価が毎回新規グラフを作るためミス率も高い。wedgef2/hh1 の先頭チェックはなお長時間級(ただし旧・無限級からは桁改善のはず — 走行継続、監視下)。

**根本策(確定)**: **Val へのレベル上界注釈** — 各値に自由レベル集合の上界を構築時に付与し、usesLvl を O(1) に。全 Val 構築サイトに触れる本格リファクタだが機械的。二次案: メモ表の @[extern] C 実装(5-10×)。

**このアークの成果物(カーネル性能基盤)**: (1) name-only defn 値キャッシュ(健全・実証済み)、(2) usesLvl/usesLvlNe の (ptr,level) メモ(指数崩壊: 14710→571)、(3) conv 対メモ、(4) デッドロック安全イディオム 2 種(スクラッチ ref 強制 / Bool の if-強制)、(5) 診断手順(macOS sample によるホットフレーム解析)。全て defnCacheEnabled ゲートでインタプリタ無影響。

## 2026-07-14 (6): 検証ストール解剖 — 二つの病理を修正(カーネル性能の大幅前進)

**病理 1(全ランナー数時間空転の真犯人)**: defn キャッシュの **(name, fresh) キーが квадratic 死**を招いていた — エントリが名前×全深度に爆発し、線形 List.find? がサンプルの 79%。**name-only キーへ復帰**(健全性根拠: 30M ヒットの uaCompMul が name-only で正しく OK — 閉じた defn 値はこの NbE では fresh 非依存)。

**病理 2(既知の「埋め込み証明サイズの壁」の正体)**: `usesLvlNe`(transp 定数性の occurs-check)が **インスタンス化ベースの歩行で指数化** — consGEquiv 内の isSetF2 級証人を共有なしに再帰歩行。**修正: usesLvl / usesLvlNe の (ptr, level) メモ化**(usesLvlMemoV/N、HashMap、キー保持でアドレス有効性担保)。**デッドロック安全の新技法: Bool 結果は `if r then (modify …) else (modify …)` の分岐で強制** — 分岐選択が r の評価を強制するのでスクラッチ ref 不要。付随: defnClosedPtrs(閉値ポインタ集合、スカラーのみで mark_mt 無害)による usesLvl 冒頭ショートカット(単独では不発 — 歩行対象は新規実体化根のため; メモ化が本命だった)。

**効果測定(sample)**: usesLvlNeRun 相対フレーム 14710 → 571(指数崩壊)。現支配項はメモ機構のルックアップ自体 = 実計算が桁違いに進行。hh1 RSS 640MB(メモ表が証人を吸収)。**先頭チェックはなお十数分〜級 — ランナー継続、監視下**。

**残る性能フロンティア**: メモ・ルックアップ自体のコスト(HashMap 汎用機構; @[extern] C 表で 5-10× 可能)、および根本策 = Val へのレベル集合注釈。

## 2026-07-14 (5): ★ メタレベル ω-亜群タワー開始(LibTower)— 全 4 レベル × 4 段一発通過 ★

**新モジュール LibTower**: 2LTT アーキテクチャの実働 — Lean(厳密メタ理論)が外部 n : Nat で対象言語の反復ループ空間 Ωⁿ(A,a) のコヒーレンス構造を添字づける:

- `omegaN A a n`: (Ωⁿ 型, 基点 reflⁿ) の Raw 対
- `towerCompD n` / `towerAssocD n` / `towerPentagonD n` / `towerEHD n`: 各レベルの合成・非切り詰め結合子・Mac Lane ペンタゴン・Eckmann–Hilton — **すべて Π A a. の総称形**(「全ての対象言語型がこの構造を持つ」)。tm は LibCoherence の総称セルの一行インスタンス化(assocConnD/pentagonConnD/eckmannHiltonD が型総称だから可能)。
- `towerLevel n : List LibDef` + `#guard (towerLevel 0..3).all (·.ok)` — **16 定義すべて通過、しかも軽量**(総称インスタンスの検査は小さい)。

**意義**: van den Berg–Garner「型は弱 ω-亜群」の cubical-2LTT 版の出発点 — 有限の各レベルでの合成+結合子+ペンタゴン+EH が、機械検証付きで、型に一様に成立。文書が「実行可能な研究方向」とした項目が実体化。次の拡張候補: 三角形段、交換法則(EH の一般化としての interchange)、レベル間の整合(cong による構造の押し出し)、n を Lean-Π で束ねた「タワー証明書」型。

Library.lean に import 追加(allDefs には n-族のため非登録 — タワーは自前ガード)。

## 2026-07-14 (4): 生きた文書 4 点更新(常設指示)

- ProjectResults EN/JA: ホモトピー仮説節の「レベル1断片」を全面改稿 — **次元1ホモトピー仮説の完全形 K(Ω(A,a),1) ≡ A の構成完了**(証明鎖の要約付き、「重い conversion 検査はネイティブ検証器で走行中」と正直に付記)+ **π₁(S¹∨S¹)=F₂ の完全構成**(共役輸送の定義的計算に言及)。
- StudyGuide EN/JA: 文献 3 項目追加 — Licata–Finster(EM 空間、LICS 2014; 本プロジェクトの dim-1 HH はその cubical 完全展開版)、HoTT Book §8.7 + Cubical Agda 自由群(簡約語戦略の背景)、GroupoidLaws(squareExchange/動く中点イディオムの出典系譜)。
- 4 PDF 再コンパイル(エラーゼロ)。

ランナー: wedgef2(9 チェック)・hh1 とも先頭チェックを粉砕中。他 3 本継続。

## 2026-07-14 (3): ★ π₁(S¹∨S¹) = F₂ 構成完結 — ネイティブ検証中 ★

**全構成完了(コンパイル成功、9 ガードは Test/WedgeF2 ネイティブランナーで検証中)**:

- `consGNoCancel : Π g w rgw. consG g (w, relax rgw) ≡ (g::w, rgw)` — 鍵の定義的事実: **redW(g::w) ≐ redAux w (inr g)**(head 検査が inl tt で true に計算され and true x ≐ x)。listrec 場合分け: nil = sigmaPropEq+refl; cons = eFalse(andElimL → notTrueFalse)→ substD で consStep の fst を b=false 分岐へ輸送(fstFam は Π e3 込みの族、atFalse = refl)→ sigmaPropEq。
- `encodeDecodeF2 : Π s. windF2(decodeF2 s) ≡ s` — 語帰納(listrec、motive = Π r 込み)。cons 鎖 4 セル: transpCompW8 → cong(trGlh)(ih(redRelax r)) → windGen(fst h)(snd h)(Σ-η)→ consGNoCancel。nil = sigmaPropEq。
- `omegaW8F2Equiv : Ω(S¹∨S¹) ≃ F₂` := isoToEquiv [windF2, decodeF2, encodeDecodeF2, decodeEncodeF2@base](decodeAll base ≐ decodeF2、windAll base ≐ windF2 conv)。
- `w8LoopIsF2 : Ω(S¹∨S¹) ≡ F₂` := ua。

**検証キュー(wedgef2、9 チェック)**: windAll → decodeAll → decodeEncodeF2 → windGen → transpCompW8 → consGNoCancel → encodeDecodeF2 → omegaW8F2Equiv → w8LoopIsF2。全 OK で **π₁(S¹∨S¹)=F₂ 正式完成** → allDefs 登録 + HANDOFF + 4 文書更新(常設指示)。

## 2026-07-14 (2): 輸送プローブ全通過 + windGen/transpCompW8 構成

**プローブ 4 連発全 PASS(決定的)**: 順方向輸送 `transp i (helix(genLoop l @ i)) s ≐ consG l s` が**全 4 文字で定義的** — 左円の直接ループのみならず、**右円の共役合成路(pushP⬝rloop±⬝pushP⁻¹)に沿う輸送まで** transpGlue + hcomp-族輸送が直接計算する。encodeDecodeF2 の (b) に補題不要。

構成(ガードは Test/WedgeF2 ネイティブ、現 5 チェック体制で再起動):
- `windGen (b1 b2 : Bool) : Π s. transp(helix∘genLoop(b1,b2)) s ≡ consG (b1,b2) s` — 二重 sumcase、各枝 refl(プローブの一般化)
- `transpCompW8 : transp(helix∘(p⬝q)) u ≡ transp(helix∘q)(transp(helix∘p) u)` — J on q、refl ケース = cong(transp-·)(transReflR p) + 定数族 constancy

**encodeDecodeF2 残り部品**: (c) redAux の構造読解 → redTail(IH 用)+ noCancel 抽出(isTrue(and …) → andElimL/R → cancels ≡ false)、(d) consGNoCancel(subst along e + fst-refl + sigmaPropEq)、(e) 主帰納(listrec、cons ケース = transpCompW8 → cong(transp-glh)(ih) → windGen → consGNoCancel)、(f) isoToEquiv 組立(windF2/decodeF2 + decodeEncodeF2/encodeDecodeF2)→ **π₁(S¹∨S¹)=F₂**。

## 2026-07-14: decodeEncodeF2 完成 — winding は全道空間で分裂単射

**`decodeEncodeF2 : Π x p. decodeAll x (windAll x p) ≡ p`(構成完了; ガードは重くネイティブ送り — 当初「軽い」と誤認したのはタイムアウト打ち切りの見落とし。教訓: timeout-kill したビルドの「エラーなし」は成功ではない)**:
- `windAll : Π x. Path base x → helixF2 x`(端点一般化 winding、transp 一発)
- J(jD)で decodeEncodeEM を鏡写し。**refl ケースは完全に定義的**: windAll base refl → transp 定数族(constancy 発火)→ nil、decodeAll base nil → pushrec→s1elim→listrec-nil → refl。d-ケース = reflD 一発。
- decodeAll の注釈は checker が信頼(defn)するため、この J 補題自体の検査は軽量 — decodeAll 本体の重い検証(Test/WedgeF2 ネイティブ)とは独立に**構成**は積める(検証はどちらも wedgef2 ランナー: windAll/decodeAll/decodeEncodeF2 の 3 チェック)。allDefs 未登録(ネイティブ通過後に)。

**π₁(S¹∨S¹)=F₂ 残り**: encodeDecodeF2(語帰納)— 必要部品: (a) `transpComp`(合成道に沿う輸送 = 輸送の合成; J で構成、refl ケースは transReflR-補正)、(b) 4 文字の順輸送 ≐ consG(左円はプローブ済み、右円共役は transpComp ×2 + ppush 定数輸送)、(c) `consGNoCancel`(reduced (h::t) ⟹ cancels h (head t) = false — redAux の構造から)、(d) sigmaPropEq で対の等式へ。その後 isoToEquiv 組立(decodeF2 側は decodeAll base と decodeWord の一致 — 定義的のはず)→ **π₁(S¹∨S¹)=F₂**。

## 2026-07-13 (15): decodeAll 構成完了 — 輸送計算が両方向とも定義的と判明

**決定的プローブ 2 連発(両方 PASS)**: (A) `transp i (helixF2(pinl(sloop ~i))) s ≐ consG letLinv s` — **ua 線の逆向き輸送も transpGlue が定義的に計算**(順方向のみ既知だった)。(B) `transp i (Path w8 base (pinl(sloop i))) p ≐ p ⬝ loopL` — 端点移動族の輸送は右合成に落ちる。この 2 つで decodeAll のループセルは「decodeCons + 消去」の純組立になった。

**`decodeAll : Π x. helixF2 x → Path w8 base x` 構成完了**(LibCircleEM、ガードはインタプリタで 15 分超のためネイティブ送り — Test/WedgeF2 ランナー粉砕中):
- 左円: s1elim、ループセル = toPathP + funExt + 点ごとセル(whiskerR(decodeCons Linv) → cancelVia[gcancel T T])
- 右円: 同型だが基底 = λs. dec(s)⬝pushP、点ごとセルは 7 セル鎖(decodeCons Rinv → assocConn ×3 シャッフル → cancelR(pushP) → cancelL(rloop) → transReflR)— foldr 生成
- ppush セル: helix が ppush 上定数 + 輸送計算により**点ごと refl**

**残り**: wedgef2 の判定待ち → decodeEncodeF2(jD)、encodeDecodeF2(語帰納 + consGNoCancel)、isoToEquiv 組立 → **π₁(S¹∨S¹)=F₂**。

**運用注意**: Library.lean の `#guard allDefs.all (·.ok)` は登録定義を全再検査する — **重い定義(decodeAll 等)はネイティブ検証が通るまで allDefs に登録しないこと**(登録すると Library のビルドが時間級化する)。decodeAllD は未登録のまま(検証後に追加)。

## 2026-07-13 (14): decode 準同型方程式完成 — `decodeCons`

**`decodeCons : Π g s. decodeWord(fst(consG g s)) ≡ decodeWord(fst s) ⬝ genLoop g`**(LibCircleEM、ガード通過)— π₁(S¹∨S¹)=F₂ の両往復の橋。

構造(設計どおり consStep の (b,e)-パラメトリック化が機能):
- `decodeConsStep g h t rt b e2`: sumcase on b、動機は `Π e2 : Path bool (cancels g h) k. …`(e2 を動機内 Π で束縛 — consStep 自身と同じ形)。**非消去枝 = refl(定義的)**、消去枝 = symm(congCell ⬝ cancelVia)where congCell = cancelsCharac に沿った頭文字書き換え、cancelVia の仮定 = gcancel(fst g)(snd g)(Σ-η conv 通過 — プローブ済み)。
- **落とし穴と修正**: sumcase の inl 枝では k := inl u(u : unit 抽象)— trueR (= inl tt) と書くと unit-η がなく不一致。枝内の証人はすべて `.inl (.var "u")` 形で書くこと。
- `decodeCons`: fst s 上の listrec(IH 不使用 — 構造の露出のみ)+ Σ-η で s = pair(fst s, snd s)。nil 枝 refl、cons 枝 = decodeConsStep を consG 自身と同じ引数 (cancels g h, plam-refl) で適用。

**残り**: decodeAll(pushrec + s1elim、ループセル = toPathP + decodeCons)、decodeEncodeF2(jD)、encodeDecodeF2(語帰納 + consGNoCancel)、isoToEquiv 組立 → π₁(S¹∨S¹)=F₂。

## 2026-07-13 (13): decode 正方形の消去セル完成(cancelVia/conjCancelGen/gcancel)

LibCircleEM に追加(LibCoherence のセルを使うため LibWords ではなくここ; w8 ヘルパはローカル再定義)、全ガード一発通過:

- `cancelVia : (q₁⬝q₂ ≡ refl) → (P⬝q₁)⬝q₂ ≡ P`(3 セル: symm assocConn + whiskerL + transReflR)
- `conjCancelGen : (p⬝q ≡ refl) → ((u⬝p)⬝u⁻¹)⬝((u⬝q)⬝u⁻¹) ≡ refl`(8 セル鎖、fold 生成: whiskL(symm assoc) → assoc → whiskR(cancelR!) → assoc → whiskR(symm assoc) → whiskR(whiskL h) → whiskR(transReflR) → cancelL[u⁻¹]。手書きネストは括弧地獄なので List.foldr で機械生成)
- `gcancel (b1 b2 : Bool) : genLoop(invLet(b1,b2)) ⬝ genLoop(b1,b2) ≡ refl` — **ブール 2 引数で言明**(Σ-η 回避)、二重 sumcase で 4 生成元: 左円 2 つは cancelL 直接(loopLinv ≐ symm loopL 定義的)、右円 2 つは conjCancelGen + cancelL。

**π₁(S¹∨S¹)=F₂ の残り(次ラウンド)**: decode 正方形の方程式 `Π s. decode(consG g s)⬝genLoop(invLet g)?? — 向きの確定含め`consStep の (b,e)-パラメトリック構造(証明側の sumcase が consStep の分岐と噛み合う設計 — F₂ ラウンドの意図された使い方)で: 非消去分岐 = cancelVia∘gcancel、消去分岐 = decode の cons 等式(定義的)+ cancelsCharac で文字を書き換え。その後 decodeAll(pushrec+s1elim、ループセル = toPathP + この方程式)、decodeEncode(jD)、encodeDecode(語帰納)、組立。

## 2026-07-13 (12): π₁(S¹∨S¹)=F₂ 開始 — decode 側構成(全ガード一発通過)

LibWords に追加: `genLoop`(文字→生成元ループ; 右円は `ppush` 経由の共役 `pushP ⬝ (pinr∘sloop±) ⬝ pushP⁻¹`)、`decodeWord`(listrec で inner-first 合成: decode(l::rest) = decode(rest) ⬝ genLoop(l) — windF2 の輸送順と整合)、`decodeF2`(fst 経由)。

**残る本体 — 次ラウンドの主タスク(EM の Codes 級)**:
1. **`decodeAll : Π x : w8. helixF2 x → Path w8 base x`**(x-一般化 decode 族): pushrec + 各円の s1elim。ループセル = 「decode 正方形」: PathP over sloop in (λx. helix x → Path(base,x)) ⟺ Π w. decode(consG L w) ≡ decode(w) ⬝ loopL。**消去が要点**: consG が頭文字を消す分岐(w = Linv::rest)では decode(rest) ≡ (decode(rest)⬝loopLinv)⬝loopL — cancelL + assocConn + transReflR で閉じる(全部品在庫あり)。非消去分岐は定義的。文字 4 種 × 消去/非消去の場合分けは cancelsCharac/decEq の計算で分岐。
2. `decodeEncodeF2` : jD で decodeEncodeEM を鏡写し(refl ケース: windF2(refl) = transp-const → nil → decode nil = refl)。
3. `encodeDecodeF2` : F₂ 上の語帰納(reduced 不変量を thread: redTail 補題 + consGNoCancel(reduced なら消去不発: cancelsCharac + decEqBool 計算)+ sigmaPropEq)。
4. 組立: isoToEquiv → `omegaW8F2Equiv` → **π₁(S¹∨S¹) = F₂**。
ガードは重ければネイティブ(Test/WedgeF2)。per-generator 輸送は「fst(pathToEquiv(ua e)) x ≐ e.fst x 定義的」(既知)により conv で落ちる見込み。

## 2026-07-13 (11): capp メモ化の試み — Lean ランタイムの壁で棚上げ(知見多数)

プロファイル(capp 2.4 億回)に基づき (closure-ptr, arg-ptr, fresh) キーの capp メモ表を実装したが、**3 つの連続する落とし穴**の末に棚上げ:

1. **共有マップへの挿入は全コピー**: `let m ← ref.get` で取った HashMap へ insert すると(ref と共有で RC≥2)バッキング配列全体をコピー — 二次爆発。
2. **lookup の局所変数が compute 中もマップを pin**: `m.size` を後で使うだけで compute 内の全ネスト挿入が共有状態に。lookup は即スコープアウトさせること。
3. **最適化の compute 浮動は不死身**: r への算術データ依存(カウンタ増分)を作っても、コンパイラは compute() を modify クロージャへ浮動させ自己デッドロック(今回は profCounters 側で `lean_st_ref_take` ブロック)。**唯一信頼できる障壁 = スクラッチ ref**: `scratch.set (some (compute ()))` — IO プリミティブの引数は ref 非保持で必ず先に評価され、IO 順序は並べ替え不能。
4. **最終壁(ランタイム)**: initialize 由来の IO.Ref へ値を格納すると `lean_mark_mt` が格納グラフ全体を歩き(以後その値の RC は原子化)、かつマップが排他所有と認識されず**毎挿入 `lean_copy_expand_array`**(RSS 44MB のまま 34% がコピー)。素朴なグローバルメモ表は Lean 4 では機能しない。**再挑戦の方向: @[extern] C サイドテーブル、または評価器への状態スレッディング**。

処置: `cappCacheEnabledRef`(常時 false)でハード無効化、コード・コメントは将来のために保存。純モデル・インタプリタ・既存 defn キャッシュは無影響(uaCompMul OK で確認)。副産物: Examples.lean の面テスト更新(DNF 一般化で (i∧i)=0 は正当受理)。

ランナー現況: circleem(toFrom)/heavy3(codes)/windf2 ≈170min CPU、hh1(ホモトピー仮説 7 チェック)≈20min+ — 全て旧(健全)バイナリで継続中。

## 2026-07-13 (10): 次元1ホモトピー仮説 — 全構成完了、ネイティブ検証中

**`homotopyHyp1 : Π A (gA : isGpd A) (a : A) (cA : isConn A a). K(Ω(A,a),1) ≡ A`** の完全な構成を書き上げた(LibCircleEM、ガードは Test/HH1 ランナーでネイティブ検証中 — インタプリタでは 16 分超で時間級と確認済み)。証明構造(em1elim 不要・Σ-道 h-レベル不要の経路を発見):

1. `loopRecCongEnc`: cong loopRec ≡ encodeEM(2 歩鎖: decodeEncodeEM で往復を挿入し、decode-at-base ≐ emloop(定義的、decode の em1elim 基底値)なので loopRecLoop(refl)が第二歩を閉じる)
2. `loopRecRetr`: decode(cong f q) ≡ q(cong decode の 1 と decodeEncodeEM)
3. `loopRecOmegaEquiv : Ω K(ΩA,1) ≃ ΩA`(isoToEquiv; section = loopRecLoop、retraction = 2)
4. `loopRecCongAll`: 全ての端点 t で cong f が同値 — **emConn + isPropIsEquiv + truncrec + transportD**(命題族の連結性転送)
5. `loopRecFibBase`: 基点ファイバー可縮 — center = (embase, refl)、収縮 = 4 の中心 (q₀,h₀) からの**対の道** plam i. pair(q₀@i, w i)、w = h₀-補正付き特異点フィラー(hcomp 四面: (i=0)↦a, (i=1)↦h@k@j, (j=0)↦a, (j=1)↦f(q₀@i)、底 (cf q₀)@(i∧j))。※ i=1 端点の conv に Σ-η が必要 — カーネルの pair-vs-neutral η を前提(FAIL ならここ)
6. `loopRecEquiv`: 全ファイバー — cA + isPropIsContr + transportD
7. `homotopyHyp1`: ua [emT, A, (loopRec, 6)]

付随修正: Examples.lean の負テスト((i∧i)=0 面の拒否)は DNF 一般化後は**正当に受理**されるため正テスト化し、代わりに項変数を面に使う真の不正例を追加。

検証状況: Test/HH1(7 チェック)ネイティブ実行中。1〜3 が通れば 4〜7 は転送・組立なので通る見込みが高い。5 の Σ-η だけ要注意。

## 2026-07-13 (9): 連結性インフラ — emConn/s1Conn(単位側の前提部品)

すべて一発通過(LibCircleEM):

- `isConnR (X, x₀) := Π x. ∥ x₀ = x ∥`(Raw ヘルパ)
- **`propToSet`**: 命題は集合(古典的四面チューブ正方形 `hcomp k [(i=0)↦h xs (p j), (i=1)↦h xs (q j), (j=0)↦h xs xs, (j=1)↦h xs ys] xs`)
- **`emConn : Π C m. isConn (K(C,m), embase)`** — **群律不要**(em1elim の動機が命題族 `∥base = t∥` なので gP は propToSet∘isPropTrunc + isSetToGpd、ループセルは汎用 propFill、2-セルは toFromD 型の toPathP + isPropPathPSet 放電)
- `s1Conn`(s1elim 版、ループセル = propFill のみ)

**次セッションの主タスク — `loopRecEquiv`(dim-1 ホモトピー仮説の完成)**: `Π A gA a (c : isConn A a). Π x. isContr (fiber (loopRec A gA a) x)`。設計済み:
1. c x : ∥a = x∥ を isPropIsContr(prop 目標)へ truncrec で消去し、transportD で基点ファイバーへ帰着。
2. **核心** isContr(fib f a): center := (embase, refl)。収縮は em1elim、動機 M(t) := Π p : Path A a (f t). Path fib center (t,p)。
3. **基底ケースは接続のみ**: base p := plam i. pair (emloop p @ i) (plam j. p@(i∧j)) — 第2成分は特異点フィラー、輸送条件は loopRecLoop(refl 証明)が定義的に吸収。
4. gP に必要な isGpd(M t): isGpdPi + isSet(Path fib …) ⟸ **未整備: fib の 1-型性**(Σ-道の特徴付け + isSetSigmaProp 流。fib = Σ t:K. Path A a (f t) は「亜群底 × 集合ファイバー」— 道空間は「Path K(集合)上の Σ、ファイバーは 2-セル空間(isGpd A より命題)」→ isSetSigmaProp が使えるはず。Σ-道 ≃ の在庫確認から)。
5. l/c セルは isPropPathPSet 放電(集合族)。
完成後: `homotopyHyp1 : Π A gA a c. Path U A (em1 Ω trans)` via ua。

## 2026-07-13 (8): 次元1ホモトピー仮説プログラム開始 — 余単位(counit)完成

**新テーマ**: 基点付き連結 1-型 A に対する `A ≃ K(π₁A,1)`(次元 1 のホモトピー仮説、S¹≃K(ℤ,1) の一般化)。今回はその**余単位側**(LibCircleEM 末尾、全て一発通過):

- **`loopGroup : Π A (gA : isGpd A) (a : A). Group`** — Ω(A,a) の群構造。**全ての群律が非切り詰めコヒーレンスセルで埋まる**: 結合律 = symm assocConn、単位律 = transReflL/R、逆元律 = cancelL(右逆元は cancelL[symm p] + symmInvol が定義的なので conv が吸収)、集合性のみ gA を使用。
- **`loopRec : K(Ω(A,a),1) → A`** — em1rec で恒等ループ写像により実現。**合成セル = transFill そのもの**(em1rec の c 引数の型 `PathP (λ i. Path A a (q@i)) p (p⬝q)` が第2章のフィラーの型と文字通り一致)。
- **`loopRecLoop : cong loopRec (emloop p) ≡ p` — refl 証明(定義的)**。

**残る作業(単位側+同値性)**: A → K(Ω(A,a),1) の構成には**連結性**(Π x. ∥a = x∥)が必要 — 方針: toFrom 型の encode-decode(S¹ 版の一般化)or「連結 1-型間の π₁-同型 ⟹ 同値」(切り詰め Whitehead)。次セッションの主задача。連結性の定義(∥·∥ ベース)は LibHITs の ∥A∥ 理論が使える。

## 2026-07-13 (7): ★ Mac Lane ペンタゴン(非切り詰め)完成 — コヒーレンスの対が閉じた ★

**`pentagonConn`(任意の型・切り詰めなし・J なし・公理なし、一発通過)**:
`assocConn p q (r⬝s) ⬝ assocConn (p⬝q) r s ≡ cong(p⬝_)(assocConn q r s) ⬝ (assocConn p (q⬝r) s ⬝ cong(_⬝s)(assocConn p q r))`
`triangleConn` と合わせ **Mac Lane コヒーレンス(五角形+三角形)が非切り詰めで完全に成立**。

最後のピース **`pentRefillRefl`(箱蓋論法)**: 詰め替えセル γ0 ≡ refl(p⬝q) を単一 hcomp で構成 —
`ε u m i := hcomp j [(i=0)↦w, (i=1)↦q((m∧¬u)∨j), (u=0)↦γ0fill(m,j), (u=1)↦pq̂(j), (m=0)↦pq̂(j), (m=1)↦pq̂(¬u∨j)] (pq̂(m∧¬u))`
**技法**: 単一 hcomp 補間の障害(辺のドリフト)は「**全 4 辺を恒真面で崩壊させ、両側の hfill(γ0fill と transFill 自身)を壁に使う**」ことで解消。m=0/m=1 辺は面枝の j=1 値 pq̂(1)≐pq に定義的に固定される。エッジが真面崩壊する立方体では枝構造の不一致が問題にならない — 今後の全ての「2 つの hcomp が等しい」型セルの標準テンプレート。

最終組立 `pentagonConn` = 6 歩鎖: unitL 逆挿入 → pentRefillRefl 逆ウィスカ → pentNatW 逆 → assocConn → pentNatL 逆 → assocConn 逆。(pentNatR/pentDiagL は結果的に未使用 — 代替経路用に保持。)

**コヒーレンス章の総括(すべて任意の型)**: transFill/transFillL(定義的端点フィラー)、assocConn(結合子)、transReflRRefl(単位子一致、定義的)、squareExchange/squareDiagL(正方形読み替え)、congSlide、natReflR/L、cancelR/L、**eckmannHilton**、**triangleConn**、**pentagonConn**。カーネル側の支え: normCof 正準化、resolveFace の DNF 選言肢検査、連言面トリック。

次候補: (a) ループ空間の H-空間/A∞-風構造の言明化(EH+ペンタゴンの系)、(b) 亜群≃1-型、(c) π₁(S¹∨S¹)=F₂、(d) ランナー結果回収(toFrom/codes 連鎖)。

## 2026-07-13 (6): チェッカーの面 DNF 一般化 + ペンタゴン第三正方形 — 残り一手

**カーネル/チェッカー改良(TypeCheck.lean)**: `resolveFace` を一般化 — 面リテラルに任意の区間式(`k∧¬m` 等、i0/i1 定数も)を許容し、面の連言を**正準 DNF の選言肢(変数代入のリスト)**へ展開、hcomp/glueTy/glueTm/glue の検査を選言肢ごとに実施(制約の立方体面による開被覆上の検査 — 健全・完全)。動機: squareExchange が面リテラルへ合成区間項を注入する初のケース(γ の連言面)。**全既存ガード通過**。

**連言面トリック**: 面 `(l=0)∧(m=1)` は m=0 で恒偽(枝ごと消滅)、m=1 で `(l=0)` に正規化 — **「片側にだけ面が現れる」補間セルを単一 hcomp で構成可能に**。これが融合セル γ を可能にした:
`γ l m := hcomp j [(i=0)↦w, (i=1)↦Q(m,l)(j), ((l=0)∧(m=1))↦(p⬝q)(i)] (transFill p q @ m @ i)`
(Q = 二重フィラー、4 特殊化がすべて定義的: Q(0,l)≐transFill q r@l、Q(m,1)≐transFillL q r@m 等)。γ(l)(0) ≐ trans p (transFill q r@l)、γ(l)(1) ≐ transFill (p⬝q) r @ l、γ(1)(m) ≐ assocConn p q r @ m — すべて**面リスト込みで文字通り一致**。

**証明済み(ガード通過)**: `pentRefill : V2 ≡ V2`(詰め替えセル = W(0,·))、`pentNatW`(第三正方形): pentDiag ⬝ cong(_⬝s)(assocConn p q r) ≡ pentRefill ⬝ assocConn (p⬝q) r s。

**ペンタゴン最終組立(残り一手)**: B ≡[(I)=pentNatL] Λ0⬝(pentDiag⬝congB3) ≡[pentNatW] Λ0⬝(pentRefill⬝Ψ1) — あとは **pentRefill ≡ refl_{V2}**(≡ γ(0) ≡ refl(p⬝q))のみ。γ(0)(m) = hcomp [(i=0)↦w, (i=1)↦q(m∨j), (m=1)↦(pq)(i)] (transFill p q@m) の「再充填」セル。単一 hcomp 補間は不可能と判定済み(m=1 端が全 u で pq に留まれない — 3 通りの設計で確認)— **2 段構成が必要**(次セッション: 中間形経由 or hfill-η 論法)。pentNatR/pentDiagL は代替経路 (II)+(III) 用に保持。

## 2026-07-13 (5): ペンタゴンの二つの半分(pentNatL/pentNatR)+ 残課題の完全な地図

**証明済み(全て一発通過、LibCoherence 第6章)**: 鍵は「**結合子をフィラーに沿って動かす**」— `Λ l := assocConn p (transFill q r @ l) (transFillL r s @ l)` は構文的正方形で、squareExchange が直接適用できる(assocConn は端点完全総称なので、引数にフィラーの papp を与えられる)。

- `pentDiag : (p⬝q)⬝(r⬝s) ≡ (p⬝(q⬝r))⬝s`(Λ-正方形の上辺)、`pentDiagL : p⬝((q⬝r)⬝s) ≡ (p⬝q)⬝(r⬝s)`(Ψ-正方形の下辺)
- `pentNatL`(I): congB1 ⬝ assocConn p (q⬝r) s ≡ assocConn p q (r⬝s) ⬝ pentDiag
- `pentNatR`(II): pentDiagL ⬝ assocConn (p⬝q) r s ≡ assocConn p (q⬝r) s ⬝ congB3
- インフラ: PentCtx 構造体(V1..V5、フィラー略記)、S1/S2 正方形

**ペンタゴン完成への残課題(完全に特定済み)**: ペンタゴン ⟸ (I)+(II)+**(IV): pentDiag⬝congB3 ≡ assocConn (p⬝q) r s**(または対称に (III))。(IV) は W-正方形 `W(l,m) := (γ(l)@m)⬝(transFillL r s @ l)` の squareExchange + unitL で落ちる。ここで **γ(l) : p⬝(transFill q r @ l) ≡ transFill (p⬝q) r @ l**(融合セル、γ(1) = assocConn p q r)が唯一の未構成セル。γ の設計: `hcomp j [(i=0)↦w, (i=1)↦Q(m,l)(j), (l=0)↦pq̂(m∨j)(i)] (pq̂(m)(i))`(Q = 二重フィラー、pq̂ = transFill p q)は m=1 端が transFill (p⬝q) r と文字通り一致するが、**m=0 端で (l=0) 面が余分**になり branch-list 構造比較で不一致。**構造的障害**: convSys は面の出現/消滅を許さない(恒真/恒偽以外)。解決には **hfill 一意性/面拡張補題**(`hcomp [sys] b ≡ hcomp [sys, φ↦hfill-restriction] b`)という新しい技術層が必要 — カーネルの hfill エンコーディングで表現可能なはず。次セッションの主задача。

## 2026-07-13 (4): カーネル面正規化 + Mac Lane 三角形(非切り詰め)

**カーネル改良 — 面リテラルの正準化(`normCof` 拡張、Interval.lean に `ofClause`/`fromDnf` 追加)**: 制約 `(r = ε)` を `s := r or ¬r` の DNF で読み、単一クローズなら原子リテラルへ分解(`¬k=1 → k=0`、`i∧j=1 → (i=1)∧(j=1)`)、充足リテラルは消去、それ以外は正準極性で保持、全体をソート・重複排除。**すべて論理的同値変形なので conv の識別が単調に増えるだけ** — 既存ガード全通過で確認済み。動機: `symm` 経由の面 `(¬k=1)` が `(k=0)` と構造比較で不一致だった(convCof はリテラル単位では `equiv` だが極性・分解は構造依存)。

**これで解禁された定義的一致(プローブで確認)**: `assocConn p refl q ≐ plam k. (symm (transReflR p) @ k) ⬝ (transReflL q @ k)` — **中央 refl の結合子は単位子正方形の対角線そのもの**(F-フィラー ≐ symm(transReflR p)、G-フィラー ≐ transReflL q、hcomp 公式が文字通り一致)。

**`triangleConn`(第5章): assocConn p refl q ⬝ cong(_⬝q)(transReflR p) ≡ cong(p⬝_)(transReflL q)、任意の型 — 3 ステップで一発通過**:
τ1 = whiskerR(symm(transReflR dg))(右単位付加)、τ2 = whiskerR(squareDiagL)(対角線 ≡ left⬝top、動く中点 `S(~u)1`)、τ4 = cancelR 直接適用(`symm(symm top) ≐ top` が定義的なので橋渡し不要)。新メタヘルパ `squareDiagL`。

Mac Lane コヒーレンスの対のうち三角形が完了。残るはペンタゴン(マスター正方形 + 補正セル、道具は全て揃った)。

## 2026-07-13 (3): Eckmann–Hilton 証明(非切り詰め・J なし)+ 正方形交換原理

**主定理 `eckmannHilton : α⬝β ≡ β⬝α`(任意の型の 2-ループ、LibCoherence 第4章)— 一発通過**。合成的ホモトピー論の古典が自作 CCHM カーネルで公理なしに閉じた。

技術基盤(第2〜3章、すべて connection のみ・hcomp 追加なし・J なし):

1. **`transReflRRefl`(第3章の入口)**: `transReflR refl ≐ transReflL refl` が**定義的**(証明 = refl)。book-HoTT では非自明な 2-パス補題。hcomp ベースの単位則のチューブが refl で全て定数になるため。この一致が EH の左右単位子の帳尻合わせを conv に吸収させる要。
2. **正方形交換原理(`squareExchange` メタヘルパ)**: 構文的正方形 `S k m` に対し `(bottom⬝right) ≡ (left⬝top)`。動く中点 = 反対角線 `S (~m) m`、両半辺は接続正方形 `S (k∧~m)(k∧m)` / `S (k∨~m)(k∨m)`。**trans 以外の hcomp 不要**。
3. インスタンス: `congSlide`(cong₂ 交換則)・`natReflR`/`natReflL`(単位子の自然性、正方形 = `transReflR (α k) @ m`)。
4. `cancelL`(`q⁻¹⬝q ≡ refl`、cancelR+単位子から)。cancelRD は LibCircleEM から LibCoherence へ移動(汎用補題のため)。
5. **EH 本体 = 18 ステップの 3-セル鎖**: 主鎖 11 歩(`U⬝(α∙β) ≡ U⬝(β∙α)`、assocConn×6 + 自然性ウィスカ×4 + congSlide×1)+ 仕上げ 7 歩(U の左消去)。`chain3` ヘルパで右結合合成。

第2章(前エントリ): `transFill`/`transFillL`(端点が定義的に落ちる PathP フィラー)+ `assocConn`(任意型の結合子、動く中点 `q k` 越しの合成)。

次: 非切り詰めペンタゴン(交換原理と同じ道具立てで、5 頂点の 3-立方体)。EH の系(π₂ の可換性の言明化、ループ空間の H-空間構造)も射程。

## 2026-07-13 (2): 非切り詰めコヒーレンス第2章開始 — 立方体結合子 assocConn

LibCoherence に **1-型仮定なし**の道具を追加(全ガード一発通過):

- `transFillD : PathP (λ k. Path A w (q k)) p (p⬝q)` — 合成の右フィラー。`(k=0)` 面をチューブに含め、恒真面の崩壊で端点が **定義的に** `p` になる設計。
- `transFillLD : PathP (λ k. Path A (q k) z) (q⬝r) r` — 左フィラー。`(k=1)↦r(j∧i)` 面で `k=1` 端点が定義的に `r`。ベースは接続 `q(k∨i)`。
- `assocConnD : p⬝(q⬝r) ≡ (p⬝q)⬝r`(任意の型)— `assocConn k := transFill p q k ⬝ transFillL q r k`、動く中点 `q k` 越しの合成。**端点一致は papp の端点注釈規則だけで落ち、立方体の検証は 2 つのフィラー内部に完全に局所化**。J 版 transAssoc と違い計算的に素直。

設計上の教訓: フィラーを「端点が定義的に正しい PathP」として切り出すと、上位セルの型検査から立方体推論が消える。ペンタゴン(非切り詰め)は次ラウンド — ルートは assocConn の 2 経路(2-step vs 3-step with cong)を繋ぐ 3-立方体。agda/cubical の GroupoidLaws.pentagonIdentity が参照点。

## 2026-07-12: implemented_by の真実 — 計測とキャッシュがついに実動

**カーネルの重要発見(将来の全性能作業の前提)**:

1. **後付け `attribute [implemented_by f] g` はコンパイルに反映されない**(エラボレータでもネイティブでも不発)。従来「インタプリタでは inert」と記録していたが、実際は**どこでも inert** だった。`@[implemented_by f]` を**宣言に直接**付けること。
2. 宣言直付けでも、純モデル本体が定数(`false` 等)だと **LCNF が本体をインライン/畳み込みして分岐ごと削除**する。対策: 本体なしの **`opaque` + implemented_by**。
3. さらに v4.31 codegen は**閉じた適用を once セルへ抽出**する(`lean_uint8_once` — サイトごとに 1 回だけ評価)。`never_extract` では防げないケースがある: unsafe 実装の**未使用引数が `__redArg` で削られ、適用が再び閉じる**ため。対策: 実行時値の引数を渡し、**実装内で本当に使う**(例: `ptrAddrUnsafe dummy == 0` で増分を分岐 — 常に 1 だが静的に消せない)。
4. この結果、`valPtrEq`/`nePtrEq`/`cloPtrEq`(conv ポインタ短絡)も**今まで一度も発火していなかった**ことが判明。opaque 化で初めて実動。
5. **ビルド時ガードは precompiled ネイティブコードで走る**ため、implemented_by が実動すると #guard も計測/キャッシュのコストを払う → 両機構は **IO.Ref フラグでゲート**(デフォルト OFF、ランナー main が `profEnable`/`defnCacheEnable` で opt-in)。ゲート前は LibGroupoid のエラボレーションが 235 分 CPU でハング級だった(ゲート後 630ms)。
6. **初の実プロファイル(uaCompMul)**: capp 2.40億 / force 5.59億 / transp 1710万 / hcomp 425万 / defn 評価 3009万(ヒット率 15 ミスのみ)。ボトルネックは force/capp の再実体化。defn 値キャッシュ単体では uaCompMul は速くならず(+20s のルックアップ代)、真価は巨大証人共有 (fromTo/toFrom) で検証中。
7. 計測フラグ OFF 時も opaque 呼び出し+ref 読みのコストは残る(uaCompMul で 115→136s)。恒久化の可否は fromTo 級での利得次第。

8. **2026-07-13 追記 — キャッシュ自己デッドロックの発見と修正**: キャッシュ有効時に toIntLoop(基準 3ms)が無限化。`sample` によるスタック採取で `evalDefnCachedUnsafe` 内の `lean_st_ref_get` が `__ulock_wait` でブロックと判明。原因: `unsafeBaseIO` はコード全体を純粋としてコンパイラに見せるため、`let v := compute ()` が `defnEvalCache.modify` のクロージャ内へ**浮動**され、modify 実行中(ref が空)に入れ子 defn 評価→同 ref への get で自己デッドロック。**教訓: unsafeBaseIO 内で IO.Ref.modify に「純粋に見える重い計算」を近づけない — get/set 分離(キャッシュは更新ロスト無害)を使う**。併せてキーを (name, fresh) に変更(閉じた defn 値の再現は fresh 毎に決定的 — 深度跨ぎ共有の理論的リスクを回避)。修正後 toIntLoop 3ms、キャッシュ実動。

ランナー再走中(デッドロック修正版): circleem(toFrom/s1EquivEM/s1IsEM/fromTo)・heavychecks3(codes→pi1EM1→isGroupoidS1→lGComp)・windf2(合成)— キャッシュ有効。

## 1. プロジェクト概要

Lean 4 (v4.31.0, `lean-toolchain` で固定) による自己完結の形式化プロジェクト。
**外部依存なし(mathlib 不使用)**。2つの層がある:

1. **Lean 内の形式化**(通常の Lean 定理): `Hott/`(univalence ⇒ funext、公理ゼロ)、
   `Logic/`(抽象不完全性定理)、`CategoryTheory/`(Lawvere 不動点定理)
2. **独自 cubical 証明支援系**(`Cubical/`): CCHM 流 cubical type theory の
   カーネル(型検査器+NbE 評価器)を Lean で実装し、その**上に**対象言語
   プログラムとして HoTT/圏論ライブラリ(51定義)を構築している

```
FormalizedMathematics/
├── Hott/{Basic,Univalence,Funext}.lean   Lean内: Voevodsky の定理(公理ゼロ)
├── Logic/Incompleteness.lean             Lean内: Löb・第一/第二不完全性
├── CategoryTheory/Lawvere.lean           Lean内: Lawvere 不動点・Cantor
└── Cubical/
    ├── Interval.lean    De Morgan 区間代数(全域関数のみ。DNF 正規形で判定的等価)
    ├── Syntax.lean      コア項(de Bruijn index)、Raw 表層構文、resolve、equivT 合成器
    ├── Semantics.lean   NbE: Val/Neutral/Closure、eval/capp/quote/conv、
    │                    Kan 演算(transp/hcomp/vcomp/hfill/transpGlue)、force、lineEquiv
    ├── TypeCheck.lean   双方向型検査器(check/infer/inferSort)、面制約下の検査
    ├── Library.lean     対象言語ライブラリ(51 LibDef、encodeDecode 量化定理まで)
    └── Examples.lean    ビルド時 #guard テスト(重い正規化テスト込み)
```

## 2. ビルドと検証

```sh
lake build                 # 全体。constancy 最適化後は数秒で完走する
lake build FormalizedMathematics.Cubical.Library   # ライブラリのみ(数秒)
```

- 検証はすべて **`#guard`**(ビルド時に評価され、失敗するとビルドが落ちる)。
  Lean 側の定理は `#print axioms` で公理ゼロを確認できる。
- **ビルド時間**: constancy 検査の最適化(2026-07-08、下記 §5)により、
  以前 10 分超だった Examples の再検証は **約 1.4 秒**になった。フルビルドは数秒。
- **デバッグ手順**(確立済みのワークフロー):
  1. scratch ディレクトリに `dbgN.lean` を書く(`import FormalizedMathematics.Cubical.Library` 等)
  2. **プロジェクトルートから** `lake env lean /path/to/dbgN.lean` で実行
     (cwd がプロジェクト外だと LEAN_PATH が通らない)
  3. カーネル内の `panic!` は Inhabited のデフォルト値(`vuniv 0` → 正規形 `univ`)を
     返して**続行**する。結果に突然 `univ` が出たら panic を疑い、
     `2>&1 | grep PANIC` でメッセージ(値のヘッドタグ付き)を見る。
     `Val.head` がデバッグ用ヘッドタグ関数として存在する。
  4. 評価が暴走したら `ps aux | grep lean` で CPU を確認し、`pkill -f "lean.*<file>"`。
     lake は失敗ビルドで .olean を消すので、ライブラリを壊すと scratch の import も
     壊れる — 問題の定義をコメントアウトして先にライブラリを復旧させる。

## 3. 完了した成果(要点)

### Lean 内形式化(安定・完成)
- `Hott.funextOfUnivalence`: univalence(構造体仮定)⇒ funext。公理ゼロ。
  ※ `Path` に対する UIP は Lean 内で証明可能なので、univalence を global axiom に
  すると矛盾する。**必ず構造体仮定方式を維持すること。**
- `Logic`: HBL 可導性条件 + 対角化仮定から Löb・第一(不可証半分)・第二不完全性。
- `CategoryTheory`: CCC を自作し Lawvere 不動点定理(一般化点、終対象不要)+ Cantor。

### Cubical カーネル(フェーズ v0 → 2a → 2b → 2d → 2b' → 2c 完了)
- **区間**: De Morgan 代数、反鎖 DNF による判定的等価(`IVal.equiv/isZero/isOne`)、
  `substLvl`/`mentions`/`mixedPolarity`(∀ 演算用)
- **Path/PathP**: `plam`/`papp`(端点注釈付き — 検査器が照合)、境界条件検査
- **transp**: constancy(quote+出現検査)、Π(逆向き fill)、Σ(順向き fill)、
  PathP(`comp` 経由)、**Glue(CCHM §6.2 完全版、枝ごとの δ = ∀i.φ 計算付き)**
- **hcomp**: 面制約系、真面選択、Π/Σ/PathP/ℕ/ℤ の構造規則、`hfill`、
  異質合成 `vcomp = hcomp∘transp`
- **Glue / univalence**: 形成・`glue`/`unglue`・遅延簡約(`force`)、
  `transport (ua e) x ⟶ e.fst x` が定義的に計算
- **HCompU**: `hcomp U [φ↦E] A = Glue [φ ↦ (E 1, lineEquiv …)] A`。
  `lineEquiv` は Semantics.lean 内の**閉じた対象言語プログラム**(Raw)で、
  カーネルが評価する(Library でその型検査も #guard 済み)
- **HIT**: S¹(`sbase`/`sloop`/`s1elim`+hcomp セルとの可換規則)、
  ℤ(strict `isuc`/`ipred` 相殺、`intrec`)
- **宇宙階層**: `U n : U (n+1)`、`inferSort` によるレベル推論、判断レベルの包摂。
  type-in-type は排除済み(負例テストあり)
- **計算のマイルストーン**(すべて #guard):
  funext が計算/`trans refl refl ⟶ refl`/`λe. transport (ua e) 0 ⟶ λe. e.fst 0`/
  `winding loop^±1 ⟶ ±1`/`winding (loop⬝loop) ⟶ +2`/`winding (intLoop n) ⟶ n`(具体値)

### 対象言語ライブラリ(`Library.lean`、51定義)
パス代数(refl/symm/trans/cong/happly/funExt)、transport/subst/**J(接続平方で導出)**、
2次元代数(**単位律=平方充填、結合律=J**)、h-level(isPropPi/isContrPi/
**isPropToIsSet=4面管平方**)、**toPathP**、等価と ua、整数(add と
**帰納法による単位律・結合律・可換律の Path 証明**)、圏論(Monoid+ℤ インスタンス、
PreCat+型の圏+**基本亜群 pathPrecat**、Functor+恒等関手、自然変換+恒等自然変換)、
円周(helix/winding/intLoop/**decodeSquareSuc**)、レベル1代数、そして
**`encodeDecode : Π (n : ℤ). winding (intLoop n) ≡ n`(量化された定理)**。

## 4. カーネル設計の最重要原則(破ると壊れる)

1. **遅延境界簡約の原則**: 境界簡約(papp の端点、`sloop 0 → base`、Glue の真面、
   S¹ hcomp セルの真面)は**先行評価してはならない**。すべて `force` で遅延させ、
   消去子・Kan 演算は**未 force の値**から構造(Glue の枝など)を先に読む。
   このセッションで踏んだバグ5件はすべて「先行簡約が Kan 演算の必要とする構造を
   破壊した」ことによる。新しい簡約規則を足すときは必ずこの原則に従うこと。
2. **`papp` の端点注釈**: 中立パスの境界規則に必須。`vplam` は端点でも
   クロージャ実体化を優先(境界条件は検査済みなので定義的に等価)。
3. **Glue 系は無濾過で保持**: `vglueTy`/`vglue` の枝リストは filter/collapse せず
   保存(枝位置の安定性)。濾過・崩壊は `force` だけが行う。
4. **fresh の配管**: 評価器は fresh レベル供給を引数で持ち回る。generic 点での
   族の検査(transp/hcomp の头部判別)はこれに依存。`force` も fresh を取る
   (セル崩壊に capp が要るため)。
5. **検査器の面制約**: 面は「区間変数 = 0/1」の連言のみ(表層)。検査は面を
   環境への代入(`restrictEnv`)として適用してから通常の変換判定。
6. **等価性 (Equiv) の標準形**: `Σ (f : T→A). Π (y : A). isContr (Σ x. Path A y (f x))`。
   カーネルの Glue 規則(ファイバー中心抽出)はこの射影構造に依存。変更禁止
   (変更するなら transpGlue / lineEquiv / equivT を同時に)。

## 5. 既知の欠陥・制限(正直な申告)

- **[重要] strict ℤ の代入不安定性**: strict な `isuc/ipred` 相殺 + `intrec` により、
  **定義的等価性が代入で閉じない**(非合流)。再現: generic な `n` では
  `intLoop (isuc n) ≐ intLoop n ⬝ loop` だが、`n := ipred y` を代入すると
  左辺は `intLoop y`(スタック)、右辺は合成のまま。すべての判断的等式は
  経路的に正しいので**無矛盾性は保たれる**が、完全な `decode`
  (paths 側の量化定理 `decodeEncode`)はこれでブロックされている。
- **[解決済み 2026-07-08] J の大型モチーフ性能爆発**: 原因は `vtransp` の
  constancy 検査(族の値を毎回 quote して出現検査)だった。修正:
  (i) `.mk env body` クロージャで `body.dependsOn 0` が偽なら即・定数の高速パス、
  (ii) quote を「早期打ち切り付きの値上の出現検査 `usesLvl`」に置換
  (quote と同じ `force` 込み走査なので意味論は不変)。効果: 旧爆発ケース
  (congTrans の J 適用)54分 → **0.2秒**、Examples 全体 635秒 → **1.4秒**。
  以前の教訓「証明の前に refl を試せ」は依然有効(この体系は驚くほど多くの
  等式が定義的。例: `winding (p⬝loop) ≐ isuc (winding p)` は中立 p でも refl)。
- **評価器の停止性は未証明**(全 `partial def`)。cubical TT の正規化は
  研究最前線(Sterling–Angiuli 2021)。偽の証明は置かないこと。
- その他: 系比較は順序依存(健全・不完全)/ `∀i` は混合極性面で保守的 ⊥ /
  `Glue` 上の `hcomp` はスタック / 宇宙包摂は判断レベルのみ /
  δ-部分の値は面の外では型的に無意味(面上でのみ参照される設計)/
  面制約の表層は変数のみ(式面・∨ なし)。

## 6. 次にやるべきこと(優先度順)

### A. 相殺なし ℤ へのリファクタ → 完全な `π₁(S¹) ≅ ℤ` — **完了(2026-07-08)**
実施内容: (A1) カーネル ℤ を `ipos/inegsuc` + `intcase` に再設計、⊤/⊥ 型
(`unit/tt/unitrec`、`empty/emptyrec`)を追加。(A2) `sucZ/predZ` と相殺の
Path 証明(各ケース refl)、**ℕ・ℤ の encode–decode による `isSetℕ`/`isSetℤ`**、
`setFill`(toPathP + isSet)、`sucEquiv` を isSet 平方で再構成。(A3) 算術法則
(単位律・結合律・モノイド)、`intLoop`、`windingCompLoop±`(**依然 refl!**)、
`encodeDecode` を intcase+natrec 構造に移植、Examples 移植、全回帰緑。
(A4) `decodeSquare`(3ケースの平方)、**`decode`**(loop セル = unglue +
`cong intLoop (predSucZ y)` 補正付き hcomp、**Π 型レベルで**)、
`decodeEncode`(J)、**`pi1S1IsoInt : Iso (base ≡ base) ℤ`**。
発見した検査器の不完全性: 面制限は env のみで Γ の型は未制限 → 面依存型の
変数を管が参照すると失敗。回避: hcomp を Π 型に持ち上げ管を λ にする。
続編(同日): `loopNeqRefl`(loop ≡ refl → ⊥、`cong winding` + `encodeZ` の
3行証明)と `s1NotSet`(円周は集合でない)— 初の否定的定理。
**`setIsoToEquiv`**(B が集合なら iso ⇒ equiv — setFill 手法の一般化、
gradLemma の実用代替)を追加し、`sucEquiv` はその1行インスタンスに
リファクタ(winding の計算はすべて保存)。可換律(addSucL/addPredL/addComm)
も pos/negsuc で再移植済み — 旧表現の負債はゼロ。ライブラリ84定義。
1. ℤ を通常の帰納型に(`izero | isuc n | ipred n` のまま相殺規則だけ除去、
   または `pos n | negsuc n` 型に再設計)。`visucV/vipredV` の相殺を削除。
2. `sucEquiv` は相殺に依存していたので、**`isoToEquiv`(gradLemma)を
   対象言語で証明**して再構成する(iso: suc/pred + 相殺の Path 証明は
   intrec で書ける)。gradLemma は平方充填 2〜3 枚の本格的証明
   (cubical Agda の `Cubical.Foundations.Isomorphism` を参照)。
3. `decode` を再構成: `decodeSquare n : PathP (λi. base ≡ loop i)
   (intLoop (pred n)) (intLoop n)` を intrec で(suc 側は既存の
   `decodeSquareSuc` の形、pred/zero 側は `(j=1) ↦ sloop(¬k ∨ i)` +
   `(i=1) ↦ q@j` の管を持つ平方 — 本書の履歴に構成メモあり)。
   `L := ⟨i⟩ λ y. decodeSquare (unglue y) @ i`(相殺なしなら
   `pred (suc y) ≡ y` は Path 証明を toPathP/hcomp で接着する必要がある
   — cubical Agda の decode の忠実な移植になる)。
4. `decodeEncode` は J(ライブラリの `jD`)+ refl ケースで閉じる(履歴に
   設計メモ: encode base refl ≐ 0、decode base 0 ≐ refl は定義的)。
5. 検証: `winding`/`intLoop` の既存 #guard がすべて通ること(相殺除去で
   一部の「定義的」だった箇所が壊れる可能性 — 特に sucEquiv のファイバー
   中心と `windingCompLoop` の refl 証明。Path 証明への置換が必要になる)。

### B. 性能: constancy 検査の改善 — **完了(2026-07-08)**
上記 §5 の解決済み項目を参照。`usesLvl`(Semantics.lean、quote の直後)が実装。
これにより A の gradLemma 系証明の性能障害は消えた。congTrans@01 と
transpTrans もライブラリに復帰済み(51定義)。

### C. `Glue` 上の `hcomp`
現在スタック。CCHM 規則: `hcomp (Glue [φ↦(T,w)] A) [ψ↦u] u₀ =
glue [φ ↦ hcomp T [ψ↦u] u₀] (hcomp A [ψ↦unglue∘u, φ↦w(hfill …)] (unglue u₀))`。
値の面制限が要る箇所は「vglue 構造の枝から取る/中立ならスタック」の
部分実装で十分(winding 系では未使用と実測済み)。

### D. 面制約の表層一般化(式面・∨)、系比較の順序非依存化

### E. ライブラリ拡張(次の有力候補)
- ~~**関手圏**~~ → **完了(2026-07-08)**: `setCatTy`・`compNat`・
  `natTransEq`(isPropPi@11 + toPathP@1 + 直接 plam の型直線 — cong-into-U は
  レベルが上がるので使わない)・`functorCat : precat₀ → setCat → precat₁`・
  `Bℤ`・`[Bℤ,Bℤ]`。教訓: (i) papp の頭が生 plam だと推論失敗 → `.ann` を巻く、
  (ii) レベル1では transport/toPathP/isPropPi の @1 変種が要る(tm は再利用可、
  ty のみ書き換え。ただし toPathP@1 は tm 内の transport 注釈も @1 に)
- **完了(2026-07-08 続)**: `pi1S1Equiv : Equiv (ΩS¹) ℤ`(setIsoToEquiv)、
  **`loopSpaceIsInt : ΩS¹ ≡ ℤ`**(ua による型の同一視)、`compFunctor`、
  `whiskerL`/`whiskerR`。ライブラリ98定義、フルビルド約50秒
- ~~`isSet (ΩS¹)`~~ → **完了**: `isSetRetract`(isPropToIsSet と同じ
  4面管平方 — 逆元律すら不要だった)経由で軽量に成立。`isPropRetract`・
  逆元律 `transInvR`(接続キャップ平方)・`transInvL`(strict 対合により
  R の1行の系)も追加。ライブラリ103定義
- ~~Hedberg~~ → **完了(2026-07-08 続)**: カーネルに**和型**を追加
  (`sum/inl/inr/sumcase`; `transp` は成分直線 `sumLeftOf/sumRightOf` に分配、
  `hcomp` は inl/inr と可換)。Bool・Dec・decEqBool・**hedberg**・isSetBool・
  notEquiv・古典デモ `transport (ua not) true ⟶ false`(計算ガード、高速)。
  ライブラリ112定義。注意: (i) convNe に新しい中立形のケースを足し忘れると
  「expected と inferred が同じに見えるのに mismatch」になる(末尾スペースで
  replace が空振りした実例あり — grep で追記を検証せよ)、(ii) 型式の中の
  `inl/inr` は推論不能なので `.ann` を巻く
- ~~interchange・isPropSigma~~ → **完了(2026-07-08)**: `interchange`
  (水平合成2定義の一致 = 成分ごとに β の自然性 + natTransEq)、
  `decEqNat`/`decEqZ`(コード経由; hedberg との合成で isSet ℕ/ℤ の
  別証明もガードで検証)、`isPropSigma`(toPathP パターン)。118定義
- **懸垂 HIT 完了(2026-07-08 続)**: カーネルに `susp/north/south/merid/
  susprec` を追加(径数付き HIT: transp は `suspLineOf` で径数直線に分配、
  merid 端点崩壊は force で遅延、susprec は vmerid・hcomp セルを未 force で
  先にマッチ — S¹ の規律を踏襲。閉包 `suspMcCod`/`suspMeridFam` で merid-case
  の Π-PathP 型を構成)。ライブラリ: S⁰≃Bool・S⁰≡Bool(transport 計算
  ガード付き)・S²:=ΣS¹・suspMap(+Id)・σ : S¹ → Ω S²。127定義
- **トーラス HIT 完了(2026-07-08 続)**: カーネルに `torus/tbase/tloopP/
  tloopQ/tsurf/torusrec`(初の2-セル構成子。force 崩壊は r 端で tloopQ s、
  s 端で tloopP r; sc の型 `PathP (λi. PathP (λj. P (tsurf i j)) (pc@i) (pc@i)) qc qc`
  は閉包 torusSurfFam/torusSurfInner で構成)。ライブラリ: **`T² ≅ S¹×S¹`**
  (Iso; 往復の全セルが定義的 — `surf i j ↔ (loop i, loop j)`)。132定義
- ~~一般 gradLemma~~ → **完了(2026-07-08 続)**: `isoToEquiv`(lemIso の
  5充填)。hfill は `hcomp [φ ↦ u(k∧j), (j=0) ↦ u₀] u₀` に符号化;複合面
  `(k∧j)=1` → 連言 `[(k,1),(j,1)]`、`(k∧j)=0` → 本体同一の2枝
  `[(k,0)]`/`[(j,0)]` に分割。**カーネル改良**: convSys が正規化
  (`normSys`: 恒偽枝除去 + `normCof`: 充足リテラル除去)— hfill の切詰めが
  制限下で位置ずれしても conv が通るために必須だった。収穫:
  **`t2EquivS1S1`・`t2IsS1S1 : T² ≡ S¹×S¹`(宇宙の等式)**。135定義
- **命題切り詰め完了(2026-07-08 続)**: カーネル `trunc/tin/squash/truncrec`
  — 再帰的パス構成子(squash の引数が自型の元)。除去子は「命題への
  非依存 recursor」(`rec (squash x y r) = prp (rec x) (rec y) @ r`;
  prp の型は Term.shift で合成、hcomp 可換は余域定数なので同質 hcomp)。
  ライブラリ: isPropTrunc(構成子そのまま)・truncMap・truncIdem
  (isoToEquiv 初適用、sect は refl)・**s1Connected(円周は連結 —
  s1elim + toPathP + squash)**・windingSurj(∃ 言明)。140定義
- **プッシュアウト完了(2026-07-08 続)**: カーネル `pushout A B C f g /
  pinl / pinr / ppush f g c r / pushrec`。設計知見: **`ppush` は f・g を
  注釈携行**(端点 `pinl (f c)`/`pinr (g c)` がセル単独では復元不能 —
  glueTm の注釈パターン)。transp は3径数直線に分配(端点側の f₁/g₁ は
  fam@1 から取得)。ライブラリ: **`suspIsPushout : Σ A ≃ pushout(⊤←A→⊤)`**
  (往復全セル定義的)、wedge・cofiber ビルダー、S¹∨S¹。146定義
- **8の字の巻き数完了(2026-07-08 続)**: `isSetProd`(Σ-η のおかげで
  hcomp 不要の直接 2-λ!)、`sucLeft/RightEquiv`、**`helix8`(pushrec を
  宇宙に除去する階数2被覆)、`wind8 : π₁(S¹∨S¹) → ℤ×ℤ`**。計算:生成元は
  1秒未満で (±1,0)/(0,±1)、L⬝R と R⬝L はともに (+1,+1)(約100秒 — ガード外の
  検証済み事実としてコメント記録)、交換子は深さ5で数十分級(合成深度に
  対し計算コストが急増 — 既知の性能特性)。151定義
- **集合商完了(2026-07-08 続)**: カーネル `quot A R / qin / qeq a b w r /
  qsquash x y p q r s / qelim`(依存除去子!mset の isSet 型は汎用閉包塔
  isSetOf1..4 で構成)。**設計判断: qelim の squash セル規則は意図的に停止
  (中立)** — 面が決まれば force で崩壊するので健全; 完全計算には
  isSet→SquareP のカーネル充填が必要(将来課題、その布石として
  `isPropPathPSet` を J で証明済み)。ライブラリ: isSetQuot(構成子)、
  **qelimProp(依存 prop-除去を qelim から導出** — isPropToIsSet + toPathP)、
  isPropQuotTotal、**truncAsQuot : ∥A∥ ≃ A/全関係**。156定義
- **ℤ ≃ (ℕ×ℕ)/∼ 完了(2026-07-08 続)**: ℕ 算術(addNat/addZeroR/addSucR/
  addComm/subNat/subSucSuc/subAddCancelR — 全て natrec + cong/trans 連鎖)、
  `nnQuotToZ`(qelim; feq は subAddCancelR 2回 + cong 2回の4連鎖)、
  `zToNNQuot`(正準代表元)、`predQ`・`fromPredZ`(predZ と predQ の絡み合い
  — qeq の証人は addSucR だけで足りる端点 conv が効く)、`nnRound`(b-帰納)、
  `zRound`、**`intAsQuot`(setIsoToEquiv)**。[(3,1)] ⟶ +2 等の計算ガード付き。
  **全14定義が一発通過。170定義。**
- **モジュール分割完了(2026-07-09)**: Library.lean(4200行)を鎖状 import の
  8モジュールに分割 — LibCore → LibSets → LibGroupoid → LibLoop → LibCats →
  LibHedberg → LibHITs → LibQuot → Library(index/summary)。分割は
  「行順を保って章境界で切断」なので依存関係は自動的に正しい(一発成功)。
  **増分ビルド: 末尾モジュール編集 69秒 → 約4秒**。lake はハッシュベース
  なのでコメント編集では下流再ビルドも起きない。今後の新規開発は原則
  LibQuot 末尾(または新モジュールを鎖に追加)+ Library.lean の allDefs 更新
- **F₂ 第1ラウンド完了(2026-07-09)**: カーネルに**リスト型**
  (`list A / lnil / lcons / listrec` — ℕ の再帰 × 和型の径数の合成;
  cons の hcomp 可換は head/tail の2成分展開、transp は要素直線 + 尾は同直線)。
  新モジュール `LibWords`: 文字 = Bool×Bool、`decEqProd`・`decEqList`
  (反駁は headD/tailD の cong + nil/cons 判別コードの subst)・
  **`isSetWord` = Hedberg 適用**(リストのコード理論を丸ごと省略!)。
  計算ガード: 語の等価が inl/inr に決定。178定義
- **F₂ 第2ラウンド完了(2026-07-09)**: Bool 補題キット(eqBool 健全性等)、
  `sigmaPropEq`・`isSetSigmaProp`(isPropPathPSet の回収)、相殺理論
  (`cancelsInv`・`cancelsCharac`)、状態渡し簡約述語 `redAux`、
  **`consG`(生成元 generic 相殺付き前置)+ 往復 `consGRound`**(inspect
  イディオム + **接続 `e@(i∧j)` による consStep 分岐書き換え** — J 不要の
  cubical 流)、`consGEquiv`(setIsoToEquiv)、**`helixF₂`・`windF₂`**。
  計算: `consG L⁻¹ (consG L []) ⟶ []`(相殺)、`windF₂ loopL ⟶ [L]`(3秒)。
  **性能壁**: 合成ループの windF₂ は consGEquiv 内蔵の isSetF2 証明
  (Hedberg 塔)を Kan ステップ毎に歩き実用時間を超過(loopSpaceIsInt と
  同根)— **カーネルの値共有/メモ化が特定済みの対策**(未着手)。206定義
- **K(G,1) 第1ラウンド完了(2026-07-09)**: カーネル HIT `em1 C m`
  (embase/emloop/emcomp(乗法注釈携行、ppush 方式)/emsquash(3-セル)/
  `em1rec` — isGroupoid 証人を要求(型は閉 Raw を resolve→eval して適用の
  lineEquiv 方式)、squash セルは意図的停止、emloop/emcomp は完全計算)。
  **罠**: パターン変数名 `i1` が Term 構成子 `.i1` に捕獲される(j1 に改名)。
  LibEM: `isSetToGpd`・`em1Z`・recursor 計算ガード・**`emloopComp`
  (emloop は準同型 — emcomp セルと trans 充填を1つの3次元 hcomp で比較、
  一発通過)**。210定義
- **K(G,1) 第2ラウンド完了(2026-07-09)**: `negZ`・逆元律(addInvPos/Neg は
  addSucL/addPredL + sucPredZ の連鎖)・`groupTy`・**`zGroup`**・
  **`emloopOne`**(emloopComp + パス亜群相殺の5連鎖)。h-level 塔:
  `isPropIsContr`(古典的4面管、一発)・`isPropIsEquiv`・`isSetPi`(η駆動)・
  `isSetEquiv`(isSetSigmaProp)・**`uaIdEquiv`(Glue 立方体
  [(j=0),(j=1),(i=1) ↦ (X,idEquiv)] X、一発)**・**`uaEta`(J@1;
  pathToEquiv refl ≐ idEquiv は定数性規則で定義的)**・`isSetRetract@10`
  (cong@10 は LibLoop に既存 — 重複定義に注意)・**`isSetPathU`**。
  罠: reflD 等の U₀-補題を宇宙(U₁ 元)に適用しない(inline plam で代替)。
  226定義
- **K(G,1) 第3ラウンド: 全定義完成・検査は一部オフライン継続(2026-07-09)**:
  hSet 塔(isPropIsSet・sigmaPropEq@10・isPropPathPSet@1・isSetRetract@11・
  hSetPath/Eta/Unique・**isGroupoidHSet**)全て検査済み ✓。
  mulREquiv・equivEq・uaInj ✓。isGpdEM(構成子)・isGpdPi(η駆動)✓。
  カーネルに**依存除去子 `em1elim`** 追加(gP : Π x. isGroupoid(P x) を要求、
  em1elimGCod 閉包は閉 Raw `em1IsGpdTm` を eval して適用; squash 停止)。
  **重要な実験結果**: `fst (pathToEquiv (ua e)) x ≐ e.fst x` と合成版が
  抽象同値でも**定義的**(0.2秒)— uaCompMul の funExt 部は0.3秒。
  ただし equivEq 層の検査が**乗算的再検査で超低速**(同一端点でも2分40秒、
  uaCompMul 全体は >68分 — .ref の再検査コストが層ごとに掛け算される)。
  **ガード保留中(定義は完成、オフライン検証走行中 — scratchpad/dbg37.out,
  dbg38.out 参照)**: uaCompMulD・lGCompD・codesD・encodeEMD(dbg37)、
  decodeEMD・encodeLoopD・decodeEncodeEMD・**pi1EM1D**(dbg38)。
  decode の設計: loop セル = Π-レベル hcomp、底は **emcomp 構成子そのもの**
  (両面を逆元律の chain で補正)、comp セル義務は「集合族上の PathP-線は
  命題」(isPropPathPSet + isSetPi + isGpdEM)で自動放電。
  **性能対策の実施結果(2026-07-10)**:
  (a) **`defn` 機構実装済み** — 検査済み定義の参照を再検査しない
  (定義環境方式; LibDef.ref = .defn name tm ty)。フルビルド 4分→2:35。
  ただし重ガード群には不十分(壁は conv/eval の値再評価と判明)。
  (b) conv に ptrEq ショートサーキット追加(値・中立・閉包)— 単独では7%。
  (c) **defn 評価キャッシュは2度失敗**: ①ポインタキー版は GC 後の
  アドレス再利用で**誤ヒット**(健全性バグ!検出はガード失敗による —
  項を保持して修正したが)②resolve が出現毎に新項を作るため全ミスで
  リスト肥大 → 名前キー版に再設計 → **原因不明の激遅化**(LibGroupoid
  が数秒→109分)で撤回。現状は非キャッシュ(eval fresh env tm)。
  **最終診断(2026-07-10 続)**: ポインタキー+HashMap(O(1))でも
  LibGroupoid >10分 → **真因確定: defn ノードの評価は閉包の再実体化毎に
  走るため数十億回オーダーで呼ばれ、IO 経由メモ化(unsafeBaseIO+Ref)の
  1回あたり数十 ns が積算されて死ぬ**。IO 系キャッシュは原理的に全滅。
  夜間ジョブも 6.75h で uaCompMul 未完 → 打ち切り。現状: 素の
  `eval fresh env tm`、全ビルド緑 2:31。
  **定義環境は threading 不要で実装完了(2026-07-10 続)**: `resolve` の
  `.defn` ケースを「名前が環境に既知なら de Bruijn 変数に解決」に変更 +
  `checkDefCtx`(文脈注入版 checkDef)+ Library.lean の `buildDefCtx`
  (全定義を1回ずつ評価して names/Γ/env を構築)・`okFast`。
  カーネル無改造・sanity ガード(intAsQuot)通過 ✓。
  **しかし uaCompMul は依然 >10分** → **最終的な壁を確定: conv 時の閉包
  再実体化**(convBinder/capp が比較のたびに新値を割り当て、共有が中間値に
  届かない)。残る対策は評価器レベルの**ハッシュコンシング**または
  **conv 結果キャッシュ**(どちらも IO オーバーヘッド問題を避ける設計が
  必要 — 研究級)。重ガード8本(→ pi1EM1)はそれまで保留。
  なお okFast 機構自体は健全で有用(以後の新定義の検査を大幅高速化する
  選択肢として利用可)
- F₂ 第3ラウンド(その後): 完全 encode–decode(decode の loop セル×4 +
  相殺 coherence 平方)
- **コヒーレンス第1章完了(2026-07-10)**: 新モジュール LibCoherence —
  **pentagon・triangle(1-型版、isGroupoid から)** + pentagonZ。
  **重要な知見**: 無切り詰め版の 4重J 戦略は不成立 — `trans refl refl` は
  具体型でのみ refl に計算し、抽象型では stuck hcomp(transAssoc(refl³) の
  nf=refl² は ℕ での話)。無切り詰めコヒーレンスは `assocRefl`・
  `transReflRRefl` 等のセルを立方体で手動 bootstrap する必要がある
  (コヒーレンス・プログラムの第2章 — 本物の研究課題)
- **S¹ ≃ K(ℤ,1) 第1ラウンド(2026-07-10)**: LibCircleEM —
  `cancelR`(汎用右相殺)・`intLoopSuc/Pred`・**`intLoopComp`(intLoop は
  準同型)**・`propFill`(汎用 prop-充填の切り出し)全て検査済み ✓。
  `isGroupoidS1` は**定義完成・検査保留**: s1elim の型付け規則が base-case
  の値(isSetLoopS1 級の巨大値)を評価して PathP 境界注釈に置くため、
  汎用補題化でも回避不能 — **評価器の値共有(defn 評価キャッシュが
  ポインタ共有を与える設計)が、残る全深部定理(pi1EM1 8本・
  isGroupoidS1・S¹≃K(ℤ,1) 往復・無切り詰めコヒーレンス)の唯一の関門**
  と最終確定。キャッシュの per-call オーバーヘッド問題とセットで解く
  必要あり(候補: eval の defn-case だけ低頻度化する項前処理 —
  checkDef 前に defn ノードを「値スロット付き」の特殊 var へ写す等)
- **突破口確立(2026-07-10 続): ネイティブ検査ランナー**。
  発見の連鎖: ① `implemented_by` は #guard(エラボレータのインタプリタ)で
  **一切効いていなかった**(ptrEq もキャッシュも未実行 — 「IO オーバー
  ヘッド説」は誤り、過去の激遅化は `eval 0 []` の意味変更起因)。
  ② よって解は「インタプリタを捨てる」: **`Test/HeavyChecks.lean` +
  lakefile の `lean_exe heavychecks`** — `lake exe heavychecks` で
  checkDef をネイティブ実行(~100倍: sanity 17ms)。
  ③ **`uaCompMul: OK(108秒)`** — インタプリタで6.75時間超だった検査が
  ネイティブで2分弱、数学の正しさが確定。
  残りの重検査(lGComp/codes/encodeEM/decodeEM/encodeLoop/
  decodeEncodeEM/**pi1EM1**/isGroupoidS1)は nohup で走行中 —
  **結果は scratchpad/heavy.out(次セッション最初に確認)**。
  運用方針: 重検査は今後ネイティブランナーに常設(#guard に戻すと
  インタプリタで再走してしまう — ライブラリ側は
  「verified natively: see Test/HeavyChecks」注記 + allDefs 登録で運用)。
  検討事項: 全ガードのランナー移行(ビルド時間も激減する見込み)、
  プロファイリング計装(profTick、ネイティブでのみ有効)は設置済み
- **カーネル頑健性課題の発見(2026-07-10 続)**: `isGroupoidS1` の
  ネイティブ検査が **PANIC**: `vintcase: not an integer` —
  経路は usesLvl(constancy 検査)→ capp → transpGlue:
  **transpGlue の「面外ジャンク値」("δ-partial values are junk off-face,
  benign" の設計想定)を usesLvl のジェネリック点での閉包実体化が歩き、
  ℤ 除去子がジャンクを踏む**。修正方向: (a) usesLvl を off-face 安全に
  (constancy 走査では Kan 計算を発火させない遅延判定)、または
  (b) 除去子群にジャンク耐性(stuck-on-value 表現)を導入。
  インタプリタでの「>10分」群の一部はこの病理と関連の可能性
- **走行中のネイティブ検査(3本、nohup)**: heavy.out(lGComp — 2h+ 継続、
  Σ-hcomp 射影 conv の疑い)、heavy2.out(codes → encode/decode →
  **pi1EM1**、isGroupoidS1 は最後尾へ)、windf2.out(L⬝L 合成 — 10分+)。
  **次セッション最初に3ファイルを確認**
- **カーネル頑健性修正完了(2026-07-11)**: 除去子・射影12箇所の
  `panic!` を**ジャンク透過**(`| junk => junk`)に変更 —
  transpGlue の「面外ジャンクは無害」哲学を全域に一貫させた。
  全ライブラリ緑・isGroupoidS1 の PANIC 解消(検査は継続走行中)。
  **重要な教訓(usesLvl の設計)**: 構造的閉包走査(実体化なし)は
  「捕獲されたが未使用の環境値」まで数える過剰近似となり、
  載荷済み定義的等式(pathToEquiv refl ≐ idEquiv → uaEta)を破壊する —
  mk-閉包の dependsOn 精密化でも特殊閉包経由の捕獲が残る。
  実体化ベースへ復帰(usesLvlClosure は定義のみ残置)。
  つまり**構造走査で安全化する路線は不可、ジャンク透過が正解**だった
- **走行中**: heavy3.out(isGroupoidS1[33分+] → codes → … → pi1EM1 →
  lGComp、ジャンク修正済みカーネルで)— 次セッション最初に確認
- **S¹ ≃ K(ℤ,1) 構成完了(2026-07-11)**: LibCircleEM に
  `toEM`(loop ↦ emloop 1)・`fromEM`(em1rec、合成セルは trans-充填+
  intLoopComp 補正)・`fromTo`(transReflL 平方の path-over 読み)・
  `invUnique`・`emNegOne`・**`toIntLoop`(cong toEM は定数動機の
  除去子-hcomp 可換により trans に定義的分配 — 検証3ms!)**・
  `toFrom`(em1elim + isPropPathPSet 放電)・`s1EquivEM`・`s1IsEM`。
  ネイティブ検証: toEM 0ms/fromEM 183ms/invUnique・emNegOne・toIntLoop
  即決 ✓。fromTo/toFrom は時間級(from の展開が isGroupoidS1 級値を
  conv に持ち込む既知パターン)— ランナー走行中。
  **カーネル: ネイティブ限定 defn 評価キャッシュ実装**(純モデル=従来
  動作でインタプリタ無影響、implemented_by はネイティブでのみ発火 —
  過去の全キャッシュ失敗の真因が「インタプリタで純モデルが走っていた」
  ことと整合する正しい設計)。ただし応用形(capp 再実体化)の conv には
  未だ効かず、fromTo/toFrom の時間級は残存 — 次の的は conv/capp 段の
  共有(要プロファイル)
- π₂(S²) 方面(Freudenthal 級 — 研究規模)
- 更なるホモトピー論: トーラス・懸垂・π₁(S¹∨S¹) など(HIT の一般化が先)

### F. カーネルの全域化とメタ理論(長期・研究級)
`partial def` を well-founded 再帰に置換 → Lean 側からカーネルの性質
(健全性・正規化)を証明する道が開く。Interval.lean は既に全域なので、
DNF 正規形の正当性証明(自由 De Morgan 代数の決定手続きの検証)が
最初の一歩として現実的。

### G. Lean 側モジュールの続き
`Logic/`: `ProvabilityTheory` の一階算術によるインスタンス化(Gödel 数化・
表現可能性 — 大規模)。`Hott/`: h-level 理論、`Equiv` の合成。

## 7. 作業のコツ(実践知)

- **Raw AST の括弧**: 深いネストで「閉じ括弧が1つ過剰」が頻出バグ。
  末尾の `)))...` は開き括弧を数えてから書く。エラーは
  `Fields missing: tm` / `unexpected token ')'` として現れる。
- **束縛名の捕獲**: Raw ビルダー(`isPropR` 等)を合成するとき、内側の
  束縛名が外側の参照を捕獲しないよう命名に注意(既存は "xp"/"yp" 等で回避)。
- **新しい #guard の追加**: 重い正規化(巻き数系)は 1 件あたり数分かかる。
  Examples に足す前に scratch で時間を測る。型検査のみの #guard は秒単位。
- **`.ref` パターン**: ライブラリ定義の再利用は `LibDef.ref = .ann tm ty`。
  項が大きくなるが検査器が毎回照合するので安全。
- **conv 失敗の読み方**: 検査器のエラーは正規形の Repr を出す。両辺の
  頭部構成子と、papp 端点注釈・hcomp 系の枝順序を最初に疑う。
  に AI 用の作業メモリがある(本書と重複するが、セッション横断の教訓を含む)。

## 8. 主要シンボル索引(Cubical/)

| シンボル | 場所 | 役割 |
|---|---|---|
| `IVal.dnf/equiv/substLvl/mixedPolarity` | Interval | 区間の判定的等価と ∀ 用素材 |
| `Term` / `Raw` / `Raw.resolve` | Syntax | コア項・表層・名前解決 |
| `Term.shift` / `equivT` / `fiberT` | Syntax | シフト・Equiv 型の項合成(Glue 検査用) |
| `eval/capp/vapp/vpapp/quote/conv` | Semantics | NbE 本体 |
| `force` | Semantics | **全遅延境界簡約**(原則 4-1) |
| `vtransp/transpGlue/cofForall` | Semantics | Kan 輸送(Glue は δ 付き完全版) |
| `vhcomp/hfillAt/vcomp/natHcomp/intHcomp` | Semantics | 合成系 |
| `vs1elim/vintrec/vunglue` | Semantics | 消去子(可換規則込み) |
| `lineEquivRaw/lineEquivTm` | Semantics | HCompU 用の閉じた対象言語プログラム |
| `usesLvl` | Semantics | constancy 用の早期打ち切り出現検査(quote と同型走査) |
| `check/infer/inferSort` | TypeCheck | 双方向検査+レベル推論 |
| `resolveFace/contradictory/restrictEnv` | TypeCheck | 面制約下の検査 |
| `checkDef/normalize` | TypeCheck | トップレベル API(閉項) |
| `LibDef/allDefs` | Library | ライブラリ枠組み(49定義) |

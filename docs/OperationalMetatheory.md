# 操作的メタ理論の正式構成(E フェーズ、2026-07-17〜)

第3次外部レビュー(2026-07-17 受領)への回答として、論文 §5–7 の
操作的体系を**正式な依存型理論のメタ理論**として完成させるための
開発文書。ここでの定義・補題・証明が v4 論文の §5–7+付録の原稿になる。

対応するレビュー指摘:
- 3.1 アルゴリズム的等式の admissibility(同値関係・合同・弱化・置換・
  文脈変換・型保存・型検査整合)→ §4–5
- 3.2 「same value」の意味(クロージャ表現)→ §1–2(表現同値 ≈)
- 3.3 occurs-check の健全性定理 → §3
- 3.4 停止性の正式な well-foundedness → §6(論理関係への畳み込み)
- 5 canonicity 完全証明+循環の解消 → §6–7
- 4 No-go の導出木と意味論的主張の精密化 → §8
- 6 Cartesian/De Morgan の二層化 → §9
- 7 HIT 署名クラスの限定 → §10

**方針の要約**: 論理関係(型値帰納の Kripke PER)を一度だけ構築し、
(a) 停止性、(b) canonicity、(c) admissibility 群のすべてをその
基本定理(fundamental theorem)の系として得る。素朴な「call graph に
新閉路なし」型の議論は全廃する。constancy 検査は表現非依存の
**仕様**(readback 台)で定義し、実装はその健全な近似とする。

---

## §1 意味領域の正式定義

### 1.1 生データ

カーネル(Semantics.lean)に即して:

- **レベル** ℓ ∈ ℕ: 自由変数(項変数・次元変数の両方)の de Bruijn
  レベル。**深さ** d: 現在の binder 入れ子数。不変量: 値 v の中の
  自由レベルはすべて < その生成時の深さ。
- **区間値** IVal: レベル生成の自由 De Morgan 代数の元
  (antichain-DNF で正規化可能; `IVal.dnf`)。
- **値** Val: 弱頭正規形。head 構成子(vpi, vlam, vsigma, vpair,
  vpathP, vplam, vglueTy, vglue, HIT 系, vne, …)+引数
  (Val / IVal / Closure / VCof / システム)。
- **クロージャ** Closure: `mk env body`(defunctionalized: 環境=値
  リスト、body=項)または合成子(reparam, transpPi, … — 有限個の
  クロージャコンビネータ)。**instantiation** `capp d c v` はクロージャ
  種で場合分けし、`mk` の場合は eval(body, env++[v]) を呼ぶ
  (**ここで評価が再入する** — 停止性が構造的でない唯一の理由)。
- **中立** Neutral: 変数に始まる遮断された除去子スタック。

### 1.2 次元作用(dimension action)

区間代入 ξ : Level ⇀ IVal の値への作用 v⟨ξ⟩ を、head を保ち IVal 部に
ξ を適用し、クロージャには環境へ点ごとに作用させるものとして定義する
(カーネルでは face 適用・`reparam` として実装されている部分作用)。
**台** supp_I(v) := readback(§3.1)に現れる区間レベルの集合。

---

## §2 表現同値 ≈ と値同値 ≡val

### 2.1 問題(レビュー 3.2 の通り)

defunctionalized NbE では `eval(Aσ, ρ)` と `eval(A, eval(σ,ρ))` の
クロージャは**内部表現まで文字通り同一にならない**
(body が Aσ' で環境が短い vs body が A' で環境が長い)。よって
旧補題 5.1 の「the same value」は構造的等号としては偽。正しくは
二段階の関係で述べる。

### 2.2 表現同値 ≈(bisimulation)

値の上の最大の関係 ≈ で次を満たすもの(余帰納的定義):

- v ≈ v' ⟹ 同じ head 構成子;
- IVal 引数・VCof 引数は**文字通り等しい**(dnf 正規形で比較;
  fresh レベルの割当は深さで決定的なので両辺で一致する — 2.4);
- Val 引数は ≈;
- クロージャ c ≈ c' ⟺ ∀ d, ∀ 引数値 w(generic 中立を含む):
  capp d c w ≈ capp d c' w;
- 中立は spine を点ごとに(head 変数は同一レベル、引数は ≈)。

直観: 「クロージャの表現の差しか違わない」。≈ は同値関係で、
すべての意味操作(capp, force, vapp, vtransp, vhcomp, conv, quote,
usesLvl の仕様版)と両立する(各操作は head・IVal・instantiation の
挙動のみで決まるため; 操作ごとの両立補題は v4 付録で個別に述べる)。

**補題 2.2.1(readback 不変性)**: v ≈ v' ⟹ quote_d(v) = quote_d(v')。
証明: quote は head で場合分けし、クロージャは generic 点で
instantiate して再帰する(binder を潜る)ので、≈ の定義がちょうど
quote の観測能力と一致する。∎(この補題が ≈ の「正しさ」の内容)

### 2.3 値同値 ≡val(型指標付き PER)

型値 T による帰納で定義する Kripke PER(世界=深さ d、未来=深さの
増加。Abel 流 NbE 正当性の標準構成):

- T = vnat: v ≡val v' ⟺ 同一数字への強制、または両方が readback の
  等しい中立;
- T = vpi d D C: f ≡val f' ⟺ ∀ d' ≥ d, ∀ w ≡val_{D} w':
  vapp f w ≡val_{capp C w} vapp f' w';
- T = vsigma: 射影ごと;
- T = vpathP F l r: p ≡val p' ⟺ ∀ 区間値 ι: vpapp p ι ≡val_{capp F ι}
  vpapp p' ι(端点では l, r と一致するので自動);
- T = vglueTy sys B: unglue 像が ≡val_B かつ各 live face 上で枝ごとに
  ≡val;
- T = vuniv: コードとして、両者の El が対等な PER を定める(型値の
  構造帰納がここで universe レベルの帰納に持ち上がる — Huber と同じ
  階層化);
- HIT: 構成子ごと(引数 ≈ ≡val、区間引数は文字通り等しい)+
  hcomp 閉包+中立。

**補題 2.3.1**: ≈ ⊆ ≡val_T(任意の T で)。**補題 2.3.2**: ≡val は
PER で、型値の ≡val-変形に沿って不変。**補題 2.3.3(conv の正当性)**:
conv_d(v, v', T) 受理 ⟺ v ≡val_T v'(健全性は conv 各節が ≡val の
定義節をそのまま検査していることによる帰納; 完全性(受理側)は
quote/readback を介した標準の NbE 完全性 — **ここが conv の対称性・
推移性の出所**: ≡val が PER なので conv も PER 的に振る舞う)。

### 2.4 fresh レベルの決定性

両辺の評価は同じ項構造を同じ深さカウンタで潜るため、生成される
generic レベルは両辺で文字通り一致する(深さ=レベルの規約)。
これが 2.2 の「IVal 部は文字通り等しい」を可能にする。v4 では
深さ規律の不変量(値の自由レベル < 深さ)を明示の補題にする。

---

## §3 constancy 検査: 仕様と実装の分離(レビュー 3.3)

### 3.1 仕様

**定義(検査の仕様)**: 族値 F(深さ d、fresh レベル ℓ で
instantiate 済み)について
```
const?_spec(F, ℓ) :⟺ ℓ ∉ FV(quote_{d+1}(F))
```
readback の自由レベル集合という**表現非依存**の条件(補題 2.2.1 より
≈ で不変)。**論文の形式的体系はこの仕様で定義する。**

### 3.2 健全性定理(レビューの要求そのもの)

**定理 3.2.1(constancy-check soundness)**:
const?_spec(F, ℓ) = true ⟹ ∀ r, s ∈ IVal: F⟨r/ℓ⟩ ≡val F⟨s/ℓ⟩、
とくに型値としての両端 F⟨0/ℓ⟩, F⟨1/ℓ⟩ は**同一の PER** を定める。

証明の骨格(v4 付録で全展開):
1. **quote/作用可換**: quote(F⟨ξ⟩) = quote(F)⟨ξ⟩(次元作用は head と
   IVal 部にしか触れず、quote は binder を generic で開く — 標準)。
2. ℓ ∉ FV(quote F) なら quote(F⟨r/ℓ⟩) = quote(F)⟨r/ℓ⟩ = quote(F) =
   quote(F⟨s/ℓ⟩)。
3. **NbE 冪等性**: v ≡val eval(quote v)(基底論理関係の標準補題;
   継承component)。よって F⟨r/ℓ⟩ ≡val eval(quote F) ≡val F⟨s/ℓ⟩。∎

### 3.3 実装は仕様の健全な近似

カーネルの `usesLvl` は quote を鏡映する走査(コード注釈どおり)で、
次の 2 点だけ仕様とずれる:
- **lb スタンプカット**(ℓ ≥ lb ⟹ 不出現): 深さ補題(lb は自由レベルの
  上界)により**正確**(仕様と一致する answer)。
- **チューブ閉包の構造走査**(instantiate せず環境を dependsOn で
  濾して走査): 出現の**過大報告**があり得る(body が実際には使わない
  経路など)。過大報告は const? の発火を**減らす**方向 — すなわち
  実装 ⟹ 仕様(usesLvl が false なら readback にも ℓ は現れない)。

**定理 3.3.1(実装健全性)**: usesLvl(ℓ, F) = false ⟹
const?_spec(F, ℓ)。よってカーネルは仕様体系の(発火がやや少ない
可能性のある)健全な実現であり、**すべての正例 probe は仕様体系の
証人でもある**。負例 probe はカーネルのアルゴリズム的等式についての
主張(従来どおり)。

### 3.4 これで正分岐の型保存が完結

定理 3.2.1 により、正分岐では両端の型値が ≡val(それどころか
readback が同一)なので、(R) の返す eval(u, ρ) は要求される型の PER に
そのまま属する。旧稿の「literally the same predicate」は
「**同一 readback をもつ ≡val な型値、よって同一の PER**」に精密化。

---

## §4 意味論的置換補題(旧補題 5.1 の正しい形)

**定理 4.1**: すべての項 t、代入 σ、環境 ρ について
```
eval(tσ, ρ) ≈ eval(t, eval(σ, ρ))
```
(≡val でなく、より強い表現同値 ≈ で成り立つ。)

証明: t の構造帰納。
- 変数・構成子・除去子: 標準(クロージャを作る節では ≈ のクロージャ節
  そのもの — capp の両辺が帰納法の仮定で ≈)。
- **transp 節**: 族値 F_L := eval(Aσ,ρ)[ℓ], F_R := eval(A,σ*ρ)[ℓ] は
  帰納法の仮定+capp 両立で F_L ≈ F_R、fresh ℓ は 2.4 により両辺同一。
  検査は**仕様**なので補題 2.2.1 により
  const?_spec(F_L,ℓ) = const?_spec(F_R,ℓ) — **分岐が必ず一致する**。
  正分岐: 帰納法の仮定(u)。負分岐: 同一 head への構造 dispatch、
  部分呼び出しは帰納法の仮定と ≈-両立補題群。∎

**注(実装との関係)**: 実装の usesLvl は ≈ の両辺で答えが一致する
保証が仕様経由でしか得られない(チューブ走査は表現依存)。これが
「体系の定義は仕様で行い、実装は健全な近似」という分離の決定的な
理由である。v4 ではこの注を明示する(査読者が突く点を先回り)。

**系 4.2(型付き置換安定性)**: Γ ⊢ t ≡alg u : A かつ Δ ⊢ σ : Γ なら
Δ ⊢ tσ ≡alg uσ : Aσ。証明: 定理 4.1+補題 2.3.1+conv の ≡val 正当性
(2.3.3)+基本定理(§5)による eval(σ,ρ_Δ) の Γ-計算可能性。∎

---

## §5 型付きアルゴリズム的等式と admissibility(レビュー 3.1)

### 5.1 定義

**定義 5.1.1**: Γ ⊢ t ≡alg u : A :⟺ 生成的環境 ρ_Γ(各変数を
generic 中立にとる)で conv_{|Γ|}(eval(t,ρ_Γ), eval(u,ρ_Γ),
eval(A,ρ_Γ)) が受理。

### 5.2 論理関係の基本定理(一度だけ証明する中心定理)

**定義 5.2.1(計算可能性)**: 型値 T 上の述語 Comp_T(v) :⟺
v ≡val_T v(PER の対角)。**項の計算可能性**: Γ ⊨ t : A :⟺
∀ d, ∀ Γ-関連環境対 ρ ≡ ρ': eval(t,ρ) が**定義され**(停止を含む)、
eval(t,ρ) ≡val_{eval(A,ρ)} eval(t,ρ')。

**定理 5.2.2(基本定理)**: Γ ⊢ t : A(T₀+(R) の型付け)⟹ Γ ⊨ t : A。

証明: 型付け導出の帰納。基底規則の全節は**継承 component**
(§9 の A/B 二層を参照)。新節は transp のみ:
- 正分岐: 定理 3.2.1 で両端の PER が同一 ⟹ IH(u) で閉じる。
- 負分岐: 基底証明の構造 transp 節。内部で発生する再帰的 transp は
  **型値の構造帰納**(Comp の定義が型値帰納なので、Π 線の cod、
  Σ 線の第2成分などは構造的に小さい型値)で処理する — 型付け導出の
  帰納と型値の帰納の**二重帰納**であることを明示し、旧稿の
  「same induction, well-founded by call graph」を全廃(レビュー 5 の
  循環疑義への回答)。停止性は Γ ⊨ t : A の定義に含まれるので、
  **別立ての停止性補題は不要になる**(§6)。∎

### 5.3 admissibility 群(すべて系)

- **同値関係**: 反射性 = 基本定理の対角; 対称・推移 = ≡val が PER
  (2.3.2)+conv 正当性(2.3.3)。
- **合同(term former ごと)**: 各 former の評価が値 former に落ち、
  ≡val の定義節がちょうど成分ごとの関係なので、成分の ≡alg から
  全体の ≡alg(v4 付録に former 別一覧表: lam/app/pair/fst/snd/
  plam/papp/transp/hcomp/glue/HIT 構成子・除去子)。transp の合同は
  族の ≡alg から検査の一致(仕様+2.2.1)を経由する点が新規。
- **弱化**: Kripke 単調性(深さ d ≤ d' で ≡val が保たれる; lb
  スタンプの深さ補題)。
- **置換**: 系 4.2。
- **文脈変換**: Γ ≡ Γ' なら ρ_Γ ≡ ρ_{Γ'}(型値 ≡val)で、≡val の
  型不変性(2.3.2)。
- **型保存(subject conversion)**: Γ ⊢ t : A, Γ ⊢ A ≡alg B : U ⟹
  Γ ⊢ t : B — 双方向検査器の conversion 節が conv を呼ぶことと 2.3.3。
- **型検査との整合**: checker 受理 ⟹ T₀+(R) 導出可能(健全性、既存)
  +基本定理で意味論的に妥当。

**定理 5.3.1(まとめ; v4 の "Algorithmic equality is an admissible
conversion relation")**: ≡alg は上記すべてを満たす型付き変換関係で
ある。

---

## §6 停止性(レビュー 3.4 への正式回答)

### 6.1 何が相互再帰か(正確な描像)

- eval は項に構造再帰**しない**: クロージャ instantiation(capp)が
  貯蔵 body の eval を再入させる。
- const? は値走査だが、**binder クロージャは generic 点で instantiate
  する**(usesLvlBinder)— 評価再入あり。チューブ閉包は非実体化走査
  (再入なし)。
- conv / quote は型値に従って再帰し、クロージャを instantiate する。

したがって素朴な項サイズ・値サイズの測度は存在しない。停止性は
**論理関係に畳み込む**(Tait 流; Huber・Sterling–Angiuli と同じ
位置付け): Γ ⊨ t : A の定義(5.2.1)が「eval が定義される(停止)」を
含み、基本定理 5.2.2 がそれを型付き項全体に拡張する。conv / quote の
停止は ≡val の型値帰納構造(универス階層で階層化)から。const? の
停止は「walked value が計算可能値」であることから(binder
instantiation は計算可能クロージャの generic 適用 = 計算可能値の
評価で停止)。

**v4 での書き方**: 「停止性定理」を独立の補題として残すが、その証明は
「基本定理の系」と一行で書き、基本定理の停止内容を明示する。
「call graph に新閉路なし」という表現は削除。

---

## §7 canonicity の完全証明(構成表)

v4 付録の目次となる完全リスト(各項目 = 補題1つ、Huber 対応節を併記):

1. 意味領域の定義(§1)— H §2 対応
2. ≈ と諸操作の両立補題群(§2.2)— 新規
3. ≡val の定義と PER 性・型不変性(§2.3)— H §3(述語)対応
4. universe 階層化(≡val_U の well-foundedness)— H 同様
5. quote/作用可換補題(3.2.1-1)— 新規(だが標準形)
6. NbE 冪等性 v ≡val eval(quote v) — H の readback 補題対応
7. constancy 仕様健全性(定理 3.2.1)— **新規・本論文の鍵**
8. 実装健全性(定理 3.3.1; lb 深さ補題を含む)— 新規(実装対応)
9. 意味論的置換補題(定理 4.1)— H の代入補題の値版
10. 基本定理(5.2.2): 基底節(継承)+ transp 正分岐(7 を使用)
    + transp 負分岐(型値帰納; 二重帰納の明示)+ hcomp 節(継承;
    transport redex を検査しないことの確認)+ Glue 節(transpGlue の
    各段が計算可能操作の合成であること)+ universe 節 + HIT 節
    (§10 の署名クラスに限定)
11. numeral inversion(closed nat の計算可能値は数字)— H 対応
12. **定理(canonicity)**: 閉 t : nat ⟹ eval(t) は数字。
13. **系**: 一貫性(0 ≢alg 1)、J-refl(strictJReflD が機械証人)。

現状: 1–9 は本文書で証明済みまたは骨格+標準形の明示、10 は構造確定
(基底節の環境版転写は v4 付録で全列挙)、11–13 は標準。
**残る本質的作業は 10 の基底節列挙の書き下しのみ**(数学的新規性は
なく、分量作業)。

---

## §8 No-go 定理の補強(レビュー 4)

### 8.1 完全な導出木(v4 §4 に収載)

型付け前提を明示した導出:
```
Γ ⊢ A : U   Γ ⊢ a b : A   Γ ⊢ p : Path A a b
Γ, i ⊢ Path A a b type(i 不出現)
─────────────────────────────────────────────── (R)
Γ ⊢ transp^i (Path A a b) i0 p ≡ p : Path A a b
─────────────────────────────────────────────── (structural PathP)
Γ ⊢ transp^i (Path A a b) i0 p ≡ ⟨j⟩ comp^i A [∂j ↦ a,b] (p j)
─────────────────────────────────────────────── (comp = hcomp∘transp; (R) で transp 部消去; 合同)
Γ ⊢ transp^i (…) i0 p ≡ ⟨j⟩ hcomp A [∂j ↦ a,b] (p j)
─────────────────────────────────────────────── (対称+推移)
Γ ⊢ p ≡ ⟨j⟩ hcomp^ι A [j=0 ↦ a, j=1 ↦ b] (p j)   (†)
```
各段の型付け・境界条件の検証を付す(chatGPT レビュー 4.3 の
チェックリスト: PathP 異種版でも端点補正の形は同じ(comp の線が
A(i, j) になるだけで、定数族では同様に hcomp 残滓)、Cartesian 版でも
残滓は同形(接続は不使用)、η_Path が効かない理由 = η は
папp/plam の相殺であり hcomp head には作用しない、「定数」は
**充填次元 ι についての**定数性)。

### 8.2 意味論的主張の精密化(方法 B を採用)

v4 では次の言い回しに統一する:
> The derived equation (†) is a constant-system hcomp-regularity
> principle. It is *refuted by our algorithmic equality*
> (machine-checked), and it is *closely related to* the regularity
> principles known to fail in cubical-sets models
> [Swan, Sattler]; we do not claim it is literally an instance of a
> published counterexample, and we leave the construction of a
> semantic countermodel for (†) as a strengthening
> (Open Problem list).
abstract の "precisely the kind of regularity that fails in the
standard models" は "a constant-system hcomp-regularity principle of
the kind excluded in standard models" に弱める。**方法 A(具体的
countermodel)は Open Problems へ**(達成すれば採択確度 60–75% 帯、
レビュー 10 の評価と一致)。

---

## §9 主定理の二層化(レビュー 6)

- **Theorem A(Cartesian 版)**: 基底 component(§7 の 10 の基底節+
  6 の readback 補題)を Sterling–Angiuli の normalization 構成から
  取る。得られる主張: Cartesian ABCFHL + 優先化 (R) の操作的体系で
  admissibility 群+canonicity+J-refl。**無条件を目指せる**が、
  S–A の構成(synthetic Tait computability)と本文書の素朴 Kripke PER
  の間の橋渡し(彼らの gluing から本稿の形の基本定理を読み出す)を
  正確に書く必要がある — v4 では「S–A の結果から (A)-component が
  従う」ことの対応表を付録に置く。
- **Theorem B(De Morgan 版)**: (A)-component を仮定として明示
  ((A1)–(A4) を §7 の補題番号に付け替えた正確な形で)。Lean 実装は
  この版の実現。

---

## §10 HIT 署名クラス(レビュー 7)

一般的な「higher inductive constructors」をやめ、次で置き換える:

**定義 10.1(argument-wise transport 署名)**: 構成子の構造 transport
が「点引数を線ごとに transport し、区間引数を不変に運ぶ」形で、
境界補正の hcomp/fill を生成しないもの。

**本カーネルの実装署名の分類**(機械検証状況込み):
| HIT | 構成子 | 分類 | switchover |
|---|---|---|---|
| list | lnil/lcons | argument-wise(点) | 収束(swListD ✅) |
| susp | north/south/merid | argument-wise(merid は区間引数運搬) | 収束(swSuspMeridD ✅) |
| pushout | pinl/pinr/ppush | argument-wise | 収束(同型の議論; probe 追加は任意) |
| S¹/torus | base/loop(P/Q)/surf | 引数なし(区間のみ) | 自明収束 |
| EM₁ | embase/emloop/emcomp | argument-wise | 同上 |
| BGpd | bpt/barr/bcomp | argument-wise | 同上 |
| quot | qin | argument-wise | 収束 |
| quot | qeq/qsquash | **構造規則なし**(非構成子は中立化) | **空虚**(臨界対が存在しない) |
| trunc | tin/squash | tin: argument-wise; squash: 同様 | 収束/空虚 |

**補題 10.2**: argument-wise 署名では switchover は (R) の引数線
崩壊のみで文字通り収束(η 不要)。証明は署名の形から一様。∎

v4 の主張は「実装された上記署名について」と明示的に限定し、
一般 HIT 署名枠組み(boundary 付き構成子が hcomp を生成する場合の
分析)は Open Problem として残す(Path の教訓から、boundary 補正を
持つ署名では非収束が予想される、と注記)。

---

## §11 残作業(v4 執筆前チェックリスト)

- [x] §2.2 の操作両立補題群の個別 statement 化 → 論文付録 B(L3–L8、
      同時余帰納の枠+操作別証明; 2026-07-17)
- [x] §7-10 基底節の環境版転写の全列挙 → 論文付録 "The fundamental
      theorem, case by case"(変数/Π/Σ/Path/宇宙/ℕ/hcomp/Glue/HIT/
      構造 dispatch(内側帰納の所在明示)/正分岐; 合同補題の非自明
      インスタンス一覧; 2026-07-17)
- [x] §8.1 導出木の LaTeX 化 → 論文 §4.3(式 (1)–(†)、型付け検証+
      スコープ4注記; 2026-07-17)
- [x] §9 Theorem A の S–A 対応表 → 論文付録 "The Sterling–Angiuli
      bridge"(arXiv:2101.11479v2 精読: Thm 42/43, Cor 47; 宇宙なし・
      HIT は S¹ のみ・非評価的手法(STC/stabilized neutrals)・
      De Morgan は mutatis mutandis 主張のみ、を確認。(B) の
      judgmental-theory 部は provided、evaluator-level 部は転写義務、
      宇宙・HIT・De Morgan は gap、と項目別に確定。coe の r=s↪a 境界
      条件 = (S_i1) の Cartesian 版という翻訳段落も追加; 2026-07-17)
- [ ] pushout ppush の switchover probe(任意; 表の網羅性向上)
- [ ] リポジトリ公開(ユーザー操作)

---

## §12 第4次レビュー対応(2026-07-17): 検査器の実装=仕様の確立ほか

### 12.1 レビュー 3.1 の検証結果 — 実装は既に仕様と一致していた(死コード発見)

レビューの論理(一方向健全性では「実装は仕様体系の実現」を導けない;
usesLvl の false negative で仕様=正分岐/実装=構造分岐に分裂し、
Path では両者が非可換)は**正しい**。しかしカーネルを精査した結果、
前提事実の方が誤っていた:

- 旧 §3.3 の「チューブ閉包の構造走査(過大近似)」は、**usesLvl の
  入口から到達不能な死コード**(`usesLvlClosure`/`usesLvlSys`、
  204 行)と、それに付随する古い doc コメントに基づく記述だった。
- 到達可能な全経路は `quote` を節ごとに正確に鏡映する:
  - `usesLvlRun` の値節 ⟷ `quote` の値節(同じ `force`、同じ構造再帰、
    IVal は `.mentions` ⟷ `quoteIVal` の FV — IVal の構造をそのまま
    写すので一致)
  - `usesLvlBinder`/`usesLvlIBinder` ⟷ `quoteBinder`/`quoteIBinder`
    (generic レベルでの capp 実体化)
  - `usesLvlNeRun` の `.transp`/`.hcomp` 節 ⟷ `quoteNe`(**hcomp
    チューブも実体化** — `usesLvlIBinder` ⟷ `quoteSys`)
- 唯一の逸脱は lb スタンプカット(深さ補題により正確)と memo
  (透明)。

**開発(2026-07-17 実施)**: 死コード 204 行を削除(lake build 成功、
golden 299 定義一致、全 probe 通過 — 到達不能性の実証)。`usesLvl` に
正確性を明示する doc コメントを追加。

**定理 12.1.1(検査器の正確性)**: `usesLvl(ℓ, F) = (ℓ ∈ FV(quote F))`。
証明: usesLvl と quote の相互再帰構造の同時帰納(節ごとの鏡映)+
lb カットの正確性(L1)+ memo の透明性。∎

**系 12.1.2**: 実装された評価器は仕様体系そのものである(分岐は常に
一致)。したがって置換補題・admissibility・canonicity は実装にそのまま
適用され、usesLvl の ≈-不変性は readback 不変性(補題 2.2.1)から
従う。旧「sound approximation」の言い回しと定理 3.3.1 は
**正確性定理に置換**(旧 3.3 節は本節が上書き)。

### 12.2 レビュー 3.2 — 体系の命名分離(T_eq / T_alg)

正しい指摘。fundamental theorem を「T₀+(R) の型付け」に対して述べると
conversion 規則が (†) 型の等式を使え、帰納の conversion 節が破綻し得る。

- **T_eq** := T₀+(R)(無制限等式理論)— No-go 解析と soundness の
  対象にのみ使用。
- **T_alg** := conversion 規則に ≡alg を用いる型付け体系(付録 A の
  規則群+conversion rule; 実装の双方向検査器と一致)。
- fundamental theorem・admissibility・canonicity はすべて **T_alg の
  型付け導出**について述べる。帰納に **conversion 節**が加わる:
  Γ ⊢ t : A, A ≡alg B ⟹ eval(t,ρ) ∈ Comp_{eval(B,ρ)} — conv 正当性
  (2.3.3)+ ≡val の型不変性(2.3.2)で閉じる(アルゴリズムが受理
  した等式だけが使われるので No-go と衝突しない — これが分離の要点)。

### 12.3 レビュー 3.4/3.5 — 部分性の形式化

eval/inst/quote/const?_spec/conv は**一つの相互再帰的部分関数族**として
定義する(数学的には: 引数と結果の組を結ぶ big-step 導出木の帰納的
定義=関数のグラフ; 実装では Lean の `partial def` がこれに対応)。
eval → const?_spec → quote → inst → eval の循環は相互定義の内部に
あり、定義自体は well-formed(導出木の存在が「定義される」の意味)。

- ≈ は**Kleene 型の余帰納的関係**: クロージャ節は
  「∀w: inst(c,w) と inst(c',w) は共に未定義、または共に定義され ≈」。
  guardedness: ≈ の各展開は値構成子を一つ横切る(生産的)。
- 両立補題(L3–L8)は「定義される側の導出木に関する帰納+結果値に
  関する余帰納」の同時論法として読む(依存グラフ:
  eval ← inst ← {transp, hcomp, glue 操作} ← eval は導出木の
  部分導出関係で整礎)。
- 置換補題は Kleene 形:「一方が定義されれば他方も定義され ≈」。
- 停止性(well-typed 入力上の全域性)は従来どおり基本定理の結論
  (意味論的型付けの定義に「定義される」を含める)。

### 12.4 レビュー 3.3 — Cartesian 層の表現

「unconditionally in the Cartesian layer」を撤回し、canonicity は
「Relative to component (B), in both presentations; in the Cartesian
fragment the judgmental-theory part of (B) follows from
Sterling–Angiuli, the evaluator-level bridge remaining open」に統一。

### 12.5 その他

- Abstract 短縮(4 論点: no-go / prioritized algorithmic system /
  admissibility+canonicity / artifact)+ 「excluded」→「closely
  related to regularity principles known to fail」。
- 実装節の記述も正確性定理に合わせ更新(ARTIFACT.md 同期)。

---

## §13 第5次レビュー対応(2026-07-17): core 断片の (B) 完全放電ほか

第5次レビュー(採択確度 35–50%; 最有効の修正 = ①exactness 完全化
②小断片で (B) を放電し無条件主定理 ③§13 の Cartesian 表現弱化)は
全項目妥当。実施:

### 13.1 無条件 core(レビュー推奨②、最大の追加)

**T^core := Π, Σ, PathP, ℕ, S¹ + transp + hcomp(Glue なし・宇宙
なし)**について base component (B) を論文内で完全放電(新付録
"Discharging the base component for the core fragment"):
- 断片が扱いやすい構造的理由を明示: 型値が**素の構造帰納**を許す
  (宇宙階層化不要)+ transport が **transpGlue に決して出会わない**。
- 内容: 論理関係の全節(ℕ/Π/Σ/PathP/S¹)、reflect/reify(readback
  正当性 — 端点 η と DNF 正準性のみが cubical 成分)、hcomp 計算可能性
  (ℕ は計算で消える/構造規則/S¹ は hcomp-cell)、transp 計算可能性
  (正分岐 = 検査健全性定理、負分岐は型値の内側帰納 — **Glue 節が
  存在しない**)、基本定理(conversion 節込み)。
- **系(Theorem A′/thm:core)**: core 上で admissibility・canonicity・
  J d refl ≡ d が**無条件**。J は Path+transp のみで定義されるので、
  論文の看板等式は完全に無条件 core の内側に住む。
- 意図的除外(Glue/宇宙/広い HIT)は「Huber/S–A の内容そのもので
  あり、圧縮して見かけの完全性を装うより開いたまま示す」と明記。

### 13.2 exactness の完全化(推奨①)

Theorem (Checker exactness) を **Kleene 形**(definedness 同時移転)に
再述し、新付録 "Checker exactness: the full clause table" を追加:
- definedness transfer(両者の big-step 導出木が同型; usesLvl 側の
  剪定(lb カット・早期終了)は definedness を壊さない)
- 値/中立/閉包実体化の全節対応表(中立 hcomp 行に「旧死コードが
  構造走査しかけた箇所」の注記)
- lb カットの**完全性**(枠組: 貯蔵レベルは lb 未満、readback 中の
  fresh レベルは束縛される ⟹ カットは仕様と同じ答え)
- memo の透明性(純関数+物理同一性キーは構造同一性を含意、
  世代スタンプ規律により衝突なし)

### 13.3 ≈ 装置の形式化(3.3)

§Partiality に追記: ≈ = 単調作用素 Φ の最大不動点(Knaster–Tarski)、
余帰納証明 = Φ-不変関係(post-fixed point)の提示、guardedness =
各余帰納仮定の使用が Φ の展開の値構成子の下にあること、同時帰納の
依存順序 = big-step 導出木の部分導出関係(有限木ゆえ整礎)。

### 13.4 表現整合(3.1 後半)

結論の「the Cartesian layer already inherits [S–A]」を撤回し、
「core は本論文で放電済み・それ以遠は judgmental-theory 部が S–A、
evaluator-level bridge/宇宙/Glue/HIT は open」に統一。abstract にも
無条件 core の一文を追加。

結果: 28 頁、0 エラー、0 未定義参照、overfull ≤ 15pt。
セマンティック countermodel(3.4)は引き続き Open Problem(採択後の
強化路線)。

---

## §14 第6次レビュー対応(2026-07-17): 無条件 core の全面展開(v7)

第6次レビュー(45–60%; 最重要 = 「無条件 core の証明を査読者が補完
なしに検証できる密度へ」)は全項目妥当。実施(論文 v7、32 頁):

1. **S¹ を core から除外**(第一優先): 最小 core = Π, Σ, PathP, ℕ +
   transp + hcomp。S¹ は独立の Proposition(明示的に proof sketch と
   ラベル)+ artifact evidence として分離 — 看板定理が HIT 義務に
   巻き込まれない。
2. **付録 F 全面増補**(第二優先; 3–4 頁 → 約 8 頁、前者別補題):
   - **帰納順序の正確化(決定的改良)**: 論理関係を「構文型 T +
     環境」に対する**構造再帰**で定義し直し(型値反転補題により
     閉包実体化 = 真部分式の評価)、「structurally smaller type value
     の順序は何か」という疑義を根本解消(順序 = 構文の部分項関係、
     測度・順序数・宇宙階層化は一切不使用と明記)。
   - 正規形・中立形の BNF 明示(core では transp-中立が生じない、
     hcomp-中立は ℕ の中立 base 上のみ、等の但し書き付き)。
   - reflect/reify を前者別に同時帰納で全ケース書き下し(PathP の
     端点 η と DNF 正準性を明示)。
   - conversion correctness(健全性 = conv 実行帰納、完全性 =
     reify + 正規形文法帰納)。
   - hcomp 計算可能性: ℕ(数字 base の構成子透過/**中立 base の
     stuck hcomp-中立ケースを正しく記述**(旧「ℕ-中立は hcomp-free」
     の誤りを修正)/**閉インスタンス注記**: 閉じた cofibration は
     決定されるので閉 hcomp は必ず計算 — canonicity で使用)、
     Π/Σ(従属第2成分の filler 経由の異種合成)/**PathP の端点
     coherence**(端点チューブ追加系の境界検査)を明示。
   - transport 計算可能性: ℕ 線は値が ℓ-自由なので正分岐必発
     (負分岐到達不能)、Π 線(w の逆向き fill 込み)、**Σ 線の
     codomain typing 詳細**(fill ū i で拡張した環境の関連性から
     族の計算可能性を導く)、PathP 線(vcomp = transp 部+端点
     チューブ hcomp)。
   - 基本定理(natrec の数字帰納+中立ケース、conversion 節込み)
     + 系(停止・canonicity・一貫性・admissibility)。
3. **Theorem 8.1 の完全証明**(第三優先): 新補題 Step soundness
   (big-step 導出帰納; **正 transp 分岐**: A₀ := quote(F) は ℓ-自由、
   IH により A[ρ̂] ≡_{T_eq} A₀ ⟹ (R) の judgmental constancy 前提が
   成立 ⟹ collapse は (R) インスタンス)+ 本定理は quote 健全性 3 本の
   合成。T_alg が T_eq より真に弱いのに各ステップは T_eq-健全という
   非対称性を本文で明示。
4. **Proposition (Strict J)**(第四優先): J_C の型・cubical 定義
   (接続 i∧j)・p:=refl 後の族値(strictConnZeroD が接続吸収の機械
   証人)・検査発火(正確性定理経由)・最終計算 d、を独立命題として
   完全証明。「全成分が最小 core 内 ⟹ 無条件」。
5. **三層の一貫表示**(2.4): イントロに「The three layers, once and
   for all」段落(Unconditional / Relative / Artifact evidence の
   itemize)+「univalent と言うとき univalence は第2・3層に住む」の
   明示。

結果: 32 頁、0 エラー、0 未定義参照、overfull ≤ 15pt。

---

## §15 第7次レビュー対応(2026-07-17): 付録 F の難所仕上げ+文献追跡可能化(v8)

第7次レビュー(55–70%; 「新結果の追加より、付録 F の数個の難しい
case を査読者が完全に追跡できる形に」)は全項目妥当。実施(v8、34 頁):

1. **reflect/reify を前者別 8 補題に分割**(Reflect/Reify × ℕ/Π/Σ/
   PathP、各々独立 statement+証明)。相互帰納規律を冒頭に明文化
   (「L(T) は真部分項 T′ の任意の L′ を使える」)。conversion
   correctness も健全性(前者別 itemize、generic 引数から任意の関連
   引数への転送は置換補題+環境無関係性で明示)/完全性(reify+
   正規形文法帰納+definedness transfer)の 2 補題に分割。
2. **従属 Σ-hcomp の完全な式**: 第1成分の合成 c、filler c̄(ι)
   (truncated hcomp、c̄(0)=fst u₀、c̄(1)=c)、第2成分の異種合成
   vcomp^ι (S[c̄(ι)/x]) [φ_k ↦ snd t_k] (snd u₀) : S[ρ+[c]] を型注釈
   付きで全表示。境界前提の継承(face 上で filler = fst t_k)も明示。
3. **PathP transport の導出形式**: 前提 (P1) l(0) ≡ p 0、(P2) r(0) ≡
   p 1、(P3) 交差面は空虚、を番号付きで導出し、結果の端点 coherence
   (E0) (result) i0 = 面崩壊 → チューブ top → transp 補正後の l(1)、
   (E1) 対称、を式番号付きで表示。
4. **Kan 補題群の同時帰納宣言**: Σ-hcomp が transport@S を、
   PathP-transport が hcomp@T を相互参照するのは真部分項に限る
   ことを preamble で明文化(循環の疑義を先回りで遮断)。
5. **結論の誤読防止**: 「unconditionally on the minimal core /
   relative to the delimited base component for the full implemented
   univalent calculus; we do NOT claim an unconditional strict J for
   the full univalent system」を結論第1段落に明記。
6. **文献の追跡可能化**: 「public discussion」を「folklore assessment
   (circulated only informally)」に置換(検証不能な特定年主張を排除)。
   Sattler 項は「unpublished observation, commonly attributed; 公刊
   された account は Swan の導入部と CCHM/ABCFHL の議論」と正直かつ
   追跡可能な形に。Arend 項に Prelude の具体 URL+accessed 日付。

結果: 34 頁、0 エラー、0 未定義参照、overfull ≤ 15pt。

---

## §16 第8次レビュー対応(2026-07-17): face-indexed world 構造(v9)

第8次レビュー(「比較的高い」評価到達; 最重要 = 付録 F の face/
cofibration 文脈の意味論的扱い)は全項目妥当。実施(v9、37 頁):

1. **World 構造の正式化**(新 subsection "Worlds: depths, dimensions,
   and faces"): world = (深さ d, cofibration ψ)、world 射 = 次元代入
   ξ with ψ′ ⊨ ψ⟨ξ⟩(弱化・face 強化・face restriction が生成例)。
   **Definition (Semantic context satisfaction)**: 区間変数は両側で
   同一の区間値、restriction エントリ φ は ψ ⊨ φ[ρ] を要求。
   **不条理 world(ψ ⊨ ⊥)では全値が関連**という規約を明示 —
   空交差の整合性条件((P3) 型)が「非形式的に自明」でなく本当に
   自明になる仕掛け。
2. **論理関係を world 指標付きに**: 全節が「全ての w′ → w について、
   次元作用で輸送した上で」と Kripke 量化(Π は将来 world の関連引数、
   PathP は将来 world 上の全区間値)。
3. **Definition (Related systems)**: チューブは制限 world
   (d, ψ∧φ_k) で関連、対ごとの整合は (d, ψ∧φ_k∧φ_l) で、base の
   adapted 条件(意味論的境界条件)も同所で。
4. **Lemma (face restriction / weakening)**: 関連性の world 関手性 —
   次元作用が forcing と可換(決定済み face は保たれ、新決定は両側
   同一に崩壊; L5)+ readback/作用可換(L14)で証明。
5. **Lemma (Boundary preservation)**: 合成は各制限 world で
   チューブ top と関連(face 決定による崩壊+関手性)。hcomp 補題群の
   仮定を Definition (Related systems) 参照+結論に boundary
   behaviour を明記する形に更新。
6. 本文 §5 の ≡val 定義に「本文では可読性のため world = 深さ;
   完全な world 構造は core では付録で明示、一般計算では (B) の
   一部(Huber の述語も face-indexed family)」の注記。

その他: No-go (3) に**明示的 substitution witness**(C(i) :=
Path A a (p i) は非定数 → 構造規則適用 → σ = [refl_a/p] で定数化 →
置換閉包+R+推移律で (†) 再導入)。Proposition J に **schema 注記**
(宇宙なしゆえ J_C はメタレベルのスキーマ、C について一様に証明;
full calculus では内部 J が相対層に住む)。「terms are never typed
in T_eq」→「not used as the type system of record(等式は言明に
現れるが型付けは現れない)」に修正。

結果: 37 頁、0 エラー、0 未定義参照、overfull ≤ 15pt。

---

## §17 第9次レビュー対応(2026-07-17): idempotence/変換健全性の再構成(v10)

第9次レビュー(60–75%; 3点: ①NbE idempotence の独立補題化 ②Π/PathP
conversion soundness の generic→arbitrary 明示 ③sorted worlds)は
全項目妥当。精査の結果、①②は素朴な項レベル証明だと NbE 正当性証明の
既知の難所(generic 点から任意引数への意味論的移行)に入るため、
**負荷点がすべて型値レベルにある**ことを利用した再構成で根本解決:

1. **Lemma (Conversion is read-back equality)**: conv 受理 ⟺
   readback 等式(両方向とも純構文的帰納; 意味論不使用)。系として
   ≡alg の同値関係性・合同性が構文的に(無害に)出る。
2. **Lemma (Type-level idempotence)**: 計算可能型値 F について
   quote(F) は構文的 core 型・well-typed で、eval(quote F) は F と
   **同一の関係を定める**。証明は型値反転を用いた構文型の構造帰納
   (Π の codomain は「構文的 S の関連環境での評価」なので
   generic→arbitrary が構文帰納で閉じる)。検査健全性定理(6.2)が
   使うのは型値の idempotence **のみ** — 「equal read-back と
   quote-eval idempotence は別定理」というレビューの指摘を認めた上で、
   必要な方を必要な場所(型)で証明。
3. **Lemma (Reindexing at PathP)**: generic 次元→任意区間値の移行は
   **world 射(次元代入)**+作用の環境点wise性で証明(項の置換補題
   への訴えは不要と明記 — 循環性疑義の遮断)。
4. **Lemma (Type conversion soundness)**: 型値の conv 受理 ⟹ 同一
   関係(readback 等式+型 idempotence の合成)。基本定理の
   conversion 節はこれで賄われる。
5. **Remark (What happened to term-level semantic soundness)**:
   任意の関数「値」に対する意味論的健全性は本論文のどの証明も
   使わない(基本定理=型述語の切替、admissibility=readback 等式の
   構文的構造、constancy=型 idempotence)ことを明示 — 見かけの
   generic→arbitrary ギャップの正確な解消(型では構文帰納で閉じ、
   項では不使用)。旧 Lemma (Conversion soundness)(項レベル、
   置換補題経由の圧縮議論)は削除。
6. **Sorted worlds**: Definition (Worlds) に「world は固定された
   sorted context shape に相対的に定義され、各レベルの項/区間の別は
   文脈が保持」の一文(レビュー③の推奨文言どおり)。
7. 引用の張り替え: 検査健全性(6.2)の step (3) を「型値
   idempotence(core では独立補題、一般では (B))」に、coretransp
   正分岐と基本定理 conversion 節を新補題に。

結果: v10、37 頁、0 エラー、0 未定義参照、overfull ≤ 15pt。
artifact URL(レビュー指摘の supplementary)は引き続きユーザー操作
待ち。

---

## §18 第10次レビュー対応(2026-07-17): 層の切替明示+Path 分離の紙上証明(v11)

第10次レビュー(「採択される可能性が高い」段階; 残 2 点)は妥当。実施:

1. **Remark (Where clause (iii) is proved, per layer)** を本文
   Lemma 5.4 直後に新設: 相対層では (iii)(項レベル健全性を含む)は
   (B) の一部として継承; 無条件 core では項レベル健全性を再証明せず
   **必要ともせず**、readback 特徴付け+型レベル健全性+完全性の
   弱いパッケージで置換(Remark F.21 参照)。「二つの証明経路は矛盾
   なく共存するが別経路であり、各定理は自層の経路を引用する」と明記
   — 査読者が矛盾と誤認する余地を遮断。
2. **Path 分離の紙上証明(core スキーマ版)**: conv=readback 等式の
   確立で可能になった強化。
   - **Lemma (hcomp/spine separation)**: 未決定 face・fill-定数
     中立チューブ・中立 base の合成 H について quote(H) ≠ quote(n)、
     core 型の構造帰納(ℕ: hcomp 項 vs spine 項の文法生成規則の相違;
     Π: η 展開後 hcompPi で S に帰着; Σ: 第1射影で T₁ に帰着;
     PathP: 端点チューブ追加系でも face 未決定のまま T₁ に帰着)。
   - **Proposition (Path separation in the core, on paper)**:
     任意の core 型 A のスキーマとして (†) の左辺 ≢alg p を無条件に
     紙上証明。「No-go の導出(T_eq)と拒否(アルゴリズム)の両方が
     無条件層の内部で紙上確立; 機械 probe は宇宙変数 A の full
     calculus の証人として追加的に残る」— 機械依存の縮減。
   - 本文 Lemma 4.5 を「Machine witness」→「Path separation」に
     改名し、core スキーマ版の紙上証明への前方参照を追加。
3. artifact URL: 引き続きユーザー操作待ち(レビューも再指摘)。

結果: v11、38 頁、0 エラー、0 未定義参照。

---

## §19 第11次レビュー対応(2026-07-17): 最終整理(v12)— 投稿可能水準の判定

第11次レビュー: 「**投稿してよい完成度**。新定理の追加より最終整理を。
採択可能性 70–80%、現実的経路は一度の revision を経て採択」。
指摘 3 点(すべて軽微・妥当)を実施:
1. §2.2 見出し「two-layer」→「**three-layer** main theorem」(本文と
   整合、継ぎ足し印象の除去)。
2. Abstract の機械検証範囲を精密化: 「All algorithmic-equality
   claims ... machine-checked」→「All concrete positive and negative
   **object-language conversion witnesses** ... machine-checked;
   **the metatheory itself is pen-and-paper**」(Theorem 級メタ定理も
   機械検証済みとの誤読を遮断、§11 の区分と完全整合)。
3. 版マーカー v12 に更新(正式投稿時に除去 — ソースに REMOVE
   BEFORE SUBMISSION コメント済み)。

v12、38 頁、0 エラー、0 未定義参照。**投稿前の残作業はリポジトリ公開
(ユーザー操作: URL・commit hash・可能なら Zenodo DOI)のみ**。
公開後: 論文 Artifact 節へ記入 → 版マーカー除去 → arXiv (CoRR) →
LMCS (episciences)。

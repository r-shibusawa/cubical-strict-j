# 混合層 I: De Morgan 凸性と strict 収縮可能性(証明ノート、2026-07-28)

## 0. 問い(realization 論文 outlook 第一項)

strict 層 ↪ full 層(Kan 操作込み)の比較の構造。とくに「充填非一意性
のもとで、strict な境界は weak な胞体をどこまで検出するか」。

## 1. 主発見: De Morgan 補間子(機械確定)

**補間子**: 境界制限が全面で一致する φ, φ′ ∈ DM(i⃗) に対し

  χ(k) := (φ ∧ ¬k) ∨ (k ∧ φ′) ∨ (φ ∧ φ′)

は (i) χ(0) = φ、χ(1) = φ′(吸収)、(ii) **各面上で k-定数**
(面上で φ = φ′ = ρ なら χ|面 = (ρ∧¬k)∨(k∧ρ)∨ρ = ρ、吸収)。

**定理(strict ホモトピー)**: 同一境界の任意の 2 つの strict 充填は
**strict なホモトピー rel boundary で結ばれる**(Kan 操作不要)。
機械証拠: `mixInterpD` — 非一意性定理の対 F1 = Q(i∧¬i)(j)、
F2 = Q((i∧¬i)∧(j∨¬j))(j) について
H := ⟨k⟩⟨i⟩⟨j⟩ Q(χ(k))(j) : Path SqLEM F1 F2 が型検査通過
(+`mixInterpCtrlD`: 補間は fiber 内を動く; 分離 guard: F1 ≢ F2 は
維持 — ホモトピーは非自明)。

**定理(strict 収縮可能性 / De Morgan 凸性)**: 固定境界の strict
充填の fiber は、strict ホモトピーの全ての階層で連結 — 2 つの
ホモトピー H, H′ も again 全面で境界一致(k-端で φ/φ′、他面で共通
境界)なので補間でき、帰納的に全高次で strict 胞体が存在する。
すなわち **boundary-restriction 写像の fiber は「strict に収縮可能」**
(補間子は fiber 上の canonical な凸構造 = 接続代数的 convex
combination)。

*証明メモ*: 一般 tuple は座標ごとに補間。型付けは境界条件のみ
使用(内部の退化は無関係)。高次段の境界一致は k-端が前段の補間で、
他面が共通境界であることから機械的。∎(骨格)

## 2. 帰結: 非一意性の正しい読み方

realization 論文の非一意性定理は「strict 層は病的」ではなく
「**fiber は複数点だが strict に可縮**」と読むのが正しい:
- Kan 世界の「充填は up to homotopy で一意」と完全に平行な現象が、
  strict 層の内部で(Kan 操作なしに)成立している。
- 比較関手 strict ↪ weak は、fiber の π₀ を潰す必要すらない —
  strict 層自身が自分の非一意性を解消する。

## 3. 次元 1 の比較図式(既存機械証拠の再配置)

- **単射**: strict ↪ full は自明に単射(同一アルゴリズムの ≡alg)。
- **非充満(同一境界に weak な新顔)**: 定数チューブ hcomp
  T = ⟨j⟩hcomp[j=0↦a,j=1↦b](p j) は境界 a→b で p と同型だが
  **T ≢ p**(jrefl 論文の path separation、機械済み)。ただし
  T ≡prop p(library の transReflR 系)— 「weak な充填は strict な
  充填と命題的に等しい」の実例。
- **新しい境界**: trans p q(a→c)は strict 層に対応物を持たない
  (strict 1-胞体の端点は単一辺の頂点対に限る — 型で見える)。
  full 層は境界のレベルで真に拡大する。

## 4. convexity 論文の構想: "De Morgan convexity and the strict–weak comparison"

1. 補間子と strict 収縮可能性定理(§1)— 主定理候補。
2. 比較関手の構造: 単射・境界拡大・同一境界での
   「weak ≡prop strict(充填可能な箱)/ weak ≢def strict」。
3. 実現定理(realization 論文)との合成: full 層の cellular presheaf 的記述への
   一歩(strict 骨格+hcomp 胞体の階層)。
4. 接続: cubical 型理論の「連結成分ごとの strict 代表元」— rewriting
   的正規形(polygraph の語の問題への布石、realization 論文 outlook 第二項)。

## 5. マイルストーン

| # | 内容 | 状態 |
|---|---|---|
| X1 | 補間ホモトピー(機械)+収縮可能性の骨格 | ✅ 本日 |
| X2 | 収縮可能性の紙上証明の完全化(高次段の境界一致の一般証明) | 次 |
| X3 | 同一境界 weak/strict の命題的一致の一般定理(充填可能箱) | — |
| X4 | convexity 論文執筆 | — |

## 6. X3 完了: (†) の命題的な影と、比較図式の完成(2026-07-28 追記)

### 定理((†) は命題的)

第 1 no-go の等式「定数チューブ hcomp ≡ base」(†) は定義的には
不可能(companion の jrefl 論文)だが、**canonical filler により命題的には
一様に成立**する:

  ⟨k⟩⟨j⟩ hcomp [j=0↦a, j=1↦b, k=0↦p j] (p j) : Path (Path A a b) p T

(k=0 で追加面が決定され composite が p j に崩壊; k=1 で偽面が
除去され T が残る)。機械: `mixFillD` ✓ + 定義的分離 T ≢ p の対照
guard ✓。一般の定数チューブ系・高次元でも同型の filler が働く
(証明は面決定と偽面除去の 2 計算のみ — 一様)。

**no-go の円環が閉じた**: (†) ∉ ≡def(jrefl 論文、原理的)かつ
(†) ∈ ≡prop(canonical filler、一様)— 「どうしても definitional に
できないものは、まさに hfill が propositional に供給するもの」。

### 定理(weak 層は命題的にも真に拡大する)

同一境界のすべての weak 胞体が strict 胞体と ≡prop になるわけでは
ない: S¹ インスタンスで winding は
trans loop loop ↦ +2、loop(φ) 型の strict 胞体 ↦ {0, ±1} を計算する
(ライブラリ既存の機械計算)。よって真の合成は新しい命題類を作る。

### 比較図式(完成形)

同一境界上の胞体の分類:
| 類 | 定義的 | 命題的 | 例 |
|---|---|---|---|
| strict 胞体 | fiber は非一意だが **strict homotopy で一意**(X2) | 同 | F1, F2 |
| 定数チューブ composite | strict と分離(no-go) | **filler で strict と同一視**(X3) | T vs p |
| 真の composite | strict と分離 | **新しい命題類**(winding) | loop∙loop |

これで convexity 論文("De Morgan convexity and the strict–weak comparison")の
主定理群が完備: (1) 補間定理+必然性(no-LEM の代償)、
(2) fiber の大域 strict 収縮可能性(共有部分複体ジグザグ)、
(3) (†) の命題化(no-go の双対)、(4) 命題的拡大(winding)。
残: X4 = 執筆。

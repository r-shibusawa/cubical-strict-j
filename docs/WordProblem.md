# 語の問題: up-to-homotopy 正規形と決定可能性の境界(証明ノート、2026-07-28)

## 0. 問い(realization/convexity 論文の outlook 合流点)

胞体的文脈(cubical polygraph)上の「語の問題」:
2 つの definable 胞体(生成子の再パラメータ化と Kan 合成で作られる語)
は自由 ∞-亜群で等しいか?本カーネルは
- **strict 語の問題**を常に決定する(実現定理+DM 代数の決定手続き)
- **propositional 語の問題**の同一視側をパス構成で、分離側を
  インスタンス化+計算不変量で扱える
という独自の計算的足場を持つ。詳細は
`docs/paperF/wordproblems.{tex,pdf}` に整理してある。

## 1. 定理 W1(次元 1・自由: 決定可能)

**主張**: 辺 computad(グラフ)上の辺-語 w₁, w₂ について、
propositional 等式 w₁ ≡prop w₂ ⟺ 簡約語(reduced word)が一致。
これはカーネル上で決定手続きになる:
- **同一視側**(簡約語が一致 ⟹ パス構成): 亜群法則のパスは
  すべて generic 文脈上でライブラリに機械構成済み —
  transAssoc(結合)・transReflL/R(単位)・transInvR/L(逆元)。
  簡約列の各ステップをこれらの合成(trans/cong)で辿る。
- **分離側**(簡約語が相違 ⟹ ≢prop): **円周・ウェッジへの
  インスタンス化**+計算する不変量。置換は ≡prop を保存するので、
  インスタンス先の不変量値の相違が generic での分離を与える:
  - 1 ループ: winding — 機械値 winding(loop)=+1、loop⁻¹=−1、
    refl=0、loop⬝loop=+2、loop⬝loop⁻¹=0(Examples/LibGroupoid)。
    ℤ の相異なる数字は ≢prop(decEqZ/encode)。
    ⟹ 例えば x·x ≢prop x(自由文脈で)。
  - 複数辺: S¹∨S¹ の被覆。Sanov 表現 F₂ ↪ SL₂(ℤ)(忠実)の被覆
    helixSL(§1.5)により、任意の語の行列値が語長に線形・
    1 文字 1ms 未満で計算できる。忠実性より
    値の一致 ⟺ F₂ での語の等式 — W1 の分離側はこれで完全。
- 正規形定理(簡約語が π₁(グラフの実現)を分類)自体は古典的;
  貢献は決定手続きの機械部品化。

## 1.5. Sanov 不変量 — 性能壁の突破は担体の再設計で

windF₂ の壁の正体は**担体に埋まる証明**だった: F₂ = 簡約語の Σ 型は
値が IsTrue 証明を持ち、被覆同値 consGEquiv は isSetF₂ 証明を埋め込む
— Kan ステップ毎にこの証明を歩く(生成元 1 つで 3 秒、合成は実行不能)。

**解決: カーネルではなく不変量を変える。** Sanov 表現
F₂ ↪ SL₂(ℤ)、L ↦ [[1,2],[0,1]]、R ↦ [[1,0],[2,1]](忠実)を使い、
担体を**証明を含まない平坦な ℤ⁴(行列)**にする(`LibSanov.lean`):
- 生成元の作用 = 行への右乗 = 初等的な整数演算の同値
  (逆写像は負の倍加の前置; 往復はキャンセル補題
  addCancel/addCancelN — addAssoc・addInvR/L・addZeroL の合成)。
- 被覆 helixSL: 8の字の各円周が ua(sanovL)/ua(sanovR) で巻く。
- windSL: 単位行列を転送 — ループの語の Sanov 行列を返す。

**実測**(`lake exe sanov`、期待行列との機械比較で全 PASS):

| 計算 | windF₂(旧) | windSL(新) |
|---|---|---|
| 生成元 1 つ | 3 秒 | **8 ms** |
| 逆元 | (未計測) | **8 ms** |
| 逐次転送(1 文字あたり) | 実行不能 | **< 1 ms** |
| L·R vs R·L | 実行不能 | [[5,2],[2,1]] vs [[1,2],[2,5]] ✓分離 |
| 交換子 [L,R] | 実行不能(wind8 では 0) | [[21,−8],[8,−3]] ≠ I |
| (L·R)³(6 文字) | 実行不能 | [[169,70],[70,29]]、< 1 ms |

- **逐次転送**(1 文字 = 1 Glue 転送、具体行列を順に送る)が実用手続き:
  語長に線形。合成ループの直接転送との一致は congTrans(cong を trans に
  分配)+ transpTrans(型パスの trans に沿う転送 = 転送の合成)—
  共に generic に機械証明済み — で命題的に保証される。
- **残るカーネル・フロンティア**(第二の壁、計測で特定):
  trans 合成ループに沿った直接転送は hcomp-in-U の入れ子 1 層なら
  約 1 分で完走(L⬝L⁻¹ ↦ I、ウェッジ共役の R ↦ [[1,0],[2,1]])だが、
  3 層(L⬝R)で超線形爆発(50 CPU 分で中断)。特定済みの対策 =
  カーネルの Kan ステップ間値共有。
- 教訓: **「証明を持たない担体+忠実表現」が up-to-homotopy
  不変量を計算可能にする** — 正規形(簡約語)を型に埋め込むのでは
  なく、自由対象を古典的行列群に忠実表現し、型理論側は被覆・転送
  だけを担う。

## 2. 定理 W2(次元 2 から: 決定不能 — strict/weak 境界=決定可能性境界)

**主張**: 2-computad(関係子つき)上の propositional 語の問題は
決定不能。∵ 任意の有限表示群 ⟨X ∣ R⟩ は「頂点 1・辺 X・関係子ごとの
2-胞体」の 2-computad にコードでき、辺-語の ≡prop は表示された群の
語の等式に一致する(Novikov–Boone により決定不能)。

- **⟸ 方向(群の等式 ⟹ パス構成)の仕組みは機械実演済み**:
  `LibWord.lean` — ℤ/2 表示 ⟨x ∣ x²⟩ の generic 文脈
  (A, a, x : Path A a a, R : x·x ≡ refl)上で、群論的帰結
  **x⁴ = 1 を明示的パスとして構成**(`wordX4D`:
  cong(·(x·x)) R ⬝ transReflL ⬝ R — 関係子 2 回+亜群法則、
  型検査通過)。一般の関係子適用列も同型(cong で文脈に埋め、
  trans で連結)— 帰納的なパス・コンパイラの仕様がここにある。
- **⟹ 方向(パス存在 ⟹ 群の等式)**: 表示複体の実現への解釈で
  π₁ に落とす。**内部実現は機械化済み**(`LibPresent.lean`、
  全 guard 通過): ℤ/2 表示 ⟨x∣x²⟩ の表示複体 =
  **RP² := cofib(deg2)** を内部構成し、
  - 貼り付け写像 deg2 : S¹→S¹ は生成子上**定義的**
    (cong deg2 loop ≐ loop⬝loop、deg2Loop)、
  - **関係子 2-胞体の実現** rp2Rel : x·x ≡ refl — ppush 円柱を
    錐点 cap の hcomp 正方形 1 個で畳む(rp2RelSq)+ congTrans、
  - **generic 導出の代入転送** wordX4RP2 : x⁴ ≡ refl in RP² —
    LibWord の表示文脈を (RP², base, x, rp2Rel) でインスタンス化
    するだけ(コンパイラ機構の内部 HIT への着地)、
  - 制御: 関係子は**判断的等式ではない**(定数 plam は型検査を
    落ちる)— 同一視は正確に propositional 層に住む(no-go 境界と
    整合)。
  さらに(`LibCover.lean`、全 guard 通過): Bool 二重被覆 covRP2 —
  円周部は loop ↦ ua(notEquiv)(covS1)、関係子 2-胞体上の延長は
  正確に整合性 **uaNotNot : ua(not)⬝ua(not) ≡ refl**
  (uaInj+equivEq+funExt+notNot の uaCompMul パターン)を要求し、
  被覆の ppush セルは congTrans@01 で分解 → J@1 で自明正方形を
  uaNotNot に沿って輸送して得る。**計算**: windRP2(refl) ⟶ true、
  windRP2(x) ⟶ false。**rp2LoopNontriv : (x ≡ refl) → ⊥** —
  rp2Rel(x²≡refl)と併せて**表示 ⟨x∣x²⟩ の忠実な実現**
  (x ≠ 1 かつ x² = 1)が機械実証。系: rp2NotSet(RP² は集合でない)。
- **対比(本ノートの要点)**: 同じ 2-computad 上でも
  **strict 語の問題は決定可能なまま**(実現定理は関係子 2-胞体を
  単に「もう一つの生成 2-胞体」として扱い、DM 決定手続きが決める)。
  すなわち:

  | 層 \\ 次元 | 1(自由) | ≥2(関係子つき) |
  |---|---|---|
  | strict | 決定可能(DM+実現) | **決定可能**(同) |
  | propositional | 決定可能(W1) | **決定不能**(W2) |

  **strict/weak 境界は、そのまま決定可能/不能の境界である。**
  (weak 化の「価値」と「代償」の同時定量化。)

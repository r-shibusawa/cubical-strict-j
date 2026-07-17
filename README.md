# FormalizedMathematics

Lean 4 (v4.31.0) による自己完結の形式化ライブラリ。外部依存なし(mathlib 不使用)。
`lake build` で全証明がカーネル検証される。

## 収録定理

### 1. HoTT: Voevodsky の定理 — univalence ⇒ 関数外延性 (`Hott/`)

**`Hott.funextOfUnivalence`** — HoTT book 定理 4.9.5 の完全な形式化。**公理ゼロ**
(`#print axioms` で確認可能)。

Lean 4 の組み込み等式 `Eq` は `Prop` に属し proof irrelevance を持つため、
**univalence 公理と非整合**である。そこで:

- `Type` 値の独自パス型 `Path` を定義し、J(パス帰納法)のみで推論する
  (`Hott/Basic.lean`)。
- univalence はグローバルな `axiom` としてではなく、仮定を束ねた構造体
  `Univalence` として定式化(`Hott/Univalence.lean`)。これにより
  「univalence ならば funext」という**含意そのもの**が公理なしの定理になる。
  (グローバル公理にすると、フラグメント外の `Eq` 推論から `Path` の UIP が
  導けて矛盾する。構造体方式ならこの問題を回避できる。)

証明の構成(`Hott/Funext.lean`):
型のパスに沿った後合成のファイバーが特異点空間に収縮すること(J で証明)を
univalence で任意の等価に輸送 → 可縮型の積の可縮性(weak funext)を
定義的リトラクトで導出 → 全空間 `Σ g, f ~ g` の可縮性から funext。
Lean の定義的 η(関数・構造体)のおかげでリトラクト条件がすべて `refl` で閉じる。

### 2. 数理論理学: 抽象不完全性定理 (`Logic/Incompleteness.lean`)

Hilbert–Bernays–Löb の可導性条件(D1–D3)+ 含意断片のヒルベルト流公理系を
構造体 `ProvabilityTheory` に公理化し、対角化(`Diagonal`)を仮定して:

- **`loeb`** — レープの定理: `T ⊢ □θ → θ` ならば `T ⊢ θ`
- **`goedel1`** — 第一不完全性(不可証半分): 無矛盾なら Gödel 文は証明不能
- **`goedel2`** — 第二不完全性: 無矛盾な `T` は自身の無矛盾性 `¬□⊥` を証明できない

PA や ZFC など算術を解釈する任意の r.e. 理論がこの構造体のインスタンスになる
(`box` = 可証性述語、`Diagonal` = 対角補題)。すべて公理ゼロ。

### 3. 圏論: Lawvere の不動点定理 (`CategoryTheory/Lawvere.lean`)

デカルト閉圏をゼロから定義し(`CCC`、curry は β 則のみ要求)、

- **`lawvere_fixed_point`** — `φ : A ⟶ Bᴬ` がステージ `Γ` で点全射なら、
  任意の `t : B ⟶ B` は不動点を持つ。一般化点で述べてあるため終対象すら不要。
- **`no_point_surjective`** — 対偶形(対角論法の統一形)。
- **`cantor`** — 型の圏 `typesCCC` に具体化して得るカントールの定理。

Cantor・Russell・Gödel・Tarski・Turing の対角論法はすべてこの一つの圏論的
事実の実例である(Lawvere 1969; Yanofsky 2003)。

### 4. Cubical カーネル(全フェーズ完了) (`Cubical/`) — 独自定理証明系

ライブラリは鎖状 import の8モジュール(`LibCore` → … → `LibQuot`、
`Library.lean` は索引)に分割されており、増分ビルドは数秒。

**univalence が公理でなく計算し、`π₁(S¹) ≅ ℤ` が(巻き数の計算だけでなく)
両方向の往復を量化した同型「定理」として対象言語内で証明された**
ミニ証明支援系:

```
ua := λ A B e. ⟨i⟩ Glue [(i=0) ↦ (A, e), (i=1) ↦ (B, idEquiv B)] B
λ e. transport (ua e) 0   ⟶   λ e. e.fst 0     (univalence の計算規則)

helix   := S¹-elim U ℤ (ua sucEquiv)            (円周の普遍被覆)
winding p := transp (λi. helix (p @ i)) 0
winding loop            ⟶  +1      winding loop⁻¹         ⟶  −1
winding (loop ⬝ loop)   ⟶  +2      winding (loop ⬝ loop⁻¹) ⟶   0

intLoop  : ℤ → (base ≡ base)                        (decode at base)
winding (p ⬝ loop) ≡ sucZ (winding p)               (refl で証明可能 — 定義的!)
encodeDecode : Π (z : ℤ). winding (intLoop z) ≡ z   (ℤ-帰納法)
decode   : Π (x : S¹). helix x → (base ≡ x)          (依存除去 + unglue + 相殺パス補正)
decodeEncode : Π x p. decode x (encode x p) ≡ p      (J)
pi1S1IsoInt : Iso (base ≡ base) ℤ                    ★ 完全な同型定理 ★

loopNeqRefl : (loop ≡ refl) → ⊥        (系: 初の否定的定理)
s1NotSet    : isSet S¹ → ⊥             (円周は集合でない)

pi1S1Equiv     : Equiv (Ω S¹) ℤ         (setIsoToEquiv — 余域 ℤ は集合)
loopSpaceIsInt : Ω S¹ ≡ ℤ               ★ univalence による型の同一視 ★
isSetLoopS1    : isSet (Ω S¹)           (ℤ のリトラクトとして)
transInvR/L    : p ⬝ p⁻¹ ≡ refl ≡ p⁻¹ ⬝ p   (亜群構造の完成)

hedberg : (Π x y. Dec (x ≡ y)) → isSet A   (Hedberg の定理)
transport (ua not) true ⟶ false            ★ 最古典の univalence 計算 ★

decEqNat / decEqZ : ℕ・ℤ の可判定等価      (コード経由; Hedberg との合成で
                                            isSet ℕ/ℤ の独立な別証明も検証)
isPropSigma : isProp の Σ-閉包

S⁰ ≃ Bool, S⁰ ≡ Bool                        (懸垂 HIT; transport で north ⟶ true)
S² := Σ S¹                                   ★ 2-球面の定義 ★
suspMap / suspMapId                          (懸垂の関手性)
σ : S¹ → Ω S²                                (π₂(S²) の生成元に対応する写像)

T² ≅ S¹ × S¹                                 ★ トーラス HIT(2-セル surf)★
isoToEquiv : Iso A B → Equiv A B             ★ 一般 gradLemma(h-level 仮定なし)★
T² ≃ S¹ × S¹,  T² ≡ S¹ × S¹                  (gradLemma + ua で宇宙の等式に)

∥A∥(命題切り詰め HIT): isProp ∥A∥・関手性・∥∥A∥∥ ≃ ∥A∥(冪等)
s1Connected : Π (x : S¹). ∥ base ≡ x ∥       ★ 円周は連結(単なる存在の定理)★
windingSurj : Π z. ∥ Σ p. winding p ≡ z ∥    (winding は全射 — ∃ 言明)

pushout HIT: Σ A ≃ pushout(⊤ ← A → ⊤)       ★ 懸垂はプッシュアウト(全セル定義的)★
wedge A∨B / cofiber / S¹∨S¹(8の字)          (標準余極限構成が1行に)

集合商 A/R(HIT): isSetQuot・依存 elimProp(qelim から導出)
truncAsQuot : ∥A∥ ≃ A/全関係                 ★ 切り詰めは商の特殊例 ★
isPropPathPSet : 集合族上の従属パスは一意     (J 一発)

intAsQuot : (ℕ×ℕ)/∼ ≃ ℤ                      ★ 整数の差表現(商の本格実用)★
  ℕ 算術(加法・可換律・減法)を natrec で整備し、商からの写像は qelim、
  往復は qelimProp + predZ/predQ の絡み合い補題で。[(3,1)] ⟶ +2 が計算

リスト型(カーネル)+ 語の基盤(F₂ への第一歩):
  decEqProd / decEqList / decEqWord            (head/tail 射影 + nil/cons コードで反駁)
  isSetWord                                     ★ Hedberg 経由 — リストのコード理論を丸ごと省略 ★
  decEqWord [L,R] [L,R] ⟶ inl,  [L,R] [R,L] ⟶ inr   (計算で判定)

K(G,1)(Eilenberg–MacLane 空間、カーネル HIT `em1`):
  emcomp : PathP (λj. base ≡ emloop h j) (emloop g) (emloop (g·h))   (乗法注釈携行の2-セル)
  emsquash(1-切り詰め3-セル)+ 除去子は isGroupoid 証人を要求
  emloopComp : emloop (g·h) ≡ emloop g ⬝ emloop h    ★ compPath 一意性の3次元立方体 ★
  emloopOne : emloop 1 ≡ refl                  (群法則 + パス亜群の相殺連鎖)
  zGroup : (ℤ, +, 0, −) の群インスタンス        (逆元律は addSucL/addPredL で帰納)
  (ホモトピー仮説レベル1「群 ≃ 点付き連結1型」への第一歩)

コヒーレンス第1章(Mac Lane、亜群形):
  pentagon : 1-型で五角形の2経路が一致    ★ コヒーレンス公理化プログラムの開始 ★
  triangle : 結合子と単位子の交換律(1-型)  + ℤ-インスタンス
  (無切り詰め版は「trans refl refl が抽象型では hcomp のまま」という
   本質的困難 = コヒーレンスセルの手動 bootstrapping が次段階)

h-level 塔と univalence η:
  isPropIsContr(4面管1発)・isPropIsEquiv・isSetPi・isSetEquiv
  uaIdEquiv : ua (idEquiv) ≡ refl              ★ Glue 立方体1発 ★
  uaEta : ua (pathToEquiv p) ≡ p               (J@1 — univalence の η 規則)
  isSetPathU : 集合間の宇宙パスは集合           (リトラクト経由)

F₂ 第2ラウンド(相殺付き前置と被覆):
  F₂ := Σ (w : Word). IsTrue (reduced w)        (isSetF2 = isSetSigmaProp)
  consG g : F₂ ≃ F₂                             ★ 相殺付き前置は同値(生成元 generic)★
    consG L⁻¹ (consG L []) ⟶ []                 (相殺が計算)
    往復証明 consGRound: inspect イディオム + 接続 e@(i∧j) による分岐書き換え
  helixF₂ : S¹∨S¹ → U,  windF₂ : π₁(S¹∨S¹) → F₂  (windF₂ loopL ⟶ [L] が3秒で計算;
    合成ループは埋め込み証明サイズの性能壁 — カーネル値共有が今後の対策)

helix8 : S¹∨S¹ → U                           ★ 8の字の階数2被覆 ★
wind8  : π₁(S¹∨S¹) → ℤ × ℤ                   (アーベル化された巻き数)
  wind8 loopL ⟶ (+1, 0)     wind8 (push⬝loopR⬝push⁻¹) ⟶ (0, +1)   — 1秒未満で計算
  wind8 (L⬝R) = wind8 (R⬝L) = (+1,+1)         — 順序が見えない = アーベル化のみ検出
                                                (F₂ の非可換性はこの不変量の先にある)
```

トーラスの往復は cubical の看板通り**全セルが定義的**
(`surf i j ↔ (loop i, loop j)`)— Book HoTT で難物のこの定理が
refl の束で閉じる様子を自前カーネルで再現。

一般 gradLemma は `lemIso` の5つの Kan 充填(hfill 3つ + 補正平方2つ)を
面制約構文に翻訳して構成:`hfill` は `k∧j` 切詰め管の `hcomp`、複合面
`(k∧j)=1` は連言、`(k∧j)=0` は本体同一の2枝分割。これに伴い conv の
システム比較を正規化(恒偽枝の除去・充足リテラルの除去)するカーネル改良を実施。

カーネルの HIT は S¹ に加えて**懸垂 `Σ A`**(`north`/`south`/`merid a r`、
除去子 `susprec`)をサポート。懸垂は**径数付き HIT** — `transp` は径数直線に
構造的に分配され(和型と同じ規律)、`merid` の端点崩壊は `force` で遅延
(S¹ の設計原則を踏襲)、`susprec` は hcomp セルと可換。

カーネルには**和型**(`A ⊎ B`、`transp` は成分直線へ構造的に分配)が追加され、
`Bool := ⊤ ⊎ ⊤`、`Dec A := A ⊎ ¬A`、ブールの可判定等価、
**Hedberg の定理**(鍵補題の refl ケースは逆元律 `transInvL`、collapse の
定数性は「⊥ からは何でも」の従属場合分け)、`isSet Bool`、
`notEquiv`(setIsoToEquiv)までが対象言語内で繋がる。

いずれもビルド時 `#guard` で機械検証される定義的等式(constancy 検査の
最適化後、全検証は数秒で完走する)。book HoTT では
univalence は計算内容を持たない公理であり、巻き数は「証明できる」だけで
計算はできない。

CCHM 流 cubical type theory の型検査器を Lean 内に実装したもの。
**Lean 本体では公理が必要な funext が、この体系では「計算するプログラム」になる**。

| ファイル | 内容 |
|---|---|
| `Interval.lean` | De Morgan 区間代数。自由 De Morgan 代数の正規形(反鎖 DNF)による判定的等価性 |
| `Syntax.lean` | コア項(de Bruijn index)+ 名前付き表層構文と解決器 |
| `Semantics.lean` | NbE 評価器・引用・変換判定。`transp`(Kan 輸送)の Π/Σ/定数族への構造規則 |
| `TypeCheck.lean` | 双方向型検査器。`plam` の**境界条件**検査、`papp` の端点注釈の検証 |
| `Library.lean` | **カーネル上に書かれた最初の HoTT/圏論ライブラリ**(51定義、下記) |
| `Examples.lean` | ビルド時 `#guard` テスト |

実装済みの Kan 構造(CCHM の fill を De Morgan 接続で構成):

- `transp` 定数族 = 恒等(正規化+出現検査による constancy 判定)
- Π 族: `transp A f = λ x₁. transp (λi. C i (w x₁ i)) (f (w x₁ 0))`、
  逆向き fill `w x₁ i = transp (λj. B (i ∨ ¬j)) x₁`
- Σ 族: 順向き fill による成分ごとの輸送
- **`hcomp`(等質合成、2a)**: 面制約(区間変数への 0/1 制約の連言)付き部分要素系。
  真面の選択、Π(引数ごと)、Σ(filler `hfill` + 異質合成 `comp = hcomp∘transp`)、
  PathP(端点を系に追加)、ℕ(`zero`/`suc` と合成の可換)の各構造規則
- **`PathP` 族上の `transp`(2a)**:
  `transp (λi. PathP (B i) (a i) (b i)) p = ⟨j⟩ comp (λi. B i j) [(j=0)↦a, (j=1)↦b] (p@j)`
- **`Glue` 型(2b)**: 形成規則(各枝の `e : Equiv T A` は可縮ファイバー定式化
  `Σ (f : T→A). Π (y : A). isContr (Σ x. Path A y (f x))` をカーネルが対象言語の
  型として合成し面制約下で検査)、`glue`/`unglue`、真面での遅延簡約
  `Glue [⊤ ↦ (T,e)] A ≡ T`(`force`)、**Glue 直線に沿った `transp`**(CCHM 6.2、
  底空間で輸送し、終点の各面で等価性の可縮ファイバー中心により補正、
  `hcomp` で底点を接着)——これが univalence の計算の心臓部
- **高次帰納型 S¹ と ℤ(2d)**: `loop : base ~ base` はパス構成子
  (`sloop r`、端点簡約は `force` で遅延——先行簡約すると Kan 演算が読むべき
  Glue 構造が消える)。除去子 `S¹-elim` は `base`/`loop` 上で計算し、
  `hcomp` セル上では合成と可換(`elim (hcomp [φ↦u] u₀) =
  comp (λi. P (hfill u u₀ i)) [φ ↦ elim∘u] (elim u₀)`)。
  ℤ は `isuc`/`ipred` が(中立項上でも)**定義的に相殺**する表現で、
  これにより `sucEquiv : ℤ ≃ ℤ` の可縮ファイバー証明が `idEquiv` と同じ
  接続トリックで書ける
- **HCompU(2b')**: 宇宙での合成は Glue に翻訳される:
  `hcomp U [φ ↦ E] A = Glue [φ ↦ (E 1, lineEquiv (E 0) (E 1) E)] A`。
  `lineEquiv`(「直線に沿った逆向き輸送は等価」)は**閉じた対象言語
  プログラム**としてカーネルが評価する(検査器自身による型検査も
  `#guard` 済み)。証明の核は関数の直線 `fᵢ := transp (λj. P@¬(i∧j))` に
  沿った `idIsEquiv` の輸送で、`f₀ ≐ id` は constancy 規則により定義的
- **一般 δ ≠ ⊥ の Glue 輸送(2b')**: 面の `∀i` 演算 `cofForall` を実装
  (DNF 極性が単一なら端点代入の連言で**正確**、混合極性は保守的に ⊥ =
  健全な未計算)。δ が生きる枝では枝型直線での輸送 `t₁' := transp Tₖ u₀`、
  底輸送への δ-管 `λi. wₖ i (fillₖ i)`(これで δ 上 `a₁' ≐ w₁ t₁'` が
  定義的に成立)、終点では可縮性の収縮パスに沿った**ファイバー Σ 型上の
  `hcomp`** で中心と δ-解を接着する(CCHM §6.2 の完全な形)
- 型検査器は `hcomp` の**辺境条件**を面制約下で検査:各枝の底面との接着
  (`u_k[j:=0] ≡ u₀ on φ_k`)と、重なる枝同士の整合性(`u_k ≡ u_l on φ_k∧φ_l`)を、
  面を環境への代入として適用した上での変換判定で確認する

機械検証されるデモ(`Examples.lean`、すべて `#guard`):

- `funext := λ A B f g h. ⟨i⟩ λ x. h x @ i` が型検査を通り、
  `funext ℕ ℕ succ succ (λx. refl) @ 0` が `λ x. succ x` に**正規化**される
- `symm := λ A a b p. ⟨i⟩ p @ ¬i`(区間の対合だけで対称性が出る)
- `transport : Π A B. Path U A B → A → B`(宇宙内のパスに沿った輸送が型検査を通る)
- **パス合成 `trans := λ .. p q. ⟨i⟩ hcomp A [(i=0)↦a, (i=1)↦q@j] (p@i)`(2a)**が
  型検査を通り、ℕ 上で `trans refl refl ⟶ refl` が**定義的に計算**される
- Σ 型上の `hcomp`、`PathP` 族上の `transp` の計算
- **univalence(2b)**: `idEquiv`(特異点空間の可縮性を De Morgan 接続
  `p @ (i∧j)` で証明する対象言語プログラム)が型検査を通過し、`ua` が
  `Path U A B` を構成、端点が `A`/`B` に計算され、
  `transport (ua (idEquiv ℕ)) 0 ⟶ 0` と
  **`λ e. transport (ua e) 0 ⟶ λ e. e.fst 0`(抽象等価でも計算)**を機械検証
- **π₁(S¹) の巻き数(2d + 2b')**: `winding loop ⟶ isuc izero`、
  `winding loop⁻¹ ⟶ ipred izero`、`winding refl ⟶ izero`、そして合成:
  **`winding (loop ⬝ loop) ⟶ isuc (isuc izero)`**、
  **`winding (loop ⬝ loop⁻¹) ⟶ izero`**(逆元の相殺)。
  汎用の `trans` プログラムで合成しても同じ値に計算される
- **encode–decode(部分)**: ℤ の除去子 `intrec`(値が `isuc`/`ipred`
  相殺済み正規形に保たれるため well-defined)を追加し、base での decode
  `intLoop : ℤ → Path S¹ base base` を ℤ-再帰で構成。往復
  `winding (intLoop n) ⟶ n` を具体的な整数(+2, −1, 0)で機械検証
- **宇宙階層(2c)**: `U n : U (n+1)`、型形成子のレベル推論(`inferSort`、
  Π/Σ は max、`Path (U n)` は級 n など)、検査判断での宇宙包摂
  (`U m ≤ U n`)。**type-in-type を排除**(`U₀ : U₀` の拒否を負例で検証)し、
  Girard パラドックスの扉を閉じた
- 健全性の負例: 境界条件違反・端点注釈の偽装・`hcomp` の底面接着違反・
  重なる枝の不整合・変数でない面制約・**等価性の証明を欠いた `Glue`**は、
  すべて拒否される

**現状の制限(正直な申告)**:

- **評価器の停止性は未証明**(`partial def`)。これは怠慢ではなく問題の性質による:
  cubical type theory の正規化定理は Sterling–Angiuli(2021)らによる研究最前線の
  主題であり、本実装の規則集合に対する停止性証明はそれ自体が研究課題である。
  偽の証明を置くことはしない。カーネルが `partial` である限り、Lean 側から
  カーネル関数の性質を証明することもできない(2c の残り半分 = カーネルの
  全域化とメタ理論の形式化は、このプロジェクトの長期目標)
- **[解決済み] strict ℤ の代入不安定性**: strict 相殺 + `intrec` は定義的
  等価性の代入安定性を壊す(非合流)ことを発見し、ℤ を `pos n | negsuc n`
  + 場合分け除去子 `intcase` に再設計して解消した。`sucEquiv` は
  **`isSet ℤ`**(⊤/⊥ 型を追加し、ℕ・ℤ の encode–decode を対象言語で証明)
  による平方充填 `setFill` で再構成。これにより完全な `decode` が可能になった
- **検査器の既知の不完全性(A4 で発見)**: 面制限は環境のみに適用され、
  文脈 Γ に格納済みの型は制限されない。そのため面依存の型を持つ変数を
  `hcomp` の管が参照すると検査に失敗する。回避パターン: **hcomp を Π 型
  レベルに持ち上げ、管を λ にする**(束縛が制限適用後に導入される)。
  `decode` の loop セルはこのパターンで構成されている
- **[解決済み] 性能**: constancy 検査を quote ベースから早期打ち切り付き
  出現検査 `usesLvl` に置換し、旧爆発ケース(J の大型モチーフ適用)が
  54分 → 0.2秒、Examples 全体が 635秒 → 1.4秒になった。`congTrans@01`・
  `transpTrans` はライブラリに復帰済み
- 面制約の表層構文は「区間変数 = 0/1」の連言に制限、系の比較は順序依存
  (健全だが不完全)、`∀i` 演算は混合極性の面で保守的に ⊥(健全な未計算)、
  `Glue` 型上の `hcomp` はスタック、宇宙包摂は判断レベルのみ(深い部分型なし)、
  δ-部分の値は面の外では型的に無意味な値として計算される(面上でのみ参照
  される — cubicaltt 系の部分要素意味論を全域値で近似する設計上の割り切り)

### 5. カーネル上の HoTT/圏論ライブラリ (`Cubical/Library.lean`)

カーネルの**中で**(対象言語プログラムとして)書かれ、ビルド時に全定義が
型検査される最初のライブラリ。51定義:

- **パス代数**: `refl` / `symm`(区間の対合)/ `trans`(`hcomp`)/ `cong` /
  `happly` / **`funExt`(公理でなくプログラム)**
- **輸送と経路帰納法**: `transport` / `subst` / **`J`** —
  book HoTT の原始規則が、接続平方 `(i,j) ↦ p @ (i∧j)` に沿った輸送として
  **導出**される(`J … refl ⟶ d` の計算も `#guard` 済み)
- **2次元パス代数**: `symmInvol`(`symm∘symm ≡ id` は De Morgan 対合の
  strict 性により `refl`!)、**単位律 `transReflL`/`transReflR`**
  (`hcomp` による平方充填の証明)、**結合律 `transAssoc`**
  (J による経路帰納法 — refl ケースを単位律と `cong` の合成で閉じる)
- **h-level**: `isContr`/`isProp`/`isSet`、特異点空間の可縮性
  `contrSingl`、`contrToProp`
- **等価と univalence**: `idEquiv` / **`ua`** / `pathToEquiv`(逆方向、
  `Equiv` 族の輸送)/ `sucEquiv`。`transport (ua e) 0 ⟶ e.fst 0` を検証
- **整数**: `add`(`intrec`)と**帰納法による法則の証明** —
  `addZeroL`・`addAssoc`・**`addComm`**(補題 `addSucL`/`addPredL` の連鎖)。
  「法則 = Path」を `intrec` で構成する対象言語内の本物の帰納的証明
  (計算検証: `2+3 ⟶ 5`、`2+(−3) ⟶ −1`)
- **圏論**: `Monoid` 型(法則は Path)と **`(ℤ, +, 0)` インスタンス**、
  `PreCat`(レベル付き:対象は `U (n+1)`、射は `U n` — **宇宙階層の本領**)と
  **型の圏**(法則は定義的 η で `refl`)、**基本亜群 `pathPrecat`**
  (対象 = 点、射 = パス、法則 = 上の平方充填証明。`Ob := A : U₀ ≤ U₁` は
  宇宙包摂が効く)、`Functor` 型と**任意の圏上の恒等関手**、
  **自然変換**と**恒等自然変換**(自然性 `idr ⬝ idl⁻¹` を圏の法則
  フィールドから抽象的に証明)
- **関手圏**: hom-set 圏 `setCatTy`、垂直合成 `compNat`(自然性は結合律2回
  + `cong` 2回の5段チェーン)、**`natTransEq`**(成分ごとの等価 ⇒ 自然変換の
  等価 — 自然性フィールドは hom-set の下で命題なので `isPropPi` + `toPathP`
  で従属パスが乗る)、そして **`functorCat : PreCat₀ → SetCat → PreCat₁`**
  (関手は U₁ に住むので関手圏はレベル1 — 宇宙階層の必然的な使用)。
  具体例: **`Bℤ`**(ℤ の delooping — 1対象圏、合成 = 加法、法則 = 移植済み
  加法法則、hom-set = `isSetℤ`)とその自己関手圏 `[Bℤ, Bℤ] : PreCat₁`。
  さらに**関手合成 `compFunctor`**(法則は `cong`/`trans` 連鎖)、
  **左右の whiskering**、そして**交換法則 `interchange`**(水平合成の
  2通りの定義の一致 — 成分ごとには β の自然性そのもので、残りは
  `natTransEq` が吸収)— **Cat の2-圏構造が検証済み**
- **円周**: `helix`(普遍被覆)/ `winding` のライブラリ化
  (`winding loop ⟶ +1` の計算検証込み)
- **h-level 理論**: `isPropPi`・`isContrPi`(Π 閉包)、
  **`isPropToIsSet`(命題は集合 — 古典的な4面管の平方を1つの `hcomp` で)**、
  **リトラクト補題 `isPropRetract`/`isSetRetract`**(同じ4面管パターン:
  B の平方を g で押して4面を retraction で補正)
- **`toPathP`**: 輸送の等式を従属パスに直す標準ツール。通常は φ 付き
  `transp` が要るが、区間スマート構成子が `A@(0∧j)` を定数族に潰すため
  この体系では `(i=0)` 面の整合が**定義的に**成立する
- **レベル1パス代数**: `refl/symm/trans/transReflR` の U₁ 版、
  混合レベル `cong`(U₀→U₁ / U₁→U₀)、`J`(U₀ 型・U₁ モチーフ / U₁ 型)
- **decode 平方**: `decodeSquareSuc : Π n. PathP (λi. base ≡ loop i)
  (intLoop n) (intLoop (suc n))`(ライブラリ初の従属パス定理)
- **量化された encode–decode(ℤ 側)**: `windingCompLoop±`
  (`winding (p ⬝ loop^±1) ≡ isuc/ipred (winding p)` が **`refl` で証明できる**
  — 除去子の可換規則 + HCompU + Glue 輸送が中立な `p` でも判断的に計算
  し切るため)、そして
  **`encodeDecode : Π (n : ℤ). winding (intLoop n) ≡ n`** — 帰納段が
  `cong isuc/ipred ih` だけの ℤ-帰納法。`π₁(S¹) ≅ ℤ` の半分が、検査済み
  実例の族ではなく**全整数に量化された定理**になった

## 検証方法

```sh
lake build          # 全証明をカーネル検証
```

```lean
#print axioms Hott.funextOfUnivalence          -- 'does not depend on any axioms'
#print axioms Logic.ProvabilityTheory.goedel2  -- 'does not depend on any axioms'
#print axioms CategoryTheory.CCC.lawvere_fixed_point  -- 同上
```

## 位置づけについての正直な注記

- ここにあるのは**既知の重要定理の検証済み形式化**であり、未解決問題の解決では
  ない。未解決問題(圏論・数理論理学のもの含む)を機械的に解く方法は存在せず、
  形式化はその探索の**基盤**である。
- HoTT フラグメントの健全性はメタ定理に依存する: `Path` に対する UIP は
  Lean 内で(`Eq` 経由で)証明可能なため、`Univalence` 構造体は Lean 内では
  *実装不能*な仮定である。だからこそ `axiom` ではなく含意として述べている。
  simplicial set モデル(Kapulkin–Lumsdaine–Voevodsky)により仮定側の整合性は
  保証される。
- 真の HoTT ネイティブ環境(univalence が定理として成立し計算する体系)には
  cubical type theory のカーネルが必要。ロードマップ参照。

## ロードマップ(「Lean を超える」ための現実的な段階)

1. **HoTT 層の拡張** — h-level の理論、`Equiv` の合成、高次帰納型のエミュレーション
   (`Quot` ベース)、`hott` 属性による大消去チェッカ(GroundZero 方式)。
2. **独自カーネルの試作** — ~~cubical type theory の型検査器を Lean 内に実装~~
   → **v0 完了**(`Cubical/`、上記)。残る段階:
   - ~~**2a. `hcomp`**(等質合成)— 部分要素と面制約の実装、`PathP` 族上の
     `transp`、パス合成 `trans` の導出~~ → **完了**(上記)
   - ~~**2b. `Glue` 型** — univalence が計算する~~ → **完了**
   - ~~**2d. 高次帰納型** — S¹ と π₁(S¹) ≅ ℤ の巻き数計算~~ → **完了**
   - ~~**2b'. HCompU + 一般 δ の Glue 輸送** — 合成ループの巻き数~~ → **完了**
   - ~~**2c(前半). 宇宙階層** — type-in-type の排除~~ → **完了**
   - ~~**encode–decode(前半)** — `intrec`・`intLoop`・往復の計算的検証~~ →
     **完了**(残件: 量化された同型定理には decodeSquare/`toPathP` の
     対象言語内開発、`Glue` 上の `hcomp`、面制約の表層一般化(式面・∨))
   - ~~**カーネル上のライブラリ** — HoTT/圏論の32定義~~ → **完了**
     (`Library.lean`。2-パス代数・基本亜群・`addComm`・自然変換・S¹ 統合
     まで。次: `isoToEquiv`(gradLemma)、関手圏(Hom の集合性が要る)、
     h-level の閉包性質、`π₁(S¹) ≅ ℤ` の量化定理)
   - **2c(後半). 停止性** — カーネルの全域化と正規化のメタ理論。
     cubical type theory の正規化(Sterling–Angiuli 2021 系の手法)を
     Lean で形式化する長期研究課題であり、偽装しない
   - **2c. 宇宙階層**(type-in-type の除去)と評価器の停止性証明
     (Lean で kernel のメタ理論を形式化する——ホスト言語が Lean である利点)
   - **2d. 高次帰納型**(円周 `S¹` など)と `π₁(S¹) ≅ ℤ` の機械計算
3. **不完全性の具体化** — `ProvabilityTheory` を実際の一階算術
   (Gödel 数化・表現可能性定理)でインスタンス化。
4. **未解決問題への接近** — 例: 高次圏論の coherence 問題群や reverse
   mathematics の未分類命題など、「形式化が実際に武器になる」問題を選定し、
   ライブラリを育てる。

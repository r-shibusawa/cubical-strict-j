# Reversal is unrepairable(証明ノート、2026-08-03)

論文 docs/paperL/unrepairable.{tex,pdf} の証明ノート。前提:
docs/ReversalQuotient.md(L = K(ℤ/2,1))。

## 1. Aut(□ⁿ) = hyperoctahedral(T1)

DM: Birkhoff 双対で束自己同型 = リテラル立方体の座標置換 S_{2n};
¬-対合との可換 ⟺ ペア交換対合の中心化 = Σₙ⋉(ℤ/2)ⁿ。
KL: 非混合 poset の自己同型は n=2 で正確に 8 個・全て ¬-可換。

## 2. 同変モデル構造の存在(T2)

ACCRS §2–5 の hyperoctahedral 移植。2 つの修正:
(i) **無点種区間**: 反転が全頂点を動かすので種の区間に大域点なし ⟹
種層は生成デバイスに降格し、cylindricity(k=1 頂点三角形、同変性
不要)・EEP(公理的)・宇宙ファイブラント性(δ-contractor 機構は
完全に無点)を cSet 層で実行。Frobenius・sm7 は Δ-移送。
(ii) **軌道亜群頂点補題**: ACCRS の頂点固定要求を除去 — H-作用を
軌道亜群上の図式に組み、連結亜群余極限で任意の頂点 v: 1 → Iᵏ/H が
生成 trivial cofibration の余極限に。⟹ 全 Iᵏ/H 可縮、特に L 可縮。

## 3. Overshoot(T3)

自由性定理(胞体上固定なし)⟹ el(Iᵏ/H) = el(Iᵏ)/H は可縮圏の
自由商 ⟹ N el(Iᵏ/H) ≃ BH。test MS の w.e. = N el(−) 弱同値なので
(L→1) ∈ W_eq ∖ W_test ⟹ **同変 MS ≠ test MS** — カルテシアン
(ACCRS 6.3.6 の一致)と正反対。診断: equivariance は固定胞体由来の
欠陥を直す技術であり、反転の欠陥は固定胞体の不在から生じる。

## 4. Crown no-go(T4)

□_DM・□_KL は相対 elegance 埋め込みを持たない(CS A.14 拡張)。
頂点レベルでは factorization が存在する(リテラル DNF の関数完全性)
が、自由代数レベルで: 三分岐強制 → crown fiber(間隔 2n、非比較)
→ 負リテラル方向の連結性による定数化 → winding b·w = a 矛盾。
機械証明書: crown 領域 CSP、DM 768 点・KL 312 点とも UNSAT。
Boolean は安定化(頂点作用が全てを決める)— Campion の
Kar(BA) = 有限集合(EZ)と整合。

## 5. test 比較の再開(T5)

folklore の証人 L は証人でない: el(L) ≃ Bℤ/2 = 型理論的答え
(K(ℤ/2,1))と一致 — 外れ者は位相実現(□_DM 上で test 関手で
ない)。カルテシアンの否定(Coquand の Q)は対角固定胞体に依存し
反転には無関係。⟹ **「CCHM は test 比較で空間を表すか
(W_type = W_test?)」は開問題**。部分結果: Cof = mono のモデル構造の
W は Cisinski localizer ⟹ W_min ⊆ W_type。

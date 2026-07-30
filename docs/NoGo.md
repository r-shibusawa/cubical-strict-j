# 自然な strict 充填の不在(証明ノート、2026-08-01)

論文 docs/paperJ/nogo.{tex,pdf} の証明ノート。前提: docs/DMFiber.md
(ファイバー定理)、docs/StrictLayer.md(ズレ公式・coherence 二分)。

## 1. No-go 定理(3 行証明)

**定理**: 境界にその strict 充填を割り当てる切断 s で、全置換に自然
(s(∂(f*g)) = f*(s(B)))なものは存在しない。n=2・endo 置換のみで既に
不成立。

証明: m := ¬x∧y∧¬y はその境界の**一意**充填(ファイバー単元)。
よって自然な s は s(∂m)=m を強制され、全転送 f*m の上でも強制される。
ところが
- (x:=y)*m = y∧¬y(2 元ファイバーの上端)
- (x:=x∧¬x)*m = (x∨¬x)∧y∧¬y(同ファイバーの下端)
は同一境界・相異なる値。∎
(対角は不可視対角点 ((0,0),(1,1)) を付加し、LEM 潰しは付加しない。)

**機械 census**: 一意充填からの強制は 54 非単元ファイバー中 42 に
及び、強制衝突は 142 対。独立に、全切断空間 2^38×4^16 の
backtracking 探索(121 endo 制約)でも解なし。

**系**: □_DM に自然な充填操作は strict 層に値を取れない —
weak 層(Kan 合成)は圏論的に必然。

## 2. median 補正構造

- **ファイバー座標公式**: φ=m∪S, φ′=m∪S′ に対し
  χ(φ,φ′) = cyl(m∪(S∩S′)) ∪ (S∖S′ を ¬k で grading) ∪
  (S′∖S を k で grading) — 2^D 上の Boolean median の k-次数化
  (4 元ファイバー全対で厳密検証)。
- **coherence は χ の反復**: Ξ := χ_l(χ_k(a,b), cyl c) の 4 面が
  χ_k(a,b) / cyl(c) / χ_l(a,c) / χ_l(b,c) に**正確に**一致
  (機械検証)。一般の補正球面は sphere-filling 定理で充填 —
  **補正系は strict に可縮**。
- AWFS の言葉で: 任意の切断は pointed-endofunctor 代数を与えるが
  monad 代数は不可能(no-go)— strictly contractible な擬構造が最適。

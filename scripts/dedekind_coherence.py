"""Coherence experiments for the algebraic separation program (O23).

(A) Half-fold rigidity at W-level: among W([3])-cells G with
    0-slice = iota:  swap-fold condition alone (G.a1 = G.b1)
    forces G unique with 1-slice = iota; diagonal-fold alone
    does not (3 candidates, 2 with 1-slice != iota).

(B) O2 configuration (fold-2 old via T = <a2,b2>, eps = 0,
    s = u&v&w): all boxes realizing a fresh fold-cylinder with
    0-end = iota have 1-end ground = iota.  (COH) holds.

(C) O1 configuration (fold-1 old via T = <a1,b1>, eps = 0,
    s = w): the two diagonal-only bad G-candidates admit no
    side prisms satisfying the fold-1 value equality and the
    fold-2 box equality.  (COH) holds.
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, Quotient

def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)
def meet(a, b): return tuple(x & y for x, y in zip(a, b))

A1c, B1c = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2c, B2c = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1c, B1c), (1, A2c, B2c)], 3)
iota = W.cls(2, (proj(2,0), proj(2,1)))
u2, w2 = proj(2,0), proj(2,1)
a2m = (u2, u2, w2); b2m = (u2, const(2,1), w2)
a1m = (const(2,0), u2, w2); b1m = (u2, const(2,0), w2)
n0m = (u2, w2, const(2,0)); n1m = (u2, w2, const(2,1))
def rc(H, m): return W.cls(2, tuple(compose(c, m, 3, 2) for c in H))

reps3 = []
seen = set()
for D in cube_cells(2, 3):
    cD = W.cls(3, D)
    if cD in seen: continue
    seen.add(cD); reps3.append(D)

# ---- (A) half-fold rigidity ----
tot = f1 = f2 = 0; f1ok = f2bad = 0
G_f2 = []
for G in reps3:
    if rc(G, n0m) != iota: continue
    tot += 1
    c1 = rc(G, a1m) == rc(G, b1m)
    c2 = rc(G, a2m) == rc(G, b2m)
    if c1:
        f1 += 1
        if rc(G, n1m) == iota: f1ok += 1
    if c2:
        f2 += 1; G_f2.append(G)
        if rc(G, n1m) != iota: f2bad += 1
print("(A) iota-sliced G:", tot, "| swap-fold only:", f1,
      "(all 1-slice iota:", f1 == f1ok, ") | diag-fold only:",
      f2, "( bad:", f2bad, ")")

# ---- (B) O2 configuration ----
r0 = (u2, w2, const(2,0))
edge1 = (const(2,1), u2, w2)
sect_uw = (u2, w2, meet(u2, w2))
nB = 0
for G in reps3:
    if rc(G, n0m) != iota: continue
    if rc(G, a1m) != rc(G, b1m): continue
    if rc(G, n1m) == iota: continue
    Ga2, Gb2 = rc(G, a2m), rc(G, b2m)
    for Da in reps3:
        if rc(Da, r0) != Ga2: continue
        for Db in reps3:
            if rc(Db, r0) != Gb2: continue
            if rc(Da, edge1) != rc(Db, edge1): continue
            if rc(Da, sect_uw) != rc(Db, sect_uw): continue
            nB += 1
print("(B) O2 config: violating realizable configurations:", nB,
      "=> (COH)", "HOLDS" if nB == 0 else "FAILS")

# ---- (C) O1 configuration ----
uslice0 = (const(2,0), u2, w2)
uslice1 = (const(2,1), u2, w2)
sect_ww = (u2, w2, w2)
nC = 0
for G in G_f2:
    if rc(G, n1m) == iota: continue
    Ga1, Gb1 = rc(G, a1m), rc(G, b1m)
    for Da in reps3:
        if rc(Da, r0) != Ga1: continue
        if rc(Da, uslice0) != rc(Da, uslice1): continue
        for Db in reps3:
            if rc(Db, r0) != Gb1: continue
            if rc(Da, sect_ww) != rc(Db, sect_ww): continue
            if rc(Da, uslice0) != rc(Db, uslice0): continue
            nC += 1
print("(C) O1 config: violating realizable configurations:", nC,
      "=> (COH)", "HOLDS" if nC == 0 else "FAILS")

# ---- (D) worst case: all four tracks old via T, no G-fold descends ----
# T = <a1,b1,a2,b2>, eps = 0, s = w&(u|v).
def join(a,b): return tuple(x | y for x,y in zip(a,b))
uk0 = (const(2,0), u2, w2)
uk1 = (const(2,1), u2, w2)
sect_wu = (u2, w2, meet(w2, u2))
sect_w  = (u2, w2, w2)
r0 = (u2, w2, const(2,0))
nD = 0; table = []
for G in reps3:
    if rc(G, n0m) != iota: continue
    Ga2, Gb2, Ga1, Gb1 = rc(G,a2m), rc(G,b2m), rc(G,a1m), rc(G,b1m)
    Da2s = [D for D in reps3 if rc(D, r0) == Ga2]
    Db2s = [D for D in reps3 if rc(D, r0) == Gb2]
    Da1s = [D for D in reps3 if rc(D, r0) == Ga1]
    Db1s = [D for D in reps3 if rc(D, r0) == Gb1]
    found = False
    for Da2 in Da2s:
        e00a = rc(Da2, uk0); e11 = rc(Da2, uk1); s2a = rc(Da2, sect_wu)
        for Db2 in Db2s:
            if rc(Db2, uk1) != e11 or rc(Db2, sect_w) != s2a: continue
            e01 = rc(Db2, uk0)
            for Da1 in Da1s:
                if rc(Da1,uk0)!=e00a or rc(Da1,uk1)!=e01: continue
                s1a = rc(Da1, sect_wu)
                for Db1 in Db1s:
                    if rc(Db1,uk0)==e00a and rc(Db1,sect_wu)==s1a:
                        found = True; break
                if found: break
            if found: break
        if found: break
    table.append((rc(G,n1m)==iota, Ga1==Gb1, Ga2==Gb2, found))
    if found and rc(G,n1m) != iota: nD += 1
print("(D) all-old config: iota-sliced G:", len(table),
      "| realizable:", sum(1 for t in table if t[3]),
      "| realizable & both G-folds:",
      sum(1 for t in table if t[3] and t[1] and t[2]),
      "| violations:", nD)
print("    => (COH)", "HOLDS" if nD == 0 else "FAILS",
      "; realizability forces both fold equalities on G:",
      all((not t[3]) or (t[1] and t[2]) for t in table))

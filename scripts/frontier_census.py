"""Census of the six n=4 frontier classes (O20): the
reflection-generated mixed classes where q_* is surjective on
F2-homology through degree 3 (nr_check.py), so that E-dom(i) is
not yet decided.  For each: group structure, maximal strata,
incidence poset of the loci (with b0/b1 of its nerve = the
homotopy type of el(Sigma) upstairs, by the nerve-of-cover
lemma), setwise stabilizers, residual actions, and pi_0 / H_1
of el(Sigma/N).

Key dichotomy: if el(Sigma) is CONTRACTIBLE (incidence nerve a
tree/point), the collage gives el(q): el(Sigma/N) -> el(cube/N)
an equivalence, so Hypothesis E-dom(i) FAILS as stated and the
class needs the type-side condition (ii) instead.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build, analyse, Cx, rank

n = 4
ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
def close(gens):
    S = {ID}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for g in gens:
            y = MUL[x][g]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
REFL = []
for a in range(NE):
    p, s = ELEMS[a]
    seen = [False]*n; ok = a != ID
    for i in range(n):
        if seen[i]: continue
        sg = s[i]; j = p[i]; seen[i] = True
        while j != i:
            seen[j] = True; sg ^= s[j]; j = p[j]
        if sg & 1: ok = False
    REFL.append(ok)
subs = {frozenset([ID]): []}
frontier = list(subs.items())
while frontier:
    new = []
    for H, gens in frontier:
        for g in range(NE):
            if g in H: continue
            H2 = close(gens + [g])
            if H2 not in subs:
                subs[H2] = gens + [g]; new.append((H2, gens + [g]))
    frontier = new
classes = {}
for H in subs:
    key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
              for g in range(NE))
    classes.setdefault(key, H)
tgt = []
for H in classes.values():
    R = [a for a in H if REFL[a]]
    if not R: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    if close(R) != H: continue
    tgt.append(H)
print(f"n={n}: reflection-generated mixed classes: {len(tgt)}", flush=True)

def cyc(a):
    p, s = ELEMS[a]
    seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        c = [i]; sg = s[i]; j = p[i]; seen[i] = True
        while j != i:
            seen[j] = True; c.append(j); sg ^= s[j]; j = p[j]
        out.append((len(c), sg & 1))
    return tuple(sorted(out))

for H in sorted(tgt, key=len):
    loci = {}
    for a in H:
        if REFL[a]:
            L = frozenset(v for v in range(1 << n) if ACT[a][v] == v)
            loci.setdefault(L, []).append(a)
    maximal = [L for L in loci if not any(L < L2 for L2 in loci)]
    HA, HB, surj = analyse(H, ACT, n, [sorted(L) for L in maximal], top=4)
    bad = [k for k, (img, ha, hb) in surj.items() if img < ha]
    if bad: continue      # settled by nr_check; skip
    Hs = sorted(H)
    print(f"\n=== FRONTIER |D|={len(H)} strata={len(maximal)} "
          f"H(elW)={[HA[k] for k in sorted(HA)]} "
          f"H(elS)={[HB[k] for k in sorted(HB)]}", flush=True)
    from collections import Counter
    print("  element cycle types:", dict(Counter(cyc(a) for a in Hs)))
    # orbits of maximal strata + setwise stabilizers + residuals
    orb = {}
    for L in maximal:
        key = min(frozenset(ACT[g][v] for v in L) for g in Hs)
        orb.setdefault(key, []).append(L)
    print(f"  maximal strata: {len(maximal)} in {len(orb)} orbit(s); "
          f"stratum vertex-sizes {[len(L) for L in maximal]}")
    for key, Ls in orb.items():
        L = Ls[0]
        setw = [g for g in Hs if frozenset(ACT[g][v] for v in L) == L]
        ptw = [g for g in setw if all(ACT[g][v] == v for v in L)]
        # residual = setwise/pointwise image on the locus
        res_perms = {tuple(ACT[g][v] for v in sorted(L)) for g in setw}
        print(f"   orbit size {len(Ls)}: |setwise|={len(setw)} "
              f"|pointwise|={len(ptw)} |residual|={len(res_perms)}")
    # incidence poset of ALL loci (closed under intersection):
    allL = set(loci)
    changed = True
    while changed:
        changed = False
        for L1 in list(allL):
            for L2 in list(allL):
                I = L1 & L2
                if I and I not in allL:
                    allL.add(I); changed = True
    allL = sorted(allL, key=lambda L: (-len(L), sorted(L)))
    edges = [(i, j) for i, L1 in enumerate(allL)
             for j, L2 in enumerate(allL) if L1 < L2]
    # nerve of the poset: b0, b1 (order complex of a poset of height<=?)
    # chains: count via DAG (Hasse not needed; order complex simplices =
    # chains). b1 of order complex = b1 of its 1-skeleton graph MINUS
    # relations from 2-chains... compute F2 homology of order cx (small)
    chains1 = edges
    chains2 = [(i, j, k) for (i, j) in edges for k in range(len(allL))
               if (j, k) in set(edges)]
    V = len(allL); E = len(chains1); F = len(chains2)
    # F2 homology of 2-truncated order complex (enough for b0,b1)
    d1 = []
    for (i, j) in chains1:
        d1.append((1 << i) ^ (1 << j))
    e_ind = {e: t for t, e in enumerate(chains1)}
    d2 = []
    for (i, j, k) in chains2:
        d2.append((1 << e_ind[(i, j)]) ^ (1 << e_ind[(j, k)])
                  ^ (1 << e_ind[(i, k)]))
    r1, r2 = rank(d1), rank(d2)
    b0 = V - r1; b1 = E - r1 - r2
    # NOTE: b0/b1 only; the order complex can be 2-dimensional, so
    # (1,0) does NOT prove contractibility -- frontier_census2.py
    # computes b2 and the chain dimensions (the tree cases have no
    # 2-chains, which does prove it).
    print(f"  isotropy poset: {V} loci, order cx: b0={b0} b1={b1} "
          f"(see frontier_census2.py for b2)")
    # pi0 and H1 of el(Sigma/N) from the B complex (Cech, top=2)
    acts = [ACT[a] for a in Hs]
    Vs = [sorted(L) for L in maximal]
    B = Cx(1 << n, acts, 2, allowed=lambda t: any(all(x in Vi for x in t)
                                                  for Vi in Vs))
    c0, c1, c2 = len(B.reps[0]), len(B.reps[1]), len(B.reps[2])
    rB1, rB2 = rank(B.d(1)), rank(B.d(2))
    print(f"  el(Sigma/N): pi0-count={c0 - rB1}  "
          f"H1(F2)={c1 - rB1 - rB2}")

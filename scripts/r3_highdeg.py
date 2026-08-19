"""R3: is j : l/N_l -> W a test equivalence?  Degrees up to 5 (O18, s.85).

The reduced vertex model U (vertices with maximal stabilisers) has only
8 elements for R3 and contains the D-orbit of the carrier, so el(W) is
computed from U^{k+1}/D and el(l/N_l) from V_l^{k+1}/N_l, with the induced
map given by the inclusion V_l <= U.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

n = 4
ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
NV = 1 << n
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
def close(g):
    S = {ID}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for a in g:
            y = MUL[x][a]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
D = sorted(close([idx[((0, 1, 3, 2), (1, 1, 0, 0))],
                  idx[((1, 2, 0, 3), (0, 0, 0, 0))],
                  idx[((0, 2, 1, 3), (1, 1, 1, 1))]]))
stab = {v: frozenset(a for a in D if ACT[a][v] == v) for v in range(NV)}
U = [v for v in range(NV) if not any(stab[v] < stab[w] for w in range(NV))]
print(f"R3: |D|={len(D)}, reduced model |U|={len(U)}: {U}", flush=True)
loci = {}
for a in D:
    if REFL[a]:
        L = frozenset(v for v in range(NV) if ACT[a][v] == v)
        loci[L] = 1
maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
seen = set()
for Ls in maximal:
    key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in D)
    if key in seen: continue
    seen.add(key)
    Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
    if len(Nl) != 8: continue
    if not set(Ls) <= set(U):
        print(f"  stratum |l|={len(Ls)} not inside U"); continue
    for top in (5, 6):
        A = VC(U, [ACT[a] for a in D], top, NV=NV)
        S = VC(Ls, [ACT[a] for a in Nl], top, NV=NV)
        HA = homology(A, top); HS = homology(S, top)
        r = {k: induced_rank(S, A, k, lambda c, m: c)
             for k in range(1, top)}
        iso = all(r[k] == HA[k] == HS[k] for k in range(1, top))
        print(f"  top={top}: |C_*(A)|={[len(x) for x in A.reps]} "
              f"H(el W)={[HA[k] for k in range(1, top)]} "
              f"H(el l/N)={[HS[k] for k in range(1, top)]} "
              f"ranks={[r[k] for k in range(1, top)]} -> "
              f"{'ISO in degrees <= ' + str(top-1) if iso else 'NOT iso'}",
              flush=True)

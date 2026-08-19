"""R4: the |l|=8 carriers and their universal covers (O18, section 85)."""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology

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
D = sorted(close([idx[((1, 0, 2, 3), (0, 0, 0, 0))],
                  idx[((0, 1, 2, 3), (1, 1, 0, 0))],
                  idx[((2, 3, 0, 1), (0, 0, 0, 0))]]))
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
    if len(Ls) != 8: continue
    Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
    Rq = [a for a in Nl if a not in Pl and any(ACT[a][w] == w for w in Ls)]
    Nprime = sorted(close(Rq + Pl))
    S = VC(Ls, [ACT[a] for a in Nl], 6, NV=NV)
    Sc = VC(Ls, [ACT[a] for a in Nprime], 6, NV=NV)
    HS = homology(S, 6); HSc = homology(Sc, 6)
    print(f"carrier |l|={len(Ls)} |N_l|={len(Nl)} |N'|={len(Nprime)}:")
    print(f"   H_*(el l/N_l)  = {[HS[k] for k in range(1, 6)]}")
    print(f"   H_*(el l/N')   = {[HSc[k] for k in range(1, 6)]}   "
          f"(universal cover; el(W) is simply connected so a retraction "
          f"lifts here)")
    # does l/N' look like W_K x cube^1 ?  (Q' acting through a coordinate
    # collapse)  -- report the coordinate action
    Pp = [a for a in Nprime if all(ACT[a][w] == w for w in Ls)]
    print(f"   |Q'| = {len(Nprime)//len(Pp)}", flush=True)

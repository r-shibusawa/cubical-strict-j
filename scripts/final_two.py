"""Decisive recomputation for the two open classes (O18, section 86).

The chain-level theory (section 86) validates the machinery: for
R4 = K wr Z/2 one has el(W) = SP^2(X), X = el(W_K), and the short exact
sequence 0 -> C(X) -> C(SP^2 X) -> (Q)_{Sigma_2} -> 0 (diagonal
subcomplex, free off-diagonal quotient) predicts the induced map of the
diagonal; the independent VC computation now agrees with it.

Here we recompute, for every carrier of R3 and R4 (and the universal
covers), the induced map H_*(el l/N_l) -> H_*(el W) in degrees 1..4.
Non-surjectivity in ANY degree certifies (NR') at that carrier.
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

CASES = [
    ("R3", [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 2, 0, 3), (0, 0, 0, 0))],
            idx[((0, 2, 1, 3), (1, 1, 1, 1))]], 5),
    ("R4", [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 2, 3), (1, 1, 0, 0))],
            idx[((2, 3, 0, 1), (0, 0, 0, 0))]], 5),
]
for name, gens, top in CASES:
    D = sorted(close(gens))
    A = VC(list(range(NV)), [ACT[a] for a in D], top, NV=NV)
    HA = homology(A, top)
    print(f"{name}: |D|={len(D)}  H_*(el W) = "
          f"{[HA[k] for k in range(1, top)]}", flush=True)
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
        Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
        Rq = [a for a in Nl if a not in Pl and any(ACT[a][w] == w for w in Ls)]
        Nprime = sorted(close(Rq + Pl)) if Rq else sorted(Pl)
        for label, grp in (("N_l", Nl), ("N' (cover)", Nprime)):
            S = VC(Ls, [ACT[a] for a in grp], top, NV=NV)
            HS = homology(S, top)
            r = {k: induced_rank(S, A, k, lambda c, m: c)
                 for k in range(1, top)}
            bad = [k for k in range(1, top) if r[k] < HA[k]]
            print(f"   |l|={len(Ls)} via {label:11s} (|grp|={len(grp):2d}): "
                  f"H={[HS[k] for k in range(1, top)]} ranks="
                  f"{[r[k] for k in range(1, top)]} -> "
                  f"{'(NR-sharp) certified in degrees ' + str(bad) if bad else 'surjective (inconclusive)'}",
                  flush=True)

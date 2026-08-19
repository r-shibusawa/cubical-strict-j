"""R4 = K wr Z/2: el(W) is the symmetric square SP^2(el(W_K)) (O18, s.85).

V = V_2 x V_2 and D = (K x K) x| C_2, so the vertex Cech model satisfies
    V^{k+1}/D = ( (V_2^{k+1}/K) x (V_2^{k+1}/K) ) / C_2 = Sym^2(S_k),
S_k := V_2^{k+1}/K being the Cech model of el(W_K).  Realisation commutes
with products and quotients, so
        el(cube^4/(K wr Z/2)) = SP^2(X),  X := el(cube^2/K) ~ RP^oo * RP^oo,
and the diagonal carrier's j is the diagonal X -> SP^2(X).

X is 2-connected (pi_1 = 1 since K is reflection-generated, H_1 = H_2 = 0),
so X ^ X is 5-connected and the quadratic construction
D_2(X) = SP^2(X)/X is 5-connected: the diagonal is an F_2-homology iso in
degrees <= 5 -- exactly what the machine sees -- and FAILS in degree 6,
where the square of the degree-3 class lives.  Hence el(W) is not a
retract of el(l/N_l) for the diagonal carrier: (NR') holds there.

This script (a) verifies the Sym^2 identification of the chain complexes,
(b) computes H_*(X) to high degree, and (c) computes the other carriers'
el to degrees 4-5 for the (NR') comparison.
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
D = sorted(close([idx[((1, 0, 2, 3), (0, 0, 0, 0))],
                  idx[((0, 1, 2, 3), (1, 1, 0, 0))],
                  idx[((2, 3, 0, 1), (0, 0, 0, 0))]]))
print(f"R4: |D|={len(D)}")

# (a) chain sizes: |V^{k+1}/D| vs (n_k^2+n_k)/2 with n_k = |V_2^{k+1}/K|
E2, i2, ID2, NE2, MUL2, INV2, ACT2 = build(2)
K = sorted(close.__wrapped__ if False else [])  # placeholder
def close2(g):
    S = {ID2}; dq = deque([ID2])
    while dq:
        x = dq.popleft()
        for a in g:
            y = MUL2[x][a]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
Kg = sorted(close2([i2[((1, 0), (0, 0))], i2[((0, 1), (1, 1))]]))
def orbits_count(vertset, acts, m, NVloc):
    seen = set(); c = 0
    for t in itertools.product(vertset, repeat=m):
        code = tuple(t)
        if code in seen: continue
        c += 1
        for A in acts:
            seen.add(tuple(A[x] for x in t))
    return c
for m in (1, 2, 3, 4):
    nk = orbits_count(range(4), [ACT2[a] for a in Kg], m, 4)
    dk = orbits_count(range(NV), [ACT[a] for a in D], m, NV)
    print(f"   m={m}: |V_2^m/K| = {nk}, (n^2+n)/2 = {(nk*nk+nk)//2}, "
          f"|V^m/D| = {dk}  -> {'MATCH' if (nk*nk+nk)//2 == dk else 'MISMATCH'}")

# (b) H_*(X) for X = el(cube^2/K)
XA = VC(list(range(4)), [ACT2[a] for a in Kg], 7, NV=4)
HX = homology(XA, 7)
print(f"   H_*(X = el(W_K)) up to degree 6: "
      f"{[HX[k] for k in range(1, 7)]}   (= RP^oo * RP^oo: H_k = k-2)")

# (c) the other carriers of R4
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
    top = 6 if len(Ls) <= 8 else 4
    S = VC(Ls, [ACT[a] for a in Nl], top, NV=NV)
    HS = homology(S, top)
    print(f"   carrier |l|={len(Ls)} |N_l|={len(Nl)}: "
          f"H_*(el l/N_l) = {[HS[k] for k in range(1, top)]}", flush=True)

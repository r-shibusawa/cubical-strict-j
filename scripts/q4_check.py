"""Degree-4 extension of the q_*-surjectivity test (O20) for the
three non-tree frontier classes at n=4 (orders 16, 32, 192).
Vertex Cech model with array-based orbit indexing (the dict of
16^6 codes is replaced by a flat int32 array).  If q_* fails to
be surjective on H_4 for a class, the sieve factorization is
excluded unconditionally there (test side), settling E-dom(i)."""
import sys, itertools
from array import array
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from strata_retract import build, rank

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
def cyc(a):
    p, s = ELEMS[a]
    seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        sg = s[i]; j = p[i]; seen[i] = True; ln = 1
        while j != i:
            seen[j] = True; ln += 1; sg ^= s[j]; j = p[j]
        out.append((ln, sg & 1))
    return tuple(sorted(out))
SIGS = {
 'circ16':  (16, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                  ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):4}),
 'wedge32': (32, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                  ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):8,
                  ((2,1),(2,1)):4, ((4,0),):8}),
 'sph192':  (192,{((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):6,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):12,
                  ((1,0),(1,1),(2,1)):24, ((1,1),(1,1),(2,0)):12,
                  ((1,0),(3,0)):32, ((1,1),(3,1)):32, ((2,0),(2,0)):12,
                  ((2,1),(2,1)):12, ((4,0),):48}),
}
subs = {frozenset([ID]): []}
fr = list(subs.items())
while fr:
    new = []
    for H, gens in fr:
        for g in range(NE):
            if g in H: continue
            H2 = close(gens + [g])
            if H2 not in subs:
                subs[H2] = gens + [g]; new.append((H2, gens + [g]))
    fr = new
classes = {}
for H in subs:
    key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
              for g in range(NE))
    classes.setdefault(key, H)
found = {}
for H in classes.values():
    R = [a for a in H if REFL[a]]
    if not R or close(R) != H: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    sig = (len(H), dict(Counter(cyc(a) for a in H)))
    for name, (sz, ct) in SIGS.items():
        if sig == (sz, ct): found[name] = sorted(H)
print("matched:", sorted(found), flush=True)

NV = 1 << n
TOP = 5   # chains in degrees 0..5 -> homology 1..4

class CxA:
    """orbit chain complex, flat-array indexing"""
    def __init__(s, acts, top, allowed=None):
        s.top = top; s.reps = []; s.ind = []
        for k in range(top + 1):
            m = k + 1; size = NV ** m
            ind = array('i', [-1]) * 1
            ind = array('i', bytes(0))
            ind = array('i', [-1]) * 0
            ind = array('i', [-1] * size)
            reps = []
            for code in range(size):
                if ind[code] >= 0: continue
                t = []; c = code
                for _ in range(m): t.append(c % NV); c //= NV
                if allowed is not None and not allowed(t):
                    ind[code] = -2; continue
                oid = len(reps); reps.append(code)
                for A in acts:
                    c2 = 0
                    for j in range(m - 1, -1, -1):
                        c2 = c2 * NV + A[t[j]]
                    ind[c2] = oid
            s.reps.append(reps); s.ind.append(ind)
            print(f"    level {k}: {len(reps)} orbits", flush=True)
    def d(s, k):
        cols = []
        ind1 = s.ind[k-1]
        for code in s.reps[k]:
            m = k + 1
            t = []; c = code
            for _ in range(m): t.append(c % NV); c //= NV
            v = 0
            for i in range(m):
                u = t[:i] + t[i+1:]; c2 = 0
                for j in range(len(u) - 1, -1, -1):
                    c2 = c2 * NV + u[j]
                v ^= 1 << ind1[c2]
            cols.append(v)
        return cols

for name in ('sph192', 'wedge32', 'circ16'):
    N = found[name]
    acts = [ACT[a] for a in N]
    loci = {}
    for a in N:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    Vsets = [set(L) for L in maximal]
    print(f"\n### {name} |N|={len(N)} strata={len(maximal)}", flush=True)
    print("  building A (full cube)...", flush=True)
    A = CxA(acts, TOP)
    print("  building B (sieve)...", flush=True)
    B = CxA(acts, TOP, allowed=lambda t: any(all(x in Vi for x in t)
                                             for Vi in Vsets))
    dA = {k: A.d(k) for k in range(1, TOP + 1)}
    rA = {k: rank(dA[k]) for k in range(1, TOP + 1)}
    HA = {k: len(A.reps[k]) - rA[k] - rA[k+1] for k in range(1, TOP)}
    dB = {k: B.d(k) for k in range(1, TOP + 1)}
    rB = {k: rank(dB[k]) for k in range(1, TOP + 1)}
    HB = {k: len(B.reps[k]) - rB[k] - rB[k+1] for k in range(1, TOP)}
    print(f"  H(elW) deg1..4 = {[HA[k] for k in sorted(HA)]}", flush=True)
    print(f"  H(elS) deg1..4 = {[HB[k] for k in sorted(HB)]}", flush=True)
    # q_* rank in each degree
    for k in range(1, TOP):
        piv = {}
        def add(v):
            while v:
                l = v.bit_length() - 1
                if l in piv: v ^= piv[l]
                else: piv[l] = v; return True
            return False
        for v in dA[k+1]: add(v)
        # kernel basis of dB_k
        piv2 = {}; comb = {}; kern = []
        for i, v in enumerate(dB[k]):
            c = 1 << i
            while v:
                l = v.bit_length() - 1
                if l in piv2:
                    v ^= piv2[l]; c ^= comb[l]
                else:
                    piv2[l] = v; comb[l] = c; c = None; break
            if c is not None: kern.append(c)
        # push cycles into A and reduce mod boundaries
        indAk = A.ind[k]
        img = 0
        for c in kern:
            v = 0
            i = 0; cc = c
            while cc:
                if cc & 1:
                    v ^= 1 << indAk[B.reps[k][i]]
                cc >>= 1; i += 1
            if add(v): img += 1
        verdict = "SURJECTIVE" if img >= HA[k] else \
                  f"NOT surjective (rank {img} < {HA[k]})"
        print(f"  q_* degree {k}: rank {img} vs H_k(elW)={HA[k]} "
              f"-> {verdict}", flush=True)

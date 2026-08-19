"""Relative Cech complex: is j : l/N_l -> W a test equivalence? (O18, s.85)

If the strata in the D-orbit of l are disjoint, the vertex set
U := D.V_l splits as a disjoint union of the strata, and the Cech orbit
complex splits into
   B_k = orbits of (k+1)-tuples lying in a SINGLE stratum   (= el(l/N_l))
   A_k = orbits of all (k+1)-tuples of U                    (= el(W) when
         U is a valid model of E_F(D), i.e. every vertex stabiliser of D
         is subconjugate to one of a vertex of U)
and el(j) is the inclusion B -> A.  So

     j is a test equivalence   <=>   H_*(A/B) = 0,

which is a much smaller computation than comparing A and B separately.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

def rank(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

def relative_homology(U, acts, strata, top):
    """H_k(A/B) for k <= top-1; strata = list of vertex subsets"""
    NU = len(U)
    pos = {v: i for i, v in enumerate(U)}
    strata_sets = [set(s) for s in strata]
    reps = []; ind = []
    for k in range(top + 1):
        m = k + 1
        seen = {}; R = []; I = {}
        for t in itertools.product(range(NU), repeat=m):
            code = 0
            for j in range(m - 1, -1, -1): code = code * NU + t[j]
            if code in I: continue
            oid = len(R); R.append(code)
            for A in acts:
                c2 = 0
                for j in range(m - 1, -1, -1):
                    c2 = c2 * NU + pos[A[U[t[j]]]]
                I[c2] = oid
            # mark
        reps.append(R); ind.append(I)
    def single(code, m):
        t = []; c = code
        for _ in range(m): t.append(U[c % NU]); c //= NU
        return any(all(x in S for x in t) for S in strata_sets)
    # relative basis: orbits not contained in a single stratum
    rel = []; relidx = []
    for k in range(top + 1):
        keep = [i for i, c in enumerate(reps[k]) if not single(c, k + 1)]
        rel.append(keep)
        m = {}
        for j, i in enumerate(keep): m[i] = j
        relidx.append(m)
    def faces(code, m):
        t = []; c = code
        for _ in range(m): t.append(c % NU); c //= NU
        out = []
        for i in range(m):
            u = t[:i] + t[i+1:]
            c2 = 0
            for j in range(len(u) - 1, -1, -1): c2 = c2 * NU + u[j]
            out.append(c2)
        return out
    def d(k):
        cols = []
        for i in rel[k]:
            code = reps[k][i]
            v = 0
            for f in faces(code, k + 1):
                oid = ind[k-1][f]
                if oid in relidx[k-1]: v ^= 1 << relidx[k-1][oid]
            cols.append(v)
        return cols
    rk = {k: rank(d(k)) for k in range(1, top + 1)}
    H = {k: len(rel[k]) - rk[k] - rk[k+1] for k in range(1, top)}
    return H, [len(r) for r in rel]

if __name__ == "__main__":
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
    print(f"R3: |D|={len(D)}")
    loci = {}
    for a in D:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    stab = {v: frozenset(a for a in D if ACT[a][v] == v) for v in range(NV)}
    for Ls in maximal:
        Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
        if len(Nl) != 8: continue
        orb = sorted({ACT[a][v] for a in D for v in Ls})
        strata = []
        seen = set()
        for a in D:
            S = tuple(sorted({ACT[a][v] for v in Ls}))
            if S not in seen: seen.add(S); strata.append(list(S))
        disjoint = (sum(len(s) for s in strata) == len(orb))
        # is U = orb a valid model?  every vertex stabiliser subconjugate
        valid = all(any(stab[v] <= stab[w] for w in orb) for v in range(NV))
        print(f"  stratum |l|={len(Ls)} |N_l|={len(Nl)}: D-orbit {len(orb)} "
              f"vertices, {len(strata)} strata, disjoint={disjoint}, "
              f"U valid model={valid}")
        if not (disjoint and valid): continue
        for top in (4, 5, 6):
            H, sizes = relative_homology(orb, [ACT[a] for a in D],
                                         strata, top)
            print(f"     top={top}: relative sizes {sizes}  "
                  f"H_*(A/B) = {[H[k] for k in range(1, top)]}", flush=True)

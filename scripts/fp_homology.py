"""el-homology with F_p coefficients (O18, section 86).

The vertex Cech model is a simplicial set, so C_*(el(cube^n/D); F_p) =
F_p[ V^{k+1}/D ] with the ALTERNATING boundary; over F_2 the signs drop
out (what all earlier scripts used), but for odd p they matter.  el is
always Q-acyclic, so any difference must be p-torsion; for groups of
order divisible by 3 the prime 3 can separate spaces that F_2 cannot.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

def orbit_complex(verts, acts, top, NV):
    reps = []; ind = []
    for k in range(top + 1):
        m = k + 1
        seen = {}; R = []
        for t in itertools.product(verts, repeat=m):
            code = 0
            for j in range(m - 1, -1, -1): code = code * NV + t[j]
            if code in seen: continue
            oid = len(R); R.append(code)
            for A in acts:
                c2 = 0
                for j in range(m - 1, -1, -1): c2 = c2 * NV + A[t[j]]
                seen[c2] = oid
        reps.append(R); ind.append(seen)
    return reps, ind

def boundary_cols(reps, ind, k, NV, p):
    cols = []
    for code in reps[k]:
        t = []; c = code
        for _ in range(k + 1): t.append(c % NV); c //= NV
        col = {}
        for i in range(k + 1):
            u = t[:i] + t[i+1:]
            c2 = 0
            for j in range(len(u) - 1, -1, -1): c2 = c2 * NV + u[j]
            j2 = ind[k-1][c2]
            col[j2] = (col.get(j2, 0) + (1 if i % 2 == 0 else p - 1)) % p
        cols.append({a: b for a, b in col.items() if b})
    return cols

def sparse_rank(cols, p):
    piv = {}          # row -> normalised column (dict)
    r = 0
    for col in cols:
        col = dict(col)
        while col:
            row = max(col)
            if row in piv:
                f = col[row] * pow(piv[row][row], p - 2, p) % p
                for a, b in piv[row].items():
                    v = (col.get(a, 0) - f * b) % p
                    if v: col[a] = v
                    elif a in col: del col[a]
            else:
                piv[row] = col; r += 1; break
    return r

def homology_fp(verts, acts, top, NV, p):
    reps, ind = orbit_complex(verts, acts, top, NV)
    rk = {k: sparse_rank(boundary_cols(reps, ind, k, NV, p), p)
          for k in range(1, top + 1)}
    return {k: len(reps[k]) - rk[k] - rk[k+1] for k in range(1, top)}, \
           [len(r) for r in reps]

if __name__ == "__main__":
    n = 4
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    NV = 1 << n
    def close(g):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for a in g:
                y = MUL[x][a]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    REFL = []
    for a in range(NE):
        pp, s = ELEMS[a]
        seen = [False]*n; ok = a != ID
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = pp[i]; seen[i] = True
            while j != i:
                seen[j] = True; sg ^= s[j]; j = pp[j]
            if sg & 1: ok = False
        REFL.append(ok)
    D = sorted(close([idx[((0, 1, 3, 2), (1, 1, 0, 0))],
                      idx[((1, 2, 0, 3), (0, 0, 0, 0))],
                      idx[((0, 2, 1, 3), (1, 1, 1, 1))]]))
    stab = {v: frozenset(a for a in D if ACT[a][v] == v) for v in range(NV)}
    U = [v for v in range(NV) if not any(stab[v] < stab[w] for w in range(NV))]
    print(f"R3: |D|={len(D)}, |U|={len(U)}")
    for p in (2, 3):
        H, sz = homology_fp(U, [ACT[a] for a in D], 5, NV, p)
        print(f"   H_*(el W; F_{p}) = {[H[k] for k in range(1,5)]}  sizes {sz}",
              flush=True)
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
        for p in (2, 3):
            H, sz = homology_fp(Ls, [ACT[a] for a in Nl], 5, NV, p)
            print(f"   carrier |l|=4 |N|=8: H_*(el l/N; F_{p}) = "
                  f"{[H[k] for k in range(1,5)]}", flush=True)

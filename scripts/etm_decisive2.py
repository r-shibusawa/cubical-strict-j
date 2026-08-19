"""Second decisive battery for the arrangement dichotomy (O20).

THEOREM (proved, transfer + cone): if a Sylow 2-subgroup of M
has a fixed point on T, then E(T)/M is F2-acyclic.

Remaining question: the exact nonvanishing condition.  Two
candidate laws, agreeing on all cases so far:
  (Syl)  H~ != 0  <=>  Sylow-2 of M is fixed-point-free;
  (EA)   H~ != 0  <=>  some elementary abelian 2-subgroup is
                       fixed-point-free.
(EA) => (Syl)-fpf, so the laws differ exactly on actions where
the Sylow 2-subgroup is fpf but every elementary abelian
2-subgroup has a fixed point.  Minimal such: Z/4 acting
faithfully on 4+2 (regular orbit + 2-orbit through the square).
More: Z/8 on 8+2, Q8-like? (Z/4 suffices), and Z/4 on 4+2+2.
"""
import itertools
from collections import deque

def close_perms(gens, T):
    idp = tuple(range(T))
    def comp(a, b): return tuple(a[b[i]] for i in range(T))
    S = {idp} | set(gens); dq = deque(S)
    while dq:
        x = dq.popleft()
        for y in list(S):
            for z in (comp(x, y), comp(y, x)):
                if z not in S: S.add(z); dq.append(z)
    return sorted(S)

def rank(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

def betti(T, M, top):
    reps = []; ind = []
    for k in range(top + 1):
        m = k + 1; size = T ** m
        arr = [-1] * size; rp = []
        for code in range(size):
            if arr[code] >= 0: continue
            t = []; c = code
            for _ in range(m): t.append(c % T); c //= T
            oid = len(rp); rp.append(code)
            for g in M:
                c2 = 0
                for j in range(m - 1, -1, -1): c2 = c2 * T + g[t[j]]
                arr[c2] = oid
        reps.append(rp); ind.append(arr)
    def dmat(k):
        cols = []
        for code in reps[k]:
            m = k + 1
            t = []; c = code
            for _ in range(m): t.append(c % T); c //= T
            v = 0
            for i in range(m):
                u = t[:i] + t[i+1:]; c2 = 0
                for j in range(len(u) - 1, -1, -1): c2 = c2 * T + u[j]
                v ^= 1 << ind[k-1][c2]
            cols.append(v)
        return cols
    r = {k: rank(dmat(k)) for k in range(1, top + 1)}
    return [len(reps[k]) - r[k] - r[k+1] for k in range(1, top)]

# Z/4 on 4+2: g = 4-cycle on {0,1,2,3} + swap {4,5}
g = (1,2,3,0, 5,4)
M1 = close_perms([g], 6)
print(f"Z/4 on 4+2: |M|={len(M1)}")
print(f"   H~(F2) deg1..5 = {betti(6, M1, 6)}", flush=True)

# Z/4 on 4+2+1? (would have global fixed pt -- skip)
# Z/4 x Z/2 on 4+2, the Z/2 acting on nothing? no...
# D4 acting on 4+2: vertices of square + the 2 diagonals
# (rotation swaps diagonals, reflections fix them or swap)
rot = (1,2,3,0, 5,4)     # diagonals {0,2},{1,3} swapped by rot
ref = (1,0,3,2, 5,4)     # edge reflection: swaps diagonals too?
# take reflection through vertices 0,2: (0)(2)(13), fixes diag {0,2}=4, {1,3}=5
ref2 = (0,3,2,1, 4,5)
D4b = close_perms([rot, ref2], 6)
elab_fpf = False
invs = [x for x in D4b if x != tuple(range(6)) and
        all(x[x[i]] == i for i in range(6))]
for a in invs:
    if not any(a[t] == t for t in range(6)):
        elab_fpf = True
for a, b in itertools.combinations(invs, 2):
    def comp(u, v): return tuple(u[v[i]] for i in range(6))
    if comp(a, b) != comp(b, a): continue
    E = close_perms([a, b], 6)
    if not any(all(x[t] == t for x in E) for t in range(6)):
        elab_fpf = True
print(f"D4 on 4+2 (vertices+diagonals): |M|={len(D4b)} "
      f"fpf={not any(all(x[t]==t for x in D4b) for t in range(6))} "
      f"elem-ab-fpf-exists={elab_fpf}")
print(f"   H~(F2) deg1..5 = {betti(6, D4b, 6)}", flush=True)

# Z/8 on 8+2 (heavier: T=10, top=5)
g8 = (1,2,3,4,5,6,7,0, 9,8)
M8 = close_perms([g8], 10)
print(f"Z/8 on 8+2: |M|={len(M8)}")
print(f"   H~(F2) deg1..4 = {betti(10, M8, 5)}", flush=True)

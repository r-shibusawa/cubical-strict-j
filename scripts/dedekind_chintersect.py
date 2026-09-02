"""O28 stage 3b: the intersection identities for the chain stratum.

The gluing route to shape-by-shape chain approximation needs:
 (I2) Ch(A) n Ch(B) = Ch(A n B) for subobjects A, B of a cube
      (Ch(A u B) = Ch(A) u Ch(B) is automatic), and
 (T2) Ch(cube^{n+1}) n P = Ch(P) for the prescribed parts
      P = S (x) cube^1 u cube^n (x) {e} of the generating boxes.
Sweep both over atom pairs in cube^2 and cube^3 wall shapes.
Every failure is listed with a witness cell.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)

K = 3
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    return [c for c in itertools.product(Dk, repeat=q)
            if all(comparable(a, b)
                   for a, b in itertools.combinations(c, 2))]
CS = {(q, k): chain_subs(q, k) for q in range(K+1) for k in range(K+1)}

def Ch(S, n):
    """chain stratum of a cell-set family S (dict k -> set)"""
    out = {k: set() for k in range(K + 1)}
    for q in range(K + 1):
        for c in S[q]:
            if rest(c, sort_sub(q), q, q) != c: continue
            for k in range(K + 1):
                for u in CS[(q, k)]:
                    out[k].add(rest(c, u, q, k) if q > 0 else
                               tuple(cc * 0 + cc for cc in
                                     rest(c, (), q, k)) if False
                               else rest(c, u, q, k))
    return out

def atom(z, j, n):
    S = {}
    for k in range(K + 1):
        _, Dk = F(k)
        S[k] = {rest(z, u, j, k)
                for u in itertools.product(Dk, repeat=j)}
    return S
def inter(A, B): return {k: A[k] & B[k] for k in range(K + 1)}

# ---- (I2) sweep over cube^2 atom pairs ----
_, D2 = F(2)
atoms2 = []
seen = set()
for z in itertools.product(D2, repeat=2):
    S = atom(z, 2, 2)
    key = frozenset(S[2])
    if key in seen: continue
    seen.add(key); atoms2.append((z, S))
fails = 0; checked = 0
for i in range(len(atoms2)):
    for j in range(i, len(atoms2)):
        A, B = atoms2[i][1], atoms2[j][1]
        AB = inter(A, B)
        lhs = inter(Ch(A, 2), Ch(B, 2)); rhs = Ch(AB, 2)
        checked += 1
        for k in range(K + 1):
            if lhs[k] != rhs[k]:
                fails += 1
                d = lhs[k] - rhs[k] or rhs[k] - lhs[k]
                print(f"(I2) FAIL atoms {atoms2[i][0]}|{atoms2[j][0]}"
                      f" level {k}: {'lhs>rhs' if lhs[k]-rhs[k] else 'rhs>lhs'}"
                      f" witness {sorted(d)[0]}", flush=True)
                break
print(f"(I2) cube^2 atom pairs: {checked} checked, {fails} fail",
      flush=True)

# ---- (T2) sweep: box shapes over cube^2, codomain cube^3 ----
xv = tuple(p[0] for p in F(1)[0])
c0_1 = tuple(0 for _ in F(1)[0]); c1_1 = tuple(1 for _ in F(1)[0])
edges = {'x1=0': (c0_1, xv), 'x1=1': (c1_1, xv),
         'x2=0': (xv, c0_1), 'x2=1': (xv, c1_1), 'diag': (xv, xv)}
def union(*Ss):
    return {k: set().union(*(S[k] for S in Ss)) for k in range(K+1)}
E1 = {n: atom(z, 1, 2) for n, z in edges.items()}
xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
full2 = atom((xx, yy), 2, 2)
walls = {
  'bdry': union(E1['x1=0'],E1['x1=1'],E1['x2=0'],E1['x2=1']),
  'horn': union(E1['x1=0'],E1['x1=1'],E1['x2=0']),
  'dDelta2': union(E1['x1=1'], E1['diag'], E1['x2=0']),
  'Lambda2': union(E1['diag'], E1['x2=0']),
  'vertex': atom((c0_1[:1]*0 or (0,), (0,)), 0, 2) if False else
            {k: {rest(((0,),(0,)), u, 0, k)
                 for u in [()]} for k in range(K+1)},
  'empty': {k: set() for k in range(K+1)},
  'full': full2,
}
def prescribed(S, e):
    """P = S x cube^1 u cube^2 x {e} as cell family in cube^3"""
    P = {}
    for k in range(K + 1):
        _, Dk = F(k)
        ce = tuple((1 if e else 0) for _ in F(k)[0])
        cells = set()
        for (c1, c2) in full2[k]:
            for ct in Dk:
                if (c1, c2) in S[k] or ct == ce:
                    cells.add((c1, c2, ct))
        P[k] = cells
    return P
t2fails = 0
for name, S in walls.items():
    if name == 'vertex': continue
    for e in (0, 1):
        P = prescribed(S, e)
        chP = Ch(P, 3)
        bad = None
        for k in range(K + 1):
            amb = {c for c in P[k]
                   if all(comparable(a, b) for a, b in
                          itertools.combinations(c, 2))}
            if amb != chP[k]:
                bad = (k, (amb - chP[k]) or (chP[k] - amb)); break
        if bad:
            t2fails += 1
            k, d = bad
            print(f"(T2) FAIL {name} e={e} level {k}: witness "
                  f"{sorted(d)[0]} ({'ambient-only' if amb-chP[k] else 'Ch-only'})",
                  flush=True)
        else:
            print(f"(T2) ok {name} e={e}", flush=True)
print(f"(T2) failures: {t2fails}", flush=True)

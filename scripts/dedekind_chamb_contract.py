"""O28 stage 3f: (B1) -- contractibility of ambient chain parts.

The subobject induction for universal chain approximation (via
the plain-SOA tower) bottoms out at:
  (B1)  Ch_amb(A) := A n Ch(cube^n) is type-contractible
        for every atom A.
Check T-Betti (validated wall-coface complex) of Ch_amb(A) for
all 12 cube^2 atoms and the 26 sampled cube^3 atoms (including
the seven (T0)-violators), plus Sing-Betti for comparison.
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from dedekind_triangulate import coface as wall_coface, rank2

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
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

def betti(S, sorted_only):
    lv = {}
    for k in range(K + 1):
        cells = sorted(S[k])
        if sorted_only:
            cells = [c for c in cells
                     if rest(c, sort_sub(k), k, k) == c]
        lv[k] = cells
    ind = {k: {c: i for i, c in enumerate(lv[k])} for k in lv}
    cof = coface_T if sorted_only else wall_coface
    r = {}
    for q in range(1, K + 1):
        cols = []
        for cell in lv[q]:
            v = 0
            for i in range(q + 1):
                fc = rest(cell, cof(i, q), q, q - 1)
                if fc not in ind[q - 1]: return None
                v ^= 1 << ind[q - 1][fc]
            cols.append(v)
        r[q] = rank2(cols)
    b = [len(lv[0]) - r[1]]
    for q in range(1, K):
        b.append(len(lv[q]) - r[q] - r[q + 1])
    return b

def atom(z, j, n):
    S = {}
    for k in range(K + 1):
        _, Dk = F(k)
        S[k] = {rest(z, u, j, k)
                for u in itertools.product(Dk, repeat=j)}
    return S
def chamb(S, n):
    return {k: {c for c in S[k]
                if all(comparable(a, b) for a, b in
                       itertools.combinations(c, 2))}
            for k in range(K + 1)}

bad = 0; tested = 0
_, D2 = F(2)
seen = set()
for z in itertools.product(D2, repeat=2):
    S = atom(z, 2, 2)
    key = frozenset(S[2])
    if key in seen: continue
    seen.add(key)
    C = chamb(S, 2)
    bt = betti(C, False); bs = betti(C, True)
    tested += 1
    if bt != [1, 0, 0] or bs != [1, 0, 0]:
        bad += 1
        print(f"(B1) cube^2 atom {z}: T {bt}, Sing {bs}", flush=True)
print(f"(B1) cube^2 atoms: {tested} tested, {bad} non-contractible",
      flush=True)

u3 = tuple(p[0] for p in F(3)[0]); v3 = tuple(p[1] for p in F(3)[0])
w3 = tuple(p[2] for p in F(3)[0])
def mt3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a & b for a, b in zip(o, x))
    return o
def jn3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a | b for a, b in zip(o, x))
    return o
pool = [mt3(u3,v3,w3), mt3(u3,v3), mt3(u3,w3), mt3(v3,w3),
        u3, v3, w3, jn3(u3,v3), jn3(u3,w3), jn3(v3,w3),
        mt3(u3,jn3(v3,w3)), mt3(v3,jn3(u3,w3)), jn3(u3,mt3(v3,w3))]
random.seed(3)
zs = [tuple(random.choice(pool) for _ in range(3)) for _ in range(25)]
zs.append((mt3(u3,v3,w3), mt3(u3,v3), mt3(u3, jn3(v3,w3))))
bad3 = 0
for i, z in enumerate(zs):
    C = chamb(atom(z, 3, 3), 3)
    bt = betti(C, False); bs = betti(C, True)
    if bt != [1, 0, 0] or bs != [1, 0, 0]:
        bad3 += 1
        print(f"(B1) cube^3 atom3#{i}: T {bt}, Sing {bs}", flush=True)
print(f"(B1) cube^3 atoms: {len(zs)} tested, {bad3} non-contractible",
      flush=True)

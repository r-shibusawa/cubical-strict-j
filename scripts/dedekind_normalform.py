"""O27 stage 13: normal forms of chain cells and T-move
connectivity.

Universal case X = cube^n.  A chain cell y (pairwise-comparable
components) has presentations y = s <> d with s a SORTED cell
(o-chain-valued tuple, level r) and d a DECREASING chain-valued
substitution [m] -> [r].  The T-moves identify
   (s <> T(h), d)  ~  (s, T(h) <> d)
for ordinal h.  Question: are all presentations of a fixed y
connected by T-moves?  (If yes, the canonical section on the
chain stratum is well-defined through the realization.)
Check exhaustively on cube^2 at target level m <= 2 with source
levels r <= 3.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F
from collections import defaultdict

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 4)}

def leq(a, b): return (a & b) == a
def chainv(c):
    return all(leq(a, b) or leq(b, a)
               for a, b in itertools.combinations(c, 2))

def o_stat(j, m):
    if j <= 0: return (1 << (1 << m)) - 1
    if j > m: return 0
    out = 0
    for pt in range(1 << m):
        if bin(pt).count('1') >= j: out |= 1 << pt
    return out

def comp1(p, v, l, m):
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

def dia(u, v, l, m):
    return tuple(comp1(c, v, l, m) for c in u)

def sorted_cells(n, r):
    """sorted cells of cube^n at level r = o-chain-valued tuples"""
    chain = [o_stat(j, r) for j in range(0, r + 2)]
    return [c for c in itertools.product(chain, repeat=n)]

def decreasing_subs(r, m):
    """decreasing chain-valued substitutions [m]->[r]: r-tuples
    over D(m), pairwise comparable, decreasing d1 >= ... >= dr"""
    out = []
    for d in itertools.product(D[m], repeat=r):
        if all(leq(d[i+1], d[i]) for i in range(r - 1)):
            out.append(d)
    return out

def ordinal_maps(a, b):
    res = []
    for vals in itertools.product(range(b + 1), repeat=a + 1):
        if all(vals[i] <= vals[i+1] for i in range(a)):
            res.append(vals)
    return res

def Tmap(f, a, b):
    """T(f): [a]->[b] as b-tuple over D(a)"""
    idx = []
    for i in range(1, b + 1):
        ks = [k for k in range(a + 1) if f[k] >= i]
        idx.append(min(ks) if ks else a + 1)
    return tuple(o_stat(k, a) for k in idx)

n = 2   # cube^2
m = 2   # target level of y
RMAX = 3
# presentations: (r, s, d): s sorted cell of cube^n level r,
# d decreasing sub [m]->[r]; y = s <> d
pres_of = defaultdict(list)
for r in range(0, RMAX + 1):
    scs = sorted_cells(n, r)
    dss = decreasing_subs(r, m)
    for s in scs:
        for d in dss:
            y = dia(s, d, r, m)
            pres_of[y].append((r, s, d))
chaincells = [y for y in itertools.product(D[m], repeat=n) if chainv(y)]
print(f"cube^{n} level {m}: chain cells {len(chaincells)}, "
      f"presented: {sum(1 for y in chaincells if y in pres_of)}")

# T-move connectivity per y: union-find over presentations
def tmoves_connected(plist):
    idx = {p: i for i, p in enumerate(plist)}
    parent = list(range(len(plist)))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    def union(i, j):
        ri, rj = find(i), find(j)
        if ri != rj: parent[ri] = rj
    for (r, s, d) in plist:
        # moves (s, T(h) <> d) <- (s <> T(h), d) for h: [r']->[r]
        for rp in range(0, RMAX + 1):
            for h in ordinal_maps(rp, r):
                Th = Tmap(h, rp, r)     # [rp]->[r]: r-tuple over D(rp)
                s2 = dia(s, Th, r, rp)  # s <> T(h): level rp cell
                # d2 with T(h) <> d2 = d? we need d = Th <> d2:
                # instead generate the move the other way:
                # from (s, e) with e = Th <> d2: enumerate d2:
                pass
        # simpler: generate moves forward: for each (r,s,d) and
        # each factorization d = Th <> d2 (h ordinal, d2
        # decreasing [m]->[rp]): connect (r,s,d) ~ (rp, s<>Th, d2)
    for (r, s, d) in plist:
        i = idx[(r, s, d)]
        for rp in range(0, RMAX + 1):
            for h in ordinal_maps(rp, r):
                Th = Tmap(h, rp, r)
                for d2 in decreasing_subs(rp, m):
                    if dia(Th, d2, rp, m) == d:
                        s2 = dia(s, Th, r, rp)
                        key = (rp, s2, d2)
                        if key in idx:
                            union(i, idx[key])
    comps = len(set(find(i) for i in range(len(plist))))
    return comps

bad = 0
worst = None
for y in chaincells:
    plist = pres_of.get(y, [])
    if not plist: continue
    comps = tmoves_connected(plist)
    if comps > 1:
        bad += 1
        if worst is None: worst = (y, comps, len(plist))
print(f"chain cells with DISCONNECTED presentation groupoid: {bad}"
      + (f"  e.g. y={worst[0]}: {worst[1]} components of "
         f"{worst[2]} presentations" if worst else ""))

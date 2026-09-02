"""O28 stage 3d: the (S-gen) condition for counit injectivity (A).

For a quotient X = cube^n/~ by chain-cell pairs, (A) reduces to:
 (S-onto) every sort-fixed class has a sort-fixed raw member
          -- TRIVIAL: c ~ c.sort and (c.sort).sort = c.sort;
 (S-gen)  the congruence restricted to chain cells is generated
          by its SORTED pairs (pairs of sort-fixed raw cells).
Test (S-gen) on adversarial quotients of cube^2, including the
cross-incomparable pair A = (x, x&y), B = (y, x&y), and on the
dunce hat itself.  Method: build the full congruence (union-find
over instance closure of the generators), build the sorted-
generated congruence (union-find over instance closure of all
identified sorted pairs), and compare the partitions on chain
cells at each level.
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

class UF:
    def __init__(s): s.p = {}
    def find(s, x):
        s.p.setdefault(x, x)
        while s.p[x] != x:
            s.p[x] = s.p[s.p[x]]; x = s.p[x]
        return x
    def union(s, a, b):
        ra, rb = s.find(a), s.find(b)
        if ra != rb: s.p[ra] = rb

def congruence(n, idents):
    """union-find per level from instance closure of idents"""
    ufs = {k: UF() for k in range(K + 1)}
    for (j, A, B) in idents:
        for k in range(K + 1):
            _, Dk = F(k)
            for u in itertools.product(Dk, repeat=j):
                ufs[k].union(rest(A, u, j, k), rest(B, u, j, k))
    return ufs

def sgen_test(name, n, idents):
    full = congruence(n, idents)
    # collect identified SORTED pairs at all levels <= K
    spairs = []
    for k in range(K + 1):
        _, Dk = F(k)
        cells = list(itertools.product(*([Dk] * n)))
        srt = [c for c in cells if rest(c, sort_sub(k), k, k) == c]
        from collections import defaultdict
        by = defaultdict(list)
        for c in srt: by[full[k].find(c)].append(c)
        for grp in by.values():
            for i in range(1, len(grp)):
                spairs.append((k, grp[0], grp[i]))
    sg = congruence(n, spairs)
    ok = True
    for k in range(K + 1):
        _, Dk = F(k)
        for c in itertools.product(*([Dk] * n)):
            if not all(comparable(a, b) for a, b in
                       itertools.combinations(c, 2)): continue
            # compare classes restricted to chain cells: two chain
            # cells full-congruent must be sorted-generated-congruent
        chain = [c for c in itertools.product(*([Dk] * n))
                 if all(comparable(a, b) for a, b in
                        itertools.combinations(c, 2))]
        from collections import defaultdict
        fullcls = defaultdict(set)
        for c in chain: fullcls[full[k].find(c)].add(c)
        for grp in fullcls.values():
            reps = {sg[k].find(c) for c in grp}
            if len(reps) > 1:
                ok = False
                a, b = sorted(grp)[0], sorted(grp)[-1]
                print(f"  (S-gen) FAIL {name} level {k}: full class "
                      f"size {len(grp)} splits into {len(reps)} "
                      f"sorted-generated classes; e.g. {a} vs {b}",
                      flush=True)
                break
        if not ok: break
    print(f"(S-gen) {name}: {'OK' if ok else 'FAIL'}", flush=True)
    return ok

xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
mt = tuple(a & b for a, b in zip(xx, yy))
jn = tuple(a | b for a, b in zip(xx, yy))
c0 = tuple(0 for _ in F(2)[0]); c1 = tuple(1 for _ in F(2)[0])
x1 = tuple(p[0] for p in F(1)[0])
c0_1 = tuple(0 for _ in F(1)[0]); c1_1 = tuple(1 for _ in F(1)[0])

tests = [
  ("dunce hat W", 2, [(1, (c0_1, x1), (x1, c0_1)),
                      (1, (x1, x1), (x1, c1_1))]),
  ("(x,x&y)~(x,x)", 2, [(2, (xx, mt), (xx, xx))]),
  ("(x,x&y)~(y,x&y)", 2, [(2, (xx, mt), (yy, mt))]),
  ("(x,x&y)~(y,y&x) twist", 2, [(2, (xx, mt), (yy, mt)),
                                (2, (mt, jn), (jn, jn))]),
  ("edge fold + square fold", 2, [(1, (c0_1, x1), (x1, c1_1)),
                                  (2, (xx, mt), (yy, mt))]),
  ("diag~edge", 2, [(1, (x1, x1), (x1, c0_1))]),
]
allok = True
for name, n, idents in tests:
    allok &= sgen_test(name, n, idents)
print(f"ALL: {'OK' if allok else 'FAILURES PRESENT'}", flush=True)

# ---- extended robustness sweep ----
import random
random.seed(7)
_, D2 = F(2)
chain2 = [c for c in itertools.product(D2, repeat=2)
          if comparable(c[0], c[1])]
extra_ok = True
for trial in range(12):
    npairs = random.choice((1, 2, 3))
    idents = []
    for _ in range(npairs):
        A = random.choice(chain2); B = random.choice(chain2)
        if A == B: continue
        idents.append((2, A, B))
    if not idents: continue
    extra_ok &= sgen_test(f"rand2#{trial} ({len(idents)}p)", 2, idents)
print(f"random cube^2 sweep: {'OK' if extra_ok else 'FAIL'}",
      flush=True)

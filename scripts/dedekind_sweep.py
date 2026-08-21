"""Systematic sweep over single-identification quotients of cube^2
on the Dedekind site (O22).

For each pair (A, B) of distinct level-j cells (j = 0, 1),
W := cube^2/(A ~ B).  Two invariants:
  - test side: F2-Betti of the triangulation T(W), degrees 0..2;
  - type side (stage zero): is [id] connected to a constant class
    by strict homotopy chains?
Hunted mismatch: T-acyclic ([1,0,0]) but [id] !~ const
  --> candidate separation witness (Dedekind would NOT present
      spaces).  The reverse mismatch (strictly contractible but
      T-nonacyclic) would indicate an engine bug.
Levels K = 3 suffice for both invariants.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, all_maps, restrict, Quotient
from dedekind_triangulate import tri_homology, coface
from collections import deque

n = 2; K = 3

def strict_census(W):
    n_ = 2
    idcell = tuple(tuple(1 if p[i] else 0 for p in F(n_)[0])
                   for i in range(n_))
    endos = []
    for Fc in cube_cells(n_, n_):
        ok = True
        for k in range(0, n_ + 1):
            groups = {}
            for u in all_maps(n_, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                c0 = W.cls(k, restrict(Fc, g[0], n_, n_, k))
                if any(W.cls(k, restrict(Fc, u, n_, n_, k)) != c0
                       for u in g[1:]):
                    ok = False; break
            if not ok: break
        if ok: endos.append(Fc)
    endo_cls = {}
    for Fc in endos: endo_cls.setdefault(W.cls(n_, Fc), Fc)
    m = n_ + 1
    adj = {c: set() for c in endo_cls}
    ptsm = F(m)[0]; ptsn = F(n_)[0]
    for H in cube_cells(n_, m):
        ok = True
        for k in range(0, n_ + 1):
            groups = {}
            for u in all_maps(n_, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                exts = []
                for u in g:
                    ptsk1 = F(k + 1)[0]; ptsk = F(k)[0]
                    idxk = {p: i for i, p in enumerate(ptsk)}
                    lift = tuple(tuple(comp[idxk[p[:-1]]] for p in ptsk1)
                                 for comp in u)
                    tvar = tuple(p[-1] for p in ptsk1)
                    exts.append(restrict(H, lift + (tvar,), n_, m, k+1))
                c0 = W.cls(k + 1, exts[0])
                if any(W.cls(k + 1, e) != c0 for e in exts[1:]):
                    ok = False; break
            if not ok: break
        if not ok: continue
        idxm = {p: i for i, p in enumerate(ptsm)}
        s0 = W.cls(n_, tuple(tuple(comp[idxm[p + (0,)]] for p in ptsn)
                             for comp in H))
        s1 = W.cls(n_, tuple(tuple(comp[idxm[p + (1,)]] for p in ptsn)
                             for comp in H))
        if s0 in adj and s1 in adj:
            adj[s0].add(s1); adj[s1].add(s0)
    idc = W.cls(n_, idcell)
    consts = set()
    for v in itertools.product((0,1), repeat=n_):
        cc = tuple(tuple(v[i] for _ in F(n_)[0]) for i in range(n_))
        consts.add(W.cls(n_, cc))
    seen = {idc}; dq = deque([idc])
    while dq:
        x = dq.popleft()
        for y in adj.get(x, ()):
            if y not in seen: seen.add(y); dq.append(y)
    return bool(seen & consts)

def cellname(c):
    return str(tuple(''.join(map(str, comp)) for comp in c))

cands = []; checked = 0
# level-0 pairs (6) and level-1 pairs (630)
jobs = []
verts = cube_cells(2, 0)
for A, B in itertools.combinations(verts, 2):
    jobs.append((0, A, B))
l1 = cube_cells(2, 1)
for A, B in itertools.combinations(l1, 2):
    jobs.append((1, A, B))
print(f"sweep over {len(jobs)} single identifications", flush=True)
for (j, A, B) in jobs:
    W = Quotient(2, [(j, A, B)], K)
    betti = tri_homology(W, 2, K)
    contr = strict_census(W)
    checked += 1
    acyc = (betti[0] == 1 and all(b == 0 for b in betti[1:]))
    if acyc and not contr:
        cands.append((j, A, B, betti))
        print(f"  CANDIDATE: j={j} A={cellname(A)} B={cellname(B)} "
              f"T-Betti={betti} but id !~ const", flush=True)
    if contr and not acyc:
        print(f"  BUG?: j={j} A={cellname(A)} B={cellname(B)} "
              f"strictly contractible but T-Betti={betti}", flush=True)
    if checked % 100 == 0:
        print(f"  ... {checked}/{len(jobs)} (candidates so far: "
              f"{len(cands)})", flush=True)
print(f"done: {checked} quotients, {len(cands)} candidates", flush=True)

"""Stage 1.5 (O22): 3-box fillers as homotopy edges.

Enumerate open 3-boxes assembled from W(2)-classes (5 faces,
edge-compatible); each filled 3-cell, when it satisfies the
homotopy-descent condition, provides strict homotopies between
its two complete opposite-face pairs.  Combined with the
stage-0 and stage-1 edges, test [id] ~ const.  A YES certifies
type-contractibility (fillers are anodyne).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from collections import deque

n = 2; K = 3

def const_f(k, v): return tuple(v for _ in F(k)[0])
def var_f(k, j):   return tuple(p[j] for p in F(k)[0])

def face_map(axis, eps, k=2):
    """site map [2] -> [3]-style: the face of cube^3 with
    coordinate 'axis' set to eps, as a 3-tuple over F(2)."""
    vs = [var_f(2, 0), var_f(2, 1)]
    out = []
    vi = 0
    for a in range(3):
        if a == axis: out.append(const_f(2, eps))
        else: out.append(vs[vi]); vi += 1
    return tuple(out)

def edge_of_face(axis, eps, axis2, eps2):
    """common edge of faces (axis,eps),(axis2,eps2): as the
    restriction recipe: for face (axis,eps) as a square with
    coords = remaining axes in order, the edge where axis2 = eps2
    is the square's restriction along a 2-tuple over F(1)."""
    rem = [a for a in range(3) if a != axis]
    j = rem.index(axis2)
    sub = []
    vi = 0
    for t in range(2):
        if t == j: sub.append(const_f(1, eps2))
        else: sub.append(var_f(1, 0))
    return tuple(sub)

def probe(name, idents):
    W = Quotient(2, idents, K)
    lv2 = W.level(2)
    # stage-0 nodes and edges (endos + strict homotopies), from
    # dedekind_sweep census logic, plus stage-1 handled separately;
    # here: nodes = strict endo classes; edges from (i) W(3)-cells
    # (stage 0) and (ii) filled 3-boxes (stage 1.5).
    def descent2(cellcls):
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                r0 = W.cls(k, restrict(cellcls, g[0], 2, 2, k))
                if any(W.cls(k, restrict(cellcls, u, 2, 2, k)) != r0
                       for u in g[1:]):
                    return False
        return True
    nodes = [c for c in lv2 if descent2(c)]
    node_set = set(nodes)
    adj = {c: set() for c in nodes}
    # stage-0 edges: W(3)-cells with homotopy descent
    pts3 = F(3)[0]; pts2 = F(2)[0]
    for H in W.level(3):
        ok = True
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                exts = []
                for u in g:
                    ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                    idxk = {p: i for i, p in enumerate(ptsk)}
                    lift = tuple(tuple(comp[idxk[p[:-1]]]
                                       for p in ptsk1) for comp in u)
                    tvar = tuple(p[-1] for p in ptsk1)
                    exts.append(W.cls(k+1,
                        restrict(H, lift + (tvar,), 2, 3, k+1)))
                if any(e != exts[0] for e in exts[1:]):
                    ok = False; break
            if not ok: break
        if not ok: continue
        s0 = W.cls(2, restrict(H, (var_f(2,0), var_f(2,1),
                                   const_f(2,0)), 2, 3, 2))
        s1 = W.cls(2, restrict(H, (var_f(2,0), var_f(2,1),
                                   const_f(2,1)), 2, 3, 2))
        if s0 in adj and s1 in adj:
            adj[s0].add(s1); adj[s1].add(s0)
    # stage-1.5: 3-box assemblies from W(2)-classes
    FACES = [(a, e) for a in range(3) for e in (0, 1)]
    def compat(asg, f1, f2):
        (a1, e1), (a2, e2) = f1, f2
        if a1 == a2: return True
        r1 = restrict(asg[f1], edge_of_face(a1, e1, a2, e2), 2, 2, 1)
        r2 = restrict(asg[f2], edge_of_face(a2, e2, a1, e1), 2, 2, 1)
        return W.cls(1, r1) == W.cls(1, r2)
    edges_added = 0; assemblies = 0
    for miss in FACES:
        present = [f for f in FACES if f != miss]
        # backtracking assembly
        def bt(i, asg):
            nonlocal edges_added, assemblies
            if i == len(present):
                assemblies += 1
                # homotopy edges along complete axes, WITH the
                # homotopy-descent check for the fresh filler:
                # every lifted restriction along a class group must
                # factor through a PRESENT face with agreeing values
                for a in range(3):
                    if a == miss[0]: continue
                    f0, f1 = asg[(a,0)], asg[(a,1)]
                    c0, c1 = W.cls(2, f0), W.cls(2, f1)
                    if not (c0 in adj and c1 in adj): continue
                    if c1 in adj[c0]: continue
                    valid = True
                    for k in range(0, 3):
                        groups = {}
                        for u in all_maps(2, k):
                            groups.setdefault(W.cls(k, u), []).append(u)
                        for g in groups.values():
                            if len(g) < 2: continue
                            vals = []
                            for u in g:
                                ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                                idxk = {q: t for t, q in
                                        enumerate(ptsk)}
                                lift = [tuple(comp[idxk[q[:-1]]]
                                              for q in ptsk1)
                                        for comp in u]
                                tvar = tuple(q[-1] for q in ptsk1)
                                trip = []
                                vi = 0
                                for ax in range(3):
                                    if ax == a: trip.append(tvar)
                                    else:
                                        trip.append(lift[vi]); vi += 1
                                # factor through a present face?
                                val = None
                                for (fa, fe) in present:
                                    if trip[fa] == const_f(k+1, fe):
                                        rem = [x for x in range(3)
                                               if x != fa]
                                        cell = restrict(
                                            asg[(fa, fe)],
                                            (trip[rem[0]],
                                             trip[rem[1]]),
                                            2, 2, k+1)
                                        val = ('w', W.cls(k+1, cell))
                                        break
                                if val is None:
                                    val = ('fresh', tuple(trip))
                                vals.append(val)
                            if any(v != vals[0] or v[0] == 'fresh'
                                   for v in vals):
                                # fresh with |g|>=2 always fails
                                # (distinct lifts) unless all equal
                                # AND attached
                                if not (all(v == vals[0]
                                            for v in vals)
                                        and vals[0][0] == 'w'):
                                    valid = False; break
                        if not valid: break
                    if valid:
                        adj[c0].add(c1); adj[c1].add(c0)
                        edges_added += 1
                return
            f = present[i]
            for cand in lv2:
                asg[f] = cand
                if all(compat(asg, f, g) for g in present[:i]
                       if g in asg):
                    bt(i + 1, asg)
            del asg[f]
        bt(0, {})
    idc = W.cls(2, (var_f(2,0), var_f(2,1)))
    consts = {W.cls(2, (const_f(2,a), const_f(2,b)))
              for a in (0,1) for b in (0,1)}
    seen = {idc}; dq = deque([idc])
    while dq:
        x = dq.popleft()
        for y in adj.get(x, ()):
            if y not in seen: seen.add(y); dq.append(y)
    hit = bool(seen & consts)
    print(f"{name}: nodes={len(nodes)} assemblies={assemblies} "
          f"new-edges={edges_added} [id]~const (stage 1.5): {hit}",
          flush=True)
    return hit

c00, x1, c11 = const_f(1,0), var_f(1,0), const_f(1,1)
probe("dunce-1", [(1, (c00,c00), (c00,x1)), (1, (x1,c11), (c11,x1))])
probe("dunce-2", [(1, (c00,c00), (x1,c00)), (1, (x1,c11), (c11,x1))])

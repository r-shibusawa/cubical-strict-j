"""Stage-2 filler probe (O22): 3-boxes with faces drawn from
W(2)-classes AND the fresh 2-box filler squares of stage 1; the
homotopy graph runs over all stage-1 nodes (including fresh
squares).  A connection [id] ~ const remains a rigorous
certificate of type-contractibility (all extensions anodyne).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from dedekind_stage1 import Stage1, const_f, var_f
from collections import deque

K = 3

def probe2(name, idents, cap_assemblies=400000):
    W = Quotient(2, idents, K)
    S = Stage1(W)
    # universe of level-2 cells: W-classes + generic fillers
    faces_pool = [('w', c) for c in W.level(2)]
    for b in range(len(S.boxes)):
        gen = (var_f(2,0), var_f(2,1))
        faces_pool.append(('n', b, gen))
    # nodes: stage-1 nodes (descent-passing level-2 universe cells)
    def descent2(cell):
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                r0 = S.restrict_cell(cell, g[0], 2, k)
                if any(S.restrict_cell(cell, u, 2, k) != r0
                       for u in g[1:]):
                    return False
        return True
    lvl2 = S.level(2)
    nodes = [c for c in lvl2 if descent2(c)]
    node_set = set(nodes)
    adj = {c: set() for c in nodes}
    # stage-1 edges: level-3 universe cells with homotopy descent
    lvl3 = S.level(3)
    def hom_descent_and_slices(H):
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                exts = []
                for u in g:
                    ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                    idxk = {q: t for t, q in enumerate(ptsk)}
                    lift = tuple(tuple(comp[idxk[q[:-1]]]
                                       for q in ptsk1) for comp in u)
                    tvar = tuple(q[-1] for q in ptsk1)
                    exts.append(S.restrict_cell(H, lift + (tvar,),
                                                3, k+1))
                if any(e != exts[0] for e in exts[1:]):
                    return None
        s0 = S.restrict_cell(H, (var_f(2,0), var_f(2,1),
                                 const_f(2,0)), 3, 2)
        s1 = S.restrict_cell(H, (var_f(2,0), var_f(2,1),
                                 const_f(2,1)), 3, 2)
        return (s0, s1)
    e1 = 0
    for H in lvl3:
        r = hom_descent_and_slices(H)
        if r and r[0] in node_set and r[1] in node_set:
            adj[r[0]].add(r[1]); adj[r[1]].add(r[0]); e1 += 1
    # stage-2: mixed 3-box assemblies
    def rcell(cell, u, k):   # restrict universe level-2 cell
        return S.restrict_cell(cell, u, 2, k)
    def edge_sub(axis, eps, axis2, eps2):
        rem = [a for a in range(3) if a != axis]
        j = rem.index(axis2)
        sub = []
        for t in range(2):
            if t == j: sub.append(const_f(1, eps2))
            else: sub.append(var_f(1, 0))
        return tuple(sub)
    FACES = [(a, e) for a in range(3) for e in (0, 1)]
    added = 0; assemblies = 0; aborted = False
    for miss in FACES:
        if aborted: break
        present = [f for f in FACES if f != miss]
        def bt(i, asg):
            nonlocal added, assemblies, aborted
            if aborted: return
            if i == len(present):
                assemblies += 1
                if assemblies > cap_assemblies:
                    aborted = True; return
                for a in range(3):
                    if a == miss[0]: continue
                    c0, c1 = asg[(a,0)], asg[(a,1)]
                    if not (c0 in adj and c1 in adj): continue
                    if c1 in adj[c0]: continue
                    # descent for the filler with t-axis = a
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
                                val = None
                                for (fa, fe) in present:
                                    if trip[fa] == const_f(k+1, fe):
                                        rem = [x for x in range(3)
                                               if x != fa]
                                        val = rcell(asg[(fa, fe)],
                                            (trip[rem[0]],
                                             trip[rem[1]]), k+1)
                                        break
                                if val is None:
                                    valid = False; break
                                vals.append(val)
                            if not valid: break
                            if any(v != vals[0] for v in vals):
                                valid = False; break
                        if not valid: break
                    if valid:
                        adj[c0].add(c1); adj[c1].add(c0)
                        added += 1
                return
            f = present[i]
            for cand in faces_pool:
                asg[f] = cand
                ok = True
                for g in present[:i]:
                    if g not in asg: continue
                    (a1,e1_), (a2,e2_) = f, g
                    if a1 == a2: continue
                    r1 = rcell(cand, edge_sub(a1,e1_,a2,e2_), 1)
                    r2 = rcell(asg[g], edge_sub(a2,e2_,a1,e1_), 1)
                    if r1 != r2: ok = False; break
                if ok: bt(i + 1, asg)
            del asg[f]
        bt(0, {})
    idc = ('w', W.cls(2, (var_f(2,0), var_f(2,1))))
    consts = {('w', W.cls(2, (const_f(2,a), const_f(2,b))))
              for a in (0,1) for b in (0,1)}
    seen = {idc}; dq = deque([idc])
    while dq:
        x = dq.popleft()
        for y in adj.get(x, ()):
            if y not in seen: seen.add(y); dq.append(y)
    hit = bool(seen & consts)
    print(f"{name}: pool={len(faces_pool)} nodes={len(nodes)} "
          f"stage1-edges={e1} assemblies={assemblies}"
          f"{' (CAP)' if aborted else ''} stage2-edges={added} "
          f"[id]~const: {hit}  reachable={len(seen)}", flush=True)
    return hit

if __name__ == '__main__':
    c00 = const_f(1,0); x1 = var_f(1,0); c11 = const_f(1,1)
    # cand-05: (0,x) ~ (x,0)  AND  (x,x) ~ (x,1)
    probe2("cand-05", [(1, (c00, x1), (x1, c00)),
                       (1, (x1, x1), (x1, c11))])

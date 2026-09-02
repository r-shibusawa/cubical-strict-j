"""O25b: multi-shell chains through FRESH intermediate cells on Q*.

By the based normal form, two fresh graph-cylinder ends are the
SAME cell of RR iff their based data coincide.  For the standard
shell (all three tracks of Q*, ends optionally included), the
based data of a fresh end at w = eps' is the finite signature
  ( eps,  G . (w = eps')-slice,  ( P_T . (w = eps')-slice )_T ).
So shells compose through fresh ends by signature matching.

This script enumerates ALL stage-one shell configurations over
Q* (and W_dunce as positive control) with
  - full track set, end squares present or absent,
  - both cone orientations eps in {0, 1},
  - arbitrary old data (G, track prisms, end prisms),
and computes the closure of the strict + basic-shell + shell-edge
+ fresh-chain relation on endomorphism classes.  Question: does
the identity class reach a constant?
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, all_maps, restrict, Quotient, compose
from dedekind_shellreach import census, proj
from collections import deque

K = 3
u1 = proj(1,0); c01 = tuple(0 for _ in F(1)[0]); c11 = tuple(1 for _ in F(1)[0])
u2, w2 = proj(2,0), proj(2,1)
c02 = tuple(0 for _ in F(2)[0]); c12 = tuple(1 for _ in F(2)[0])

def analyze(idents, name):
    W = Quotient(2, idents, K)
    endo_cls, adj, shell_adj, idc, consts = census(W, idents)
    reps3 = {}
    for c in cube_cells(2, 3):
        cl = W.cls(3, c)
        if cl not in reps3: reps3[cl] = c
    all3 = list(reps3)
    RC = {}
    def r32(cl, mp):
        key = (cl, mp)
        v = RC.get(key)
        if v is None:
            H = reps3[cl]
            v = W.cls(2, tuple(compose(c, mp, 3, 2) for c in H))
            RC[key] = v
        return v
    # coordinate maps
    def rslice(e):  # third coordinate := e  (prism r-slices, G w-slices)
        return (u2, w2, c02 if e == 0 else c12)
    def wslice(e):  # second coordinate := e (track-prism w-slices)
        return (u2, c02 if e == 0 else c12, w2)
    tracks = []
    for (j, A, B) in idents:
        for T in (A, B):
            if T not in tracks: tracks.append(T)
    def lift1(T):
        return (compose(T[0], (u2,), 1, 2), compose(T[1], (u2,), 1, 2))
    def gtrack(T):
        T1, T2 = lift1(T); return (T1, T2, w2)
    def cedge(T):
        T1, T2 = lift1(T); return (T1, T2, w2)
    def tvert(T, e):
        return (T[0][e], T[1][e])
    tlist = [tuple(T) for T in tracks]
    tmap = {tuple(T): T for T in tracks}
    vshare = []
    for a in range(len(tlist)):
        for b in range(a+1, len(tlist)):
            for ea in (0,1):
                for eb in (0,1):
                    if tvert(tmap[tlist[a]], ea) == tvert(tmap[tlist[b]], eb):
                        vshare.append((tlist[a], ea, tlist[b], eb))
    fold_pairs = [(idents[i][1], idents[i][2]) for i in range(len(idents))]

    # graph over nodes: ('o', endo_cls) and ('f', signature)
    G_edges = set()
    def add_edge(x, y):
        if x != y:
            G_edges.add((x, y)); G_edges.add((y, x))

    for eps in (0, 1):
        base = rslice(eps); val = rslice(1 - eps)
        by_base = {}
        for cl in all3:
            by_base.setdefault(r32(cl, base), []).append(cl)
        for Gcl in all3:
            Gtr = {t: r32(Gcl, gtrack(tmap[t])) for t in tlist}
            Gs = {0: r32(Gcl, rslice(0) if False else (u2, w2, c02)),
                  1: r32(Gcl, (u2, w2, c12))}
            # NOTE: G's w-slices substitute the THIRD coordinate of
            # G's (u,v,w); same tuple shape as rslice, reused safely.
            PTs = {t: by_base.get(Gtr[t], []) for t in tlist}
            if any(not v for v in PTs.values()): continue
            Cc = {e: by_base.get(Gs[e], []) for e in (0, 1)}
            def go(k, assign):
                if k == len(tlist):
                    for (A, B) in fold_pairs:
                        if r32(assign[tuple(A)], val) != r32(assign[tuple(B)], val):
                            return
                    for (ta, ea, tb, eb) in vshare:
                        ma = (c02 if ea == 0 else c12, u2, w2)
                        mb = (c02 if eb == 0 else c12, u2, w2)
                        if r32(assign[ta], ma) != r32(assign[tb], mb):
                            return
                    # per end: old candidates (via C) and the fresh signature
                    ends = {}
                    for e in (0, 1):
                        olds = set()
                        for C in Cc[e]:
                            if all(r32(C, cedge(tmap[t])) ==
                                   r32(assign[t], wslice(e)) for t in tlist):
                                olds.add(r32(C, val))
                        sig = (eps, Gs[e],
                               tuple(r32(assign[t], wslice(e)) for t in tlist))
                        ends[e] = (olds, sig)
                    o0, s0 = ends[0]; o1, s1 = ends[1]
                    for a in o0:
                        for b in o1:
                            if a in endo_cls and b in endo_cls:
                                add_edge(('o', a), ('o', b))
                    for a in o0:
                        if a in endo_cls:
                            add_edge(('o', a), ('f', s1))
                    for b in o1:
                        if b in endo_cls:
                            add_edge(('f', s0), ('o', b))
                    add_edge(('f', s0), ('f', s1))
                    return
                t = tlist[k]
                for P in PTs[t]:
                    assign[t] = P
                    go(k+1, assign)
                if t in assign: del assign[t]
            go(0, {})

    # closure: strict + basic shell + all shell/fresh edges
    adj_all = {}
    def push(x, y):
        adj_all.setdefault(x, set()).add(y)
    for c, ns in adj.items():
        for y in ns: push(('o', c), ('o', y))
    for c, ns in shell_adj.items():
        for y in ns: push(('o', c), ('o', y))
    for (x, y) in G_edges:
        push(x, y)
    start = ('o', idc)
    seen = {start}; dq = deque([start])
    while dq:
        x = dq.popleft()
        for y in adj_all.get(x, ()):
            if y not in seen: seen.add(y); dq.append(y)
    reached_endos = {c for (tag, c) in seen if tag == 'o'}
    hit = bool(reached_endos & consts)
    n_f = sum(1 for x in seen if x[0] == 'f')
    print(f"{name}: endos={len(endo_cls)} edges={len(G_edges)//2} "
          f"| id-component endos={len(reached_endos)} "
          f"fresh-nodes={n_f} | reaches const: {hit}", flush=True)
    return hit

A_l = (c01, u1); A_b = (u1, c01); A_d = (u1, u1)
A_t = (u1, c11); A_r = (c11, u1)
analyze([(1, A_l, A_b), (1, A_d, A_t)], "W_dunce (control)")
analyze([(1, A_l, A_d), (1, A_l, A_t)], "Q* (left=diag=top)")

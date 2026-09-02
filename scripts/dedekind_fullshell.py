"""O25: full one-shell relation (arbitrary base G, arbitrary prism
data, s = const_1) on the six shell-resistant quotients of the
square.  All six realize (up to the u<->v mirror) the single
congruence Q* = square/(left = diag = top); each has 6 strict
endomorphism classes and 7 full-shell edges, and the identity
class reaches no constant: Q* resists strict homotopy, the
basic shell moves, and every single-shell configuration over an
arbitrary base at the first stage.  Q* is simply connected and
Z-acyclic (dedekind_pi1 / dedekind_zhomology), hence
test-contractible: the sharpest remaining candidate witness for
the Dedekind separation."""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, all_maps, restrict, Quotient, compose
from dedekind_shellreach import census, reach, proj
from collections import deque

K = 3
u1 = proj(1,0); c01 = tuple(0 for _ in F(1)[0]); c11 = tuple(1 for _ in F(1)[0])
u2, w2 = proj(2,0), proj(2,1)
c02 = tuple(0 for _ in F(2)[0]); c12 = tuple(1 for _ in F(2)[0])

def analyze(idents, name):
    W = Quotient(2, idents, K)
    endo_cls, adj, shell_adj, idc, consts = census(W, idents)
    # level-3 class reps
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
    r0m = (u2, w2, c02); r1m = (u2, w2, c12)
    w0m = (u2, c02, w2); w1m = (u2, c12, w2)
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
    def vfacemap(e):
        return (c02 if e == 0 else c12, u2, w2)
    def tvert(T, e):
        return (T[0][e], T[1][e])
    by_r0 = {}
    for cl in all3:
        by_r0.setdefault(r32(cl, r0m), []).append(cl)
    fold_pairs = [(idents[i][1], idents[i][2]) for i in range(len(idents))]
    tlist = [tuple(T) for T in tracks]
    tmap = {tuple(T): T for T in tracks}
    # precompute vertex-sharing pairs
    vshare = []
    for a in range(len(tlist)):
        for b in range(a+1, len(tlist)):
            for ea in (0,1):
                for eb in (0,1):
                    if tvert(tmap[tlist[a]], ea) == tvert(tmap[tlist[b]], eb):
                        vshare.append((tlist[a], ea, tlist[b], eb))
    edges = set()
    for Gcl in all3:
        Gtr = {t: r32(Gcl, gtrack(tmap[t])) for t in tlist}
        # G's w-slices: substitute the THIRD (w) coordinate
        Gw0 = r32(Gcl, (u2, w2, c02)); Gw1 = r32(Gcl, (u2, w2, c12))
        C0s = by_r0.get(Gw0, []); C1s = by_r0.get(Gw1, [])
        if not C0s or not C1s: continue
        PTs = {t: by_r0.get(Gtr[t], []) for t in tlist}
        if any(not v for v in PTs.values()): continue
        def go(k, assign):
            if k == len(tlist):
                for (A, B) in fold_pairs:
                    if r32(assign[tuple(A)], r1m) != r32(assign[tuple(B)], r1m):
                        return
                for (ta, ea, tb, eb) in vshare:
                    if r32(assign[ta], vfacemap(ea)) != r32(assign[tb], vfacemap(eb)):
                        return
                e0set = set(); e1set = set()
                for C0 in C0s:
                    if all(r32(C0, cedge(tmap[t])) == r32(assign[t], w0m)
                           for t in tlist):
                        e0set.add(r32(C0, r1m))
                for C1 in C1s:
                    if all(r32(C1, cedge(tmap[t])) == r32(assign[t], w1m)
                           for t in tlist):
                        e1set.add(r32(C1, r1m))
                for e0 in e0set:
                    for e1 in e1set:
                        if e0 in endo_cls and e1 in endo_cls and e0 != e1:
                            edges.add((e0, e1)); edges.add((e1, e0))
                return
            t = tlist[k]
            for P in PTs[t]:
                assign[t] = P
                go(k+1, assign)
            if t in assign: del assign[t]
        go(0, {})
    fs_adj = {c: set() for c in endo_cls}
    for (a, b) in edges:
        fs_adj[a].add(b)
    r_strict = reach([adj], idc, consts)
    r_shell = reach([adj, shell_adj], idc, consts)
    r_full = reach([adj, shell_adj, fs_adj], idc, consts)
    print(f"{name}: endos={len(endo_cls)} fulledges={len(edges)//2} "
          f"strict={r_strict} shell={r_shell} fullshell={r_full}",
          flush=True)
    return r_full

A_l = (c01, u1); A_b = (u1, c01); A_d = (u1, u1)
A_t = (u1, c11); A_r = (c11, u1)
survivors = [
    [(1, A_l, A_d), (1, A_l, A_t)],
    [(1, A_l, A_d), (1, A_d, A_t)],
    [(1, A_l, A_t), (1, A_d, A_t)],
    [(1, A_b, A_d), (1, A_b, A_r)],
    [(1, A_b, A_d), (1, A_d, A_r)],
    [(1, A_b, A_r), (1, A_d, A_r)],
]
analyze([(1, A_l, A_b), (1, A_d, A_t)], "W_dunce (sanity)")
res = [analyze(sv, f"survivor{i+1}") for i, sv in enumerate(survivors)]
print("full-shell contracts all survivors:", all(res), flush=True)

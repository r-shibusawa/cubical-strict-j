"""O25: strict + shell reachability census on quotients of the
square (Dedekind site).

The shell-move theorem: for a congruence quotient
Q = cube^2/(A_i ~ B_i), two endomorphism cells g, g' with raw
representatives having EQUAL raw tracks (g.A_i = g'.A_i and
g.B_i = g'.B_i as raw cube cells) are type-homotopic in every
fibrant target, via the wedge-cone shell
(track prisms = cone of the common track, end prisms = cones
of g and g').  This script computes, for each quotient:
  - strict reach: is [id] ~ const under strict cylinders?
  - shell reach: same, adding shell edges (shared raw track
    signature);
  - T-Betti (test side).
Consistency: shell-contractible => type-contractible =>
test-contractible => acyclic; any shell-contractible quotient
with nontrivial Betti indicates an error.
Interesting survivors: acyclic but NOT shell-contractible.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, all_maps, restrict, Quotient
from dedekind_triangulate import tri_homology
from collections import deque

K = 3

def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)

def census(W, idents):
    """endo classes, strict adjacency, shell adjacency, id, consts"""
    n_ = 2
    idcell = (proj(2,0), proj(2,1))
    # endo condition: class-level descent (all congruent maps agree)
    groups_by_k = {}
    for k in range(0, n_ + 1):
        groups = {}
        for u in all_maps(n_, k):
            groups.setdefault(W.cls(k, u), []).append(u)
        groups_by_k[k] = [g for g in groups.values() if len(g) > 1]
    def is_endo(Fc):
        for k in range(0, n_ + 1):
            for g in groups_by_k[k]:
                c0 = W.cls(k, restrict(Fc, g[0], n_, n_, k))
                if any(W.cls(k, restrict(Fc, u, n_, n_, k)) != c0
                       for u in g[1:]):
                    return False
        return True
    endo_raw = [Fc for Fc in cube_cells(n_, n_) if is_endo(Fc)]
    endo_cls = set(W.cls(n_, Fc) for Fc in endo_raw)

    # strict cylinders (level 3)
    m = n_ + 1
    ptsm, _ = F(m); ptsn, _ = F(n_)
    idxm = {p: i for i, p in enumerate(ptsm)}
    adj = {c: set() for c in endo_cls}
    cylgroups = {}
    for k in range(0, n_ + 1):
        cylgroups[k] = groups_by_k[k]
    for H in cube_cells(n_, m):
        ok = True
        for k in range(0, n_ + 1):
            ptsk1, _ = F(k + 1); ptsk, _ = F(k)
            idxk = {p: i for i, p in enumerate(ptsk)}
            for g in cylgroups[k]:
                exts = []
                for u in g:
                    lift = tuple(tuple(comp[idxk[p[:-1]]] for p in ptsk1)
                                 for comp in u)
                    tvar = tuple(p[-1] for p in ptsk1)
                    exts.append(restrict(H, lift + (tvar,), n_, m, k+1))
                c0 = W.cls(k + 1, exts[0])
                if any(W.cls(k + 1, e) != c0 for e in exts[1:]):
                    ok = False; break
            if not ok: break
        if not ok: continue
        s0 = W.cls(n_, tuple(tuple(comp[idxm[p + (0,)]] for p in ptsn)
                             for comp in H))
        s1 = W.cls(n_, tuple(tuple(comp[idxm[p + (1,)]] for p in ptsn)
                             for comp in H))
        if s0 in adj and s1 in adj:
            adj[s0].add(s1); adj[s1].add(s0)

    # shell edges: shared CONE-CLASS track signature over the
    # generators (wedge cone /\ and join cone \/ separately)
    def cone_cls(x, j, op):
        # x = level-j cell of cube^2; cone = level j+1 cell
        ptsj1, _ = F(j + 1); ptsj, _ = F(j)
        idxj = {p: i for i, p in enumerate(ptsj)}
        rvar = tuple(p[-1] for p in ptsj1)
        comps = []
        for comp in x:
            lift = tuple(comp[idxj[p[:-1]]] for p in ptsj1)
            if op == 'and':
                comps.append(tuple(a & b for a, b in zip(lift, rvar)))
            else:
                comps.append(tuple(a | b for a, b in zip(lift, rvar)))
        return W.cls(j + 1, tuple(comps))
    shell_adj = {c: set() for c in endo_cls}
    for op in ('and', 'or'):
        sig_map = {}
        for Fc in endo_raw:
            sig = []
            for (j, A, B) in idents:
                sig.append(cone_cls(restrict(Fc, A, n_, n_, j), j, op))
                sig.append(cone_cls(restrict(Fc, B, n_, n_, j), j, op))
            sig = tuple(sig)
            sig_map.setdefault(sig, set()).add(W.cls(n_, Fc))
        for classes in sig_map.values():
            cl = list(classes)
            for a in cl:
                for b in cl:
                    if a != b:
                        shell_adj[a].add(b)

    idc = W.cls(n_, idcell)
    consts = set()
    for v in itertools.product((0,1), repeat=n_):
        cc = tuple(tuple(v[i] for _ in F(n_)[0]) for i in range(n_))
        consts.add(W.cls(n_, cc))
    return endo_cls, adj, shell_adj, idc, consts

def reach(adj_list, start, targets):
    seen = {start}; dq = deque([start])
    while dq:
        x = dq.popleft()
        if x in targets: return True
        for adj in adj_list:
            for y in adj.get(x, ()):
                if y not in seen:
                    seen.add(y); dq.append(y)
    return bool(seen & targets)

def run(idents, name):
    W = Quotient(2, idents, K)
    betti = tri_homology(W, 2, K)
    endo_cls, adj, shell_adj, idc, consts = census(W, idents)
    strict = reach([adj], idc, consts)
    shell = reach([adj, shell_adj], idc, consts)
    acyc = (betti[0] == 1 and all(b == 0 for b in betti[1:]))
    return betti, acyc, strict, shell

if __name__ == '__main__':
    fam = sys.argv[1] if len(sys.argv) > 1 else 'sanity'
    if fam == 'sanity':
        u1 = proj(1,0); c0 = tuple(0 for _ in F(1)[0]); c1 = tuple(1 for _ in F(1)[0])
        A1, B1 = (c0, u1), (u1, c0)
        A2, B2 = (u1, u1), (u1, c1)
        for name, idents in [
            ("W_dunce (both folds)", [(1, A1, B1), (1, A2, B2)]),
            ("swap fold only",       [(1, A1, B1)]),
            ("diag fold only",       [(1, A2, B2)]),
        ]:
            betti, acyc, strict, shell = run(idents, name)
            print(f"{name}: Betti={betti} acyclic={acyc} "
                  f"strict={strict} shell={shell}", flush=True)
    elif fam == 'singles':
        jobs = []
        verts = cube_cells(2, 0)
        for A, B in itertools.combinations(verts, 2):
            jobs.append((0, A, B))
        l1 = cube_cells(2, 1)
        for A, B in itertools.combinations(l1, 2):
            jobs.append((1, A, B))
        print(f"singles: {len(jobs)}", flush=True)
        stats = {"acyc_shell":0, "acyc_strict":0, "acyc_only_shell":0,
                 "survivor":0, "nonacyc":0, "VIOLATION":0}
        for i, (j, A, B) in enumerate(jobs):
            betti, acyc, strict, shell = run([(j, A, B)], "")
            if not acyc:
                stats["nonacyc"] += 1
                if shell:
                    stats["VIOLATION"] += 1
                    print(f"  VIOLATION (shell-contractible, Betti={betti}):"
                          f" j={j} A={A} B={B}", flush=True)
            else:
                if shell: stats["acyc_shell"] += 1
                if strict: stats["acyc_strict"] += 1
                if shell and not strict: stats["acyc_only_shell"] += 1
                if not shell:
                    stats["survivor"] += 1
                    print(f"  SURVIVOR (acyclic, not shell-contractible):"
                          f" j={j} A={A} B={B} Betti={betti}", flush=True)
            if (i+1) % 100 == 0:
                print(f"  ... {i+1}/{len(jobs)} {stats}", flush=True)
        print("SINGLES DONE:", stats, flush=True)
    elif fam in ('doubles', 'level2'):
        singles = []
        verts = cube_cells(2, 0)
        for A, B in itertools.combinations(verts, 2):
            singles.append((0, A, B))
        l1 = cube_cells(2, 1)
        for A, B in itertools.combinations(l1, 2):
            singles.append((1, A, B))
        jobs = []
        if fam == 'doubles':
            for s1_, s2_ in itertools.combinations(singles, 2):
                jobs.append([s1_, s2_])
        else:
            l2 = cube_cells(2, 2)
            for A, B in itertools.combinations(l2, 2):
                jobs.append([(2, A, B)])
        print(f"{fam}: {len(jobs)}", flush=True)
        stats = {"acyc_shell":0, "acyc_strict":0, "acyc_only_shell":0,
                 "survivor":0, "nonacyc":0, "VIOLATION":0}
        survivors = []
        for i, idents in enumerate(jobs):
            try:
                betti, acyc, strict, shell = run(idents, "")
            except Exception as e:
                print(f"  ERROR at {idents}: {e}", flush=True)
                continue
            if not acyc:
                stats["nonacyc"] += 1
                if shell:
                    stats["VIOLATION"] += 1
                    print(f"  VIOLATION Betti={betti}: {idents}",
                          flush=True)
            else:
                if shell: stats["acyc_shell"] += 1
                if strict: stats["acyc_strict"] += 1
                if shell and not strict:
                    stats["acyc_only_shell"] += 1
                    print(f"  ONLY-SHELL: {idents}", flush=True)
                if not shell:
                    stats["survivor"] += 1
                    survivors.append(idents)
                    print(f"  SURVIVOR Betti={betti}: {idents}",
                          flush=True)
            if (i+1) % 50 == 0:
                print(f"  ... {i+1}/{len(jobs)} {stats}", flush=True)
        print(f"{fam.upper()} DONE:", stats, flush=True)
        for sv in survivors:
            print("  survivor:", sv, flush=True)

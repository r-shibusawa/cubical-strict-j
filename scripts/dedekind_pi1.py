"""pi_1 of the triangulation T(W) for the 16 resistant candidates
(O22).  Edge-path presentation: generators = 1-simplices (classes
of W(1)); relations: degenerate 1-simplices = 1, and for each
2-simplex s: d2(s) . d0(s) = d1(s); spanning-tree edges = 1.
Then Todd-Coxeter coset enumeration over the trivial subgroup
(cap 20000 cosets): total collapse => pi_1 = 1."""
import sys, ast
sys.path.insert(0, 'scripts')
from dedekind_site import F, restrict, Quotient
from dedekind_triangulate import coface

def pi1_presentation(W):
    v = W.level(0); e = W.level(1); t = W.level(2)
    vi = {c: i for i, c in enumerate(v)}
    ei = {c: i for i, c in enumerate(e)}
    # faces of 1-simplices: d0, d1 (cofaces q=1: i=0 -> x:=1;
    # i=1 -> x:=0): d_i via coface(i,1)
    ends = []
    for c in e:
        d0 = W.cls(0, restrict(c, coface(0, 1), 2, 1, 0))
        d1 = W.cls(0, restrict(c, coface(1, 1), 2, 1, 0))
        ends.append((vi[d1], vi[d0]))   # edge: d1 -> d0 (convention)
    # degenerate edges: s0 of vertices: the degeneracy [1]->[0]:
    # constant substitution: edge = vertex-degenerate iff its cell
    # is the restriction of a vertex along the unique map
    degen = set()
    for c0 in v:
        # degenerate edge = c0 restricted along the 1-tuple ()...
        # cell of level 1 = vertex components extended constantly
        dc = tuple(tuple(comp[0] for _ in F(1)[0]) for comp in c0)
        degen.add(ei[W.cls(1, dc)])
    rels = []
    for c in t:
        d0 = ei[W.cls(1, restrict(c, coface(0, 2), 2, 2, 1))]
        d1 = ei[W.cls(1, restrict(c, coface(1, 2), 2, 2, 1))]
        d2 = ei[W.cls(1, restrict(c, coface(2, 2), 2, 2, 1))]
        rels.append((d2, d0, d1))   # g_{d2} g_{d0} = g_{d1}
    return len(v), ends, degen, rels

def todd_coxeter(ngen, relwords, cap=20000):
    """coset enumeration of the trivial subgroup in
    <g_0..g_{ngen-1} | relwords>; relword = list of (gen, exp+-1).
    Returns number of cosets or None if cap exceeded."""
    # tables: for each generator, forward and inverse maps
    import itertools
    tab = [dict() for _ in range(2 * ngen)]  # 2g: g, 2g+1: g^-1
    def lit(g, inv): return 2 * g + (1 if inv else 0)
    reps = [0]; parent = {0: 0}
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    nxt = [1]
    pending = []
    def union(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[max(a,b)] = min(a,b); pending.append((a, b))
    def scan(coset, word):
        # apply word to coset, deducing/creating
        cur = find(coset)
        path = [cur]
        for (g, inv) in word:
            l = lit(g, inv)
            cur = find(cur)
            if cur in tab[l]:
                cur = find(tab[l][cur])
            else:
                new = nxt[0]; nxt[0] += 1
                if new > 20000: raise OverflowError
                parent[new] = new
                tab[l][cur] = new
                tab[lit(g, not inv)][new] = cur
                cur = new
            path.append(cur)
        union(path[0], path[-1])
    words = relwords
    # iterate scanning all relators at all cosets until stable
    import collections
    tries = 0
    while True:
        tries += 1
        changed = False
        # process pending merges: merge tables
        while pending:
            a, b = pending.pop()
            a, b = find(a), find(b)
            for l in range(2 * ngen):
                for src in list(tab[l].keys()):
                    s2, d2 = find(src), find(tab[l][src])
                    if s2 != src or find(tab[l][src]) != tab[l][src]:
                        del tab[l][src]
                        if s2 in tab[l]:
                            union(find(tab[l][s2]), d2)
                        else:
                            tab[l][s2] = d2
        size_before = nxt[0]
        live = sorted({find(x) for x in range(nxt[0])
                       if find(x) == x})
        for c in live:
            for w in words:
                try: scan(c, w)
                except OverflowError: return None
        while pending:
            a, b = pending.pop()
            for l in range(2 * ngen):
                for src in list(tab[l].keys()):
                    s2 = find(src); d2 = find(tab[l][src])
                    if s2 != src:
                        del tab[l][src]
                        if s2 in tab[l]: union(find(tab[l][s2]), d2)
                        else: tab[l][s2] = d2
                    elif d2 != tab[l][src]:
                        tab[l][src] = d2
        live2 = {find(x) for x in range(nxt[0]) if find(x) == x}
        if len(live2) == len(live) and nxt[0] == size_before:
            return len(live2)
        if tries > 200: return None

from sweep2_candidates import CANDIDATES as cands
RESIST = [5,6,11,12,13,14,15,16,18,20,21,22,23,24,25,27]
for i in RESIST:
    W = Quotient(2, cands[i], 2)
    nv, ends, degen, rels = pi1_presentation(W)
    ngen = len(ends)
    words = []
    for g in degen: words.append([(g, False)])
    # spanning tree on vertices via edges
    seen = {0}; tree = set()
    changed = True
    while changed:
        changed = False
        for gi, (a, b) in enumerate(ends):
            if a in seen and b not in seen:
                seen.add(b); tree.add(gi); changed = True
            elif b in seen and a not in seen:
                seen.add(a); tree.add(gi); changed = True
    for g in tree: words.append([(g, False)])
    for (a, b, c) in rels:
        words.append([(a, False), (b, False), (c, True)])
    n = todd_coxeter(ngen, words)
    print(f"cand-{i:02d}: verts={nv} gens={ngen} "
          f"degen={len(degen)} tree={len(tree)} rels={len(rels)} "
          f"|pi1| = {n if n is not None else '>cap/unstable'}",
          flush=True)

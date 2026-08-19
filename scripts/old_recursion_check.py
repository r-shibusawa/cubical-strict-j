"""Faithful evaluation of the SECTION-71 recursion, compared with the
closed-form criterion of section 75.

Section 71 (n=3-calibrated) recursion:
    trivial / free / common fixed cell        -> AGREE
    median-reducible (odd blocks, S_m x <z>)  -> AGREE (reduce, recurse)
    block product                             -> SEP iff some factor SEP
    otherwise (mixed, non-median, non-product)-> SEP
Closed form (section 75):
    SEP(H) <=> the reflections of H have no common fixed vertex.

The two agree on every subgroup of B_1..B_3 and first differ at n = 4.
"""
import itertools
from collections import deque, Counter

class Bn:
    def __init__(self, n):
        self.n = n
        self.ELEMS = [(p, s) for p in itertools.permutations(range(n))
                      for s in itertools.product((0, 1), repeat=n)]
        self.idx = {e: i for i, e in enumerate(self.ELEMS)}
        self.NE = len(self.ELEMS)
        self.ID = self.idx[(tuple(range(n)), (0,)*n)]
        def mmr(e1, e2):
            (p1, s1), (p2, s2) = e1, e2
            return (tuple(p2[p1[i]] for i in range(n)),
                    tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
        self.MUL = [[self.idx[mmr(self.ELEMS[a], self.ELEMS[b])]
                     for b in range(self.NE)] for a in range(self.NE)]
        self.INV = [next(b for b in range(self.NE) if self.MUL[a][b] == self.ID)
                    for a in range(self.NE)]
        def cyc(e):
            p, s = e; seen = [False]*n; out = []
            for i in range(n):
                if seen[i]: continue
                sg = s[i]; j = p[i]; seen[i] = True
                while j != i:
                    seen[j] = True; sg ^= s[j]; j = p[j]
                out.append(sg & 1)
            return out
        self.REFL = [a != self.ID and all(g == 0 for g in cyc(self.ELEMS[a]))
                     for a in range(self.NE)]
        self.ACT = []
        for a in range(self.NE):
            p, s = self.ELEMS[a]
            self.ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i)
                                 for i in range(n)) for v in range(1 << n)])
    def close(self, gens):
        S = {self.ID}; dq = deque([self.ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = self.MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    def subgroups(self):
        subs = {frozenset([self.ID]): []}
        frontier = list(subs.items())
        while frontier:
            new = []
            for H, gens in frontier:
                for g in range(self.NE):
                    if g in H: continue
                    H2 = self.close(gens + [g])
                    if H2 not in subs:
                        subs[H2] = gens + [g]; new.append((H2, gens + [g]))
            frontier = new
        return list(subs)
    def fixed_vertex(self, S):
        return any(all(self.ACT[a][v] == v for a in S)
                   for v in range(1 << self.n))
    def orbits(self, H):
        par = list(range(self.n))
        def f(i):
            while par[i] != i: par[i] = par[par[i]]; i = par[i]
            return i
        for a in H:
            p, _ = self.ELEMS[a]
            for i in range(self.n):
                ra, rb = f(i), f(p[i])
                if ra != rb: par[ra] = rb
        gr = {}
        for i in range(self.n): gr.setdefault(f(i), []).append(i)
        return sorted(tuple(v) for v in gr.values())

B = {n: Bn(n) for n in (1, 2, 3, 4)}

def embed(H, A, src, dst):
    """restriction of H to the slot set A, read inside B_{|A|}"""
    A = sorted(A); pos = {v: i for i, v in enumerate(A)}
    out = set()
    for a in H:
        p, s = src.ELEMS[a]
        q = [pos[p[v]] for v in A]; t = [s[v] for v in A]
        out.add(dst.idx[(tuple(q), tuple(t))])
    return frozenset(out)

def median_data(H, G):
    n = G.n; orb = G.orbits(H); k = len(orb)
    parts = []
    for asg in itertools.product(range(k), repeat=k):
        if any(asg[i] > max(asg[:i], default=-1) + 1 for i in range(k)):
            continue
        gr = {}
        for i, b in enumerate(asg): gr.setdefault(b, []).extend(orb[i])
        P = sorted(tuple(sorted(v)) for v in gr.values())
        if all(len(b) % 2 for b in P) and any(len(b) >= 3 for b in P):
            parts.append(P)
    for eps in range(1 << n):
        d = G.idx[(tuple(range(n)), tuple((eps >> i) & 1 for i in range(n)))]
        conj = {a: G.ELEMS[G.MUL[G.MUL[d][a]][G.INV[d]]] for a in H}
        for P in parts:
            if not all(len(set(s[i] for i in b)) == 1
                       for (_, s) in conj.values() for b in P): continue
            k2 = len(P); T = B[k2]
            blk = {}
            for j, b in enumerate(P):
                for i in b: blk[i] = j
            red = set()
            for a, (p, s) in conj.items():
                q = [blk[p[b[0]]] for b in P]
                t = [s[b[0]] for b in P]
                red.add(T.idx[(tuple(q), tuple(t))])
            red = frozenset(red)
            if all(T.MUL[x][y] in red for x in red for y in red):
                return k2, red
    return None

def product_splits(H, G):
    orb = G.orbits(H); out = []
    for r in range(1, len(orb)):
        for sel in itertools.combinations(range(len(orb)), r):
            A = [i for k in sel for i in orb[k]]
            Ac = [i for i in range(G.n) if i not in A]
            def restrict(a, S):
                p, s = G.ELEMS[a]
                q = list(range(G.n)); t = [0]*G.n
                for i in S: q[i] = p[i]; t[i] = s[i]
                return G.idx[(tuple(q), tuple(t))]
            if all(restrict(a, A) in H for a in H):
                out.append((A, Ac))
    return out

memo = {}
def old_fate(n, H):
    G = B[n]
    key = (n, H)
    if key in memo: return memo[key]
    memo[key] = 'AGREE'                      # provisional, no cycles occur
    if len(H) == 1: r = 'AGREE'
    elif not any(G.REFL[a] for a in H): r = 'AGREE'
    elif G.fixed_vertex(H): r = 'AGREE'
    else:
        md = median_data(H, G)
        if md is not None:
            k, red = md; r = old_fate(k, red)
        else:
            sp = product_splits(H, G)
            if sp:
                r = 'AGREE'
                for A, Ac in sp:
                    fa = old_fate(len(A), embed(H, A, G, B[len(A)]))
                    fb = old_fate(len(Ac), embed(H, Ac, G, B[len(Ac)]))
                    if 'SEP' in (fa, fb): r = 'SEP'
            else:
                r = 'SEP'                    # section 71 terminal clause
    memo[key] = r
    return r

def closed(n, H):
    G = B[n]
    R = [a for a in H if G.REFL[a]]
    return 'SEP' if (R and not G.fixed_vertex(R)) else 'AGREE'

for n in (1, 2, 3, 4):
    G = B[n]; subs = G.subgroups()
    diff = [H for H in subs if old_fate(n, H) != closed(n, H)]
    co = Counter(closed(n, H) for H in subs)
    print(f"n={n}: {len(subs)} subgroups, closed form {dict(co)}, "
          f"section-71 recursion differs on {len(diff)}")
    for H in sorted(diff, key=lambda X: (len(X), sorted(X))):
        R = [a for a in H if G.REFL[a]]
        print(f"    |H|={len(H):3d} |<R>|={len(G.close(R)):3d} #R={len(R)}  "
              f"section71={old_fate(n,H)} closed={closed(n,H)}")
        print(f"        H = {[G.ELEMS[a] for a in sorted(H)]}")

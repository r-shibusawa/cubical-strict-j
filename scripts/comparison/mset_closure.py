"""Generic finite-universe test of the finite join question.
For a finite monoid (Cayley table T, product T[a][b] = a*b) and idempotent ideals D, E:
  W_D = {f : f bijective on X.e for every idempotent e in D}   (local isomorphisms for J_D)
  W_{I'} = {f : f bijective on X.e for every idempotent e in D ∩ E}  (I' = M E(D∩E) M).
We enumerate all right M-sets of size <= n (one per isomorphism class), all equivariant maps,
and the two-out-of-three closure of W_D u W_E; we report how many W_{I'}-maps are derived."""
import itertools as it, sys, time
from collections import deque

def generators(T):
    """a small generating set of the monoid: greedy"""
    n = len(T); gens = []; span = {0}
    def close(S):
        S = set(S); q = deque(S)
        while q:
            a = q.popleft()
            for b in list(S):
                for c in (T[a][b], T[b][a]):
                    if c not in S: S.add(c); q.append(c)
        return S
    for g in range(1, n):
        if g not in span:
            gens.append(g); span = close(span | {g})
    return gens

def words(T, gens):
    """express every element as a word in gens (BFS from 1 = element 0)"""
    n = len(T); w = {0: ()}; q = deque([0])
    while q:
        a = q.popleft()
        for g in gens:
            b = T[a][g]
            if b not in w: w[b] = w[a] + (g,); q.append(b)
    assert len(w) == n
    return w

def actions(T, n):
    """all right M-actions on {0..n-1} (labelled), as dict act[(x,m)]"""
    N = len(T); gens = generators(T); W = words(T, gens)
    out = []
    for tabs in it.product(it.product(range(n), repeat=n), repeat=len(gens)):
        gact = {g: tabs[i] for i, g in enumerate(gens)}
        act = {}
        for x in range(n):
            for m in range(N):
                y = x
                for g in W[m]: y = gact[g][y]
                act[(x, m)] = y
        if all(act[(act[(x, a)], b)] == act[(x, T[a][b])] for x in range(n) for a in range(N) for b in range(N)):
            out.append(act)
    return out

def canon(act, n, N):
    best = None
    for p in it.permutations(range(n)):
        tab = [None] * (n * N)
        for x in range(n):
            for m in range(N): tab[p[x] * N + m] = p[act[(x, m)]]
        key = tuple(tab)
        if best is None or key < best: best = key
    return best

def homs(X, Xa, Y, Ya, N):
    gens = []; cov = set()
    for x in X:
        if x not in cov: gens.append(x); cov |= {Xa[(x, m)] for m in range(N)}
    expr = {}
    for g in gens:
        for m in range(N): expr.setdefault(Xa[(g, m)], (g, m))
    res = []
    def rec(i, phi):
        if i == len(gens):
            full = {x: Ya[(phi[expr[x][0]], expr[x][1])] for x in X}
            if all(full[Xa[(x, m)]] == Ya[(full[x], m)] for x in X for m in range(N)):
                res.append(tuple(full[x] for x in X))
            return
        for y in Y:
            phi[gens[i]] = y; rec(i + 1, phi); del phi[gens[i]]
    rec(0, {}); return res

def run(T, D, E, nmax, log=print):
    N = len(T)
    idem = lambda I: [e for e in I if T[e][e] == e]
    ED, EE = idem(D), idem(E); EJ = [e for e in ED if e in E]
    objs = []
    for n in range(1, nmax + 1):
        seen = {}
        for a in actions(T, n):
            c = canon(a, n, N)
            if c not in seen: seen[c] = a
        objs += [(n, a) for a in seen.values()]
    log(f"universe: {len(objs)} M-sets of size <= {nmax}; idempotents D:{ED} E:{EE} D∩E:{EJ}")
    X = [list(range(n)) for n, _ in objs]; A = [a for _, a in objs]; K = len(objs)
    t0 = time.time(); H = {(i, j): homs(X[i], A[i], X[j], A[j], N) for i in range(K) for j in range(K)}
    log(f"{sum(len(v) for v in H.values())} maps ({time.time()-t0:.0f}s)")
    def bij(f, i, j, es):
        for e in es:
            S = {x for x in X[i] if A[i][(x, e)] == x}; Tt = {y for y in X[j] if A[j][(y, e)] == y}
            img = {f[x] for x in S}
            if not (len(img) == len(S) == len(Tt) and img == Tt): return False
        return True
    W = set(); WJ = set()
    for (i, j), fs in H.items():
        for f in fs:
            if bij(f, i, j, ED) or bij(f, i, j, EE) or (i == j and len(set(f)) == len(X[i])): W.add((i, j, f))
            if bij(f, i, j, EJ): WJ.add((i, j, f))
    log(f"|W_D u W_E u Iso| = {len(W)}, |W_I'| = {len(WJ)}")
    changed = True; rounds = 0
    while changed:
        changed = False; rounds += 1
        for (i, j, f) in list(W):
            for k in range(K):
                for g in H[(j, k)]:
                    gf = tuple(g[y] for y in f); gW = (j, k, g) in W; gfW = (i, k, gf) in W
                    if gW and not gfW: W.add((i, k, gf)); changed = True
                    elif gfW and not gW: W.add((j, k, g)); changed = True
                for g in H[(k, i)]:
                    fg = tuple(f[y] for y in g)
                    if (k, j, fg) in W and (k, i, g) not in W: W.add((k, i, g)); changed = True
        log(f" round {rounds}: |W| = {len(W)}; W_I' derived: {len(W & WJ)} / {len(WJ)}")
    return len(WJ - W)

if __name__ == "__main__":
    from threefold_transformation import two_sided_ideals, product
    which = sys.argv[1]; nmax = int(sys.argv[2])
    if which == 'cyc':
        from cycle_monoid import cycle_monoid
        T = cycle_monoid(int(sys.argv[3]), int(sys.argv[4]))
    elif which == 'diamond':
        from threefold_contracted import poset_category, poset_from_edges
        T = poset_category(poset_from_edges(4, [(0,1),(0,2),(0,3),(1,3),(2,3)]), [0,1,2,3])
    elif which == 'nil':
        from nilcycle import T
    elif which == 'small':
        from monoids_small import monoids
        T = list(monoids(int(sys.argv[3])))[int(sys.argv[4])]
    M = frozenset(range(len(T)))
    ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != M]
    pairs = [(A, B) for i, A in enumerate(ideals) for B in ideals[i+1:] if not (A <= B or B <= A)]
    print(f"{len(pairs)} incomparable pairs")
    worst = 0
    for D, E in pairs:
        und = run(T, D, E, nmax); worst = max(worst, und)
        print(f"pair |D|={len(D)} |E|={len(E)}: undecided W_I' maps = {und}")
    print("RESULT undecided total:", worst)

"""The co-tower invariant Lambda(X) = lim_k X (x)_M T2_k, where T2_k is the alternating
DOUBLE-block biset tower (D(x)D)(x)(E(x)E)(x)... (k blocks) with maps multiplying the outer
block into X.  Lambda inverts W_D and W_E (f in W_D => f (x) D (x) D is an iso, since
Hom(f (x) D (x) D, Z) = Hom(f, a_D Z); the D-starting and E-starting towers are mutually
cofinal).  If Lambda(eta_X) is not bijective for the unit eta_X : X -> a_{I'} X, then
eta_X is NOT in W_D v W_E, i.e. W_D v W_E != W_{J_D v J_E}: joins are not preserved.
Cayley table T[a][b] = a*b.  Right M-sets: x*m.  Bisets: left/right actions."""
import itertools as it, sys
from threefold_transformation import two_sided_ideals, product

class UF:
    def __init__(self, elems): self.p = {e: e for e in elems}
    def find(self, x):
        while self.p[x] != x: self.p[x] = self.p[self.p[x]]; x = self.p[x]
        return x
    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b: self.p[a] = b

def build_tower(T, seq):
    """stages[j] for j=0..len(seq)-1: stage j = seq[j] (x) stage j-1 (slots: seq[j] leftmost).
    Each stage: elems (class ids), lact[(m,c)], ract[(c,m)], mu[c] -> class of previous stage, rep."""
    n = len(T)
    D0 = sorted(seq[0])
    st = {'elems': D0, 'lact': {(m, d): T[m][d] for m in range(n) for d in D0},
          'ract': {(d, m): T[d][m] for m in range(n) for d in D0}, 'mu': None, 'rep': {d: (d,) for d in D0}}
    stages = [st]
    for j in range(1, len(seq)):
        Dj = sorted(seq[j]); prev = stages[-1]
        pairs = [(d, t) for d in Dj for t in prev['elems']]
        uf = UF(pairs)
        for d in Dj:
            for t in prev['elems']:
                for m in range(n):
                    uf.union((T[d][m], t), (d, prev['lact'][(m, t)]))
        classes = {}
        for p in pairs: classes.setdefault(uf.find(p), []).append(p)
        elems = list(classes)
        lact = {}; ract = {}; mu = {}; rep = {}
        for c in elems:
            d, t = classes[c][0]; rep[c] = (d,) + prev['rep'][t]
            for m in range(n):
                lact[(m, c)] = uf.find((T[m][d], t))
                ract[(c, m)] = uf.find((d, prev['ract'][(t, m)]))
            mu[c] = prev['lact'][(d, t)]
        stages.append({'elems': elems, 'lact': lact, 'ract': ract, 'mu': mu, 'rep': rep})
    return stages

def right_tensor(X, Xact, stage, n):
    """X (x)_M (stage) for a right M-set X (elems X, Xact[(x,m)]); returns (elems, class-of dict)"""
    pairs = [(x, t) for x in X for t in stage['elems']]
    uf = UF(pairs)
    for x in X:
        for t in stage['elems']:
            for m in range(n):
                uf.union((Xact[(x, m)], t), (x, stage['lact'][(m, t)]))
    cl = {p: uf.find(p) for p in pairs}
    return sorted(set(cl.values())), cl

def cotower(T, X, Xact, stages):
    """Theta_j = X (x) stage j with maps Theta_j -> Theta_{j-1}: [x,t] -> [x, mu(t)].
    Returns list of (elems, cl) and the transition maps as dicts."""
    n = len(T); out = []; maps = []
    for j, st in enumerate(stages):
        elems, cl = right_tensor(X, Xact, st, n); out.append((elems, cl))
        if j > 0:
            prev_cl = out[j - 1][1]
            f = {}
            for (x, t), c in cl.items():
                target = prev_cl[(x, st['mu'][t])]
                if c in f and f[c] != target: raise RuntimeError("transition not well defined")
                f[c] = target
            maps.append(f)
    return out, maps

def limit_sizes(out, maps):
    """stable images in each stage: S_j = image of Theta_k -> Theta_j for k large; sizes and whether
    the transition maps restricted to stable images are bijective (then |lim| = |S_j| eventually)."""
    N = len(out)
    stable = []
    for j in range(N):
        img = set(out[j][0])
        for k in range(j + 1, N):
            # image of Theta_k in Theta_j: compose maps
            cur = set(out[k][0])
            for l in range(k, j, -1):
                cur = {maps[l - 1][c] for c in cur}
            img &= cur
        stable.append(img)
    return [len(s) for s in stable], stable

def hom_right(T, P_elems, P_ract, P_gens, X, Xact):
    """right M-set maps P -> X, P generated (as right M-set) by P_gens; brute force on generator values."""
    n = len(T)
    # express each element of P as gen * m
    expr = {}
    for g in P_gens:
        for m in range(n):
            expr.setdefault(P_ract[(g, m)], (g, m))
    assert set(expr) == set(P_elems), "generators do not generate"
    homs = []
    for vals in it.product(X, repeat=len(P_gens)):
        phi = {}
        ok = True
        gv = dict(zip(P_gens, vals))
        for p in P_elems:
            g, m = expr[p]; phi[p] = Xact[(gv[g], m)]
        # check equivariance
        for p in P_elems:
            for m in range(n):
                if phi[P_ract[(p, m)]] != Xact[(phi[p], m)]: ok = False; break
            if not ok: break
        if ok: homs.append(tuple(phi[p] for p in P_elems))
    return homs

def analyse(T, D, E, kblocks=5, names=None, log=print):
    n = len(T); M = frozenset(range(n))
    # I' = largest idempotent ideal in D∩E = M E(D∩E) M
    I = D & E
    idem = [e for e in I if T[e][e] == e]
    Ip = frozenset(T[T[a][e]][b] for e in idem for a in range(n) for b in range(n))
    assert product(T, Ip, Ip) == Ip
    seq = []
    for b in range(kblocks):
        seq += [D, D] if b % 2 == 0 else [E, E]
    stages = build_tower(T, seq)
    # X = M (free right M-set)
    Xm = list(range(n)); Xm_act = {(x, m): T[x][m] for x in Xm for m in range(n)}
    outM, mapsM = cotower(T, Xm, Xm_act, stages)
    sizesM, stM = limit_sizes(outM, mapsM)
    # A = a_{I'} M = Hom_M(I'(x)I', M) as a right M-set
    Pst = build_tower(T, [Ip, Ip])[1]
    P_elems = Pst['elems']; P_ract = Pst['ract']
    # right generators of P: classes [i, i'] ... take all classes whose rep first slot is an idempotent? use all elems as gens (safe but slow) -> reduce greedily
    gens = []; covered = set()
    for p in P_elems:
        if p not in covered:
            gens.append(p); covered |= {P_ract[(p, m)] for m in range(n)}
    homs = hom_right(T, P_elems, P_ract, gens, Xm, Xm_act)
    A = list(range(len(homs))); hidx = {h: i for i, h in enumerate(homs)}
    # right action on A: (phi*m)(p) = phi(m p)  -- needs left action of m on P
    P_lact = Pst['lact']
    A_act = {}
    for i, h in enumerate(homs):
        phi = dict(zip(P_elems, h))
        for m in range(n):
            A_act[(i, m)] = hidx[tuple(phi[P_lact[(m, p)]] for p in P_elems)]
    # unit eta: M -> A, x -> (p -> x * (product of p))... eta(x)(p) = x * mult(p) where mult(p) = product of slots
    mult = {p: T[Pst['rep'][p][0]][Pst['rep'][p][1]] for p in P_elems}
    eta = {x: hidx[tuple(T[x][mult[p]] for p in P_elems)] for x in Xm}
    outA, mapsA = cotower(T, A, A_act, stages)
    sizesA, stA = limit_sizes(outA, mapsA)
    # induced map on stage j: [x,t] -> [eta(x), t]; check bijectivity on stable images at the last stage
    j = len(stages) - 1
    clM = outM[j][1]; clA = outA[j][1]
    induced = {}
    for (x, t), c in clM.items(): induced[c] = clA[(eta[x], t)]
    img = {induced[c] for c in stM[j]}
    inj = len(img) == len(stM[j]); surj = img >= stA[j]
    log(f"  |I'|={len(Ip)} |P|={len(P_elems)} |a M|={len(A)} ; tower sizes (blocks): M: {[len(o[0]) for o in outM]} stable {sizesM}; A: {[len(o[0]) for o in outA]} stable {sizesA}")
    log(f"  Lambda(eta) on stable images of the last stage: injective={inj} surjective={surj}  (|Lambda M|~{sizesM[-1]}, |Lambda A|~{sizesA[-1]})")
    return inj and surj

if __name__ == "__main__":
    from cycle_monoid import cycle_monoid
    for n, L in [(2, 3), (2, 4), (3, 4)]:
        T = cycle_monoid(n, L); N = len(T); M = frozenset(range(N))
        ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != M]
        pairs = [(D, E) for i, D in enumerate(ideals) for E in ideals[i + 1:] if not (D <= E or E <= D)]
        print(f"cycle monoid n={n} L={L} |M|={N}: {len(pairs)} incomparable pairs")
        for D, E in pairs[:4]:
            print(f" pair |D|={len(D)} |E|={len(E)}")
            ok = analyse(T, D, E, kblocks=5 if N < 20 else 4)
            print("  => Lambda(eta) bijective:", ok, flush=True)

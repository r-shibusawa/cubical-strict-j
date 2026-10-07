"""Finite-universe 2-out-of-3 closure test for W_D v W_E on a finite monoid.
Universe: a finite family of right M-sets (M, a_{I'}M, plus-tower stages Phi_k M, P = I'(x)I', ...).
All equivariant maps between them are enumerated (backtracking on generators); W_D-membership of
f is decided by a_D f = Hom(D(x)D, f) bijective.  The closure of W_D u W_E under composition and
two-out-of-three inside the universe is computed; if it contains the unit eta : M -> a_{I'} M, then
eta is in the join (positive certificate)."""
import itertools as it, sys, time
from threefold_transformation import two_sided_ideals, product
from cotower_invariant import build_tower, UF

def generators(elems, act, n):
    g = []; cov = set()
    for p in elems:
        if p not in cov: g.append(p); cov |= {act[(p, m)] for m in range(n)}
    return g

def homs(X, Y, n):
    """all right-M-set maps X -> Y; X=(elems, act), Y=(elems, act). Backtracking over generators."""
    Xe, Xa = X; Ye, Ya = Y
    gens = generators(Xe, Xa, n)
    # orbit expressions: each x = g * m
    expr = {}
    for g in gens:
        for m in range(n): expr.setdefault(Xa[(g, m)], (g, m))
    result = []
    phi = {}
    def consistent():
        for x in Xe:
            g, m = expr[x]
            if g in phi: phi[x] = Ya[(phi[g], m)]
        for x in Xe:
            if x in phi:
                for m in range(n):
                    y = Xa[(x, m)]
                    if y in phi and phi[y] != Ya[(phi[x], m)]: return False
        return True
    def rec(i):
        if i == len(gens):
            result.append(tuple(phi[x] for x in Xe)); return
        g = gens[i]
        for y in Ye:
            saved = dict(phi)
            phi[g] = y
            if consistent(): rec(i + 1)
            phi.clear(); phi.update(saved)
    rec(0)
    return result

def sheafify_maps(T, DD, X, n):
    """a_D X = Hom(DD, X) where DD = biset stage viewed as a right M-set; backtracking enumeration."""
    return homs((DD['elems'], DD['ract']), X, n)

def run(T, D, E, kmax=4, log=print):
    n = len(T); M = frozenset(range(n))
    I = D & E; idem = [e for e in I if T[e][e] == e]
    Ip = frozenset(T[T[a][e]][b] for e in idem for a in range(n) for b in range(n))
    # objects
    objs = {}
    Xm = (list(range(n)), {(x, m): T[x][m] for x in range(n) for m in range(n)}); objs['M'] = Xm
    def hom_object(B, X):  # Hom(B, X) as right M-set, B a biset stage
        hs = sheafify_maps(T, B, X, n)
        idx = {h: i for i, h in enumerate(hs)}
        act = {}
        for i, h in enumerate(hs):
            phi = dict(zip(B['elems'], h))
            for m in range(n): act[(i, m)] = idx[tuple(phi[B['lact'][(m, p)]] for p in B['elems'])]
        return (list(range(len(hs))), act), hs
    DD = build_tower(T, [D, D])[1]; EE = build_tower(T, [E, E])[1]; PP = build_tower(T, [Ip, Ip])[1]
    A, Ahs = hom_object(PP, Xm); objs['A'] = A
    Pobj = (PP['elems'], PP['ract']); objs['P'] = Pobj
    seq = []
    for j in range(kmax): seq.append(D if j % 2 == 0 else E)
    stages = build_tower(T, seq)
    for k in range(1, kmax + 1):
        Ph, _ = hom_object(stages[k - 1], Xm); objs[f'Phi{k}'] = Ph
    # relabel every object so that elements are 0..N-1
    for k in list(objs):
        el, act = objs[k]; idx = {e: i for i, e in enumerate(el)}
        objs[k] = (list(range(len(el))), {(idx[e], m): idx[act[(e, m)]] for e in el for m in range(n)})
        if k == 'A': Aidx_map = idx
    log("objects: " + ", ".join(f"{k}({len(v[0])})" for k, v in objs.items()))
    names = list(objs)
    # all homs
    H = {}
    t0 = time.time()
    for X in names:
        for Y in names:
            t1 = time.time(); H[(X, Y)] = homs(objs[X], objs[Y], n)
            log(f"  Hom({X},{Y}): {len(H[(X,Y)])} maps, gens={len(generators(objs[X][0], objs[X][1], n))} ({time.time()-t1:.0f}s)")
    log(f"hom sizes: " + ", ".join(f"{X}->{Y}:{len(H[(X,Y)])}" for X in names for Y in names) + f"  ({time.time()-t0:.0f}s)")
    # W_D membership via a_D: precompute Hom(DD, X) for each object and the induced map
    aD = {X: sheafify_maps(T, DD, objs[X], n) for X in names}
    aE = {X: sheafify_maps(T, EE, objs[X], n) for X in names}
    def in_W(f, X, Y, a, B):
        # a_B f : Hom(B,X) -> Hom(B,Y), phi -> f o phi ; bijective?
        img = set()
        for h in a[X]:
            img.add(tuple(f[x] for x in h))
        return len(img) == len(a[X]) == len(a[Y]) and img == set(a[Y])
    W = set()
    for (X, Y), fs in H.items():
        for f in fs:
            if in_W(f, X, Y, aD, DD) or in_W(f, X, Y, aE, EE): W.add((X, Y, f))
            elif X == Y and len(set(f)) == len(objs[X][0]): W.add((X, Y, f))  # iso
    log(f"|W_D u W_E u Iso| in universe: {len(W)} of {sum(len(v) for v in H.values())} maps")
    # eta: M -> A
    Pmult = {p: T[PP['rep'][p][0]][PP['rep'][p][1]] for p in PP['elems']}
    Aidx = {h: i for i, h in enumerate(Ahs)}
    eta = tuple(Aidx[tuple(T[x][Pmult[p]] for p in PP['elems'])] for x in range(n))
    log(f"eta in W_D u W_E: {('M','A',eta) in W}")
    # closure
    changed = True; rounds = 0
    while changed:
        changed = False; rounds += 1
        for X in names:
            for Y in names:
                for Z in names:
                    for f in H[(X, Y)]:
                        fW = (X, Y, f) in W
                        for g in H[(Y, Z)]:
                            gW = (Y, Z, g) in W
                            gf = tuple(g[y] for y in f)
                            gfW = (X, Z, gf) in W
                            if fW and gW and not gfW: W.add((X, Z, gf)); changed = True
                            elif gfW and gW and not fW: W.add((X, Y, f)); changed = True
                            elif gfW and fW and not gW: W.add((Y, Z, g)); changed = True
        log(f" round {rounds}: |W|={len(W)}  eta in W: {('M','A',eta) in W}")
    return ('M', 'A', eta) in W

if __name__ == "__main__":
    from cycle_monoid import cycle_monoid
    T = cycle_monoid(2, 3); n = len(T); M = frozenset(range(n))
    ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != M]
    D, E = [(A, B) for i, A in enumerate(ideals) for B in ideals[i + 1:] if not (A <= B or B <= A)][0]
    print("result:", run(T, D, E, kmax=int(sys.argv[1]) if len(sys.argv) > 1 else 4))

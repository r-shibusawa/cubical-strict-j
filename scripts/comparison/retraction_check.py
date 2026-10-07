"""Check of Lemmas 2.3-2.4 of Paper0034 on small monoids: with P = I'(x)I', T_k = D_k(x)...(x)D_1,
  m_k : P (x) T_k -> P,  [i,i',d_k..d_1] -> [i, i' d_k ... d_1]   is bijective (classes),
  r_k : T_k -> P,        [d_k..d_1] -> [d_k..d_{j+1} product, d_j..d_1 product]  (k >= 4m, j = 2m),
  r_k o eps_k = m_k  where eps_k [p, t] = (product of p) . t.
Classes are computed incrementally (cotower_invariant.build_tower)."""
import sys
from cotower_invariant import build_tower
from threefold_transformation import two_sided_ideals, product

def check(T, D, E, log=print):
    N = len(T); M = frozenset(range(N))
    idem = [e for e in D & E if T[e][e] == e]
    Ip = frozenset(T[T[a][e]][b] for e in idem for a in range(N) for b in range(N))
    prod = lambda A, B: frozenset(T[a][b] for a in A for b in B)
    m = 1
    for first, second in ((D, E), (E, D)):
        Pp = prod(first, second); mm = 1
        while Pp != Ip: Pp = prod(Pp, prod(first, second)); mm += 1
        m = max(m, mm)
    k = 4 * m; j = 2 * m
    seqT = [D if i % 2 == 0 else E for i in range(k)]          # D_1 = D rightmost first
    stT = build_tower(T, seqT)[-1]                              # T_k
    stPT = build_tower(T, seqT + [Ip, Ip])[-1]                  # P (x) T_k  (I' (x) I' (x) T_k)
    stP = build_tower(T, [Ip, Ip])[-1]                          # P
    # class lookup helpers via representatives: we need class-of for arbitrary tuples -> rebuild union-find? use rep->class via 'rep' dicts
    # build a map from tuple -> class using the stored rep of each class is not available for all tuples; instead
    # recompute classes with a direct union-find over all tuples for P (small) and use multiplicative images.
    import itertools as it
    from tensor_multi import multitensor
    ufP = multitensor(T, [Ip, Ip])
    def Pclass(a, b): return ufP.find((a, b))
    def mult(seq_vals):
        r = seq_vals[0]
        for x in seq_vals[1:]: r = T[r][x]
        return r
    # m_k on representatives of P(x)T_k classes
    imgs = {}
    for c in stPT['elems']:
        rep = stPT['rep'][c]            # (i, i', d_k, ..., d_1)
        i, ip = rep[0], rep[1]; ds = rep[2:]
        imgs[c] = Pclass(i, T[ip][mult(ds)] if ds else ip)
    bij = len(set(imgs.values())) == len(stPT['elems']) == len(set(ufP.find(t) for t in it.product(sorted(Ip), repeat=2)))
    # r_k o eps_k vs m_k on representatives
    ok = True
    for c in stPT['elems']:
        rep = stPT['rep'][c]; i, ip = rep[0], rep[1]; ds = list(rep[2:])
        pbar = T[i][ip]
        # eps: [p, t] -> (pbar d_k, d_{k-1}, ..., d_1)
        t2 = [T[pbar][ds[0]]] + ds[1:]
        A = mult(t2[:k - j]); B = mult(t2[k - j:])
        if Pclass(A, B) != imgs[c]: ok = False; break
    log(f"  |D|={len(D)} |E|={len(E)} |I'|={len(Ip)} m={m} k={k}: |T_k|={len(stT['elems'])} |P⊗T_k|={len(stPT['elems'])} |P|={len(stP['elems'])}; m_k bijective={bij}; r_k∘eps_k=m_k on reps={ok}")
    return bij and ok

if __name__ == "__main__":
    which = sys.argv[1]
    if which == 'nil':
        from nilcycle import T
    elif which == 'cyc':
        from cycle_monoid import cycle_monoid; T = cycle_monoid(int(sys.argv[2]), int(sys.argv[3]))
    elif which == 'small':
        from monoids_small import monoids; T = list(monoids(int(sys.argv[2])))[int(sys.argv[3])]
    elif which == 'diamond':
        from threefold_contracted import poset_category, poset_from_edges
        T = poset_category(poset_from_edges(4, [(0,1),(0,2),(0,3),(1,3),(2,3)]), [0,1,2,3])
    M = frozenset(range(len(T)))
    ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != M]
    allok = True
    for i, D in enumerate(ideals):
        for E in ideals[i+1:]:
            if D <= E or E <= D: continue
            allok &= check(T, D, E)
    print("ALL OK:", allok)

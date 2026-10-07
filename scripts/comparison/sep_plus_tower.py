"""Search for a canonical tower reaching the join sheafification: words in the four operations
  +D (plus construction X^{+D} = Hom_M(D, X)),  +E,
  ^D (separated quotient: identify x ~ x' iff x d = x' d for all d in D),  ^E,
applied to every right M-set X of size <= n; a word 'works' for X if the result is an I'-sheaf.
Each unit X -> X^{+D}, X -> X^{^D} lies in W_D, so a word working for all X gives a natural
transformation id => P into I'-sheaves with components in the join, hence (join theorem)
W_D v W_E = W_{I'}.  Reports the shortest words working for all test objects."""
import itertools as it, sys
from mset_closure import actions, canon, homs

def plus(T, I, X, Xa):
    """Hom_M(I, X): I a right ideal (sub right M-set of M), X right M-set; result as (elems, act)"""
    N = len(T); Ie = sorted(I); Ia = {(d, m): T[d][m] for d in Ie for m in range(N)}
    hs = homs(Ie, Ia, X, Xa, N)
    idx = {h: i for i, h in enumerate(hs)}
    act = {}
    for i, h in enumerate(hs):
        phi = dict(zip(Ie, h))
        for m in range(N): act[(i, m)] = idx[tuple(phi[T[m][d]] for d in Ie)]
    return list(range(len(hs))), act

def sep(T, I, X, Xa):
    N = len(T)
    key = {x: tuple(Xa[(x, d)] for d in sorted(I)) for x in X}
    classes = {}
    for x in X: classes.setdefault(key[x], []).append(x)
    rep = {x: min(classes[key[x]]) for x in X}
    elems = sorted(set(rep.values())); idx = {e: i for i, e in enumerate(elems)}
    act = {(idx[e], m): idx[rep[Xa[(e, m)]]] for e in elems for m in range(N)}
    return list(range(len(elems))), act

def is_sheaf(T, Ip, X, Xa):
    """X is an I'-sheaf iff the unit X -> Hom(I'⊗I', X) is bijective; here one checks the plus unit twice"""
    N = len(T)
    P1, P1a = plus(T, Ip, X, Xa)
    if len(P1) != len(X): return False
    P2, P2a = plus(T, Ip, P1, P1a)
    return len(P2) == len(X)

def run(T, D, E, nmax, maxlen=6, log=print):
    N = len(T); M = frozenset(range(N))
    idem = [e for e in D & E if T[e][e] == e]
    Ip = frozenset(T[T[a][e]][b] for e in idem for a in range(N) for b in range(N))
    objs = []
    for n in range(1, nmax + 1):
        seen = {}
        for a in actions(T, n):
            c = canon(a, n, N)
            if c not in seen: seen[c] = a
        objs += [(list(range(n)), a) for a in seen.values()]
    log(f"{len(objs)} test objects (size <= {nmax}); |I'| = {len(Ip)}")
    ops = {'+D': lambda X, Xa: plus(T, D, X, Xa), '+E': lambda X, Xa: plus(T, E, X, Xa),
           '^D': lambda X, Xa: sep(T, D, X, Xa), '^E': lambda X, Xa: sep(T, E, X, Xa)}
    good = []
    for L in range(1, maxlen + 1):
        for word in it.product(ops, repeat=L):
            if any(word[i] == word[i + 1] for i in range(L - 1)): continue
            ok = True
            for X, Xa in objs:
                Y, Ya = X, Xa
                for w in word:
                    Y, Ya = ops[w](Y, Ya)
                    if len(Y) > 60: ok = False; break
                if not ok or not is_sheaf(T, Ip, Y, Ya): ok = False; break
            if ok: good.append(word); log(f"  word works for all: {' '.join(word)}")
        if good: break
    if not good: log("  no word up to length", maxlen)
    return good

if __name__ == "__main__":
    from threefold_transformation import two_sided_ideals, product
    which = sys.argv[1]; nmax = int(sys.argv[2])
    if which == 'nil':
        from nilcycle import T
    elif which == 'cyc':
        from cycle_monoid import cycle_monoid; T = cycle_monoid(int(sys.argv[3]), int(sys.argv[4]))
    elif which == 'diamond':
        from threefold_contracted import poset_category, poset_from_edges
        T = poset_category(poset_from_edges(4, [(0,1),(0,2),(0,3),(1,3),(2,3)]), [0,1,2,3])
    elif which == 'small':
        from monoids_small import monoids; T = list(monoids(int(sys.argv[3])))[int(sys.argv[4])]
    M = frozenset(range(len(T)))
    ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != M]
    pairs = [(A, B) for i, A in enumerate(ideals) for B in ideals[i+1:] if not (A <= B or B <= A)]
    for D, E in pairs:
        print(f"pair |D|={len(D)} |E|={len(E)}"); run(T, D, E, nmax)

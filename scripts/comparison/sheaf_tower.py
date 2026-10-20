"""Does the tower of alternating sheafifications a_E a_D a_E a_D ... reach the join sheafification
uniformly when the ideal chain (DE)^k stabilises?

On a monoid M with idempotent two-sided ideals D, E, a_D X = X^{+D+D} (plus construction twice).  The
join of the two classes of local isomorphisms equals the class for J_{I'} whenever the chain stabilises
(here on every finite monoid), by the criterion of the paper on joins of Lawvere-Tierney topologies.
This script tests whether the stronger, classical sufficient condition of the join theorem --
(a_E a_D)^k X is an I'-sheaf for all X, for one k -- holds, on the order-8 contracted monoid of the
nil example (cf. the finite-category paper, Section 7) and on small cyclic contracted monoids.
Words in +D, +E of any shape (repeated letters allowed) up to a given length are tried.
"""
import itertools as it, sys
from sep_plus_tower import plus, is_sheaf
from mset_closure import actions, canon

def test(T, D, E, nmax, maxlen, log=print):
    N = len(T)
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
    ops = {'+D': lambda X, Xa: plus(T, D, X, Xa), '+E': lambda X, Xa: plus(T, E, X, Xa)}
    def works(word):
        for X, Xa in objs:
            Y, Ya = X, Xa
            for w in word:
                Y, Ya = ops[w](Y, Ya)
                if len(Y) > 80: return None
            if not is_sheaf(T, Ip, Y, Ya): return False
        return True
    # the sheafification tower (a_E a_D)^k = (+D +D +E +E)^k and the mixed tower
    for k in range(1, maxlen // 4 + 1):
        for word in [('+D', '+D', '+E', '+E') * k, ('+E', '+E', '+D', '+D') * k]:
            r = works(word)
            log(f"  {' '.join(word)} : {'sheaf for all' if r else ('too big' if r is None else 'NOT a sheaf for some X')}")
    best = None
    for L in range(1, maxlen + 1):
        for word in it.product(ops, repeat=L):
            if works(word): best = word; break
        if best: break
    log("  shortest pure plus word working for all test objects:", ' '.join(best) if best else f"none up to length {maxlen}")

if __name__ == "__main__":
    from threefold_transformation import two_sided_ideals, product
    which = sys.argv[1]; nmax = int(sys.argv[2]); maxlen = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    if which == 'nil':
        from nilcycle import T
    else:
        from cycle_monoid import cycle_monoid; T = cycle_monoid(int(sys.argv[4]), int(sys.argv[5]))
    N = len(T)
    ideals = [I for I in two_sided_ideals(T) if I and product(T, I, I) == I and I != frozenset(range(N))]
    for D in ideals:
        for E in ideals:
            if D < E or E < D or D == E: continue
            if product(T, D, E) == product(T, E, D) == D & E: continue
            print(f"pair |D|={len(D)} |E|={len(E)}  D∩E idempotent: {product(T, D & E, D & E) == D & E}")
            test(T, D, E, nmax, maxlen)

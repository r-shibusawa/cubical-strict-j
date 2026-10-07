"""Check of the proof strategy for the finite join theorem:
  (2) alternating separated quotients Q_D, Q_E, ... reach the J-separated quotient (J = E(D) ∩ E(E))
      in at most 2m steps (m with (DE)^m = I'), each quotient map in W_D or W_E;
  (3) on a J-separated Y the plus tower Y -> Y^{+D} -> Y^{+D+E} -> ... consists of J-separated objects
      with injective units, and reaches the I'-sheaf a_{I'} Y (then stays).
For every right M-set X of size <= n we verify both and report the numbers of steps."""
import sys
from mset_closure import actions, canon
from sep_plus_tower import plus, sep, is_sheaf

def jsep(T, Ip, X, Xa):
    """is X separated for J_{I'}: x.a = y.a for all a in the ideal I' implies x = y"""
    for x in X:
        for y in X:
            if x < y and all(Xa[(x, a)] == Xa[(y, a)] for a in Ip):
                return False
    return True

def run(T, D, E, nmax, log=print):
    N = len(T); M = frozenset(range(N))
    ED = [e for e in D if T[e][e] == e]; EE = [e for e in E if T[e][e] == e]; EJ = [e for e in ED if e in E]
    Ip = frozenset(T[T[a][e]][b] for e in EJ for a in range(N) for b in range(N))
    # m with (DE)^m = I'
    prod = lambda A, B: frozenset(T[a][b] for a in A for b in B)
    m = 1
    for first, second in ((D, E), (E, D)):
        P = prod(first, second); mm = 1
        while P != Ip: P = prod(P, prod(first, second)); mm += 1
        m = max(m, mm)
    objs = []
    for n in range(1, nmax + 1):
        seen = {}
        for a in actions(T, n):
            c = canon(a, n, N)
            if c not in seen: seen[c] = a
        objs += [(list(range(n)), a) for a in seen.values()]
    log(f"|M|={N} |D|={len(D)} |E|={len(E)} |I'|={len(Ip)} m={m}; {len(objs)} test objects")
    maxq = 0; maxp = 0; bad = 0
    for X, Xa in objs:
        Y, Ya = X, Xa; q = 0
        while not jsep(T, Ip, Y, Ya):
            Y, Ya = (sep(T, D, Y, Ya) if q % 2 == 0 else sep(T, E, Y, Ya)); q += 1
            if q > 2 * m + 2: break
        if not jsep(T, Ip, Y, Ya): bad += 1; log("  quotient tower did not reach J-separated:", len(X)); continue
        maxq = max(maxq, q)
        # plus tower on Y
        Z, Za = Y, Ya; p = 0; ok = True
        while not is_sheaf(T, Ip, Z, Za):
            Z2, Z2a = (plus(T, D, Z, Za) if p % 2 == 0 else plus(T, E, Z, Za)); p += 1
            if not jsep(T, Ip, Z2, Z2a): ok = False; log("  plus stage not J-separated!"); break
            if len(Z2) < len(Z): ok = False; log("  size decreased: unit not injective!"); break
            Z, Za = Z2, Z2a
            if p > 12 or len(Z) > 400: ok = False; log("  plus tower too long/large"); break
        if not ok: bad += 1; continue
        maxp = max(maxp, p)
    log(f"  all {len(objs)} objects OK: {bad == 0}; max quotient steps {maxq} (bound 2m={2*m}), max plus steps {maxp}")
    return bad

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
    tot = 0
    for D, E in pairs: tot += run(T, D, E, nmax)
    print("TOTAL failures:", tot)

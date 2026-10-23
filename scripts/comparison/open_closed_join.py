"""Joins of an open or a closed nucleus with an arbitrary nucleus on finite frames.

A finite frame is taken as the lattice of up-sets of a small poset (a finite distributive lattice).  Sublocales
are the subsets closed under meets and under x -> s for all x (s in the subset); the nucleus of a sublocale S
is n(x) = meet of {s in S : s >= x}, and the join of two nuclei is the nucleus of the intersection of their
sublocales.  The script checks, for every sublocale S and every element a:
    (u_a v n)(x) = a -> n(x)      (open nucleus u_a(x) = a -> x; so u_a v n = u_a o n, k = 1),
    (c_a v n)(x) = n(a v x)       (closed nucleus c_a(x) = a v x; so c_a v n = n o c_a, k = 1),
and the one-sided commutations n u_a <= u_a n and c_a n <= n c_a that imply them; it also counts the pairs of
sublocales (S, S') for which neither composite n n' nor n' n is already the join (k >= 2 needed), and checks the
characterisations
    n v m = n o m for all m  <=>  n(x) lies in {y -> x : y in L} for all x   (on a finite frame: n open),
    n v m = m o n for all m  <=>  n is closed.
"""
import itertools as it

def upsets(poset_le, n):
    els = range(n)
    ups = []
    for bits in range(1 << n):
        U = {i for i in els if bits >> i & 1}
        if all((j in U) for i in U for j in els if poset_le(i, j)):
            ups.append(frozenset(U))
    return ups

class Frame:
    def __init__(self, ups):
        self.L = ups; self.top = max(ups, key=len); self.bot = frozenset()
    def le(self, x, y): return x <= y
    def meet(self, x, y): return x & y
    def join(self, x, y): return x | y
    def imp(self, a, x):
        # largest up-set y with y & a <= x
        cands = [y for y in self.L if (y & a) <= x]
        return max(cands, key=len) if cands else None
    def is_sublocale(self, S):
        return self.top in S and all(self.meet(s, t) in S for s in S for t in S) and all(self.imp(x, s) in S for x in self.L for s in S)
    def nucleus(self, S):
        def n(x):
            cands = [s for s in S if x <= s]
            r = self.top
            for s in cands: r = r & s
            return r
        return n

def analyse(poset_le, n, name):
    F = Frame(upsets(poset_le, n)); L = F.L
    subs = [frozenset(S) for r in range(1, len(L) + 1) for S in it.combinations(L, r) if F.is_sublocale(frozenset(S))]
    nuc = {S: F.nucleus(S) for S in subs}
    bad_open = bad_closed = bad_ineq = 0; pairs_k2 = 0; total_pairs = 0
    for S in subs:
        nS = nuc[S]
        for a in L:
            ua = lambda x, a=a: F.imp(a, x); ca = lambda x, a=a: F.join(a, x)
            Sua = frozenset(x for x in L if ua(x) == x); Sca = frozenset(x for x in L if ca(x) == x)
            joinU = nuc[S & Sua]; joinC = nuc[S & Sca]
            for x in L:
                if joinU(x) != F.imp(a, nS(x)): bad_open += 1
                if joinC(x) != nS(F.join(a, x)): bad_closed += 1
                if not (nS(ua(x)) <= ua(nS(x))) or not (ca(nS(x)) <= nS(ca(x))): bad_ineq += 1
    for S, T in it.combinations(subs, 2):
        total_pairs += 1
        nS, nT = nuc[S], nuc[T]; j = nuc[S & T]
        if not all(nS(nT(x)) == j(x) for x in L) and not all(nT(nS(x)) == j(x) for x in L): pairs_k2 += 1
    print(f"{name}: |L|={len(L)}, sublocales={len(subs)}; open identity failures={bad_open}, closed={bad_closed}, "
          f"inequality failures={bad_ineq}; pairs needing k>=2: {pairs_k2}/{total_pairs}")
    opens = {frozenset(x for x in L if F.imp(a, x) == x) for a in L}
    closeds = {frozenset(x for x in L if F.join(a, x) == x) for a in L}
    last = {S for S in subs if all(nuc[T](nuc[S](x)) <= nuc[S](nuc[T](x)) for T in subs for x in L)}   # n v m = n o m for all m
    first = {S for S in subs if all(nuc[S](nuc[T](x)) <= nuc[T](nuc[S](x)) for T in subs for x in L)}  # n v m = m o n for all m
    bx = {S for S in subs if all(any(F.imp(y, x) == nuc[S](x) for y in L) for x in L)}                  # n(x) in b(x) for all x
    print(f"   'n v m = n o m for all m': {len(last)} nuclei = opens: {last == opens}, = those with n(x) in b(x): {last == bx}; "
          f"'n v m = m o n for all m': {len(first)} nuclei = closeds: {first == closeds}")

if __name__ == "__main__":
    analyse(lambda i, j: i <= j, 3, "3-chain (frame = 4-chain)")
    analyse(lambda i, j: i == j, 3, "3-antichain (frame = 2^3)")
    analyse(lambda i, j: i == j or (i == 0 and j in (1, 2)), 3, "V-poset 0<1, 0<2")
    analyse(lambda i, j: i == j or (j == 2 and i in (0, 1)), 3, "Lambda-poset 0<2, 1<2")
    analyse(lambda i, j: i == j or (i, j) in {(0, 2), (1, 2), (0, 3), (1, 3)}, 4, "2+2 crown")

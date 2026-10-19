"""Alternating chains of idempotent ideals in a finite category.

For idempotent two-sided ideals D, E of a finite category, let m be the first index with
(DE)^m = (DE)^{m+1} =: I'.  Checked here:
  (1) I' I' = I', D I' = I' D = E I' = I' E = I', (ED)^{m+1} = I';
  (2) every alternating product of at least 2(m+1) factors equals I';
  (3) (ED)^m = I' can FAIL (the two-object category 0 -> 1 with D, E the ideals of arrows
      through 0, respectively through 1: DE = {}, ED = {a}).
A finite category is given by a list of arrows with a partial composition table comp[f][g] =
f o g (None if not composable).  Random examples: transformation monoids and the arrow category
of random finite posets."""
import itertools as it, random, sys

def ideal_product(comp, A, B):
    return frozenset(comp[f][g] for f in A for g in B if comp[f][g] is not None)

def is_ideal(comp, n, A):
    return all(comp[f][g] in A for f in A for g in range(n) if comp[f][g] is not None) and \
           all(comp[g][f] in A for f in A for g in range(n) if comp[g][f] is not None)

def two_sided_ideals(comp, n, limit=4096):
    gen = {}
    for f in range(n):
        S = {f}; frontier = [f]
        while frontier:
            h = frontier.pop()
            for g in range(n):
                for x in (comp[h][g], comp[g][h]):
                    if x is not None and x not in S: S.add(x); frontier.append(x)
        gen[f] = frozenset(S)
    ideals = {frozenset()}
    for f in range(n):
        new = {I | gen[f] for I in ideals}
        ideals |= new
        if len(ideals) > limit: return None
    return ideals

def chain(comp, D, E):
    A = ideal_product(comp, D, E); seq = [A]
    while True:
        B = ideal_product(comp, ideal_product(comp, A, D), E)
        if B == A: return seq
        A = B; seq.append(A)

def alt_products(comp, D, E, length, start):
    P = start
    letters = [D, E] if start is D else [E, D]
    P = letters[0]
    for i in range(1, length): P = ideal_product(comp, P, letters[i % 2])
    return P

def check_pair(comp, D, E):
    seq = chain(comp, D, E); m = len(seq); Ip = seq[-1]
    assert ideal_product(comp, Ip, Ip) == Ip
    for X in (D, E):
        assert ideal_product(comp, X, Ip) == Ip and ideal_product(comp, Ip, X) == Ip
    seqED = chain(comp, E, D)
    EDm1 = alt_products(comp, D, E, 2 * (m + 1), E)
    assert EDm1 == Ip, "(ED)^{m+1} != I'"
    for L in range(2 * (m + 1), 2 * (m + 1) + 3):
        assert alt_products(comp, D, E, L, D) == Ip and alt_products(comp, D, E, L, E) == Ip
    EDm = alt_products(comp, D, E, 2 * m, E)
    return m, EDm == Ip

def transformation_monoid(n, k, rng):
    gens = [tuple(rng.randrange(n) for _ in range(n)) for _ in range(k)]
    elems = {tuple(range(n))}; frontier = list(elems)
    while frontier:
        f = frontier.pop()
        for g in gens:
            h = tuple(g[f[i]] for i in range(n))
            if h not in elems: elems.add(h); frontier.append(h)
    el = sorted(elems); idx = {e: i for i, e in enumerate(el)}
    comp = [[idx[tuple(f[g[i]] for i in range(n))] for g in el] for f in el]
    return comp

def poset_category(n, p, rng):
    le = [[i == j for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p: le[i][j] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    arrows = [(i, j) for i in range(n) for j in range(n) if le[i][j]]
    idx = {a: t for t, a in enumerate(arrows)}
    comp = [[idx[(g[0], f[1])] if g[1] == f[0] else None for g in arrows] for f in arrows]
    return comp

def two_object_example():
    # arrows: 0 = id_0, 1 = id_1, 2 = a : 0 -> 1 ; comp[f][g] = f o g
    comp = [[0, None, None], [None, 1, 2], [2, None, None]]
    D = frozenset({0, 2}); E = frozenset({1, 2})
    assert is_ideal(comp, 3, D) and is_ideal(comp, 3, E)
    assert ideal_product(comp, D, D) == D and ideal_product(comp, E, E) == E
    DE = ideal_product(comp, D, E); ED = ideal_product(comp, E, D)
    print("two-object category: DE =", set(DE), " ED =", set(ED))
    m, same = check_pair(comp, D, E)
    print("  m =", m, " (ED)^m == I' :", same, " (ED)^{m+1} == I' : True (asserted)")
    assert not same

def main():
    two_object_example()
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    pairs = fails = 0; maxm = 0
    for trial in range(60):
        if trial % 2 == 0:
            comp = transformation_monoid(rng.randrange(3, 5), rng.randrange(1, 3), rng)
        else:
            comp = poset_category(rng.randrange(3, 7), 0.4, rng)
        n = len(comp)
        if n > 60: continue
        ideals = two_sided_ideals(comp, n)
        if ideals is None: continue
        idem = [I for I in ideals if ideal_product(comp, I, I) == I]
        for D in idem:
            for E in idem:
                m, same = check_pair(comp, D, E); pairs += 1; maxm = max(maxm, m)
                if not same: fails += 1
    print(f"random categories: {pairs} pairs checked, all assertions hold; max m = {maxm};")
    print(f"  pairs with (ED)^m != I' (stabilisation index of the ED chain larger): {fails}")

if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------------------------
# Ideals generated by objects on finite posets: D_A = arrows passing through a point of A.
# Claims checked: (DE)^k = D_{A∩B} iff 2k > L, where L is the longest strictly alternating chain
# b_1 < a_1 < ... (b_i in B, a_i in A) inside an interval disjoint from A∩B; the chain stabilises
# at index floor(L/2)+1 with I' = D_{A∩B}.  Also the example N, A = evens, B = odds ∪ 4N (L = 3).

def poset_data(n, p, rng=None, le=None):
    if le is None:
        le = [[i == j for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p: le[i][j] = True
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    if le[i][k] and le[k][j]: le[i][j] = True
    arrows = [(i, j) for i in range(n) for j in range(n) if le[i][j]]
    idx = {a: t for t, a in enumerate(arrows)}
    comp = [[idx[(g[0], f[1])] if g[1] == f[0] else None for g in arrows] for f in arrows]
    return le, arrows, idx, comp

def through(le, arrows, idx, A):
    return frozenset(idx[(i, j)] for (i, j) in arrows if any(le[i][c] and le[c][j] for c in A))

def longest_alt(le, n, A, B):
    """Longest strictly alternating chain b_1<a_1<... inside an interval [i,j] disjoint from A∩B."""
    AB = A & B; best = 0
    for i in range(n):
        for j in range(n):
            if not le[i][j] or any(le[i][c] and le[c][j] for c in AB): continue
            pts = [c for c in range(n) if le[i][c] and le[c][j]]
            # longest path alternating B, A, B, ... in the strict order restricted to pts
            memo = {}
            def f(c, want_A):
                key = (c, want_A)
                if key in memo: return memo[key]
                S = A if want_A else B
                v = 0
                for d in pts:
                    if d != c and le[c][d] and d in S: v = max(v, 1 + f(d, not want_A))
                memo[key] = v; return v
            for b in pts:
                if b in B: best = max(best, 1 + f(b, True))
    return best

def check_objects(le, n, A, B):
    _, arrows, idx, comp = poset_data(n, 0, le=le)
    D = through(le, arrows, idx, A); E = through(le, arrows, idx, B); DAB = through(le, arrows, idx, A & B)
    seq = chain(comp, D, E); m = len(seq); Ip = seq[-1]
    L = longest_alt(le, n, A, B)
    assert Ip == DAB, "I' != D_{A∩B}"
    assert m == L // 2 + 1, (m, L)
    for k in range(1, m + 2):
        Pk = alt_products(comp, D, E, 2 * k, D)
        assert (Pk == DAB) == (2 * k > L)
    return m, L

def objects_main():
    rng = random.Random(7); pairs = 0; maxL = 0
    for trial in range(150):
        n = rng.randrange(3, 8)
        le, *_ = poset_data(n, rng.choice([0.3, 0.5, 0.8]), rng)
        for _ in range(6):
            A = frozenset(c for c in range(n) if rng.random() < 0.5)
            B = frozenset(c for c in range(n) if rng.random() < 0.5)
            m, L = check_objects(le, n, A, B); pairs += 1; maxL = max(maxL, L)
    print(f"object-generated ideals on random finite posets: {pairs} pairs, I' = D_(A∩B) and m = L//2+1 always; max L = {maxL}")
    N = 24; le = [[i <= j for j in range(N)] for i in range(N)]
    A = frozenset(range(0, N, 2)); B = frozenset(c for c in range(N) if c % 2 == 1 or c % 4 == 0)
    m, L = check_objects(le, N, A, B)
    print(f"N truncated at {N}, A = evens, B = odds ∪ 4N: L = {L}, m = {m}, I' = D_(4N)")
    B2 = frozenset(range(1, N, 2)); m2, L2 = check_objects(le, N, A, B2)
    print(f"N truncated at {N}, A = evens, B = odds: L = {L2}, m = {m2} (grows with the truncation)")

if __name__ == "__main__":
    objects_main()

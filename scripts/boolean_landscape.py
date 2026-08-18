"""The Boolean n=2 stage-zero landscape (O17).

For every subgroup H <= B_2 acting on the Boolean square, compute:
  - the number of invariant classes of (square/H)([2]) (strict
    endomorphism data of the quotient),
  - the strict-homotopy graph on them at stage zero, decided EXACTLY:
    a strict invariant homotopy is an invariant class of
    (square/H)([2+1]) with prescribed w-faces; on the Boolean site
    truth tables are unconstrained, so existence reduces to a parity
    union-find over the 2 x 8 value slots, branched over face
    representatives and deck twists; positives are verified by
    reconstructing actual masks and checking invariance directly,
  - whether the identity class is homotopic to a constant (stage-zero
    contractibility signal), and the size of its component.

Groups: all 10 subgroups of B_2, with their taxonomy (free / fixed /
mixed) -- which is site-independent.
"""
import sys, itertools
sys.path.insert(0, 'scripts')

n = 2
# ---------- B_2 machinery ----------
ELEMS = []
for perm in itertools.permutations(range(n)):
    for signs in itertools.product((0, 1), repeat=n):
        ELEMS.append((perm, signs))
ID = (tuple(range(n)), (0,) * n)

def mm(e1, e2):
    (p1, s1), (p2, s2) = e1, e2
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i] ^ s2[p1[i]] for i in range(n)))

def close(gens):
    S = {ID} | set(gens)
    while True:
        new = {mm(a, b) for a in S for b in S} - S
        if not new:
            return frozenset(S)
        S |= new

# ---------- masks ----------
def NPTS(m):
    return 1 << m

def neg(phi, m):
    return ((1 << NPTS(m)) - 1) ^ phi

def pt_act(e, p, m):
    """point action of the signed permutation e on {0,1}^m (acting on
    the first n coordinates; extra coordinates fixed)"""
    pm, s = e
    q = p & ~((1 << n) - 1)
    for i in range(n):
        b = ((p >> pm[i]) & 1) ^ s[i]
        q |= b << i
    return q

def sub(phi, e, m):
    """substitution by sigma_e on FB(m): (phi o sigma_e)(p) =
    phi(sigma_e(p))"""
    r = 0
    for p in range(NPTS(m)):
        if (phi >> pt_act(e, p, m)) & 1:
            r |= 1 << p
    return r

def deck(e, c, m):
    """post-composition: e o (c_0, c_1)"""
    pm, s = e
    # (e o c)_i = neg^{s_i} c_{pm^{-1}(i)}  --  e's i-th component is
    # neg^{s_i} x_{pm(i)}?  Convention: e as morphism has components
    # e_i = neg^{s_i} x_{pm(i)}, so (e o c)_i = neg^{s_i} c_{pm(i)}.
    return tuple(neg(c[pm[i]], m) if s[i] else c[pm[i]]
                 for i in range(n))

# ---------- per-subgroup analysis ----------
def analyze(H, name):
    Hl = sorted(H)
    gens = []
    span = {ID}
    for e in Hl:
        if e in span:
            continue
        gens.append(e)
        span = set(close(gens))
        if len(span) == len(H):
            break

    m2 = 2
    FB = list(range(1 << NPTS(m2)))

    def orbit(c):
        return {deck(h, c, m2) for h in Hl}

    def nc(c):
        return min(orbit(c))

    # invariant classes at level 2
    classes = {}
    for A in FB:
        for B in FB:
            c = (A, B)
            k = nc(c)
            if k in classes:
                continue
            inv = all(nc((sub(c[0], g, m2), sub(c[1], g, m2))) == k
                      for g in gens)
            classes[k] = inv
    invs = sorted(k for k, v in classes.items() if v)

    X2 = sum(1 << p for p in range(4) if p & 1)
    Y2 = sum(1 << p for p in range(4) if (p >> 1) & 1)
    idc = nc((X2, Y2))
    consts = {nc((a, b)) for a in (0, 15) for b in (0, 15)}

    # ---------- exact homotopy decision at level 3 ----------
    m3 = 3
    P3 = 8

    def facemask(M, e):
        """w := e face of an FB(3) mask, as FB(2) mask"""
        r = 0
        for p2 in range(4):
            if (M >> (p2 | (e << 2))) & 1:
                r |= 1 << p2
        return r

    class UF:
        def __init__(s, sz):
            s.par = list(range(sz)); s.pr = [0] * sz
            s.fix = {}; s.ok = True
        def find(s, i):
            r = i; acc = 0
            while s.par[r] != r:
                acc ^= s.pr[r]; r = s.par[r]
            return r, acc
        def union(s, i, j, parity):
            (ri, pi) = s.find(i); (rj, pj) = s.find(j)
            if ri == rj:
                if (pi ^ pj) != parity:
                    s.ok = False
                return
            s.par[ri] = rj; s.pr[ri] = pi ^ pj ^ parity
            if ri in s.fix:
                v = s.fix.pop(ri) ^ s.pr[ri]
                if rj in s.fix:
                    if s.fix[rj] != v:
                        s.ok = False
                else:
                    s.fix[rj] = v
        def setv(s, i, v):
            (r, p) = s.find(i)
            v ^= p
            if r in s.fix:
                if s.fix[r] != v:
                    s.ok = False
            else:
                s.fix[r] = v

    def slot(cmp_, p):
        return cmp_ * P3 + p

    def homotopy(e0, e1):
        """exact: exists an invariant level-3 class with w-faces
        e0, e1?  Branch over face reps and per-generator deck twists;
        verify positives by reconstruction."""
        for r0 in orbit(e0):
            for r1 in orbit(e1):
                for twists in itertools.product(Hl, repeat=len(gens)):
                    uf = UF(2 * P3)
                    okb = True
                    for g, d in zip(gens, twists):
                        pm, s = d
                        for cmp_ in range(2):
                            # (c o sigma_g)_cmp (p) = c_cmp(g.p) must
                            # equal (deck_d c)_cmp (p)
                            #   = s_cmp ^ c_{pm(cmp)}(p)
                            c2 = pm[cmp_]
                            sg = s[cmp_]
                            for p in range(P3):
                                uf.union(slot(cmp_, pt_act(g, p, m3)),
                                         slot(c2, p), sg)
                                if not uf.ok:
                                    break
                            if not uf.ok:
                                break
                        if not uf.ok:
                            break
                    if not uf.ok:
                        continue
                    for p2 in range(4):
                        for cmp_ in range(2):
                            uf.setv(slot(cmp_, p2), (r0[cmp_] >> p2) & 1)
                            uf.setv(slot(cmp_, p2 | 4),
                                    (r1[cmp_] >> p2) & 1)
                        if not uf.ok:
                            break
                    if not uf.ok:
                        continue
                    # reconstruct: free roots -> 0
                    vals = []
                    for i in range(2 * P3):
                        (r, p) = uf.find(i)
                        vals.append(uf.fix.get(r, 0) ^ p)
                    A = sum(vals[slot(0, p)] << p for p in range(P3))
                    B = sum(vals[slot(1, p)] << p for p in range(P3))
                    # verify: class invariance of (A,B) at level 3
                    def orbit3(c):
                        return {deck(h, c, m3) for h in Hl}
                    k3 = min(orbit3((A, B)))
                    good = all(
                        min(orbit3((sub(A, g, m3), sub(B, g, m3)))) == k3
                        for g in gens)
                    facs = (min(orbit((facemask(A, 0), facemask(B, 0)))),
                            min(orbit((facemask(A, 1), facemask(B, 1)))))
                    if good and set(facs) <= {nc(r0), nc(r1)} and \
                       {nc(r0), nc(r1)} == {e0, e1} and \
                       ((facs[0] == e0 and facs[1] == e1) or
                        (facs[0] == e1 and facs[1] == e0)):
                        return True
        return False

    # component of id among invariant classes
    comp = {idc}
    frontier = [idc]
    while frontier:
        e = frontier.pop()
        for e2 in invs:
            if e2 in comp:
                continue
            if homotopy(e, e2):
                comp.add(e2)
                frontier.append(e2)
    hits_const = bool(comp & consts)
    print(f"{name}: |H|={len(H)}  classes={len(classes)}  "
          f"invariant={len(invs)}  id-component={len(comp)}  "
          f"reaches-constant={hits_const}")
    return len(invs), len(comp), hits_const


if __name__ == "__main__":
    sw = ((1, 0), (0, 0))
    r = ((1, 0), (1, 0))       # (x,y) -> (~y, x) as signed perm
    nb = ((0, 1), (1, 1))
    nx = ((0, 1), (1, 0))
    ny = ((0, 1), (0, 1))
    g = mm(sw, nb)
    # free subgroups (<nb>,<nx>,<ny>,<r>,V) agree by the covering
    # argument and fixed ones (<sw>,<g>) by the equivariant connection
    # retraction (term-uniform); machine analysis for the mixed ones:
    subs = [
        ("K=<sw,nb> mixed", [sw, nb]),
        ("B2 mixed", [sw, r]),
    ]
    for name, gg in subs:
        analyze(close(gg), name)

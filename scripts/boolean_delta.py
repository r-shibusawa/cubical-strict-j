"""Boolean delta-obstruction certificates (O17).

Port of delta_obstruction.py to the Boolean site.  Setting: H <= B_n
mixed with exactly two reflections h1, h2 (disjoint fixed loci),
trivial realizable characters; the two-stratum join model
J = cube^{m1} * cube^{m2} carries the twisted H-action nu.  An
H-invariant interior class of (J/H)([n]) is a cell c (components in
FB(n), i.e., arbitrary functions {0,1}^n -> {0,1}) with
c o sigma_h = nu(delta(h)) . c for a homomorphism delta: H -> H,
where the deck action nu permutes the join coordinates and flips
values by OUTPUT complement (no rho-twist: Boolean negation is
pointwise).

CERTIFICATE: for every delta with nu o delta coordinate-nontrivial,
the parity system on variables X_{j,p} (join coordinate j, point
p in {0,1}^n) is inconsistent  ==>  every invariant interior class
is strict.  On the Boolean site the criterion is EXACT in both
directions: an assignment of truth tables is unconstrained (no
monotonicity), so system consistency is equivalent to the existence
of an invariant cell with twist delta.

Validation: n = 2, K = <sw, g> and G2 = B2 must certify, matching
the Boolean stage-0 censuses (essential = 0, boolean_site.py).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from delta_obstruction import make_group_tools, locus_pattern, \
    act_on_pattern, match_pattern


def certify_boolean(n, H_gens, name):
    ELEMS, ID, mm, close, cycles, has_fixed_cell = make_group_tools(n)
    H = sorted(close(H_gens))
    refl = [h for h in H if has_fixed_cell(h)]
    assert len(refl) == 2, (name, len(refl))
    h1, h2 = refl
    m1, m2 = len(cycles(h1)), len(cycles(h2))
    pat1 = locus_pattern(h1, n, cycles)
    pat2 = locus_pattern(h2, n, cycles)

    nu = {}
    for h in H:
        a1 = match_pattern(act_on_pattern(h, pat1, n), pat1, m1)
        a2 = match_pattern(act_on_pattern(h, pat2, n), pat2, m2)
        if a1 is not None and a2 is not None:
            nu[h] = (0, a1, a2)
        else:
            b1 = match_pattern(act_on_pattern(h, pat1, n), pat2, m1)
            b2 = match_pattern(act_on_pattern(h, pat2, n), pat1, m2)
            assert b1 is not None and b2 is not None, (name, h)
            nu[h] = (1, b1, b2)

    M = m1 + m2 + 1
    T = M - 1

    def coord_act(nuh):
        eps, x1, x2 = nuh
        out = [None] * M
        if eps == 0:
            for j in range(m1):
                out[j] = (x1[j][0], x1[j][1])
            for j in range(m2):
                out[m1 + j] = (m1 + x2[j][0], x2[j][1])
            out[T] = (T, 0)
        else:
            for j in range(m1):
                out[j] = (m1 + x1[j][0], x1[j][1])
            for j in range(m2):
                out[m1 + j] = (x2[j][0], x2[j][1])
            out[T] = (T, 1)
        return out

    # Boolean points: all of {0,1}^n; substitution point action of h
    pts = list(range(1 << n))

    def sub_pt(e, p):
        """point action of the signed permutation e = (perm, signs):
        the substitution sigma_e sends the point p to the point whose
        i-th coordinate is  p_{perm(i)} xor signs(i)."""
        pm, s = e
        q = 0
        for i in range(n):
            b = ((p >> pm[i]) & 1) ^ s[i]
            q |= b << i
        return q

    # homomorphisms delta: H -> H via generator images
    gens = []
    span = {ID}
    for e in H:
        if e in span:
            continue
        gens.append(e)
        span = set(close(gens))
        if len(span) == len(H):
            break
    homs = []
    for imgs in itertools.product(H, repeat=len(gens)):
        d = {ID: ID}
        for g, im in zip(gens, imgs):
            d[g] = im
        ok = True
        while ok and len(d) < len(H):
            prog = False
            for a in list(d):
                for b in list(d):
                    c = mm(a, b)
                    v = mm(d[a], d[b])
                    if c in d:
                        if d[c] != v:
                            ok = False
                            break
                    else:
                        d[c] = v
                        prog = True
                if not ok:
                    break
            if not prog:
                break
        if ok and len(d) == len(H) and \
           all(d[mm(a, b)] == mm(d[a], d[b]) for a in H for b in H):
            homs.append(d)

    unobstructed = []
    triv = 0
    NPTS = len(pts)
    for delta in homs:
        acts = {h: coord_act(nu[delta[h]]) for h in H}
        if all(all(a[j] == (j, 0) for j in range(M))
               for a in acts.values()):
            triv += 1
            continue
        size = M * NPTS
        parent = list(range(size))
        par = [0] * size

        def findp(i):
            r = i
            acc = 0
            while parent[r] != r:
                acc ^= par[r]
                r = parent[r]
            return r, acc

        ok = True
        for h in H:
            if h == ID:
                continue
            A = acts[h]
            for j in range(M):
                j2, sgn = A[j]
                for p in pts:
                    # (c o sigma_h)_j (p) = c_j(sigma_h p)  must equal
                    # (nu(delta h) . c)_j (p) = sgn xor c_{j2}(p)
                    (ri, pi) = findp(j * NPTS + sub_pt(h, p))
                    (rj, pj) = findp(j2 * NPTS + p)
                    if ri == rj:
                        if (pi ^ pj) != sgn:
                            ok = False
                            break
                    else:
                        parent[ri] = rj
                        par[ri] = pi ^ pj ^ sgn
                if not ok:
                    break
            if not ok:
                break
        if ok:
            unobstructed.append(delta)

    status = "CERTIFIED (all invariant classes strict)" if not \
        unobstructed else \
        f"UNCERTIFIED: {len(unobstructed)} consistent nontrivial delta"
    print(f"{name}: |H|={len(H)} m1={m1} m2={m2} homs={len(homs)} "
          f"(coord-trivial {triv}) -> {status}")
    return not unobstructed


if __name__ == "__main__":
    sw2 = ((1, 0), (0, 0))
    g2 = ((1, 0), (1, 1))
    r2 = ((1, 0), (1, 0))
    ok = True
    ok &= certify_boolean(2, [sw2, g2], "Boolean n=2 K=<sw,g>")
    ok &= certify_boolean(2, [sw2, r2], "Boolean n=2 G2=B2")

    # n=3: the two-stratum disjoint candidates (as in delta_obstruction)
    ELEMS3, ID3, mm3, close3, cycles3, hfc3 = make_group_tools(3)
    subs = {frozenset([ID3])}
    frontier = {frozenset([ID3])}
    while frontier:
        new = set()
        for Hf in frontier:
            for e in ELEMS3:
                if e in Hf:
                    continue
                H2 = close3(set(Hf) | {e})
                if H2 not in subs:
                    new.add(H2)
        subs |= new
        frontier = new
    targets = []
    for Hf in sorted(subs, key=len):
        refl = [h for h in Hf if hfc3(h)]
        if len(refl) != 2:
            continue
        Hsub = close3(refl)
        parent = list(range(3))
        par = [0] * 3

        def findp(i):
            r = i
            acc = 0
            while parent[r] != r:
                acc ^= par[r]
                r = parent[r]
            return r, acc

        okc = True
        for (p, s) in Hsub:
            for i in range(3):
                (ri, pi), (rj, pj) = findp(i), findp(p[i])
                if ri == rj:
                    if (pi ^ pj) != (s[i] & 1):
                        okc = False
                        break
                else:
                    parent[ri] = rj
                    par[ri] = pi ^ pj ^ (s[i] & 1)
            if not okc:
                break
        if okc:
            continue
        targets.append(Hf)
    print(f"\nBoolean n=3 two-stratum disjoint candidates: {len(targets)}")
    for Hf in targets:
        gens = []
        span = {ID3}
        for e in sorted(Hf):
            if e in span:
                continue
            gens.append(e)
            span = set(close3(gens))
            if len(span) == len(Hf):
                break
        ok &= certify_boolean(3, gens, f"Boolean n=3 |H|={len(Hf)}")
    print("\nALL CERTIFIED" if ok else "\nSOME UNCERTIFIED")

"""Kleene-sound delta-obstruction certificate: the De Morgan system
restricted to the unmixed (proper) middle points (see
kleene_certificates3.py for the soundness argument).

Original docstring:

Setting: H <= B_n mixed with exactly two reflections h1, h2 (fixed loci
l1, l2 disjoint), trivial realizable characters.  The join model
J = cube^{m1} * cube^{m2} (mi = #cycles of hi) carries the twisted
H-action nu: H -> Aut(join coordinates) (signed perms of the d-params
and a-params, swapping the blocks and negating t on the swap coset).
Phi_j = F(p1_j(d), p2_j(a), t) is H-equivariant (identities: self-dual,
F(x,y,~t)=F(y,x,t), faces).

An H-invariant interior class of (J/H~)([n]) is a cell c (components in
DM(u_1..u_n)) with c∘σ_h = nu(δ(h))·c for a homomorphism δ: H -> H.
CERTIFICATE: for every δ with nu∘δ nontrivial, the vector parity system
(coordinate, middle-level point) is inconsistent  ==>  every invariant
interior class is strict (essential = 0), with NO finite enumeration
of DM(n).  Exactness of the criterion: weight rule (Sec 33), vectorized.

Validation: for n=2, K and G2 must certify (matching the censuses of
collage_type11.py / collage_type12.py: essential = 0).
"""
import sys, itertools
sys.path.insert(0, 'scripts')


def make_group_tools(n):
    ELEMS = []
    for perm in itertools.permutations(range(n)):
        for signs in itertools.product((0,1), repeat=n):
            ELEMS.append((perm, signs))
    ID = (tuple(range(n)), (0,)*n)
    def mm(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    def close(gens):
        S = {ID} | set(gens)
        while True:
            new = {mm(a,b) for a in S for b in S} - S
            if not new: return frozenset(S)
            S |= new
    def cycles(e):
        p, s = e
        seen = [False]*n; out = []
        for i in range(n):
            if seen[i]: continue
            cyc = [i]; seen[i] = True; j = p[i]; sg = s[i]
            while j != i:
                seen[j] = True; cyc.append(j); sg ^= s[j]; j = p[j]
            out.append((tuple(cyc), sg & 1))
        return out
    def has_fixed_cell(e):
        return e != ID and all(sg == 0 for _, sg in cycles(e))
    return ELEMS, ID, mm, close, cycles, has_fixed_cell


def locus_pattern(h, n, cycles):
    """Parametrization p of the fixed locus of h: slot -> (param, sign).
    Cells fixed by h: slot i carries (~)^{sig(i)} m_{param(i)}, signs
    propagated along each (even) cycle from its minimum slot."""
    pat = [None]*n
    for j, (cyc, sg) in enumerate(cycles(h)):
        assert sg == 0
        s = 0
        # walk the cycle propagating: (h∘c)(i) = ~^{s_h(i)} c(perm_h(i)) = c(i)
        # so c(i) = ~^{s_h(i)} c(perm_h(i)); start at cyc[0] with sign 0
        p, sgn = h
        i = cyc[0]; cur = 0
        for _ in range(len(cyc)):
            pat[i] = (j, cur)
            cur ^= sgn[i]
            i = p[i]
        assert i == cyc[0] and cur == 0
    return pat


def act_on_pattern(h, pat, n):
    """Pattern of h∘c for c with pattern pat: (h∘c)(i) = ~^{s_h(i)} c(perm_h(i))."""
    p, s = h
    return [(pat[p[i]][0], pat[p[i]][1] ^ s[i]) for i in range(n)]


def match_pattern(newpat, pat, m):
    """Express newpat as (signed param perm) applied to pat's params, if the
    param-partition agrees.  Returns list param -> (param', sign) or None."""
    out = [None]*m
    n = len(pat)
    for i in range(n):
        j, s = pat[i]; j2, s2 = newpat[i]
        cand = (j2, s ^ s2)
        if out[j] is None: out[j] = cand
        elif out[j] != cand: return None
    if any(o is None for o in out): return None
    if sorted(o[0] for o in out) != list(range(m)): return None
    return out


def certify(n, H_gens, name):
    ELEMS, ID, mm, close, cycles, has_fixed_cell = make_group_tools(n)
    H = sorted(close(H_gens))
    refl = [h for h in H if has_fixed_cell(h)]
    assert len(refl) == 2, (name, len(refl))
    h1, h2 = refl
    m1, m2 = len(cycles(h1)), len(cycles(h2))
    pat1, pat2 = locus_pattern(h1, n, cycles), locus_pattern(h2, n, cycles)
    # sanity: h1 fixes its own locus
    assert match_pattern(act_on_pattern(h1, pat1, n), pat1, m1) == \
           [(j,0) for j in range(m1)]

    # nu(h): (eps, sp1, sp2): eps=0 preserve (sp1 on d-params, sp2 on a-params);
    # eps=1 swap (sp1: d-params -> a-params, sp2: a-params -> d-params), t -> ~t
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

    # coordinates of J: 0..m1-1 = d-params, m1..m1+m2-1 = a-params, last = t
    M = m1 + m2 + 1
    T = M - 1
    def coord_act(nuh):
        """coordinate action A: for equation c∘σ_h = A·c: returns list
        coord j -> (coord j', sign): (A·c)_j = ~^{sign} c_{j'}."""
        eps, x1, x2 = nuh
        out = [None]*M
        if eps == 0:
            for j in range(m1):
                out[j] = (x1[j][0], x1[j][1])
            for j in range(m2):
                out[m1+j] = (m1 + x2[j][0], x2[j][1])
            out[T] = (T, 0)
        else:
            # h∘p1 = p2∘x1: the d-block maps to the a-block
            for j in range(m1):
                out[j] = (m1 + x1[j][0], x1[j][1])
            for j in range(m2):
                out[m1+j] = (x2[j][0], x2[j][1])
            out[T] = (T, 1)
        return out

    # middle level of L_n and the two point maps
    NL = 1 << (2*n)
    pts = [p for p in range(NL) if bin(p).count('1') == n and
           all(((p >> (2*i)) & 1) != ((p >> (2*i+1)) & 1)
               for i in range(n))]
    def sub_pt(e, p):
        pm, s = e
        c = [(p >> i) & 1 for i in range(2*n)]
        d = [0]*(2*n)
        for i in range(n):
            vx, vnx = c[2*pm[i]], c[2*pm[i]+1]
            if s[i]: vx, vnx = vnx, vx
            d[2*i], d[2*i+1] = vx, vnx
        return sum(b << i for i, b in enumerate(d))
    def rho_pt(p):
        c = [(p >> i) & 1 for i in range(2*n)]
        d = []
        for i in range(n):
            d += [1 - c[2*i+1], 1 - c[2*i]]
        return sum(b << i for i, b in enumerate(d))

    # enumerate homomorphisms delta: H -> H via generator images
    gens = []
    span = {ID}
    for e in H:
        if e in span: continue
        gens.append(e); span = set(close(gens))
        if len(span) == len(H): break
    homs = []
    for imgs in itertools.product(H, repeat=len(gens)):
        d = {ID: ID}
        for g, im in zip(gens, imgs): d[g] = im
        ok = True
        while ok and len(d) < len(H):
            prog = False
            for a in list(d):
                for b in list(d):
                    c = mm(a, b); v = mm(d[a], d[b])
                    if c in d:
                        if d[c] != v: ok = False; break
                    else:
                        d[c] = v; prog = True
                if not ok: break
            if not prog: break
        if ok and len(d) == len(H) and \
           all(d[mm(a,b)] == mm(d[a], d[b]) for a in H for b in H):
            homs.append(d)

    idx = {p: i for i, p in enumerate(pts)}
    unobstructed = []
    triv_count = 0
    for delta in homs:
        acts = {h: coord_act(nu[delta[h]]) for h in H}
        if all(all(a[j] == (j, 0) for j in range(M)) for a in acts.values()):
            triv_count += 1
            continue  # coordinate-trivial: strict classes, fine
        # parity union-find on (coord, middle point)
        size = M * len(pts)
        parent = list(range(size)); par = [0]*size
        def findp(i):
            r = i; acc = 0
            while parent[r] != r:
                acc ^= par[r]; r = parent[r]
            return r, acc
        ok = True
        for h in H:
            if h == ID: continue
            A = acts[h]
            for j in range(M):
                j2, s = A[j]
                for q in pts:
                    # X_{j, sub_pt(h,q)} = s XOR X_{j2, rho^s(q)}
                    lq = sub_pt(h, q)
                    rq = rho_pt(q) if s else q
                    (ri, pi) = findp(j*len(pts) + idx[lq])
                    (rj, pj) = findp(j2*len(pts) + idx[rq])
                    if ri == rj:
                        if (pi ^ pj) != s: ok = False; break
                    else:
                        parent[ri] = rj; par[ri] = pi ^ pj ^ s
                if not ok: break
            if not ok: break
        if ok:
            unobstructed.append(delta)

    status = "CERTIFIED (essential = 0)" if not unobstructed else \
             f"INCONCLUSIVE: {len(unobstructed)} unobstructed nontrivial delta"
    print(f"{name}: |H|={len(H)} m1={m1} m2={m2} homs={len(homs)} "
          f"(coord-trivial {triv_count}) -> {status}")
    return not unobstructed


if __name__ == "__main__":
    # ---- n=2 validation: K and G2 ----
    sw2 = ((1,0),(0,0))
    g2  = ((1,0),(1,1))
    r2  = ((1,0),(1,0))   # rotation: x<-~y, y<-x  as signed permutation
    certify(2, [sw2, g2], "n=2 K=<sw,g>")
    certify(2, [sw2, r2], "n=2 G2=B2")

    # ---- n=3 targets: the six two-stratum subgroups ----
    ELEMS3, ID3, mm3, close3, cycles3, hfc3 = make_group_tools(3)
    seen = set()
    targets = []
    subs = {frozenset([ID3])}
    frontier = {frozenset([ID3])}
    while frontier:
        new = set()
        for Hf in frontier:
            for e in ELEMS3:
                if e in Hf: continue
                H2 = close3(set(Hf) | {e})
                if H2 not in subs: new.add(H2)
        subs |= new
        frontier = new
    for Hf in sorted(subs, key=len):
        refl = [h for h in Hf if hfc3(h)]
        if len(refl) != 2: continue
        # mixed: no common fixed cell of the whole group (quick: pairwise none)
        # disjointness of the two loci == <h1,h2> has no common fixed cell:
        # parity union-find on slots
        Hsub = close3(refl)
        parent = list(range(3)); par = [0]*3
        def findp(i):
            r = i; acc = 0
            while parent[r] != r:
                acc ^= par[r]; r = parent[r]
            return r, acc
        okc = True
        for (p, s) in Hsub:
            for i in range(3):
                (ri, pi), (rj, pj) = findp(i), findp(p[i])
                if ri == rj:
                    if (pi ^ pj) != (s[i] & 1): okc = False; break
                else:
                    parent[ri] = rj; par[ri] = pi ^ pj ^ (s[i] & 1)
            if not okc: break
        if okc: continue          # loci intersect (or common fixed layer)
        key = frozenset(Hf)
        if key in seen: continue
        seen.add(key)
        targets.append(Hf)

    print(f"\nn=3 two-stratum disjoint candidates: {len(targets)}")
    ok_all = True
    for Hf in targets:
        gens = []
        span = {ID3}
        for e in sorted(Hf):
            if e in span: continue
            gens.append(e); span = set(close3(gens))
            if len(span) == len(Hf): break
        ok_all &= certify(3, gens, f"n=3 |H|={len(Hf)}")
    print("\nALL CERTIFIED" if ok_all else "\nSOME INCONCLUSIVE")

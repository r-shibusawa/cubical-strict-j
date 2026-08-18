"""Fate of the Boolean-UNCERTIFIED n=3 two-stratum subgroups (O17).

For each two-stratum disjoint subgroup H <= B_3 whose Boolean
delta-certificate fails, this script:
  (1) reconstructs, for every consistent nontrivial delta, an explicit
      H-invariant interior cell c of (J_H/H)([3]) (components in
      FB(3), coordinates = m1 d-params + m2 a-params + t) from the
      parity system (exactness: any consistent assignment is a cell),
      and verifies the twisted invariance directly;
  (2) checks whether the class of c has a strictly invariant
      representative in its deck orbit (if yes it is not essential);
  (3) decides EXACTLY whether c is invariantly homotopic, at stage
      zero, to an end-supported class (t-component constant): the
      "slide-null" test that drives the nullity theorem;
  (4) computes the collage image Phi(c) in FB(3)^3 and reports its
      class in (cube^3/H)([3]) (generic class or not).

Outcome (3) = False for all deltas  ==>  the stage-zero nullity
genuinely fails on the Boolean site for H, so the De Morgan
separation proof does not transfer; (4) probes whether the rigid
classes interact with the collage as section-like data.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from delta_obstruction import make_group_tools, locus_pattern, \
    act_on_pattern, match_pattern

n = 3
ELEMS, ID, mm, close, cycles, has_fixed_cell = make_group_tools(n)

# ---------- mask machinery over {0,1}^m ----------
def NP(m):
    return 1 << m

def neg(phi, m):
    return ((1 << NP(m)) - 1) ^ phi

def pt_act(e, p, m):
    """point action of the signed permutation e (on the first n
    coords; extra coords fixed)"""
    pm, s = e
    q = p & ~((1 << n) - 1)
    for i in range(n):
        q |= (((p >> pm[i]) & 1) ^ s[i]) << i
    return q

def sub(phi, e, m):
    r = 0
    for p in range(NP(m)):
        if (phi >> pt_act(e, p, m)) & 1:
            r |= 1 << p
    return r

# ---------- parity UF ----------
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


def analyze_group(H_gens, name):
    H = sorted(close(H_gens))
    refl = [h for h in H if has_fixed_cell(h)]
    assert len(refl) == 2
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

    ACT = {h: coord_act(nu[h]) for h in H}

    # generators + homomorphisms delta: H -> H
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
                    c = mm(a, b); v = mm(d[a], d[b])
                    if c in d:
                        if d[c] != v:
                            ok = False; break
                    else:
                        d[c] = v; prog = True
                if not ok:
                    break
            if not prog:
                break
        if ok and len(d) == len(H) and \
           all(d[mm(a, b)] == mm(d[a], d[b]) for a in H for b in H):
            homs.append(d)

    P3 = NP(3)

    def slot3(j, p):
        return j * P3 + p

    def invariance_system(delta, m):
        """UF for level-m cells with twist delta; returns UF or None"""
        Pm = NP(m)
        uf = UF(M * Pm)
        for h in H:
            if h == ID:
                continue
            A = ACT[delta[h]]
            for j in range(M):
                j2, sgn = A[j]
                for p in range(Pm):
                    uf.union(j * Pm + pt_act(h, p, m), j2 * Pm + p, sgn)
                    if not uf.ok:
                        return None
        return uf

    def gen_system(twists, m):
        """UF from generator relations only: for each generator g with
        chosen deck twist k_g:  c o sigma_g = nu(k_g) . c  (this is
        EXACT for class invariance: a class is invariant iff such a
        choice exists per generator)"""
        Pm = NP(m)
        uf = UF(M * Pm)
        for g, k in zip(gens, twists):
            A = ACT[k]
            for j in range(M):
                j2, sgn = A[j]
                for p in range(Pm):
                    uf.union(j * Pm + pt_act(g, p, m), j2 * Pm + p, sgn)
                    if not uf.ok:
                        return None
        return uf

    def class_invariant(c, m):
        orb = set(deck_orbit(c, m))
        return all(tuple(sub(x, g, m) for x in c2) in orb
                   for g in gens for c2 in [min(orb)])

    def reconstruct(uf, m):
        Pm = NP(m)
        vals = []
        for i in range(M * Pm):
            (r, p) = uf.find(i)
            vals.append(uf.fix.get(r, 0) ^ p)
        return [sum(vals[j * Pm + p] << p for p in range(Pm))
                for j in range(M)]

    def verify_inv(c, delta, m):
        for h in H:
            if h == ID:
                continue
            A = ACT[delta[h]]
            for j in range(M):
                j2, sgn = A[j]
                lhs = sub(c[j], h, m)
                rhs = neg(c[j2], m) if sgn else c[j2]
                if lhs != rhs:
                    return False
        return True

    def deck_orbit(c, m):
        out = []
        for h in H:
            A = ACT[h]
            cc = [None] * M
            for j in range(M):
                j2, sgn = A[j]
                cc[j] = neg(c[j2], m) if sgn else c[j2]
            out.append(tuple(cc))
        return out

    def is_strict_class(c, m):
        for cc in deck_orbit(c, m):
            if all(tuple(sub(x, g, m) for x in cc) == tuple(cc)
                   for g in gens):
                return True
        return False

    # collage image: Phi_i = F(l1_i, l2_i, t)
    def F(d, a, t, m):
        return (d & neg(t, m)) | (a & t) | (d & a)

    def collage_image(c, m):
        out = []
        for i in range(n):
            j1, s1 = pat1[i]
            j2, s2 = pat2[i]
            d = neg(c[j1], m) if s1 else c[j1]
            a = neg(c[m1 + j2], m) if s2 else c[m1 + j2]
            out.append(F(d, a, c[T], m))
        return tuple(out)

    def cube_class(cc, m):
        """normalize a cube^3-cell tuple under the deck action of H"""
        orb = []
        for h in H:
            pm, s = h
            orb.append(tuple(neg(cc[pm[i]], m) if s[i] else cc[pm[i]]
                             for i in range(n)))
        return min(orb)

    genc = cube_class(tuple(
        sum(1 << p for p in range(P3) if (p >> i) & 1)
        for i in range(n)), 3)

    # slide-null test at level 4 (homotopy coordinate w = 4th var)
    P4 = NP(4)

    def null_test(c):
        """exists invariant level-4 class with w=0 face a deck
        translate of c and w=1 face end-supported (t constant)?
        Exact: branch over face representatives and per-generator
        twists; verify positives by reconstruction."""
        for rep in deck_orbit(c, 3):
            for twists in itertools.product(H, repeat=len(gens)):
                uf0 = gen_system(twists, 4)
                if uf0 is None:
                    continue
                for endv in (0, 1):
                    import copy
                    uf = copy.deepcopy(uf0)
                    for p3 in range(P3):
                        for j in range(M):
                            uf.setv(j * P4 + p3, (rep[j] >> p3) & 1)
                        uf.setv(T * P4 + (p3 | 8), endv)
                        if not uf.ok:
                            break
                    if not uf.ok:
                        continue
                    c4 = tuple(reconstruct(uf, 4))
                    # verify: class invariance + faces
                    orb4 = set(deck_orbit(c4, 4))
                    k4 = min(orb4)
                    if not all(min(set(deck_orbit(
                            tuple(sub(x, g, 4) for x in c4), 4))) == k4
                            for g in gens):
                        continue
                    f0 = tuple(sum(((c4[j] >> p) & 1) << p
                               for p in range(P3)) for j in range(M))
                    tf1 = sum((((c4[T] >> (p | 8)) & 1)) << p
                              for p in range(P3))
                    if f0 == tuple(rep) and                        tf1 in (0, (1 << P3) - 1):
                        return True
        return False

    # ---- run over consistent nontrivial deltas ----
    print(f"{name}: |H|={len(H)} m1={m1} m2={m2}  gens={gens}")
    found = []
    for delta in homs:
        A = {h: ACT[delta[h]] for h in H}
        if all(all(a[j] == (j, 0) for j in range(M))
               for a in A.values()):
            continue
        uf = invariance_system(delta, 3)
        if uf is None:
            continue
        # look for an INTERIOR realization: T-component non-constant
        interior = None
        import copy
        for p in range(P3):
            for q in range(P3):
                if p == q:
                    continue
                uf2 = copy.deepcopy(uf)
                uf2.setv(T * P3 + p, 0)
                uf2.setv(T * P3 + q, 1)
                if uf2.ok:
                    cand = tuple(reconstruct(uf2, 3))
                    if verify_inv(cand, delta, 3):
                        interior = cand
                        break
            if interior:
                break
        if interior is None:
            print("  delta: consistent only on END cells "
                  "(T forced constant) -- harmless")
            continue
        c = interior
        strict = is_strict_class(c, 3)
        nul = null_test(c)
        img = cube_class(collage_image(c, 3), 3)
        found.append((c, strict, nul, img == genc))
        print(f"  INTERIOR delta-cell: strict-rep={strict}  "
              f"slide-null={nul}  collage-image=generic:{img == genc}")
        print(f"    c = {[format(x, '08b') for x in c]}")
    if not found:
        print("  (no consistent nontrivial delta)")
    return found


if __name__ == "__main__":
    # rebuild the two-stratum disjoint candidates, pick |H| = 8 ones
    subs = {frozenset([ID])}
    frontier = {frozenset([ID])}
    while frontier:
        new = set()
        for Hf in frontier:
            for e in ELEMS:
                if e in Hf:
                    continue
                H2 = close(set(Hf) | {e})
                if H2 not in subs:
                    new.add(H2)
        subs |= new
        frontier = new
    targets = []
    for Hf in sorted(subs, key=len):
        refl = [h for h in Hf if has_fixed_cell(h)]
        if len(refl) != 2:
            continue
        Hsub = close(refl)
        parent = list(range(3)); par = [0] * 3
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
                    if (pi ^ pj) != (s[i] & 1):
                        okc = False; break
                else:
                    parent[ri] = rj; par[ri] = pi ^ pj ^ (s[i] & 1)
            if not okc:
                break
        if okc:
            continue
        targets.append(Hf)
    done = 0
    for Hf in targets:
        if len(Hf) < 8:
            continue
        gens = []
        span = {ID}
        for e in sorted(Hf):
            if e in span:
                continue
            gens.append(e)
            span = set(close(gens))
            if len(span) == len(Hf):
                break
        analyze_group(gens, f"n=3 |H|={len(Hf)} #{done}")
        done += 1

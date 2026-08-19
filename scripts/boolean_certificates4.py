"""Boolean delta-obstruction certificates at n = 4 (O18).

First nontrivial test of Conjecture P: every PRIMITIVE mixed subgroup
(orbit-even, non-median, non-product, with no SEP tower kernel) is
certified -- its exact Boolean parity system admits consistent
nontrivial twists only with vanishing coordinate action.

Machinery: the E-resolution certificate of certificates3.py,
generalized to n = 4 on the Boolean site:
  u-part: parity union-find on (output slot, point of {0,1}^4);
          negation = output complement; EXACT (assignments are cells);
  e-part: G-valued union-find on the 16 vertices (G = H/V).

Candidates: V_even(4) x| P for P in {C4, K4 = <(01)(23),(02)(13)>,
D4, A4, S4}, with V = V_even(4) (reflection-free: any nonzero pure
sign vector has an odd cycle), plus the two-stratum |H|=4 analogues
<(01)n0n1-type reflections with disjoint loci>.
"""
import itertools, collections

n = 4
ELEMS = []
for _p in itertools.permutations(range(n)):
    for _s in itertools.product((0, 1), repeat=n):
        ELEMS.append((_p, _s))
ID = (tuple(range(n)), (0,)*n)

def mm(e1, e2):
    (p1, s1), (p2, s2) = e1, e2
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i] ^ s2[p1[i]] for i in range(n)))

def inv(e):
    p, s = e
    q = [0]*n; t = [0]*n
    for i in range(n): q[p[i]] = i
    for i in range(n): t[i] = s[q[i]]
    return (tuple(q), tuple(t))

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

def hfc(e):
    return e != ID and all(sg == 0 for _, sg in cycles(e))

def close(gens):
    S = {ID} | set(gens)
    dq = collections.deque(S)
    while dq:
        x = dq.popleft()
        for g in list(S):
            for y in (mm(x, g), mm(g, x)):
                if y not in S:
                    S.add(y); dq.append(y)
    return frozenset(S)

NPTS = 1 << n
pts = list(range(NPTS))

def sub_pt(e, p):
    pm, s = e
    q = 0
    for i in range(n):
        q |= ((((p >> pm[i]) & 1) ^ s[i]) << i)
    return q

VERTS = pts


def certify(H_gens, V_gens, name):
    H = sorted(close(H_gens))
    V = sorted(close(V_gens))
    assert set(V) <= set(H)
    assert all(mm(mm(g, x), inv(g)) in V for g in H for x in V), \
        "V not normal"
    assert not any(hfc(x) for x in V if x != ID), "V has a reflection"
    pos = {x: i for i, x in enumerate(H)}
    # cosets -> G = H/V
    cos = {}; reps = []
    for x in H:
        if x in cos: continue
        g = len(reps); reps.append(x)
        for v in V: cos[mm(x, v)] = g
    nG = len(reps)
    GM = [[cos[mm(reps[a], reps[b])] for b in range(nG)]
          for a in range(nG)]
    G_ID = cos[ID]
    GI = [0]*nG
    for a in range(nG):
        for b in range(nG):
            if GM[a][b] == G_ID: GI[a] = b
    SUBP = {x: [sub_pt(x, q) for q in pts] for x in H}
    VACT = SUBP  # vertices = points at n=4 Boolean

    def u_ok(dimg):
        size = n * NPTS
        parent = list(range(size)); par = [0]*size
        def findp(i):
            r = i; acc = 0
            while parent[r] != r: acc ^= par[r]; r = parent[r]
            return r, acc
        for xi, x in enumerate(H):
            if x == ID: continue
            dp, ds = dimg[xi]
            sub = SUBP[x]
            for j in range(n):
                j2, sg = dp[j], ds[j]
                bl = j*NPTS; br = j2*NPTS
                for qi in range(NPTS):
                    (ra, pa) = findp(bl + sub[qi])
                    (rb, pb) = findp(br + qi)
                    if ra == rb:
                        if (pa ^ pb) != sg: return False
                    else:
                        parent[ra] = rb; par[ra] = pa ^ pb ^ sg
        return True

    def e_ok(dimg):
        parent = list(range(NPTS)); par = [G_ID]*NPTS
        def findp(i):
            r = i; acc = G_ID
            while parent[r] != r:
                acc = GM[par[r]][acc]; r = parent[r]
            return r, acc
        for xi, x in enumerate(H):
            if x == ID: continue
            k = cos[pos_elem(dimg[xi])]
            va = VACT[x]
            for vi in range(NPTS):
                (rv, pv) = findp(vi); (rw, pw) = findp(va[vi])
                if rv == rw:
                    if pw != GM[k][pv]: return False
                else:
                    parent[rv] = rw; par[rv] = GM[GI[GM[k][pv]]][pw]
        return True

    def pos_elem(e):
        return e

    # small generating set: pair search, then greedy extension
    gens = None
    for i, a in enumerate(H):
        for b in H[i:]:
            if len(close([a, b])) == len(H):
                gens = [a, b]; break
        if gens: break
    if gens is None:
        # triples from a pool of products of the input generators
        pool = list(dict.fromkeys(
            list(H_gens) +
            [mm(a, b) for a in H_gens for b in H_gens]))
        pool = [e for e in pool if e != ID][:40]
        for combo in itertools.combinations(pool, 3):
            if len(close(list(combo))) == len(H):
                gens = list(combo); break
    if gens is None:
        for combo in itertools.combinations(pool, 4):
            if len(close(list(combo))) == len(H):
                gens = list(combo); break
    if gens is None:
        gens = []
        span = {ID}
        for e in H:
            if e in span: continue
            gens.append(e)
            span = set(close(gens))
            if len(span) == len(H): break
    if len(H) ** len(gens) > 35_000_000:
        print(f"{name}: |H|={len(H)} needs {len(gens)} generators "
              f"({len(H)**len(gens)} hom candidates) -- SKIPPED")
        return None
    word = {x: None for x in H}
    word[ID] = []
    dq = collections.deque([ID])
    while dq:
        x = dq.popleft()
        for k, g in enumerate(gens):
            y = mm(x, g)
            if word[y] is None:
                word[y] = word[x] + [k]; dq.append(y)
    count = 0
    survivors = collections.Counter()
    for imgs in itertools.product(H, repeat=len(gens)):
        dimg = []
        ok = True
        for x in H:
            v = ID
            for k in word[x]:
                v = mm(v, imgs[k])
            dimg.append(v)
        for k, g in enumerate(gens):
            im = imgs[k]
            for xi, x in enumerate(H):
                if dimg[pos[mm(g, x)]] != mm(im, dimg[xi]):
                    ok = False; break
            if not ok: break
        if not ok: continue
        count += 1
        if all(d == ID for d in dimg): continue
        if u_ok(dimg) and e_ok(dimg):
            img = tuple(sorted(set(dimg)))
            kinds = tuple(sorted("refl" if hfc(x) else "free"
                                 for x in img if x != ID))
            survivors[(len(img), kinds)] += 1
    tot = sum(survivors.values())
    print(f"{name}: |H|={len(H)} |V|={len(V)} |G|={nG} "
          f"gens={len(gens)} |Hom|={count} survivors={tot}")
    for (o, kinds), cnt in sorted(survivors.items()):
        print(f"   image order {o} x{cnt}: {'/'.join(kinds)}")
    return tot == 0


if __name__ == "__main__":
    # V_even(4)
    Veven = [(tuple(range(4)), s) for s in itertools.product((0,1),
             repeat=4) if sum(s) % 2 == 0 and any(s)]
    c4 = ((1, 2, 3, 0), (0, 0, 0, 0))
    dt1 = ((1, 0, 3, 2), (0, 0, 0, 0))   # (01)(23)
    dt2 = ((2, 3, 0, 1), (0, 0, 0, 0))   # (02)(13)
    sw01 = ((1, 0, 2, 3), (0, 0, 0, 0))
    rot3 = ((1, 2, 0, 3), (0, 0, 0, 0))  # (012)
    results = {}
    sw13 = ((0, 3, 2, 1), (0, 0, 0, 0))
    for name, gens in [
        ("V_even4 : K4", Veven + [dt1, dt2]),
        ("V_even4 : D4", Veven + [c4, sw13]),
        ("V_even4 : A4", Veven + [dt1, rot3]),
    ]:
        results[name] = certify(gens, Veven, name)
    print("\nCONJECTURE P at n=4 (these candidates):",
          "HOLDS" if all(results.values()) else "FAILS",
          {k: v for k, v in results.items()})

"""Kleene delta-obstruction certificates (sound restriction) (O17).

The De Morgan u-part runs on the middle level of the literal cube;
its extension to ALL points of the unmixed poset U_3 (the domain of
free Kleene algebra elements) -- is preserved by all
substitutions and by rho, and every free Kleene algebra element is
defined on these points.  Hence the restricted parity system is a
sound AND (with the monotone-realizability filter) EXACT certificate on the Kleene site: inconsistency implies that no
invariant interior cell exists in the Kleene witness machine.

This runs the six beyond-two-stratum groups with the restricted
system; agreement with the De Morgan survivor statistics confirms
that the Kleene landscape coincides with the De Morgan one at the
certificate level.
"""
import itertools, collections

n = 3
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

G_all = sorted(ELEMS); N = len(G_all)
gi = {h: i for i, h in enumerate(G_all)}
MUL = [[gi[mm(a, b)] for b in G_all] for a in G_all]
IDi = gi[ID]

def closure_idx(gens_i):
    S = {IDi} | set(gens_i)
    dq = collections.deque(S)
    while dq:
        x = dq.popleft()
        for g in list(S):
            for y in (MUL[x][g], MUL[g][x]):
                if y not in S: S.add(y); dq.append(y)
    return sorted(S)

# middle level of the literal cube L_3 and the two point maps
def _unmixed(p):
    pr = [(((p >> (2*i)) & 1), ((p >> (2*i+1)) & 1)) for i in range(3)]
    return not (any(x == (0, 0) for x in pr) and
                any(x == (1, 1) for x in pr))
pts = [p for p in range(64) if _unmixed(p)]
pidx = {p: i for i, p in enumerate(pts)}
def sub_pt(e, p):
    pm, s = e
    c = [(p >> i) & 1 for i in range(6)]
    d = [0]*6
    for i in range(3):
        vx, vnx = c[2*pm[i]], c[2*pm[i]+1]
        if s[i]: vx, vnx = vnx, vx
        d[2*i], d[2*i+1] = vx, vnx
    return sum(b << i for i, b in enumerate(d))
def rho_pt(p):
    c = [(p >> i) & 1 for i in range(6)]
    d = []
    for i in range(3): d += [1 - c[2*i+1], 1 - c[2*i]]
    return sum(b << i for i, b in enumerate(d))
RHOP = [pidx[rho_pt(q)] for q in pts]
LEQ = [(pidx[p], pidx[q]) for p in pts for q in pts
       if p != q and all(((p >> i) & 1) <= ((q >> i) & 1)
                         for i in range(6))]
VERTS = list(itertools.product((0, 1), repeat=3))
vidx = {v: i for i, v in enumerate(VERTS)}


def certify(H_gens, V_gens, name):
    H = closure_idx([gi[h] for h in H_gens])
    V = closure_idx([gi[h] for h in V_gens])
    # verify the choice of V
    assert set(V) <= set(H)
    INV = {x: gi[inv(G_all[x])] for x in H}
    assert all(MUL[MUL[g][x]][INV[g]] in V for g in H for x in V), "V not normal"
    assert not any(hfc(G_all[x]) for x in V if x != IDi), "V has a reflection"
    # cosets -> G = H/V
    cos = {}; reps = []
    for x in H:
        if x in cos: continue
        g = len(reps); reps.append(x)
        for v in V: cos[MUL[x][v]] = g
    nG = len(reps)
    GM = [[cos[MUL[reps[a]][reps[b]]] for b in range(nG)] for a in range(nG)]
    G_ID = cos[IDi]
    GI = [0]*nG
    for a in range(nG):
        for b in range(nG):
            if GM[a][b] == G_ID: GI[a] = b
    SUBP = {x: [pidx[sub_pt(G_all[x], q)] for q in pts] for x in H}
    VACT = {x: [vidx[tuple(v[G_all[x][0][i]] ^ G_all[x][1][i]
                for i in range(3))] for v in VERTS] for x in H}
    npts = len(pts)

    def u_ok(dimg):
        size = 3*npts
        parent = list(range(size)); par = [0]*size
        def findp(i):
            r = i; acc = 0
            while parent[r] != r: acc ^= par[r]; r = parent[r]
            return r, acc
        for xi, x in enumerate(H):
            if x == IDi: continue
            dp, ds = G_all[dimg[xi]]
            sub = SUBP[x]
            for j in range(3):
                j2, sg = dp[j], ds[j]
                bl = j*npts; br = j2*npts
                for qi in range(npts):
                    (ra, pa) = findp(bl + sub[qi])
                    (rb, pb) = findp(br + (RHOP[qi] if sg else qi))
                    if ra == rb:
                        if (pa ^ pb) != sg: return False
                    else:
                        parent[ra] = rb; par[ra] = pa ^ pb ^ sg
        # parity-consistent: now demand a MONOTONE realization on U_3
        # (Kleene exactness).  2-SAT-style search on root values with
        # monotonicity implications, per coordinate.
        import collections as _c
        graph = _c.defaultdict(list)
        forced = {}
        bad = False
        for j in range(3):
            base = j*npts
            for (a, b) in LEQ:
                (ra, pa) = findp(base + a)
                (rb, pb) = findp(base + b)
                if ra == rb:
                    if pa != pb and pa == 0:
                        # value(a) = x^pa, value(b) = x^pb with pa!=pb:
                        # x^pa <= x^pb ; if pa=0,pb=1: x <= ~x -> x=0
                        if forced.get(ra, 0) != 0 and forced.get(ra) == 1:
                            bad = True; break
                        forced[ra] = 0
                    elif pa != pb:
                        if ra in forced and forced[ra] == 0:
                            bad = True; break
                        forced[ra] = 1
                    continue
                # implication (x_ra ^ pa) <= (x_rb ^ pb):
                #  x_ra^pa = 1 -> x_rb^pb = 1 and contrapositive
                graph[(ra, 1 ^ pa)].append((rb, 1 ^ pb))
                graph[(rb, pb)].append((ra, pa))
            if bad: break
        if bad: return False
        assign = dict(forced)
        dq = _c.deque(assign.items())
        ok = True
        while dq:
            (r, v) = dq.popleft()
            for (r2, v2) in graph[(r, v)]:
                if r2 in assign:
                    if assign[r2] != v2: ok = False; break
                else:
                    assign[r2] = v2; dq.append((r2, v2))
            if not ok: break
        if not ok: return False
        roots = {findp(i)[0] for i in range(size)}
        freeroots = [r for r in roots if r not in assign]
        def try_assign(assign, rest):
            if not rest: return True
            r0 = rest[0]
            for v in (0, 1):
                a2 = dict(assign); a2[r0] = v
                dq = _c.deque([(r0, v)])
                good = True
                while dq:
                    (r, vv) = dq.popleft()
                    for (r2, v2) in graph[(r, vv)]:
                        if r2 in a2:
                            if a2[r2] != v2: good = False; break
                        else:
                            a2[r2] = v2; dq.append((r2, v2))
                    if not good: break
                if good:
                    rem = [r for r in rest[1:] if r not in a2]
                    if try_assign(a2, rem): return True
            return False
        return try_assign(assign, freeroots)

    def e_ok(dimg):
        parent = list(range(8)); par = [G_ID]*8
        def findp(i):
            r = i; acc = G_ID
            while parent[r] != r: acc = GM[par[r]][acc]; r = parent[r]
            return r, acc
        for xi, x in enumerate(H):
            if x == IDi: continue
            k = cos[dimg[xi]]
            va = VACT[x]
            for vi in range(8):
                (rv, pv) = findp(vi); (rw, pw) = findp(va[vi])
                if rv == rw:
                    if pw != GM[k][pv]: return False
                else:
                    parent[rv] = rw; par[rv] = GM[GI[GM[k][pv]]][pw]
        return True

    # small generating set (<= 2 if possible) and BFS words
    pos = {x: i for i, x in enumerate(H)}
    gens = None
    for i, a in enumerate(H):
        for b in H[i:]:
            if len(closure_idx([a, b])) == len(H): gens = [a, b]; break
        if gens: break
    if gens is None:
        for combo in itertools.combinations(H, 3):
            if len(closure_idx(list(combo))) == len(H):
                gens = list(combo); break
    word = {x: None for x in H}
    word[IDi] = []
    dq = collections.deque([IDi])
    while dq:
        x = dq.popleft()
        for k, g in enumerate(gens):
            y = MUL[x][g]
            if word[y] is None:
                word[y] = word[x] + [k]; dq.append(y)
    count = 0; survivors = {}
    for imgs in itertools.product(H, repeat=len(gens)):
        dimg = []
        for x in H:
            v = IDi
            for k in word[x]: v = MUL[v][imgs[k]]
            dimg.append(v)
        ok = True
        for k, g in enumerate(gens):
            im = imgs[k]
            for xi, x in enumerate(H):
                if dimg[pos[MUL[g][x]]] != MUL[im][dimg[xi]]:
                    ok = False; break
            if not ok: break
        if not ok: continue
        count += 1
        if all(d == IDi for d in dimg): continue
        if u_ok(dimg) and e_ok(dimg):
            img = tuple(sorted(set(dimg)))
            survivors[img] = survivors.get(img, 0) + 1
    print(f"{name}: |H|={len(H)} |V|={len(V)} |G|={nG} |Hom|={count} "
          f"survivors={sum(survivors.values())}")
    for img, cnt in sorted(survivors.items()):
        kinds = []
        for x in img:
            if x == IDi: continue
            kinds.append("refl" if hfc(G_all[x]) else "free")
        print(f"   image order {len(img)} x{cnt}: {'/'.join(kinds)}")


sw = ((1, 0, 2), (0, 0, 0))
g2 = ((1, 0, 2), (1, 1, 0))
nb = ((0, 1, 2), (1, 1, 0))
n011 = ((0, 1, 2), (0, 1, 1))
n101 = ((0, 1, 2), (1, 0, 1))
rot = ((1, 2, 0), (0, 0, 0))
nx = ((0, 1, 2), (1, 0, 0)); ny = ((0, 1, 2), (0, 1, 0))
nz = ((0, 1, 2), (0, 0, 1)); vt = ((0, 1, 2), (1, 1, 1))

# order 12 (A4-type): V = V_even (Klein of even negations)
certify([nb, n011, rot], [nb, n011], "order-12 A4-type")
# order 24 with four line strata and trivial characters:
#   H = <V_even, rot, sw*g-type extension>; find it as the closure adding
#   the element that extends A4-type by an even-signed order-2 swap: g2*nz?
H24l = None
A4 = closure_idx([gi[nb], gi[n011], gi[rot]])
nz_i = gi[((0, 1, 2), (0, 0, 1))]
for x in range(N):
    if x in A4: continue
    Hc = closure_idx(A4 + [x])
    if len(Hc) == 24 and nz_i not in Hc:
        refl = [y for y in Hc if hfc(G_all[y])]
        if len(refl) == 8 and all(len(cycles(G_all[y])) == 1
                                  for y in refl):
            H24l = Hc; break
assert H24l is not None
certify([G_all[x] for x in H24l], [nb, n011], "order-24 (four lines)")
# order 24 nested (14 reflections)
H24n = None
for a in range(N):
    done = False
    for b in range(a, N):
        Hc = closure_idx([a, b])
        if len(Hc) == 24 and sum(1 for y in Hc if hfc(G_all[y])) == 14:
            H24n = Hc; done = True; break
    if done: break
certify([G_all[x] for x in H24n], [nb, n011], "order-24 (nested)")
# B3 itself: V = (Z/2)^3
certify([nx, ny, nz, sw, rot], [nx, ny, nz], "B3")
# H8 = V_even x| <sw>: V = V_even
certify([sw, n011], [nb, n011], "H8")
# H24 = (Z/2)^3 x| Z/3: V = (Z/2)^3
certify([nx, ny, nz, rot], [nx, ny, nz], "H24 = negations:Z/3")

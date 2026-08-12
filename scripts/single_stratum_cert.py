"""Single-stratum E-resolution collage: the combined delta-certificate.

Case |H|=12 (A4-type, reduced single stratum): the witness model is
    J := (cube^3 x E) cup_i horns(l_i x E x cube^1 -> l_i),
E = codiscrete nerve of Z/3 (contractible, levelwise finite, free Z/3),
H acting on cube^3 standardly and on E via chi3: H ->> H/V = Z/3.

Body classes of (J/H~)([3]) with twist delta: Hom(H, H) require
  (u-part)  u_j o sigma_h = (~)^{s} u_{pi(j)}   [delta(h) post-action]
  (e-part)  eps o (h on vertices) = rho^{chi3(delta(h))} o eps,
            eps: vertices(cube^3) -> Z/3
Certificate: for every delta whose combined action is nontrivial, one of
the two systems is inconsistent  ==>  NO twisted body classes at all
(here even delta = trivial is blocked on the u-part: H is mixed, no
common fixed cells), so stage-0 invariant classes live only in the
horn/end sieve, where the flow slide gives nullity.

u-part: vector parity union-find on (output slot, middle-level point)
  (exact by the weight rule, Sec 33/37).
e-part: union-find on vertices with Z/3 parities.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
exec(open('scripts/delta_obstruction.py').read().split("# ---- n=2 validation")[0])

n = 3
ELEMS, ID, mm, close, cycles, hfc = make_group_tools(n)

def inv(e):
    p, s = e
    q = [0]*n; t = [0]*n
    for i in range(n): q[p[i]] = i
    for i in range(n): t[i] = s[q[i]]
    return (tuple(q), tuple(t))

# find the |H|=12 mixed-trivial target: V (Klein, free) + 8 order-3 refl
subs = {frozenset([ID])}; frontier = {frozenset([ID])}
while frontier:
    new = set()
    for Hf in frontier:
        for e in ELEMS:
            if e in Hf: continue
            H2 = close(set(Hf) | {e})
            if H2 not in subs: new.add(H2)
    subs |= new; frontier = new

target = None
for Hf in sorted(subs, key=len):
    if len(Hf) != 12: continue
    refl = [h for h in Hf if hfc(h)]
    if len(refl) != 8: continue
    if all(len(cycles(h)) == 1 for h in refl):
        target = Hf; break
assert target is not None
H = sorted(target)
print(f"target |H| = {len(H)}, reflections = {sum(1 for h in H if hfc(h))}")

# V = free radical (order 4), chi3: H -> Z/3 = H/V
V = [h for h in H if h == ID or (not hfc(h) and mm(h, h) == ID)]
assert len(V) == 4
# chi3: pick an order-3 element g0; cosets V, gV, g^2V
g0 = next(h for h in H if hfc(h))
cos1 = {mm(g0, v) for v in V}
cos2 = {mm(mm(g0, g0), v) for v in V}
def chi3(h):
    if h in V: return 0
    if h in cos1: return 1
    assert h in cos2
    return 2
# homomorphism check of chi3
assert all(chi3(mm(a,b)) == (chi3(a)+chi3(b)) % 3 for a in H for b in H)

# vertex action of h on {0,1}^3: v |-> (v_{perm} xor signs) (POST action
# consistent with cell action: (h.c)(i) = ~^{s_i} c(perm_i))
def vert_act(h, v):
    p, s = h
    return tuple(v[p[i]] ^ s[i] for i in range(3))
VERTS = list(itertools.product((0,1), repeat=3))

# middle level of L_3
NL = 64
pts = [p for p in range(NL) if bin(p).count('1') == 3]
idx = {p: i for i, p in enumerate(pts)}
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

def u_system_consistent(delta):
    """u_j o sigma_h = ~^{s_h(j)} u_{perm_h(j)} with (perm_h, s_h) = delta(h)."""
    size = 3 * len(pts)
    parent = list(range(size)); par = [0]*size
    def findp(i):
        r = i; acc = 0
        while parent[r] != r:
            acc ^= par[r]; r = parent[r]
        return r, acc
    for h in H:
        if h == ID: continue
        dp, ds = delta[h]
        for j in range(3):
            j2, s = dp[j], ds[j]
            # (delta(h) . u)(j) = ~^{ds[j]} u(dp[j]); equation u_j∘σ_h = that
            for q in pts:
                lq = sub_pt(h, q)
                rq = rho_pt(q) if s else q
                (ri, pi) = findp(j*len(pts) + idx[lq])
                (rj, pj) = findp(j2*len(pts) + idx[rq])
                if ri == rj:
                    if (pi ^ pj) != s: return False
                else:
                    parent[ri] = rj; par[ri] = pi ^ pj ^ s
    return True

def e_system_consistent(delta):
    """eps: VERTS -> Z/3 with eps(vert_act(h, v)) = eps(v) + chi3(delta(h))."""
    parent = {v: v for v in VERTS}; par = {v: 0 for v in VERTS}
    def findp(v):
        r = v; acc = 0
        while parent[r] != r:
            acc = (acc + par[r]) % 3; r = parent[r]
        return r, acc
    for h in H:
        if h == ID: continue
        k = chi3(delta[h])
        for v in VERTS:
            w = vert_act(h, v)
            (rv, pv) = findp(v); (rw, pw) = findp(w)
            # eps(w) = eps(v) + k  =>  parity(w) - parity(v) = k (rel roots)
            if rv == rw:
                if (pw - pv) % 3 != k % 3: return False
            else:
                parent[rv] = rw; par[rv] = (pw - k - pv) % 3
    return True

# enumerate delta: Hom(H, H)
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
print(f"|Hom(H,H)| = {len(homs)}")

unblocked = []
trivial_ok = 0
for delta in homs:
    if all(v == ID for v in delta.values()):
        # trivial delta = STRICT classes: factor through the contractible
        # cover C = cube^3 x E  ==>  null.  Harmless; count separately.
        if u_system_consistent(delta) and e_system_consistent(delta):
            trivial_ok += 1
        continue
    if u_system_consistent(delta) and e_system_consistent(delta):
        unblocked.append(delta)

print(f"nontrivial delta unblocked: {len(unblocked)} "
      f"(trivial delta consistent: {trivial_ok} — strict, null via C)")
print("CERTIFIED: all nontrivial delta blocked"
      if not unblocked else "INCONCLUSIVE")

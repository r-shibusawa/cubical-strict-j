"""O28 stage 2f: uniformity identifications as the kill mechanism.

lem:garner(ii) identifies val(b.sigma^, c) = val(b, sigma^.c)
along cartesian morphisms of the generating category J.  For the
boundary box shape (del cube^2 into cube^2) x delta^e, the swap
transposition is cartesian (del is swap-stable), so a box whose
datum is swap-invariant has its wad FOLDED by the swap acting on
the first two coordinates -- identifying free sorted positions
(o1,o2,t) ~ (o2,o1,t).  This is the first mechanism that can
change Ch-homology (probes 2c-2e show free wads are inert).
Enumerate swap-invariant boundary boxes, impose the fold on the
free chain stratum, and rerun the kill test.
"""
import sys, itertools, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

K = 3
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], K)

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
sortedW = {q: [c for c in W.level(q)
               if act(c, sort_sub(q), q, q) == c] for q in range(K+1)}
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    return [c for c in itertools.product(Dk, repeat=q)
            if all(comparable(a,b) for a,b in itertools.combinations(c,2))]
ChW = {}
for k in range(K + 1):
    cells = set()
    for q in range(K + 1):
        for s in sortedW[q]:
            for u in chain_subs(q, k):
                cells.add(act(s, u, q, k) if q > 0 else
                          W.cls(k, restrict(s, tuple(), 2, 0, k)))
    ChW[k] = sorted(cells)

ZERO = {q: tuple(0 for _ in F(q)[0]) for q in range(K+2)}
ONE  = {q: tuple(1 for _ in F(q)[0]) for q in range(K+2)}
tvar = tuple(p[0] for p in F(1)[0])
FACES = ['x1=0', 'x1=1', 'x2=0', 'x2=1']
FMAP = {'x1=0': (ZERO[1], tvar), 'x1=1': (ONE[1], tvar),
        'x2=0': (tvar, ZERO[1]), 'x2=1': (tvar, ONE[1])}
def in_face(c12, g, q):
    c1, c2 = c12
    return {'x1=0': c1 == ZERO[q], 'x1=1': c1 == ONE[q],
            'x2=0': c2 == ZERO[q], 'x2=1': c2 == ONE[q]}[g]
def face_ends(g):
    return {'x1=0': (('0','0'), ('0','1')),
            'x1=1': (('1','0'), ('1','1')),
            'x2=0': (('0','0'), ('1','0')),
            'x2=1': (('0','1'), ('1','1'))}[g]
def o_chain(q): return [o_stat_t(j, q) for j in range(0, q + 2)]
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)
def pos_face(c, i, q):
    Tf = coface_T(i, q)
    return tuple(compose(comp, Tf, q, q - 1) for comp in c)
def pos_sub(c, u, q, k):
    return tuple(compose(comp, u, q, k) for comp in c)

W2 = W.level(2)
def face_cell(x, g): return act(x, FMAP[g], 2, 1)
def cyl_end(h, e):
    return act(h, (tvar, ONE[1] if e else ZERO[1]), 2, 1)
def cyl_v(h, side):
    return act(h, ((ONE[1] if side else ZERO[1]), tvar), 2, 1)
SWAP2 = (proj := None)
xy2 = (tuple(p[0] for p in F(2)[0]), tuple(p[1] for p in F(2)[0]))
swap_sub = (xy2[1], xy2[0])   # substitution (y, x) on [2]

# boundary-box data, swap-invariant:
#   w0 . swap = w0,  H[x1=e'] = H[x2=e'] . (swap on s? )
# side cylinders: swap exchanges faces x1=e' <-> x2=e' with the
# same parameter; invariance: H['x1=a'] = H['x2=a'] for a=0,1
def swapface(g):
    return {'x1=0': 'x2=0', 'x1=1': 'x2=1',
            'x2=0': 'x1=0', 'x2=1': 'x1=1'}[g]

kept = FACES[:]
def inP(c, q, e):
    E = ONE[q] if e else ZERO[q]
    return (c[2] == E
            or any(in_face((c[0], c[1]), g, q) for g in kept))

oldI = {c: i for i, c in enumerate(ChW[2])}
def oldbit(cell):
    if cell not in oldI: oldI[cell] = len(oldI)
    return oldI[cell]
basis = []
def insert(v):
    cur = v
    for p in basis: cur = min(cur, cur ^ p)
    if cur: basis.append(cur); return True
    return False
for s in ChW[3]:
    v = 0
    for i in range(4):
        v ^= 1 << oldbit(act(s, coface_T(i, 3), 3, 2))
    insert(v)
print(f"old d3 rank = {len(basis)}", flush=True)

t0 = time.time()
total = 0; gained_any = 0
for e in (0, 1):
    # free chain positions (closure), with swap-orbit quotient
    newCh = {2: set(), 3: set()}
    for q in range(K + 1):
        for c in itertools.product(o_chain(q), repeat=3):
            if inP(c, q, e): continue
            for k in (2, 3):
                for u in chain_subs(q, k):
                    ci = pos_sub(c, u, q, k)
                    if not inP(ci, k, e):
                        newCh[k].add(ci)
    def rep(c, k):
        cs = (compose(c[0], swap_sub, 2, 2) if False else c)
        # swap acts on positions: (c1,c2,ct) -> (c2,c1,ct)
        cw = (c[1], c[0], c[2])
        return min(c, cw)
    free2 = {}
    for c in sorted(newCh[2]):
        free2.setdefault(rep(c, 2), len(free2))
    plan = []
    for c in sorted({rep(c, 3) for c in newCh[3]}):
        rows = []
        ok = True
        for i in range(4):
            fc = pos_face(c, i, 3)
            if inP(fc, 2, e):
                rows.append(('P', fc))
            else:
                r = rep(fc, 2)
                if r in free2: rows.append(('F', free2[r]))
                else: ok = False
        if ok: plan.append(rows)
    nb = 0; gained = 0
    for w0 in W2:
        if act(w0, swap_sub, 2, 2) != w0: continue
        cand = {}
        okw = True
        for g in ('x1=0', 'x1=1'):
            cand[g] = [h for h in W2
                       if cyl_end(h, e) == face_cell(w0, g)]
        for h1, h2 in itertools.product(cand['x1=0'], cand['x1=1']):
            # swap-invariant datum: H[x2=a] := H[x1=a]
            H = {'x1=0': h1, 'x1=1': h2, 'x2=0': h1, 'x2=1': h2}
            # bottom-match for the x2 faces:
            if cyl_end(h1, e) != face_cell(w0, 'x2=0'): continue
            if cyl_end(h2, e) != face_cell(w0, 'x2=1'): continue
            corner = {}; ok = True
            for g in kept:
                e0, e1 = face_ends(g)
                for edge, vert in ((cyl_v(H[g], 0), e0),
                                   (cyl_v(H[g], 1), e1)):
                    if corner.setdefault(vert, edge) != edge:
                        ok = False; break
                if not ok: break
            if not ok: continue
            def b_val(fc):
                if fc[2] == (ONE[2] if e else ZERO[2]):
                    return act(w0, (fc[0], fc[1]), 2, 2)
                g = next(g for g in kept if in_face((fc[0],fc[1]),g,2))
                s = fc[1] if g in ('x1=0','x1=1') else fc[0]
                return act(H[g], (s, fc[2]), 2, 2)
            piv = {}
            for rows in plan:
                nv = 0; ov = 0
                for r in rows:
                    if r[0] == 'P': ov ^= 1 << oldbit(b_val(r[1]))
                    else: nv ^= 1 << r[1]
                while nv:
                    low = nv & -nv
                    if low in piv:
                        pn, po = piv[low]; nv ^= pn; ov ^= po
                    else:
                        piv[low] = (nv, ov); ov = 0; break
                if ov:
                    if insert(ov): gained += 1
            nb += 1
    total += nb
    print(f"e={e}: swap-invariant bdry boxes {nb}, "
          f"gained {gained}, cum rank {len(basis)}, "
          f"{time.time()-t0:.0f}s", flush=True)
    gained_any += gained

b1i = {c: i for i, c in enumerate(ChW[1])}
o2 = {c: i for i, c in enumerate(ChW[2])}
piv2 = {}; kernel = []
for c in ChW[2]:
    col = 0
    for i in range(3):
        col ^= 1 << b1i[act(c, coface_T(i, 2), 2, 1)]
    comb = 1 << o2[c]
    cur, curc = col, comb
    while cur:
        low = cur & -cur
        if low in piv2:
            pc, pcc = piv2[low]; cur ^= pc; curc ^= pcc
        else:
            piv2[low] = (cur, curc); curc = 0; break
    if curc: kernel.append(curc)
survivors = 0
snap = list(basis)
for kv in kernel:
    v = 0
    for cc, i in o2.items():
        if (kv >> i) & 1: v |= 1 << oldI[cc]
    cur = v
    for p in snap: cur = min(cur, cur ^ p)
    if cur: snap.append(cur); survivors += 1
print(f"total swap-folded boxes {total}; "
      f"old Z2 dim = {len(kernel)}; surviving classes = {survivors} "
      f"(stage-0 H2 was 14)", flush=True)

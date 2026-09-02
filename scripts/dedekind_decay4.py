"""O28 stage 2d: stage-1 decay probe with the FULL chain stratum.

New cells of Ch(R1 W) contributed by a box are not only the
sorted free positions but all their chain instances: positions
c = c_s . u with c_s a free sorted position and u a chain
substitution (these stay free since the prescribed part is a
subpresheaf).  Enumerate that closure at levels 2 and 3 and rerun
the box-local kill test.
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
SHAPES = []
for e in (0, 1):
    for f in FACES:
        SHAPES.append(([g for g in FACES if g != f], e, f'horn-{f}-e{e}'))
    SHAPES.append((FACES[:], e, f'bdry-e{e}'))

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
    """instance of position c (level q) along substitution u"""
    return tuple(compose(comp, u, q, k) for comp in c)

def precompute(shape):
    kept, e, name = shape
    E = {q: (ONE[q] if e else ZERO[q]) for q in range(K + 1)}
    def inP(c, q):
        return (c[2] == E[q]
                or any(in_face((c[0], c[1]), g, q) for g in kept))
    # free sorted positions at levels 0..3, then chain-instance
    # closure at levels 2 and 3
    newCh = {2: set(), 3: set()}
    for q in range(K + 1):
        for c in itertools.product(o_chain(q), repeat=3):
            if inP(c, q): continue
            for k in (2, 3):
                for u in chain_subs(q, k):
                    ci = pos_sub(c, u, q, k)
                    if not inP(ci, k):
                        newCh[k].add(ci)
    free2 = {c: i for i, c in enumerate(sorted(newCh[2]))}
    plan = []
    for c in sorted(newCh[3]):
        rows = []
        for i in range(4):
            fc = pos_face(c, i, 3)
            if fc[2] == E[2]:
                rows.append(('w0', (fc[0], fc[1])))
            else:
                hit = next((g for g in kept
                            if in_face((fc[0], fc[1]), g, 2)), None)
                if hit is not None:
                    s = fc[1] if hit in ('x1=0', 'x1=1') else fc[0]
                    rows.append(('side', hit, (s, fc[2])))
                elif fc in free2:
                    rows.append(('free2', free2[fc]))
                else:
                    rows.append(('freeUnsorted', fc))
        plan.append(rows)
    return free2, plan, E, name

W2 = W.level(2)
def face_cell(x, g): return act(x, FMAP[g], 2, 1)
def cyl_end(h, e):
    return act(h, (tvar, ONE[1] if e else ZERO[1]), 2, 1)
def cyl_v(h, side):
    return act(h, ((ONE[1] if side else ZERO[1]), tvar), 2, 1)

oldI = {c: i for i, c in enumerate(ChW[2])}
def oldbit(cell):
    if cell not in oldI: oldI[cell] = len(oldI)
    return oldI[cell]

t0 = time.time()
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

unsorted_hits = 0
total_boxes = 0
for shape in SHAPES:
    kept, e, name0 = shape
    free2, plan, E, name = precompute(shape)
    print(f"{name}: newCh2 {len(free2)}, newCh3 {len(plan)}", flush=True)
    nb = 0
    for w0 in W2:
        cand = {g: [h for h in W2 if cyl_end(h, e) == face_cell(w0, g)]
                for g in kept}
        for hs in itertools.product(*(cand[g] for g in kept)):
            H = dict(zip(kept, hs))
            corner = {}; ok = True
            for g in kept:
                e0, e1 = face_ends(g)
                for edge, vert in ((cyl_v(H[g], 0), e0),
                                   (cyl_v(H[g], 1), e1)):
                    if corner.setdefault(vert, edge) != edge:
                        ok = False; break
                if not ok: break
            if not ok: continue
            piv = {}
            for rows in plan:
                nv = 0; ov = 0; skip = False
                for r in rows:
                    if r[0] == 'w0':
                        ov ^= 1 << oldbit(act(w0, r[1], 2, 2))
                    elif r[0] == 'side':
                        ov ^= 1 << oldbit(act(H[r[1]], r[2], 2, 2))
                    elif r[0] == 'free2':
                        nv ^= 1 << r[1]
                    else:
                        skip = True
                if skip:
                    unsorted_hits += 1; continue
                while nv:
                    low = nv & -nv
                    if low in piv:
                        pn, po = piv[low]; nv ^= pn; ov ^= po
                    else:
                        piv[low] = (nv, ov); ov = 0; break
                if ov: insert(ov)
            nb += 1
    total_boxes += nb
    print(f"  boxes {nb}, cum rank {len(basis)}, "
          f"{time.time()-t0:.0f}s", flush=True)
print(f"total boxes = {total_boxes}, faces at non-Ch free "
      f"positions skipped: {unsorted_hits}", flush=True)

b1i = {c: i for i, c in enumerate(ChW[1])}
o2 = {c: i for i, c in enumerate(ChW[2])}
piv = {}; kernel = []
for c in ChW[2]:
    col = 0
    for i in range(3):
        col ^= 1 << b1i[act(c, coface_T(i, 2), 2, 1)]
    comb = 1 << o2[c]
    cur, curc = col, comb
    while cur:
        low = cur & -cur
        if low in piv:
            pc, pcc = piv[low]; cur ^= pc; curc ^= pcc
        else:
            piv[low] = (cur, curc); curc = 0; break
    if curc: kernel.append(curc)
survivors = 0
snap = list(basis)
for kv in kernel:
    v = 0
    for c, i in o2.items():
        if (kv >> i) & 1: v |= 1 << oldI[c]
    cur = v
    for p in snap: cur = min(cur, cur ^ p)
    if cur: snap.append(cur); survivors += 1
print(f"old Z2 dim = {len(kernel)}; surviving classes = {survivors} "
      f"(stage-0 H2 was 14)", flush=True)

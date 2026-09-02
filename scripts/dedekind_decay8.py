"""O28 stage 2h: DIAGONAL-WALL (realized-horn) boxes.

Theory forces the kill: Real_D is left Quillen for Kan-Quillen
(prop:triangres + rem:horns), so Sing(RR W) -> pt is a trivial
fibration and H2(Sing RR W) = 0.  The classes must die -- and the
canonical killers are horn fillings of Sing(RR W), whose boxes
are (Real Lambda^n_k into cube^n) x delta^e with S the union of
walls {x1=1}, {xi=x_{i+1}} (DIAGONAL walls), {xn=0} minus one.
These shapes were absent from all previous probes.  Enumerate all
data for the n=2 family (codomain cube^3) and kill-test.
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

# walls of realized dDelta^2 in cube^2, as (name, membership,
# parametrization s of the wall, vertex ends of the wall edge)
def wall_mem(wl, c12, q):
    c1, c2 = c12
    if wl == 'A': return c1 == ONE[q]
    if wl == 'D': return c1 == c2
    if wl == 'B': return c2 == ZERO[q]
def wall_param(wl, c12):
    return c12[1] if wl == 'A' else c12[0]
def wall_facecell(wl, w0):
    if wl == 'A': return act(w0, (ONE[1], tvar), 2, 1)
    if wl == 'D': return act(w0, (tvar, tvar), 2, 1)
    if wl == 'B': return act(w0, (tvar, ZERO[1]), 2, 1)
def wall_ends(wl):
    if wl == 'A': return (('1','0'), ('1','1'))
    if wl == 'D': return (('0','0'), ('1','1'))
    if wl == 'B': return (('0','0'), ('1','0'))

SHAPES = []
for e in (0, 1):
    SHAPES.append((['A','D','B'], e, f'dDelta2-e{e}'))
    for omit in 'ADB':
        keep = [w for w in 'ADB' if w != omit]
        SHAPES.append((keep, e, f'Lambda2-no{omit}-e{e}'))

W2 = W.level(2)
def cyl_end(h, e):
    return act(h, (tvar, ONE[1] if e else ZERO[1]), 2, 1)
def cyl_v(h, side):
    return act(h, ((ONE[1] if side else ZERO[1]), tvar), 2, 1)

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

t0 = time.time(); total = 0
for kept, e, name in SHAPES:
    E = {q: (ONE[q] if e else ZERO[q]) for q in range(K + 1)}
    def inP(c, q):
        return (c[2] == E[q]
                or any(wall_mem(wl, (c[0], c[1]), q) for wl in kept))
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
        rows = []; ok = True
        for i in range(4):
            fc = pos_face(c, i, 3)
            if inP(fc, 2):
                if fc[2] == E[2]:
                    rows.append(('w0', (fc[0], fc[1])))
                else:
                    wl = next(w for w in kept
                              if wall_mem(w, (fc[0], fc[1]), 2))
                    rows.append(('side', wl,
                                 (wall_param(wl, (fc[0], fc[1])),
                                  fc[2])))
            elif fc in free2:
                rows.append(('F', free2[fc]))
            else:
                ok = False
        if ok: plan.append(rows)
    nb = 0; gained = 0
    for w0 in W2:
        cand = {wl: [h for h in W2
                     if cyl_end(h, e) == wall_facecell(wl, w0)]
                for wl in kept}
        for hs in itertools.product(*(cand[wl] for wl in kept)):
            H = dict(zip(kept, hs))
            corner = {}; ok = True
            for wl in kept:
                e0, e1 = wall_ends(wl)
                for edge, vert in ((cyl_v(H[wl], 0), e0),
                                   (cyl_v(H[wl], 1), e1)):
                    if corner.setdefault(vert, edge) != edge:
                        ok = False; break
                if not ok: break
            if not ok: continue
            piv = {}
            for rows in plan:
                nv = 0; ov = 0
                for r in rows:
                    if r[0] == 'w0':
                        ov ^= 1 << oldbit(act(w0, r[1], 2, 2))
                    elif r[0] == 'side':
                        ov ^= 1 << oldbit(act(H[r[1]], r[2], 2, 2))
                    else:
                        nv ^= 1 << r[1]
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
    print(f"{name}: newCh2 {len(free2)}, newCh3 {len(plan)}, "
          f"boxes {nb}, gained {gained}, cum rank {len(basis)}, "
          f"{time.time()-t0:.0f}s", flush=True)

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
print(f"total diagonal-wall boxes {total}; old Z2 dim = {len(kernel)}; "
      f"surviving classes = {survivors} (stage-0 H2 was 14)",
      flush=True)

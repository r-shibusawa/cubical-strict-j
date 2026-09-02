"""O28 stage 2e: the SHELL box as H2-killer.

The shell box (T into cube^3) x delta^0 with the contraction
certificate Phi (dedekind_shell.py) is a generating trivial
cofibration over W = W_andor.  Its filler is a 4-cell of R1(W)
whose codomain cube^4 has many free sorted positions.  Test
whether the resulting new Ch 3-cells' boundaries kill the 14
old H2-classes (box-local computation as in decay3/4).
"""
import sys, itertools, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

K = 3
def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)
def meet(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a & b for a, b in zip(out, x))
    return out
def join(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a | b for a, b in zip(out, x))
    return out

A1c, B1c = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2c, B2c = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1c, B1c), (1, A2c, B2c)], K)

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
print(f"Ch(W) levels: {[len(ChW[k]) for k in range(K+1)]}", flush=True)

# shell data
p3, q3, r3 = proj(3,0), proj(3,1), proj(3,2)
PR = {'a2': (meet(p3,r3), meet(p3,r3)),
      'b2': (meet(p3,r3), r3),
      'a1': (const(3,0), meet(p3,r3)),
      'b1': (const(3,0), meet(p3,r3)),
      'n0': (meet(p3,r3), meet(q3,r3)),
      'n1': (meet(p3,q3,r3), meet(r3, join(p3,q3)))}
ZERO = {q: const(q,0) for q in range(K+1)}
ONE  = {q: const(q,1) for q in range(K+1)}
def square_fact(c123, q):
    c1, c2, c3 = c123
    if c1 == c2:      return ('a2', (c1, c3))
    if c2 == ONE[q]:  return ('b2', (c1, c3))
    if c1 == ZERO[q]: return ('a1', (c2, c3))
    if c2 == ZERO[q]: return ('b1', (c1, c3))
    if c3 == ZERO[q]: return ('n0', (c1, c2))
    if c3 == ONE[q]:  return ('n1', (c1, c2))
    return None
def inP(c, q):
    return c[3] == ZERO[q] or square_fact(c[:3], q) is not None
def b_val(c, q):
    if c[3] == ZERO[q] and square_fact(c[:3], q) is None:
        return W.cls(q, (const(q,0), const(q,0)))
    n, z = square_fact(c[:3], q)
    sub = (z[0], z[1], c[3])
    return W.cls(q, tuple(compose(comp, sub, 3, q) for comp in PR[n]))

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

# new Ch cells: chain-instance closure of free sorted positions
newCh = {2: set(), 3: set()}
for q in range(K + 1):
    for c in itertools.product(o_chain(q), repeat=4):
        if inP(c, q): continue
        for k in (2, 3):
            for u in chain_subs(q, k):
                ci = pos_sub(c, u, q, k)
                if not inP(ci, k):
                    newCh[k].add(ci)
print(f"shell box: newCh2 {len(newCh[2])}, newCh3 {len(newCh[3])}",
      flush=True)

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

free2 = {c: i for i, c in enumerate(sorted(newCh[2]))}
piv = {}
skipped = 0
gained = 0
for c in sorted(newCh[3]):
    nv = 0; ov = 0; bad = False
    for i in range(4):
        fc = pos_face(c, i, 3)
        if inP(fc, 2):
            ov ^= 1 << oldbit(b_val(fc, 2))
        elif fc in free2:
            nv ^= 1 << free2[fc]
        else:
            bad = True
    if bad: skipped += 1; continue
    while nv:
        low = nv & -nv
        if low in piv:
            pn, po = piv[low]; nv ^= pn; ov ^= po
        else:
            piv[low] = (nv, ov); ov = 0; break
    if ov:
        if insert(ov): gained += 1
print(f"faces outside Ch skipped: {skipped}; "
      f"new boundary vectors gained: {gained}; "
      f"total rank = {len(basis)}", flush=True)

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
print(f"old Z2 dim = {len(kernel)}; surviving classes = {survivors} "
      f"(stage-0 H2 was 14)", flush=True)

"""Base-fact upgrade for the algebraic isolation program (O23).

(1) Fold-compatible box coordinates: the s in F(3) with
    s(u,u,w) = s(u,1,w) and s(0,u,w) = s(u,0,w) are exactly
    {0, 1, w, u&v, u&v&w, (u&v)|w}  (six elements).

(2) Section base fact for W_{^v} = square/(swap fold, diag fold):
    for every fold-cylinder H in W([3]) (fold conditions in the
    first two coordinates, third coordinate free), the six
    monotone sections H.(u,v,r(u,v)), r in F(2), are either all
    equal to iota (class of the generic cell) or none is.
    Also re-verifies: the only fold-cylinders with an END in the
    class of iota are iota-constant (base fact (ii)), and the
    stronger statement: any fold-cylinder with SOME section =
    iota has ALL sections = iota (and is the degenerate
    cylinder iota.pr).
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, Quotient

def proj(k, i):
    """i-th projection in F(k)"""
    pts, _ = F(k)
    return tuple(p[i] for p in pts)

def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)

def meet(a, b): return tuple(x & y for x, y in zip(a, b))
def join(a, b): return tuple(x | y for x, y in zip(a, b))

# ---------- (1) fold-compatible box coordinates ----------
u2, w2 = proj(2,0), proj(2,1)          # F(2) vars (u,w)
a2 = (u2, u2, w2)   # (u,u,w): [2]->[3]
b2 = (u2, const(2,1), w2)
a1 = (const(2,0), u2, w2)
b1 = (u2, const(2,0), w2)
_, F3 = F(3)
good = [s for s in F3
        if compose(s, a2, 3, 2) == compose(s, b2, 3, 2)
        and compose(s, a1, 3, 2) == compose(s, b1, 3, 2)]
u3, v3, w3 = proj(3,0), proj(3,1), proj(3,2)
expected = {const(3,0), const(3,1), w3, meet(u3,v3),
            meet(meet(u3,v3),w3), join(meet(u3,v3),w3)}
print("(1) fold-compatible s:", len(good),
      "matches expected six:", set(good) == expected)

# ---------- (2) section base fact on W ----------
A1, B1 = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2, B2 = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1, B1), (1, A2, B2)], 3)

iota = W.cls(2, (proj(2,0), proj(2,1)))

# fold maps [2]->[3] and section maps
_, F2 = F(2)
folds = [(a1, b1), (a2, b2)]
sections = [(proj(2,0), proj(2,1), r) for r in F2]  # z_r = (u,v,r)

# enumerate fold-cylinders: classes of level-3 cells with fold conds
from collections import defaultdict
seen = set()
n_cyl = 0; n_iota_cyl = 0; ok_all = True; ok_ends = True
for H in cube_cells(2, 3):
    cH = W.cls(3, H)
    if cH in seen: continue
    seen.add(cH)
    if not all(W.cls(2, tuple(compose(c, a, 3, 2) for c in H)) ==
               W.cls(2, tuple(compose(c, b, 3, 2) for c in H))
               for a, b in folds):
        continue
    n_cyl += 1
    secs = [W.cls(2, tuple(compose(c, z, 3, 2) for c in H))
            for z in sections]
    hit = [sc == iota for sc in secs]
    if any(hit):
        n_iota_cyl += 1
        if not all(hit): ok_all = False
        # ends = sections at r = const:
    # base fact (ii) re-check: end in iota class => constant
    e0 = W.cls(2, tuple(compose(c, (proj(2,0), proj(2,1), const(2,0)), 3, 2) for c in H))
    e1 = W.cls(2, tuple(compose(c, (proj(2,0), proj(2,1), const(2,1)), 3, 2) for c in H))
    if (e0 == iota or e1 == iota) and not (e0 == iota and e1 == iota):
        ok_ends = False

print("(2) fold-cylinder classes in W([3]):", n_cyl)
print("    cylinders with some section = iota:", n_iota_cyl)
print("    all-sections-iota whenever some section is iota:", ok_all)
print("    ends: one end iota => both ends iota:", ok_ends)

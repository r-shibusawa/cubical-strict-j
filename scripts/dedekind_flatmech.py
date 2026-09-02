"""O28 stage 7e: decode the flat strict pairs -- what is the
mechanism, and does it iterate to an infinite flat tower?"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from collections import defaultdict

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def cells(z, m, n, k):
    _, Dk = F(k)
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))
def poly_name(f, m):
    pts, _ = F(m)
    ones = [p for p, v in zip(pts, f) if v]
    if not ones: return "0"
    if len(ones) == len(pts): return "1"
    mins = [p for p in ones
            if not any(q != p and all(a <= b for a, b in zip(q, p))
                       for q in ones)]
    terms = []
    for p in mins:
        vs = [f"x{i+1}" for i, b in enumerate(p) if b]
        terms.append("^".join(vs) if vs else "1")
    return " v ".join(terms)

random.seed(29)
n, m = 3, 3
_, D3 = F(3)
gens = random.sample(list(itertools.product(D3, repeat=3)), 2500)
groups = defaultdict(list)
for z in gens:
    fp = (cells(z, m, n, 1), cells(z, m, n, 2))
    groups[fp].append(z)
def member(z2, z, k):
    _, Dk = F(k)
    for u in itertools.product(Dk, repeat=m):
        if rest(z, u, m, k) == z2: return True
    return False

pairs = []
for fp, zs in groups.items():
    if len(zs) < 2: continue
    by3 = defaultdict(list)
    for z in zs: by3[cells(z, m, n, 3)].append(z)
    if len(by3) < 2: continue
    keys = sorted(by3, key=len)
    small, big = by3[keys[0]][0], by3[keys[-1]][0]
    if member(small, big, 3) and not member(big, small, 3):
        pairs.append((big, small))
for big, small in pairs:
    print("A  =", tuple(poly_name(c, 3) for c in big), flush=True)
    print("A' =", tuple(poly_name(c, 3) for c in small), flush=True)
    # which substitution: small = big o u?
    for u in itertools.product(D3, repeat=3):
        if rest(big, u, 3, 3) == small:
            print("  u =", tuple(poly_name(c, 3) for c in u),
                  flush=True)
            break
    print("---", flush=True)

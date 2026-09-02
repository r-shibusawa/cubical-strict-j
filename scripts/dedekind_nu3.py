"""O28 stage 7d: the three ambiguous fingerprint groups of cube^3
-- are their members in containment (breaking nu_2-drop) or
incomparable (nu_2-drop survives)?"""
import sys, itertools, random, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from collections import defaultdict

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def cells(z, m, n, k):
    _, Dk = F(k)
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))

random.seed(29)
n, m = 3, 3
_, D3 = F(3)
gens = random.sample(list(itertools.product(D3, repeat=3)), 2500)
groups = defaultdict(list)
for z in gens:
    fp = (cells(z, m, n, 1), cells(z, m, n, 2))
    groups[fp].append(z)
def member(z2, z, k):
    """z2 (level k) in <z>? exact early-exit"""
    _, Dk = F(k)
    for u in itertools.product(Dk, repeat=m):
        if rest(z, u, m, k) == z2: return True
    return False

found = 0
for fp, zs in groups.items():
    if len(zs) < 2: continue
    if len(zs) > 6: zs = random.sample(zs, 6)
    # partition members by level-3 set
    by3 = defaultdict(list)
    for z in zs: by3[cells(z, m, n, 3)].append(z)
    if len(by3) < 2: continue
    found += 1
    reps = [v[0] for v in by3.values()]
    print(f"group #{found}: {len(by3)} distinct atoms, "
          f"level-3 sizes {[len(k) for k in by3]}", flush=True)
    for i in range(len(reps)):
        for j in range(len(reps)):
            if i == j: continue
            zi, zj = reps[i], reps[j]
            inc = member(zj, zi, 3)   # zj in <zi>?
            if inc:
                back = member(zi, zj, 3)
                rel = "EQUAL?!" if back else "STRICT FLAT PAIR"
                print(f"  atom{j} in atom{i}: {rel}", flush=True)
    else:
        pass
print(f"ambiguous groups analyzed: {found}", flush=True)

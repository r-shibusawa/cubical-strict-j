"""Referee check 2b: for idempotent substitutions eps on [n], does the
atom <eps> admit a 'unit' c = eps o v with some power c^k = eps, c != eps,
and c NOT of the form eps o pi (pi a coordinate permutation)?
Such c is a generator-level coincidence in X = <eps>/(eps ~ c) that the
idempotent-power reduction of lem:minpres cannot remove (the reduction
loops: idempotent power of c is eps itself, same atom, same |L|).
"""
import sys, itertools
sys.path.insert(0, '/Users/shibusawa/Dev/DIT/FormalizedMathematics/scripts')
from dedekind_site import F, compose

n = 3
Dn = F(n)[1]
pts, _ = F(n)
projs = [tuple(p[i] for p in pts) for i in range(n)]
perms = [tuple(projs[i] for i in pi)
         for pi in itertools.permutations(range(n))]

def sub(t, u):
    return tuple(compose(c, u, n, n) for c in t)

cells = list(itertools.product(Dn, repeat=n))
idems = [e for e in cells if sub(e, e) == e]
print(f"n={n}: {len(idems)} idempotents", flush=True)

found = 0
for ei, eps in enumerate(idems):
    if eps == tuple(projs):  # identity: units are the permutations
        continue
    perminst = {sub(eps, pi) for pi in perms}
    for v in cells:
        c = sub(eps, v)
        if c == eps or c in perminst: continue
        # powers of c
        p = c; k = 1; ok = False
        seen = set()
        while p not in seen:
            seen.add(p)
            p = sub(p, c); k += 1
            if p == eps:
                ok = True; break
        if ok:
            found += 1
            print(f"UNIT FOUND: eps={eps}\n  c={c} (c^{k}=eps), "
                  f"not a permutation instance", flush=True)
            break
    if found >= 4: break
print(f"total found: {found}")

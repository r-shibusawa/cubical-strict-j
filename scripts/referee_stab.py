"""Referee check 2 (lem:minpres): find b in D(n)^n, e in D(n)^n with
 - e NOT a coordinate permutation (non-invertible substitution),
 - idempotent power eps of e satisfies b o eps = b  (reduction vacuous),
 - b o e is NOT a permutation instance of b (b o e != b o pi for all pi).
Such (b, e) defeats the written reduction argument: e generates a
'self-stabilizer'-type coincidence that the idempotent-power retraction
cannot remove.  (Whether it defeats the LEMMA depends on whether some
other minimal presentation avoids it, but it refutes the given proof.)
"""
import sys, itertools
sys.path.insert(0, '/Users/shibusawa/Dev/DIT/FormalizedMathematics/scripts')
from dedekind_site import F, compose

def sub(t, u, n):
    # t, u: n-tuples over D(n); t o u
    return tuple(compose(c, u, n, n) for c in t)

def run(n, bs, es, perms):
    found = 0
    for e in es:
        if e in perms: continue
        # idempotent power
        p = e
        seen = {e: 1}
        k = 1
        while True:
            p2 = sub(p, p, n)
            if p2 == p: break
            p = sub(p, e, n)
            k += 1
            if k > 64: break
        # p is now some power; find true idempotent power by doubling
        # simpler: iterate powers until repetition, pick idempotent among them
        powers = [e]
        cur = e
        for _ in range(40):
            cur = sub(cur, e, n)
            powers.append(cur)
            if cur == powers[-2]: break
        idems = [q for q in powers if sub(q, q, n) == q]
        if not idems: continue
        eps = idems[0]
        for b in bs:
            if sub(b, eps, n) != b: continue
            be = sub(b, e, n)
            if any(be == sub(b, pi, n) for pi in perms): continue
            print(f"FOUND n={n}: b={b} e={e} eps={eps} b.e={be}")
            found += 1
            if found >= 5: return found
    return found

for n in (2,):
    Dn = F(n)[1]
    pts, _ = F(n)
    projs = [tuple(p[i] for p in pts) for i in range(n)]
    perms = [tuple(projs[i] for i in pi)
             for pi in itertools.permutations(range(n))]
    cells = list(itertools.product(Dn, repeat=n))
    f = run(n, cells, cells, perms)
    print(f"n={n}: found {f}", flush=True)

# n=3 sampled
import random
random.seed(3)
n = 3
Dn = F(n)[1]
pts, _ = F(n)
projs = [tuple(p[i] for p in pts) for i in range(n)]
perms = [tuple(projs[i] for i in pi)
         for pi in itertools.permutations(range(n))]
cells = list(itertools.product(Dn, repeat=n))
bs = random.sample(cells, 400)
es = random.sample(cells, 400)
f = run(n, bs, es, perms)
print(f"n=3 (sampled): found {f}", flush=True)

"""O28 stage 3c: the master identity (T0): S n Ch(cube^n) = Ch(S)
for subpresheaves S of a cube (ambient chain cells lying in S are
already chain instances of sorted cells OF S).

(T0) implies (I2) and (T2) formally.  Sweep: all cube^2 atoms,
standard wall shapes, random two-atom unions, all sampled cube^3
frontier atoms, and cylinders S (x) cube^1 inside cube^3.
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
K = 3
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    return [c for c in itertools.product(Dk, repeat=q)
            if all(comparable(a,b) for a,b in itertools.combinations(c,2))]
CS = {(q,k): chain_subs(q,k) for q in range(K+1) for k in range(K+1)}
def Ch(S):
    out = {k: set() for k in range(K + 1)}
    for q in range(K + 1):
        for c in S[q]:
            if rest(c, sort_sub(q), q, q) != c: continue
            for k in range(K + 1):
                for u in CS[(q, k)]:
                    out[k].add(rest(c, u, q, k))
    return out
def ambient(S, n):
    return {k: {c for c in S[k]
                if all(comparable(a,b)
                       for a,b in itertools.combinations(c,2))}
            for k in range(K + 1)}
def t0(S, n, name):
    chS = Ch(S); amb = ambient(S, n)
    for k in range(K + 1):
        if amb[k] != chS[k]:
            d1 = amb[k] - chS[k]; d2 = chS[k] - amb[k]
            print(f"(T0) FAIL {name} level {k}: "
                  f"amb-only {len(d1)}, ch-only {len(d2)}; "
                  f"witness {sorted(d1 or d2)[0]}", flush=True)
            return False
    return True
def atom(z, j, n):
    S = {}
    for k in range(K + 1):
        _, Dk = F(k)
        S[k] = {rest(z, u, j, k)
                for u in itertools.product(Dk, repeat=j)}
    return S
def union(*Ss):
    return {k: set().union(*(S[k] for S in Ss)) for k in range(K+1)}

_, D2 = F(2)
atoms2 = []
seen = set()
for z in itertools.product(D2, repeat=2):
    S = atom(z, 2, 2)
    key = frozenset(S[2])
    if key in seen: continue
    seen.add(key); atoms2.append(S)
ok = sum(t0(S, 2, f"atom2#{i}") for i, S in enumerate(atoms2))
print(f"(T0) cube^2 atoms: {ok}/{len(atoms2)} ok", flush=True)
random.seed(2)
cnt = 0
for _ in range(30):
    A, B = random.sample(atoms2, 2)
    cnt += t0(union(A, B), 2, "union2")
print(f"(T0) cube^2 random unions: {cnt}/30 ok", flush=True)

_, D3 = F(3)
u3 = tuple(p[0] for p in F(3)[0]); v3 = tuple(p[1] for p in F(3)[0])
w3 = tuple(p[2] for p in F(3)[0])
def mt3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a & b for a, b in zip(o, x))
    return o
def jn3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a | b for a, b in zip(o, x))
    return o
pool = [mt3(u3,v3,w3), mt3(u3,v3), mt3(u3,w3), mt3(v3,w3),
        u3, v3, w3, jn3(u3,v3), jn3(u3,w3), jn3(v3,w3),
        mt3(u3,jn3(v3,w3)), mt3(v3,jn3(u3,w3)), jn3(u3,mt3(v3,w3))]
random.seed(3)
zs = [tuple(random.choice(pool) for _ in range(3)) for _ in range(25)]
zs.append((mt3(u3,v3,w3), mt3(u3,v3), mt3(u3, jn3(v3,w3))))  # T5
cnt3 = 0
for i, z in enumerate(zs):
    cnt3 += t0(atom(z, 3, 3), 3, f"atom3#{i}")
print(f"(T0) cube^3 atoms: {cnt3}/{len(zs)} ok", flush=True)

# cylinders S x cube^1 in cube^3 for a few S
xv = tuple(p[0] for p in F(1)[0])
c01 = tuple(0 for _ in F(1)[0]); c11 = tuple(1 for _ in F(1)[0])
E = {n: atom(z, 1, 2) for n, z in
     {'x1=0': (c01, xv), 'x1=1': (c11, xv), 'x2=0': (xv, c01),
      'x2=1': (xv, c11), 'diag': (xv, xv)}.items()}
xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
tests = {'bdry': union(E['x1=0'],E['x1=1'],E['x2=0'],E['x2=1']),
         'dDelta2': union(E['x1=1'], E['diag'], E['x2=0']),
         'O': atom((mt3(xx,yy)[:len(xx)] if False else
                    tuple(a & b for a,b in zip(xx,yy)),
                    tuple(a | b for a,b in zip(xx,yy))), 2, 2),
         'full': atom((xx, yy), 2, 2)}
cntc = 0
for name, S in tests.items():
    cyl = {}
    for k in range(K + 1):
        _, Dk = F(k)
        cyl[k] = {(c1, c2, ct) for (c1, c2) in S[k] for ct in Dk}
    cntc += t0(cyl, 3, f"cyl-{name}")
print(f"(T0) cylinders: {cntc}/{len(tests)} ok", flush=True)

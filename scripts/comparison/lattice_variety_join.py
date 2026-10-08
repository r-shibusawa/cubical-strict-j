"""Joins of lattice varieties vs meets of samenesses (congruence-distributive, not permutable).
V = var(M3) (SI members 2, M3), V' = var(N5) (SI members 2, N5), V v V' (SI members 2, M3, N5)
by Jonsson's lemma.  theta_V(A) = meet of the congruences of A with SI quotient in SI(V).
W_V = {h : A/theta_V(A) -> B/theta_V(B) bijective}.  Test W_{V v V'} == W_V  ∩  W_{V'} on lattice
homomorphisms between sublattices (size <= SMAX) of small products of 2, M3, N5.
"""
import itertools as it, random, sys

class Lat:
    def __init__(self, n, meet, join):
        self.n = n; self.meet = meet; self.join = join
    def le(self, a, b): return self.meet[a][b] == a

def from_poset(elems, leq):
    n = len(elems)
    idx = {e: i for i, e in enumerate(elems)}
    meet = [[None]*n for _ in range(n)]; join = [[None]*n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            lo = [c for c in range(n) if leq(elems[c], elems[a]) and leq(elems[c], elems[b])]
            m = [c for c in lo if all(leq(elems[d], elems[c]) for d in lo)]
            up = [c for c in range(n) if leq(elems[a], elems[c]) and leq(elems[b], elems[c])]
            j = [c for c in up if all(leq(elems[c], elems[d]) for d in up)]
            assert len(m) == 1 and len(j) == 1
            meet[a][b] = m[0]; join[a][b] = j[0]
    return Lat(n, meet, join)

TWO = from_poset([0, 1], lambda a, b: a <= b)
M3 = from_poset(['0', 'a', 'b', 'c', '1'], lambda x, y: x == y or x == '0' or y == '1')
N5 = from_poset(['0', 'a', 'b', 'c', '1'], lambda x, y: x == y or x == '0' or y == '1' or (x, y) == ('a', 'b'))

def product(L, M):
    n = L.n * M.n
    def enc(a, b): return a * M.n + b
    meet = [[0]*n for _ in range(n)]; join = [[0]*n for _ in range(n)]
    for a1 in range(L.n):
        for b1 in range(M.n):
            for a2 in range(L.n):
                for b2 in range(M.n):
                    meet[enc(a1,b1)][enc(a2,b2)] = enc(L.meet[a1][a2], M.meet[b1][b2])
                    join[enc(a1,b1)][enc(a2,b2)] = enc(L.join[a1][a2], M.join[b1][b2])
    return Lat(n, meet, join)

def sublattice(P, gens):
    S = set(gens); frontier = list(S)
    while frontier:
        new = []
        for a in list(S):
            for b in frontier:
                for c in (P.meet[a][b], P.join[a][b]):
                    if c not in S: S.add(c); new.append(c)
        frontier = new
    el = sorted(S); idx = {e: i for i, e in enumerate(el)}
    return Lat(len(el), [[idx[P.meet[a][b]] for b in el] for a in el], [[idx[P.join[a][b]] for b in el] for a in el])

def canon(L):
    """isomorphism-invariant key (brute force for n<=8)."""
    best = None
    for p in it.permutations(range(L.n)):
        key = tuple(p[L.meet[a][b]] for a in range(L.n) for b in range(L.n)) + tuple(p[L.join[a][b]] for a in range(L.n) for b in range(L.n))
        # cheap pruning: compare lexicographically
        if best is None or key < best: best = key
    return best

def iso(L, M):
    return L.n == M.n and canon(L) == canon(M)

def cg(L, pairs):
    n = L.n; parent = list(range(n))
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    todo = list(pairs); 
    while todo:
        u, v = todo.pop(); ru, rv = find(u), find(v)
        if ru == rv: continue
        parent[ru] = rv
        for c in range(n):
            todo.append((L.meet[u][c], L.meet[v][c])); todo.append((L.join[u][c], L.join[v][c]))
    return tuple(find(x) for x in range(n))

def quotient(L, th):
    cl = sorted(set(th)); idx = {c: i for i, c in enumerate(cl)}
    rep = {c: next(x for x in range(L.n) if th[x] == c) for c in cl}
    n = len(cl)
    meet = [[idx[th[L.meet[rep[a]][rep[b]]]] for b in cl] for a in cl]
    join = [[idx[th[L.join[rep[a]][rep[b]]]] for b in cl] for a in cl]
    return Lat(n, meet, join)

def all_congruences(L):
    princ = {cg(L, [(a, b)]) for a in range(L.n) for b in range(a + 1, L.n)}
    delta = tuple(range(L.n)); cons = {delta} | princ
    frontier = list(princ)
    while frontier:
        new = []
        for t in frontier:
            for s in list(cons):
                j = cg(L, [(x, t[x]) for x in range(L.n)] + [(x, s[x]) for x in range(L.n)])
                if j not in cons: cons.add(j); new.append(j)
        frontier = new
    return cons

SI = {'M3': [TWO, M3], 'N5': [TWO, N5], 'join': [TWO, M3, N5]}
_vcache = {}
def verbal(L, name):
    key = (id(L), name)
    if key in _vcache: return _vcache[key]
    ths = []
    for th in all_congruences(L):
        Q = quotient(L, th)
        if any(iso(Q, S) for S in SI[name]): ths.append(th)
    # meet of the congruences (including the total one if none): elements x,y identified iff identified by all
    n = L.n
    if not ths: res = tuple([0]*n)
    else:
        classes = {}
        res = []
        for x in range(n):
            sig = tuple(th[x] for th in ths)
            classes.setdefault(sig, x); res.append(classes[sig])
        res = tuple(res)
    _vcache[key] = res; return res

def induced_bijective(A, B, h, name):
    tA = verbal(A, name); tB = verbal(B, name)
    img = {}
    for x in range(A.n):
        c, d = tA[x], tB[h[x]]
        if c in img and img[c] != d: return False
        img[c] = d
    return len(set(img.values())) == len(img) == len(set(tB))

def homs(A, B, limit=20000):
    out = []
    order = list(range(A.n))
    h = [None]*A.n
    def ok(i):
        for j in range(i + 1):
            if h[A.meet[order[i]][order[j]]] is not None and h[A.meet[order[i]][order[j]]] != B.meet[h[order[i]]][h[order[j]]]: return False
            if h[A.join[order[i]][order[j]]] is not None and h[A.join[order[i]][order[j]]] != B.join[h[order[i]]][h[order[j]]]: return False
        return True
    def rec(i):
        if len(out) >= limit: return
        if i == A.n: out.append(tuple(h)); return
        for b in range(B.n):
            h[order[i]] = b
            if ok(i): rec(i + 1)
            h[order[i]] = None
    rec(0)
    # filter full check
    return [hh for hh in out if all(hh[A.meet[a][b]] == B.meet[hh[a]][hh[b]] and hh[A.join[a][b]] == B.join[hh[a]][hh[b]] for a in range(A.n) for b in range(A.n))]

if __name__ == "__main__":
    SMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    random.seed(seed)
    bases = [product(M3, N5), product(M3, M3), product(N5, N5), product(product(TWO, TWO), N5), product(product(TWO, TWO), M3), product(M3, TWO), product(N5, TWO)]
    fam = {}
    for P in bases:
        for _ in range(400):
            k = random.choice([1, 2, 2, 3, 3, 4])
            L = sublattice(P, random.sample(range(P.n), k))
            if L.n <= SMAX and L.n >= 2:
                key = (L.n, canon(L)) if L.n <= 7 else (L.n, random.random())
                fam.setdefault(key, L)
    for L in (TWO, M3, N5): fam.setdefault((L.n, canon(L)), L)
    lats = list(fam.values())
    print("lattices:", len(lats), "sizes:", sorted(L.n for L in lats), flush=True)
    cnt = fails = 0
    for A in lats:
        for B in lats:
            for h in homs(A, B):
                v = induced_bijective(A, B, h, 'M3'); vp = induced_bijective(A, B, h, 'N5'); j = induced_bijective(A, B, h, 'join')
                cnt += 1
                if (v and vp) != j:
                    fails += 1
                    if fails <= 5: print("FAIL", A.n, B.n, h, v, vp, j, flush=True)
    print(f"homs={cnt} failures={fails}", flush=True)

"""The order-8 'nilpotent cycle' monoid Mbar = {1, 1_a, 1_b, u, v, uv, vu, 0}: contracted monoid of
the category a <-> b (u: a->b, v: b->a) with all words of length >= 3 equal to 0 (the Rees
quotient of the cyclic monoid M(2,3) by its ideal of long arrows).  Product = 'then'.
Its ideals D = <1_b>, E = <1_a> have D ∩ E = {u,v,uv,vu,0}, non-idempotent, I' = {0}.
W_E = {f : f bijective on X.1_a}, W_D = {f : f bijective on X.1_b}, W_{I'} = {f : bijective on X.0}.
Tools: Cayley table, enumeration of all right Mbar-sets of size <= n (as structures
(X, A=X.1_a, B=X.1_b, Z=X.0, p_a, p_b, u, v)), canonical forms, and the finite-universe
two-out-of-three closure of W_D u W_E, checking whether every W_{I'}-map is derived."""
import itertools as it, sys
from threefold_transformation import two_sided_ideals, product

ONE, A1, B1, U, V, UV, VU, Z0 = range(8)
NAMES = ['1','1a','1b','u','v','uv','vu','0']
# arrows: (src,tgt) with 1_a=(a,a),1_b=(b,b),u=(a,b),v=(b,a),uv=(a,a),vu=(b,b); lengths 0,0,1,1,2,2
INFO = {A1:('a','a',0), B1:('b','b',0), U:('a','b',1), V:('b','a',1), UV:('a','a',2), VU:('b','b',2)}
def mul(x, y):
    if x == ONE: return y
    if y == ONE: return x
    if x == Z0 or y == Z0: return Z0
    s1,t1,l1 = INFO[x]; s2,t2,l2 = INFO[y]
    if t1 != s2: return Z0
    l = l1 + l2
    if l >= 3: return Z0
    for k,(s,t,ll) in INFO.items():
        if (s,t,ll) == (s1,t2,l): return k
    raise RuntimeError
T = [[mul(x,y) for y in range(8)] for x in range(8)]

def msets(n):
    """all right Mbar-sets on {0..n-1} (labelled), as action tables act[(x,m)]"""
    X = list(range(n)); out = []
    for A in it.product([0,1], repeat=n):
        Aset = [x for x in X if A[x]]
        if not Aset: continue
        for B in it.product([0,1], repeat=n):
            Bset = [x for x in X if B[x]]
            if not Bset: continue
            Zc = [x for x in X if A[x] and B[x]]
            for Zsel in it.product([0,1], repeat=len(Zc)):
                Zset = [x for x,s in zip(Zc,Zsel) if s]
                if not Zset: continue
                # p_a: X -> A identity on A; p_b: X -> B identity on B; on A, p_b = r (into Z); on B, p_a = r
                freeX = [x for x in X if not A[x] and not B[x]]
                for pa_free in it.product(Aset, repeat=len(freeX)):
                    for pb_free in it.product(Bset, repeat=len(freeX)):
                        for rA in it.product(Zset, repeat=len(Aset)):      # p_b on A (= r on A)
                            for rB in it.product(Zset, repeat=len(Bset)):  # p_a on B (= r on B)
                                pa = {}; pb = {}
                                for x in Aset: pa[x] = x
                                for x in Bset: pb[x] = x
                                for x,a in zip(Aset, rA): pb[x] = a
                                for x,b in zip(Bset, rB): pa[x] = b
                                for x,a in zip(freeX, pa_free): pa[x] = a
                                for x,b in zip(freeX, pb_free): pb[x] = b
                                # consistency: on Z, pa=pb=id requires rA[z]=z, rB[z]=z
                                if any(pb[z] != z or pa[z] != z for z in Zset): continue
                                # r = pb o pa = pa o pb
                                r = {x: pb[pa[x]] for x in X}
                                if any(pa[pb[x]] != r[x] for x in X): continue
                                if any(r[x] not in Zset for x in X): continue
                                for ut in it.product(Bset, repeat=len(Aset)):
                                    u = dict(zip(Aset, ut))
                                    if any(u[z] != z for z in Zset): continue
                                    for vt in it.product(Aset, repeat=len(Bset)):
                                        v = dict(zip(Bset, vt))
                                        if any(v[z] != z for z in Zset): continue
                                        # relations: (uv)^2 = r on A, (vu)^2 = r on B, r(u x)=r(x), r(v y)=r(y)
                                        ok = True
                                        for x in Aset:
                                            if v[u[v[u[x]]]] != r[x] or r[u[x]] != r[x]: ok = False; break
                                        if not ok: continue
                                        for y in Bset:
                                            if u[v[u[v[y]]]] != r[y] or r[v[y]] != r[y]: ok = False; break
                                        if not ok: continue
                                        act = {}
                                        for x in X:
                                            act[(x,ONE)] = x; act[(x,A1)] = pa[x]; act[(x,B1)] = pb[x]
                                            act[(x,U)] = u[pa[x]]; act[(x,V)] = v[pb[x]]
                                            act[(x,UV)] = v[u[pa[x]]]; act[(x,VU)] = u[v[pb[x]]]; act[(x,Z0)] = r[x]
                                        # verify action axiom
                                        if all(act[(act[(x,m)],m2)] == act[(x,T[m][m2])] for x in X for m in range(8) for m2 in range(8)):
                                            out.append(act)
    return out

def canon(act, n):
    best = None
    for p in it.permutations(range(n)):
        key = tuple(p[act[(x,m)]] for x in range(n) for m in range(8))
        # relabel: element x -> p[x]; table indexed by new labels
        tab = [None]*(n*8)
        for x in range(n):
            for m in range(8): tab[p[x]*8+m] = p[act[(x,m)]]
        key = tuple(tab)
        if best is None or key < best: best = key
    return best

def homs(X, Xa, Y, Ya, n=8):
    """equivariant maps X->Y (X,Y element lists; Xa, Ya action dicts). Backtracking on generators."""
    gens = []; cov = set()
    for x in X:
        if x not in cov: gens.append(x); cov |= {Xa[(x,m)] for m in range(n)}
    expr = {}
    for g in gens:
        for m in range(n): expr.setdefault(Xa[(g,m)], (g,m))
    res = []
    def rec(i, phi):
        if i == len(gens):
            full = {}
            for x in X:
                g,m = expr[x]; full[x] = Ya[(phi[g],m)]
            if all(full[Xa[(x,m)]] == Ya[(full[x],m)] for x in X for m in range(n)):
                res.append(tuple(full[x] for x in X))
            return
        for y in Y:
            phi[gens[i]] = y; rec(i+1, phi); del phi[gens[i]]
    rec(0, {}); return res

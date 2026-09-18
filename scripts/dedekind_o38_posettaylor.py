"""Taylor (4-ary Siggers) test for a finite poset P given by its <= relation.
CSP(P, <=_P) is in P iff P has a Taylor polymorphism (idempotent, monotone in
the poset order, Siggers identity). NP-complete otherwise (Bulatov-Zhuk)."""
import itertools as it
from pysat.solvers import Glucose3
def has_taylor_poset(N, le):   # le[i][j] = (i <= j) in P, elements 0..N-1
    # covers for monotonicity encoding: use full le (monotone in each arg)
    tuples=list(it.product(range(N),repeat=4)); ti={t:k for k,t in enumerate(tuples)}
    # output s(t) in P: encode as one-hot over N values (exactly one true)
    def var(k,val): return k*N+val+1
    g=Glucose3()
    for k in range(len(tuples)):
        g.add_clause([var(k,v) for v in range(N)])          # at least one
        for a in range(N):
            for b in range(a+1,N):
                g.add_clause([-var(k,a),-var(k,b)])         # at most one
    # idempotent
    for x in range(N):
        k=ti[(x,x,x,x)]
        g.add_clause([var(k,x)])
        for v in range(N):
            if v!=x: g.add_clause([-var(k,v)])
    # monotone in each argument: if t <= t' (componentwise in poset order) then s(t) <= s(t')
    def cle(t,t2): return all(le[t[p]][t2[p]] for p in range(4))
    # only need covering pairs; use all comparable pairs for correctness (N small)
    for t in tuples:
        for t2 in tuples:
            if t!=t2 and cle(t,t2):
                k,k2=ti[t],ti[t2]
                # s(t) <= s(t2): for each value a of s(t), s(t2) must be some b>=a
                for a in range(N):
                    g.add_clause([-var(k,a)]+[var(k2,b) for b in range(N) if le[a][b]])
    # Siggers: s(a,r,e,a)=s(r,a,r,e)
    for a in range(N):
        for r in range(N):
            for e in range(N):
                k1=ti[(a,r,e,a)];k2=ti[(r,a,r,e)]
                for v in range(N):
                    g.add_clause([-var(k1,v),var(k2,v)]); g.add_clause([var(k1,v),-var(k2,v)])
    res=g.solve(); g.delete(); return res

def make_le(N, relations):
    # relations: list of (i,j) meaning i<j (strict); build reflexive-transitive
    le=[[i==j for j in range(N)] for i in range(N)]
    for i,j in relations: le[i][j]=True
    # transitive closure
    for k in range(N):
        for i in range(N):
            for j in range(N):
                if le[i][k] and le[k][j]: le[i][j]=True
    return le

# Candidates (element indices). B=bottom, T=top.
tests={}
# N5: 0=bot,1=a,2=b,3=c,4=top ; 0<1<2<4, 0<3<4
tests["N5"]=(5,[(0,1),(1,2),(2,4),(0,3),(3,4)])
# M3 (lattice): 0<{1,2,3}<4
tests["M3"]=(5,[(0,1),(0,2),(0,3),(1,4),(2,4),(3,4)])
# bounded 3-crown: bot=0, a=1,2,3, b=4,5,6, top=7 ; a_i<b_j iff i!=j
crown=[(0,1),(0,2),(0,3),(4,7),(5,7),(6,7)]
ai=[1,2,3]; bj=[4,5,6]
for x in range(3):
    for y in range(3):
        if x!=y: crown.append((ai[x],bj[y]))
tests["bounded-3-crown"]=(8,crown)
# bounded "4-crown" a_i<b_j iff i!=j (4 each)
c4=[]; a4=[1,2,3,4]; b4=[5,6,7,8]
for x in a4: c4.append((0,x))
for y in b4: c4.append((y,9))
for x in range(4):
    for y in range(4):
        if x!=y: c4.append((a4[x],b4[y]))
tests["bounded-4-crown"]=(10,c4)
for name,(N,rels) in tests.items():
    le=make_le(N,rels)
    print(f"{name}: N={N}  Taylor(P)={has_taylor_poset(N,le)}",flush=True)

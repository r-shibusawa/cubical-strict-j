"""Object-free test for the finite-category join conjecture (monoid case).

For idempotent two-sided ideals D, D' of a finite monoid M, the k-fold alternating
sheafification is Phi_k X = Hom_M(T_k, X) where T_k = D_k (x)_M ... (x)_M D_1 (tensor
of M-M-bisets, alternating D_1 = D, D_2 = D', ...), and the unit Phi_{k-1} -> Phi_k is
induced by multiplication T_k = D_k (x) T_{k-1} -> T_{k-1}.  By Yoneda, the chain
stabilises for ALL M-sets X iff these multiplication maps become bijective; the
limit should be (D n D') (x) (D n D') (= a_{D n D'}).  This script computes the tower.
"""
import itertools as it, sys
from monoids_small import monoids
from topjoin_monoid import idem_two_sided

def tensor(T,A,B):
    """A (x)_M B for sub-bisets A,B of M (two-sided ideals): pairs (a,b) modulo (a m, b) ~ (a, m b).
    Returns (classes as frozensets of pairs, class-of function)."""
    n=len(T); pairs=[(a,b) for a in A for b in B]
    parent={p:p for p in pairs}
    def find(p):
        while parent[p]!=p: parent[p]=parent[parent[p]]; p=parent[p]
        return p
    def union(p,q):
        rp,rq=find(p),find(q)
        if rp!=rq: parent[rp]=rq
    for a in A:
        for b in B:
            for m in range(n):
                union((T[a][m],b),(a,T[m][b]))
    classes={}
    for p in pairs: classes.setdefault(find(p),set()).add(p)
    return classes

def tensor_general(T,A_elems,A_act,B):
    """A (x)_M B where A is a finite M-M-biset given by elements and actions A_act[('l',m,a)], A_act[('r',a,m)]; B an ideal."""
    n=len(T); pairs=[(a,b) for a in A_elems for b in B]
    parent={p:p for p in pairs}
    def find(p):
        while parent[p]!=p: parent[p]=parent[parent[p]]; p=parent[p]
        return p
    def union(p,q):
        rp,rq=find(p),find(q)
        if rp!=rq: parent[rp]=rq
    for a in A_elems:
        for b in B:
            for m in range(n):
                union((A_act[('r',a,m)],b),(a,T[m][b]))
    classes={}
    for p in pairs: classes.setdefault(find(p),set()).add(p)
    reps={p:find(p) for p in pairs}
    # induced actions: left m.(a(x)b) = (m.a)(x)b ; right (a(x)b).m = a(x)(b m)
    elems=list(classes.keys()); act={}
    for c in elems:
        a,b=next(iter(classes[c]))
        for m in range(n):
            act[('l',m,c)]=reps[(A_act[('l',m,a)],b)]
            act[('r',c,m)]=reps[(a,T[b][m])]
    return elems,act,reps

def ideal_as_biset(T,D):
    n=len(T); act={}
    for d in D:
        for m in range(n): act[('l',m,d)]=T[m][d]; act[('r',d,m)]=T[d][m]
    return sorted(D),act

def tower(T,D,E,kmax=8):
    """T_1 = D, T_k = D_k (x) T_{k-1}; multiplication maps mu_k : T_k -> T_{k-1}; returns sizes and whether mu_k bijective."""
    n=len(T)
    A_elems,A_act=ideal_as_biset(T,D)
    sizes=[len(A_elems)]; bij=[]
    prev_elems,prev_act=A_elems,A_act
    for k in range(2,kmax+1):
        Dk=D if k%2==1 else E
        elems,act,reps=tensor_general(T,prev_elems,prev_act,Dk) if False else (None,None,None)
        # T_k = Dk (x) T_{k-1}: tensor with the ideal on the LEFT; build via symmetric routine
        # pairs (d, t) with d in Dk, t in T_{k-1}; relation (d m, t) ~ (d, m.t)
        pairs=[(d,t) for d in Dk for t in prev_elems]
        parent={p:p for p in pairs}
        def find(p):
            while parent[p]!=p: parent[p]=parent[parent[p]]; p=parent[p]
            return p
        def union(p,q):
            rp,rq=find(p),find(q)
            if rp!=rq: parent[rp]=rq
        for d in Dk:
            for t in prev_elems:
                for m in range(n): union((T[d][m],t),(d,prev_act[('l',m,t)]))
        classes={}
        for p in pairs: classes.setdefault(find(p),set()).add(p)
        elems=list(classes.keys()); rep={p:find(p) for p in pairs}
        act={}
        for c in elems:
            d,t=next(iter(classes[c]))
            for m in range(n):
                act[('l',m,c)]=rep[(T[m][d],t)]; act[('r',c,m)]=rep[(d,prev_act[('r',t,m)])]
        # multiplication mu: T_k -> T_{k-1}, d (x) t -> d.t  (well defined: (d m).t = d.(m.t))
        mu={c:prev_act[('l',next(iter(classes[c]))[0],next(iter(classes[c]))[1])] for c in elems}
        # check well-definedness over the whole class
        for c in elems:
            assert all(prev_act[('l',d,t)]==mu[c] for (d,t) in classes[c])
        sizes.append(len(elems)); bij.append(len(set(mu.values()))==len(elems)==len(prev_elems))
        prev_elems,prev_act=elems,act
    return sizes,bij

if __name__=='__main__':
    nmax=int(sys.argv[1]) if len(sys.argv)>1 else 5
    for n in range(2,nmax+1):
        for i,Tm in enumerate(monoids(n)):
            ideals=idem_two_sided(Tm)
            for D in ideals:
                for E in ideals:
                    if D<=E or E<=D: continue
                    sizes,bij=tower(Tm,D,E)
                    DE=D&E
                    # size of (DnD')(x)(DnD')
                    cl=tensor(Tm,DE,DE); target=len(cl)
                    first=next((k+2 for k,b in enumerate(bij) if b and all(bij[k:])),None)
                    print("monoid%d#%d D=%s E=%s sizes=%s bij=%s |(DnE)x(DnE)|=%d stable_from=%s"%(n,i,sorted(D),sorted(E),sizes,''.join('1' if b else '0' for b in bij),target,first))

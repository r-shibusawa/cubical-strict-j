"""Experiment: joins and meets of topologies inside Same(M-Set).

M finite monoid; topologies = idempotent two-sided ideals D (Thm 5.1 of paper 29),
J_D = {right ideals containing D}, least cover D.  Sheafification by the plus
construction: X^+ = Hom_M(D, X) with (phi.m)(d) = phi(m d), unit x -> (d -> x.d);
iterate until the unit is bijective (finite, so it stabilises).
  join of topologies  <->  D n D'      meet of topologies <-> D u D'
Tests, on all monoids of order <= 4 and the free band on two generators (+1):
 (J) alternating chain X -> a_D X -> a_D' a_D X -> ... reaches a (D n D')-sheaf
     after finitely many steps  (=> W_D v W_D' = W_{D n D'});
 (M) for equivariant maps f: a_D f iso and a_D' f iso  =>  a_{D u D'} f iso
     (=> W_D n W_D' = W_{D u D'}), and the converse.
"""
import itertools as it, sys

def monoids(n):
    """Cayley tables of all monoids on range(n) with identity 0, up to isomorphism."""
    out=[]; seen=set()
    idx=[(a,b) for a in range(1,n) for b in range(1,n)]
    for vals in it.product(range(n),repeat=len(idx)):
        T=[[0]*n for _ in range(n)]
        for a in range(n): T[0][a]=a; T[a][0]=a
        for (a,b),v in zip(idx,vals): T[a][b]=v
        ok=True
        for a in range(1,n):
            for b in range(1,n):
                for c in range(1,n):
                    if T[T[a][b]][c]!=T[a][T[b][c]]: ok=False; break
                if not ok: break
            if not ok: break
        if not ok: continue
        key=min(tuple(tuple(s[T[si[a]][si[b]]] for b in range(n)) for a in range(n))
                for s in it.permutations(range(n)) if s[0]==0 for si in [tuple(s.index(i) for i in range(n))])
        if key in seen: continue
        seen.add(key); out.append(T)
    return out

def free_band2():
    # elements: 1,e,f,ef,fe,efe,fef ; words in {e,f} reduced by idempotency: represent as reduced words
    els=['','e','f','ef','fe','efe','fef']
    def red(w):
        # reduce word over {e,f} using xx=x and the band identity: in the free band on 2 generators,
        # words are determined by (first letter, last letter, content); map to canonical
        if w=='': return ''
        s=set(w)
        if len(s)==1: return w[0]
        a,b=w[0],w[-1]
        return a+b if a!=b else a+('f' if a=='e' else 'e')+a
    T=[[els.index(red(x+y)) for y in els] for x in els]
    return T

def right_ideals(T):
    n=len(T); out=[]
    for r in range(n+1):
        for S in it.combinations(range(n),r):
            S=frozenset(S)
            if all(T[s][m] in S for s in S for m in range(n)): out.append(S)
    return out

def idem_two_sided(T):
    n=len(T); out=[]
    for S in right_ideals(T):
        if all(T[m][s] in S for s in S for m in range(n)) and all(any(T[a][b]==d for a in S for b in S) for d in S):
            out.append(S)
    return out

class MSet:
    def __init__(self,T,elems,act):  # act[(x,m)] -> element
        self.T=T; self.elems=list(elems); self.act=act
    def check(self):
        n=len(self.T)
        for x in self.elems:
            assert self.act[(x,0)]==x
            for m in range(n):
                for k in range(n):
                    assert self.act[(self.act[(x,m)],k)]==self.act[(x,self.T[m][k])]

def hom_maps(D,X):
    """equivariant maps D -> X (D a right ideal, elements of M)"""
    D=sorted(D); n=len(X.T); out=[]
    # phi determined by values on generators; brute force with pruning: choose phi on all of D
    for choice in it.product(X.elems,repeat=len(D)):
        phi=dict(zip(D,choice))
        if all(phi[X.T[d][m]]==X.act[(phi[d],m)] for d in D for m in range(n)): out.append(tuple(sorted(phi.items())))
    return out

def plus(D,X):
    n=len(X.T); H=hom_maps(D,X)
    act={}
    for phi in H:
        pd=dict(phi)
        for m in range(n):
            act[(phi,m)]=tuple(sorted((d,pd[X.T[m][d]]) for d in D))
    Y=MSet(X.T,H,act); Y.check()
    unit={x:tuple(sorted((d,X.act[(x,d)]) for d in D)) for x in X.elems}
    return Y,unit

def sheafify(D,X):
    """a_D X := X^{++} (plus construction twice; always a sheaf), with unit X -> X^{++}.
    Elements of X^{++} are nested tuples of depth exactly 2, so a_D f = f^{++} is computed uniformly."""
    Y1,v1=plus(D,X); Y2,v2=plus(D,Y1)
    assert is_sheaf(D,Y2)
    return Y2,{x:v2[v1[x]] for x in X.elems}

def is_sheaf(D,X):
    Z,v=plus(D,X); return len(set(v.values()))==len(X.elems)==len(Z.elems)

def cyclic_msets(T,maxsize=4):
    """quotients of the right regular M-set by right congruences, of size <= maxsize"""
    n=len(T); out=[]
    # partitions of range(n)
    def partitions(s):
        if not s: yield []; return
        first=s[0]
        for p in partitions(s[1:]):
            for i in range(len(p)): yield p[:i]+[[first]+p[i]]+p[i+1:]
            yield [[first]]+p
    for p in partitions(list(range(n))):
        if len(p)>maxsize: continue
        cls={x:i for i,b in enumerate(p) for x in b}
        if all(cls[T[a][m]]==cls[T[b][m]] for b_ in p for a in b_ for b in b_ for m in range(n)):
            act={(i,m):cls[T[p[i][0]][m]] for i in range(len(p)) for m in range(n)}
            X=MSet(T,range(len(p)),act); X.check(); out.append(X)
    return out

def equivariant_maps(X,Y):
    n=len(X.T); out=[]
    for choice in it.product(Y.elems,repeat=len(X.elems)):
        f=dict(zip(X.elems,choice))
        if all(f[X.act[(x,m)]]==Y.act[(f[x],m)] for x in X.elems for m in range(n)): out.append(f)
    return out

def apply_sheaf(D,f,X,Y):
    """a_D f = f^{++} : X^{++} -> Y^{++}"""
    aX,_=sheafify(D,X); aY,_=sheafify(D,Y)
    g={e:tuple(sorted((d,tuple(sorted((d2,f[x]) for d2,x in v))) for d,v in e)) for e in aX.elems}
    assert all(v in aY.elems for v in g.values())
    return g,aX,aY

def run(T,name,maxsize=4):
    ideals=idem_two_sided(T)
    pairs=[(D,E) for D in ideals for E in ideals if not (D<=E or E<=D)]
    Xs=cyclic_msets(T,maxsize)
    print("%s: |M|=%d, idempotent ideals=%d, incomparable pairs=%d, test M-sets=%d"%(name,len(T),len(ideals),len(pairs),len(Xs)))
    worst=0; meet_fail=0; meet_conv_fail=0; tested=0
    for D,E in pairs:
        DE=D&E; DU=D|E
        for X in Xs:
            Z=X; k=0
            while not is_sheaf(DE,Z):
                Z,_=sheafify(D if k%2==0 else E,Z); k+=1
                if k>8: print("  NO STABILISATION",sorted(D),sorted(E)); return
            worst=max(worst,k)
        for X in Xs:
            for Y in Xs:
                for f in equivariant_maps(X,Y):
                    tested+=1
                    gD,_,_=apply_sheaf(D,f,X,Y); gE,_,_=apply_sheaf(E,f,X,Y); gU,aX,aY=apply_sheaf(DU,f,X,Y)
                    isoD=len(set(gD.values()))==len(gD)==len(sheafify(D,Y)[0].elems)
                    isoE=len(set(gE.values()))==len(gE)==len(sheafify(E,Y)[0].elems)
                    isoU=len(set(gU.values()))==len(gU)==len(aY.elems)
                    if isoD and isoE and not isoU: meet_fail+=1
                    if isoU and not (isoD and isoE): meet_conv_fail+=1
    print("  (J) alternating chains stabilise; worst steps = %d"%worst)
    print("  (M) maps tested = %d; [a_D f, a_E f iso but a_{DuE} f not] = %d; [a_{DuE} f iso but not both] = %d"%(tested,meet_fail,meet_conv_fail))

if __name__=='__main__':
    import sys
    from monoids_small import monoids as monoids_bt
    nmax=int(sys.argv[1]) if len(sys.argv)>1 else 4
    maxsize=int(sys.argv[2]) if len(sys.argv)>2 else 4
    total=0
    for n in range(2,nmax+1):
        for i,T in enumerate(monoids_bt(n)):
            ideals=idem_two_sided(T)
            if any(not (D<=E or E<=D) for D in ideals for E in ideals):
                total+=1; run(T,"monoid%d#%d"%(n,i),maxsize=maxsize)
    print("monoids with incomparable idempotent ideals:",total)

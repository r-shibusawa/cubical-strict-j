"""Multi-fold tensor products of two-sided ideals of a finite monoid and the canonical
multiplication maps between them.  Elements of A_1 (x) ... (x) A_k are classes of tuples."""
import itertools as it, sys
from monoids_small import monoids
from topjoin_monoid import idem_two_sided

class UF:
    def __init__(self,elems): self.p={e:e for e in elems}
    def find(self,x):
        while self.p[x]!=x: self.p[x]=self.p[self.p[x]]; x=self.p[x]
        return x
    def union(self,a,b):
        ra,rb=self.find(a),self.find(b)
        if ra!=rb: self.p[ra]=rb

def multitensor(T,ideals):
    """classes of tuples (a_1,...,a_k) under (.., a_i m, a_{i+1}, ..) ~ (.., a_i, m a_{i+1}, ..)"""
    n=len(T); tuples=list(it.product(*[sorted(A) for A in ideals])); uf=UF(tuples)
    k=len(ideals)
    for t in tuples:
        for i in range(k-1):
            for m in range(n):
                t2=list(t); t2[i]=T[t[i]][m]; t2[i+1]=t[i+1]  # (a_i m, a_{i+1})
                t3=list(t); t3[i]=t[i]; t3[i+1]=T[m][t[i+1]]   # (a_i, m a_{i+1})
                # relation: (a_i m) (x) a_{i+1} ~ a_i (x) (m a_{i+1}) -- both derived from (a_i, m, a_{i+1})
                uf.union(tuple(t2),tuple(t3))
    return uf

def classes(uf,tuples):
    cl={}
    for t in tuples: cl.setdefault(uf.find(t),[]).append(t)
    return cl

def mult_map_bijective(T,ideals,i):
    """canonical map A_1(x)..(x)A_k -> A_1(x)..(x)(A_i A_{i+1})(x)..(x)A_k (multiply positions i,i+1); bijective?"""
    src=multitensor(T,ideals)
    prod=frozenset(T[a][b] for a in ideals[i] for b in ideals[i+1])
    tgt_ideals=ideals[:i]+[prod]+ideals[i+2:]
    tgt=multitensor(T,tgt_ideals)
    tuples=list(it.product(*[sorted(A) for A in ideals]))
    img={}
    for t in tuples:
        s=src.find(t); u=list(t[:i])+[T[t[i]][t[i+1]]]+list(t[i+2:]); v=tgt.find(tuple(u))
        if s in img and img[s]!=v: return None  # not well defined (should not happen)
        img[s]=v
    nsrc=len(set(src.find(t) for t in tuples)); ntgt=len(set(tgt.find(t) for t in it.product(*[sorted(A) for A in tgt_ideals])))
    return (len(set(img.values()))==nsrc==ntgt, nsrc, ntgt)

if __name__=='__main__':
    nmax=int(sys.argv[1]) if len(sys.argv)>1 else 5
    stats={}
    for n in range(2,nmax+1):
        for i,Tm in enumerate(monoids(n)):
            ideals=[D for D in idem_two_sided(Tm) if D]
            for D in ideals:
                for E in ideals:
                    if D<=E or E<=D: continue
                    I=D&E
                    # (alpha) D E E D -> D E D (multiply middle) ; (beta) D E E D -> (DE)(ED) = I (x) I ; (gamma) D E D vs I (x) I sizes
                    a=mult_map_bijective(Tm,[D,E,E,D],1)
                    # beta: multiply positions 0,1 then 1,2 of the result: two steps
                    b1=mult_map_bijective(Tm,[D,E,E,D],0); b2=mult_map_bijective(Tm,[I,E,D],1)
                    key=(a[0],b1[0],b2[0]); stats[key]=stats.get(key,0)+1
                    if not (a[0] and b1[0] and b2[0]):
                        print("monoid%d#%d D=%s E=%s alpha=%s beta1=%s beta2=%s"%(n,i,sorted(D),sorted(E),a,b1,b2))
    print("stats (alpha bij, beta1 bij, beta2 bij):",stats)

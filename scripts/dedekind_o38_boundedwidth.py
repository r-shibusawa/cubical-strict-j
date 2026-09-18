import itertools as it, time
from pysat.solvers import Glucose3
from collections import defaultdict
def verts(m): return list(it.product((0,1),repeat=m))
def leq(a,b): return all(x<=y for x,y in zip(a,b))
m=3; V=verts(m); Vi={v:i for i,v in enumerate(V)}; N=8
cov=defaultdict(list)
for a in V:
    for b in V:
        if leq(a,b) and sum(b)-sum(a)==1: cov[Vi[a]].append(Vi[b])
def base(g,arity,Fs,var,ti,tuples):
    singles={next(iter(F)) for F in Fs if len(F)==1}
    for xi in range(N):
        if V[xi] in singles:
            t=tuple([xi]*arity)
            for j in range(m): g.add_clause([var(ti[t],j) if V[xi][j]==1 else -var(ti[t],j)])
    for F in Fs:
        mem=[Vi[v] for v in F]; nF=[w for w in V if w not in F]
        for t in it.product(mem,repeat=arity):
            k=ti[t]
            for w in nF: g.add_clause([-var(k,j) if w[j]==1 else var(k,j) for j in range(m)])
    for t in tuples:
        k=ti[t]
        for pos in range(arity):
            for bi in cov[t[pos]]:
                t2=list(t);t2[pos]=bi;k2=ti[tuple(t2)]
                for j in range(m): g.add_clause([-var(k,j),var(k2,j)])
def linked_wnu(Fs):
    # 3-ary WNU v and 4-ary WNU w with v(y,x,x)=w(y,x,x,x): certifies bounded width (KKVW)
    t3=list(it.product(range(N),repeat=3)); i3={t:k for k,t in enumerate(t3)}
    t4=list(it.product(range(N),repeat=4)); i4={t:k for k,t in enumerate(t4)}
    off=len(t3)*m
    def v3(k,j): return k*m+j+1
    def w4(k,j): return off+k*m+j+1
    g=Glucose3()
    base(g,3,Fs,v3,i3,t3); base(g,4,Fs,w4,i4,t4)
    def eqv(k1,k2,f1,f2):
        for j in range(m): g.add_clause([-f1(k1,j),f2(k2,j)]);g.add_clause([f1(k1,j),-f2(k2,j)])
    for x in range(N):
        for y in range(N):
            # WNU3
            a=i3[(y,x,x)];b=i3[(x,y,x)];c=i3[(x,x,y)]
            eqv(a,b,v3,v3); eqv(a,c,v3,v3)
            # WNU4
            p=[i4[tuple([x]*4)] for _ in range(0)]
            d=i4[(y,x,x,x)];e=i4[(x,y,x,x)];f=i4[(x,x,y,x)];h=i4[(x,x,x,y)]
            eqv(d,e,w4,w4); eqv(d,f,w4,w4); eqv(d,h,w4,w4)
            # link: v(y,x,x) = w(y,x,x,x)
            eqv(a,d,v3,w4)
    r=g.solve();g.delete();return r
# enumerate 882 partitions
def partitions(coll):
    coll=list(coll)
    if len(coll)==1: yield [coll]; return
    first=coll[0]
    for sm in partitions(coll[1:]):
        for i in range(len(sm)): yield sm[:i]+[[first]+sm[i]]+sm[i+1:]
        yield [[first]]+sm
def oc(bl):
    B=set(bl)
    for a in bl:
        for c in bl:
            for b in range(N):
                if leq(V[a],V[b]) and leq(V[b],V[c]) and b not in B: return False
    return True
def pq(part):
    k=len(part); rel=[[i!=j and any(leq(V[x],V[y]) for x in part[i] for y in part[j]) for j in range(k)] for i in range(k)]
    for i in range(k):
        for j in range(k):
            if i!=j and rel[i][j] and rel[j][i]: return False
    return True
t0=time.time(); tot=0; nobw=0
for part in partitions(range(N)):
    if not all(oc(b) for b in part): continue
    if not pq(part): continue
    tot+=1
    Fs=[set(V[i] for i in b) for b in part]
    if not linked_wnu(Fs):
        nobw+=1
        if nobw<=5: print("  NO bounded-width:",[sorted(F) for F in Fs],flush=True)
    if tot%200==0: print(f"  ...{tot} done, no-bw {nobw} [{time.time()-t0:.0f}s]",flush=True)
print(f"882-check: order-convex poset partitions {tot}; WITHOUT linked-WNU (not bounded width): {nobw} [{time.time()-t0:.0f}s]")
print("=> domain B^3: (<=,fibres(z)) ALWAYS has BOUNDED WIDTH" if nobw==0 else "=> some are not bounded width")

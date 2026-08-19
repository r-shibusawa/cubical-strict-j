"""Hypothesis E-dom(ii) verification at stage zero (O19, stage 1).

For the n = 3 separation bases N in {A4-type, nested-24} on the
Boolean site: enumerates the strictly invariant endomorphism classes
of cube^3/N (components are N-invariant functions = functions
constant on the vertex orbits; 4 invariant functions, 8 classes for
both groups), checks that the identity class is not strictly
invariant, and decides -- exactly, by the parity union-find with
reconstruction-verified positives -- that the identity is directly
homotopic to NONE of them.  Together with the Klein-machine
component computation ({id} alone, boolean_landscape.py), this is
the stage-zero verification of Hypothesis E-dom(ii) for all n <= 3
bases of the separation criterion.
"""
import itertools as it, collections
n=3
ELEMS=[]
for p in it.permutations(range(n)):
    for s in it.product((0,1),repeat=n):
        ELEMS.append((p,s))
ID=(tuple(range(n)),(0,)*n)
def mm(a,b):
    (p1,s1),(p2,s2)=a,b
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i]^s2[p1[i]] for i in range(n)))
def close(g):
    S={ID}|set(g)
    dq=collections.deque(S)
    while dq:
        x=dq.popleft()
        for y in list(S):
            for z in (mm(x,y),mm(y,x)):
                if z not in S: S.add(z);dq.append(z)
    return S
nb=((0,1,2),(1,1,0)); n011=((0,1,2),(0,1,1)); rot=((1,2,0),(0,0,0))
sw=((1,0,2),(0,0,0))
A4=sorted(close([nb,n011,rot]))
NEST=sorted(close([nb,n011,rot,sw]))

def run(name,H):
    gens=[]
    span={ID}
    for e in H:
        if e in span: continue
        gens.append(e); span=set(close(gens))
        if len(span)==len(H): break
    m=3; P=8; m4=4; P4=16
    PT3={h:[0]*P for h in H}
    PT4={h:[0]*P4 for h in H}
    for h in H:
        pm,s=h
        for p in range(P):
            q=0
            for i in range(n): q|=((((p>>pm[i])&1)^s[i])<<i)
            PT3[h][p]=q
        for p in range(P4):
            q=p&8
            for i in range(n): q|=((((p>>pm[i])&1)^s[i])<<i)
            PT4[h][p]=q
    def sub3(phi,h):
        r=0
        for p in range(P):
            if (phi>>PT3[h][p])&1: r|=1<<p
        return r
    def sub4(phi,h):
        r=0
        for p in range(P4):
            if (phi>>PT4[h][p])&1: r|=1<<p
        return r
    def neg3(phi): return phi^255
    def neg4(phi): return phi^65535
    def deck3(h,c):
        pm,s=h
        return tuple(neg3(c[pm[i]]) if s[i] else c[pm[i]] for i in range(n))
    def deck4(h,c):
        pm,s=h
        return tuple(neg4(c[pm[i]]) if s[i] else c[pm[i]] for i in range(n))
    def orb3(c): return {deck3(h,c) for h in H}
    def nc3(c): return min(orb3(c))
    invfns=[phi for phi in range(256)
            if all(sub3(phi,g)==phi for g in gens)]
    strict={nc3((a,b,c0)) for a in invfns for b in invfns for c0 in invfns}
    X=[sum(1<<p for p in range(P) if (p>>i)&1) for i in range(n)]
    idc=nc3(tuple(X))
    print(f"{name}: |H|={len(H)} gens={len(gens)} invfns={len(invfns)} "
          f"strict classes={len(strict)} id strict: {idc in strict}",
          flush=True)
    def slot(c,p): return c*P4+p
    class UF:
        __slots__=('par','pr','fix','ok')
        def __init__(s,sz):
            s.par=list(range(sz)); s.pr=[0]*sz; s.fix={}; s.ok=True
        def find(s,i):
            r=i;acc=0
            while s.par[r]!=r: acc^=s.pr[r]; r=s.par[r]
            return r,acc
        def union(s,i,j,par):
            ri,pi=s.find(i); rj,pj=s.find(j)
            if ri==rj:
                if (pi^pj)!=par: s.ok=False
                return
            s.par[ri]=rj; s.pr[ri]=pi^pj^par
            if ri in s.fix:
                v=s.fix.pop(ri)^s.pr[ri]
                if rj in s.fix:
                    if s.fix[rj]!=v: s.ok=False
                else: s.fix[rj]=v
        def setv(s,i,v):
            r,p=s.find(i)
            v^=p
            if r in s.fix:
                if s.fix[r]!=v: s.ok=False
            else: s.fix[r]=v
    r0=min(orb3(tuple(X)))
    def homotopy(e1):
        for r1 in orb3(e1):
            for tw in it.product(H,repeat=len(gens)):
                uf=UF(n*P4)
                ok=True
                for g,d in zip(gens,tw):
                    pm,s=d
                    pt=PT4[g]
                    for c_ in range(n):
                        c2=pm[c_]; sg=s[c_]
                        b1=c_*P4; b2=c2*P4
                        for p in range(P4):
                            uf.union(b1+pt[p], b2+p, sg)
                            if not uf.ok: ok=False; break
                        if not ok: break
                    if not ok: break
                if not ok: continue
                for p3 in range(P):
                    for c_ in range(n):
                        uf.setv(slot(c_,p3),(r0[c_]>>p3)&1)
                        uf.setv(slot(c_,p3|8),(r1[c_]>>p3)&1)
                    if not uf.ok: break
                if not uf.ok: continue
                vals=[]
                for i in range(n*P4):
                    r,p=uf.find(i)
                    vals.append(uf.fix.get(r,0)^p)
                C4=tuple(sum(vals[slot(c_,p)]<<p for p in range(P4))
                         for c_ in range(n))
                orb4={deck4(h,C4) for h in H}
                k4=min(orb4)
                if all(min({deck4(h,tuple(sub4(x,g) for x in C4))
                            for h in H})==k4 for g in gens):
                    return True
        return False
    reach=[k for k in strict if k!=idc and homotopy(k)]
    print(f"  id directly homotopic to strict classes: {len(reach)}",
          flush=True)

run("A4-type",A4)
run("nested-24",NEST)

"""Paper C milestone 3, step 1: Grothendieck topologies on the TRUNCATED CUBE
CATEGORY □_{<=N} (faces + degeneracies only) and on the truncated simplex
category Δ_{<=N}, via Theorem D' (topologies = idempotent two-sided ideals).
Question: besides the dimension ideals D_n = {maps factoring through dim <= n}
(which give the n-coskeletal sheaf samenesses), are there other topologies?"""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat

# ---- cube category: a map [m]->[n] is an n-tuple over {'0','1',x1..xm}, variables used at most once, in increasing order
def cube_maps(m,n):
    syms=['0','1']+[f"x{i}" for i in range(1,m+1)]; out=[]
    for t in it.product(syms,repeat=n):
        vs=[int(s[1:]) for s in t if s[0]=='x']
        if len(vs)==len(set(vs)) and vs==sorted(vs): out.append(t)
    return out
def cube_comp(g,f,m):   # f:[m]->[k] (tuple length k), g:[k]->[n]; (g∘f)_j = g_j with x_i replaced by f_i
    return tuple(s if s[0]!='x' else f[int(s[1:])-1] for s in g)
# ---- simplex category: a map [m]->[n] is a monotone map {0..m}->{0..n}
def simp_maps(m,n): return [t for t in it.product(range(n+1),repeat=m+1) if all(t[i]<=t[i+1] for i in range(m))]
def simp_comp(g,f,m): return tuple(g[f[i]] for i in range(len(f)))

def build(N,maps,comp):
    objs=list(range(N+1)); homs={}; comp_d={}; name={}
    for a in objs:
        for b in objs:
            homs[(a,b)]=[]
            for t in maps(a,b):
                nm=f"{a}>{b}:{'.'.join(map(str,t))}"; homs[(a,b)].append(nm); name[nm]=(a,b,t)
    ident={a:[nm for nm in homs[(a,a)] if name[nm][2]==(tuple(f"x{i+1}" for i in range(a)) if maps is cube_maps else tuple(range(a+1)))][0] for a in objs}
    for f,(a,b,tf) in name.items():
        for g,(c,d,tg) in name.items():
            if b==c: comp_d[(g,f)]=f"{a}>{d}:{'.'.join(map(str,comp(tg,tf,a)))}"
    C=Cat(objs,homs,comp_d,ident); return C,name
def ideals(C):
    M=sorted(C.mors)
    def principal(f):
        P={f}; ch=True
        while ch:
            ch=False
            for d in list(P):
                for g in M:
                    if C.tgt[d]==C.src[g]:
                        x=C.comp[(g,d)]; 
                        if x not in P: P.add(x); ch=True
                    if C.tgt[g]==C.src[d]:
                        x=C.comp[(d,g)]
                        if x not in P: P.add(x); ch=True
        return frozenset(P)
    prin=sorted(set(principal(f) for f in M),key=len)
    # every two-sided ideal is a union of principal ideals; enumerate unions of antichains of generators
    idl=set([frozenset()])
    for r in range(1,len(prin)+1):
        for S in it.combinations(prin,r): idl.add(frozenset().union(*S))
    idem=[D for D in idl if all(any(C.comp[(a,b)]==d for a in D for b in D if C.tgt[b]==C.src[a]) for d in D)]
    return sorted(idl,key=len),sorted(idem,key=len),prin
def describe(C,name,D):
    if not D: return "∅"
    dims=sorted(set(name[m][0] for m in D)|set(name[m][1] for m in D))
    # dimension ideal test: D = maps factoring through some object of dim <= n ?
    def factors_through_dim(f,n):
        a,b,t=name[f]
        if a<=n or b<=n: return True
        return any(C.comp[(g,h)]==f for h in C.mors for g in C.mors if C.src[h]==a and C.tgt[g]==b and C.tgt[h]==C.src[g] and C.tgt[h]<=n)
    for n in range(max(C.objs)+1):
        Dn=frozenset(f for f in C.mors if factors_through_dim(f,n))
        if D==Dn: return f"D_{n} (maps factoring through dim<={n})"
    idents=[a for a in C.objs if C.ident[a] in D]
    return f"other: |D|={len(D)}, contains identities of {idents}"
for label,N,maps,comp in [("cube □_{<=1}",1,cube_maps,cube_comp),("cube □_{<=2}",2,cube_maps,cube_comp),("simplex Δ_{<=1}",1,simp_maps,simp_comp),("simplex Δ_{<=2}",2,simp_maps,simp_comp)]:
    C,name=build(N,maps,comp); idl,idem,prin=ideals(C)
    print(f"=== {label}: {len(C.mors)} morphisms, {len(prin)} principal ideals, {len(idl)} two-sided ideals, {len(idem)} idempotent => |Top| = {len(idem)}",flush=True)
    for D in idem: print("   ",describe(C,name,D))

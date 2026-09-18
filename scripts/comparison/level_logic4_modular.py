"""Review-driven: is (non-)modularity modally definable over SAMENESS frames?
Need a p-morphism  F(C) ->> F(D)  with F(C) modular and F(D) NOT modular, BOTH
sameness frames (the earlier Same(C12)->>N5 fails this: N5 is not known to be a
sameness frame).  Also verify the reviewer's B3 ->> M3 for distributivity.
Step 1: modularity of every small sameness frame; find the smallest non-modular.
Step 2: search p-morphisms from modular sameness frames onto it."""
import sys, itertools as it, json; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns)
poset_cat,all_posets,group_cat,cyclic,klein,sym3,quat8,width,height,join=[ns[k] for k in
   ("poset_cat","all_posets","group_cat","cyclic","klein","sym3","quat8","width","height","join")]
P=lambda *a,**k: print(*a,**k,flush=True)
def modular(S): return all(join(S,a,x&b)==join(S,a,x)&b for a in S for b in S if a<=b for x in S)
def distributive(S): return all(a&join(S,b,x)==join(S,a&b,a&x) for a in S for b in S for x in S)
def alt4():
    Ps=[p for p in it.permutations(range(4)) if sum(1 for i in range(4) for j in range(i+1,4) if p[i]>p[j])%2==0]
    nm={p:''.join(map(str,p)) for p in Ps}
    return [nm[p] for p in Ps],{(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(4))] for p in Ps for q in Ps},nm[(0,1,2,3)]
def dihedral4():
    r=(1,2,3,0); s=(0,3,2,1); pm=lambda p,q: tuple(p[q[i]] for i in range(4))
    G={(0,1,2,3)}; ch=True
    while ch:
        ch=False
        for g in list(G):
            for h in (r,s):
                x=pm(g,h)
                if x not in G: G.add(x); ch=True
    Ps=sorted(G); nm={p:''.join(map(str,p)) for p in Ps}
    return [nm[p] for p in Ps],{(nm[p],nm[q]):nm[pm(p,q)] for p in Ps for q in Ps},nm[(0,1,2,3)]
def product(g1,g2):
    e1,m1,i1=g1; e2,m2,i2=g2
    el=[f"{a}|{b}" for a in e1 for b in e2]
    return el,{(f"{a}|{b}",f"{c}|{d}"):f"{m1[(a,c)]}|{m2[(b,d)]}" for a in e1 for b in e2 for c in e1 for d in e2},f"{i1}|{i2}"
def parallel(n):   # n independent parallel arrows x->y : Same = Boolean 2^n
    names=[f"f{i}" for i in range(n)]
    homs={(0,0):['x'],(1,1):['y'],(0,1):names}
    comp={('x','x'):'x',('y','y'):'y'}
    for f in names: comp[(f,'x')]=f; comp[('y',f)]=f
    return Cat([0,1],homs,comp,{0:'x',1:'y'})

frames=[]
for n in range(1,5):
    for R in all_posets(n): frames.append((f"poset{n}{sorted(R)}",poset_cat(n,R)))
C2,C3,C4=cyclic(2),cyclic(3),cyclic(4)
for nm,g in [("C6",cyclic(6)),("C8",cyclic(8)),("C12",cyclic(12)),("V4",klein()),("S3",sym3()),("Q8",quat8()),
             ("A4",alt4()),("D4",dihedral4()),("C2xC4",product(C2,C4)),("C3xC3",product(C3,C3)),("C2^3",product(C2,product(C2,C2)))]:
    frames.append((nm,group_cat(*g)))
for n in (2,3,4,5): frames.append((f"parallel{n}",parallel(n)))
SS=[]
for name,C in frames:
    S=[frozenset(w) for w in all_samenesses(C)[0]]; SS.append((name,S,modular(S),distributive(S)))
P("=== step 1: modularity / distributivity of small sameness frames ===")
nonmod=sorted([(len(S),name) for name,S,m,d in SS if not m])
P("non-modular sameness frames (|Same|, source):", nonmod[:12])
P("smallest non-modular:", nonmod[0] if nonmod else None)
mods=[(name,S) for name,S,m,d in SS if m]
P(f"modular sameness frames available as sources: {len(mods)}  (incl. Boolean parallel2..5)")

# ---- p-morphism search (pruned) ----
def pmorph(S,W,T):     # T = (elements list, leq set) ; S source family, W root
    tel,tleq=T; U=sorted([u for u in S if W<=u],key=len)
    tbot=[t for t in tel if all((t,x) in tleq for x in tel)][0]; ttop=[t for t in tel if all((x,t) in tleq for x in tel)][0]
    top=max(U,key=len); f={}
    def ok(x,v): return all(((fu,v) in tleq) if u<=x else True for u,fu in f.items()) and all(((v,fu) in tleq) if x<=u else True for u,fu in f.items())
    def rec(i):
        if i==len(U):
            if set(f.values())!=set(tel): return False
            return all(any(x<=x2 and f[x2]==v2 for x2 in U) for x in U for v2 in tel if (f[x],v2) in tleq)
        x=U[i]
        for v in ([tbot] if i==0 else [ttop] if x==top else tel):
            if ok(x,v):
                f[x]=v
                if rec(i+1): return True
                del f[x]
        return False
    return dict(f) if rec(0) else None
def as_target(S):
    el=[frozenset(s) for s in S]; leq={(a,b) for a in el for b in el if a<=b}; return el,leq
def tdims(T):
    el,leq=T
    w=max(len(A) for r in range(1,len(el)+1) for A in it.combinations(el,r) if all((x,y) not in leq and (y,x) not in leq for x,y in it.combinations(A,2)))
    return w,height(el)

# ---- reviewer's B3 ->> M3 (distributivity) ----
P("\n=== distributivity: B3 = Same(parallel3) ->> M3 = Same(V4)? ===")
B3=[S for name,S,m,d in SS if name=="parallel3"][0]; M3=[S for name,S,m,d in SS if name=="V4"][0]
f=pmorph(B3,frozenset(min(B3,key=len)),as_target(M3))
P("B3 distributive:",distributive(B3)," M3 distributive:",distributive(M3)," p-morphism B3->>M3 found:",f is not None)

# ---- modularity: modular source ->> smallest non-modular sameness frame ----
P("\n=== modularity: modular sameness frame ->> non-modular sameness frame? ===")
found=None
for tsize,tname in nonmod[:3]:
    T_S=[S for name,S,m,d in SS if name==tname][0]; T=as_target(T_S); tw,th=tdims(T)
    P(f"  target {tname} (|Same|={tsize}, width {tw}, height {th})")
    for sname,S in sorted(mods,key=lambda p:len(p[1])):
        for W in S:
            U=[u for u in S if W<=u]
            if len(U)<tsize or height(U)<th or width(U)<tw: continue
            f=pmorph(S,W,T)
            if f: found=(sname,len(S),tname,tsize,W,f); break
        if found: break
    if found: break
if found:
    sname,ss,tname,ts,W,f=found
    P(f"  FOUND: {sname} (|Same|={ss}, modular) ->> {tname} (|Same|={ts}, NON-modular), root |W|={len(W)}")
    json.dump({"source":sname,"target":tname,"root":sorted(W),"map":{"|".join(sorted(k)):"|".join(sorted(v)) for k,v in f.items()}},
              open((('docs/paperB/' if __import__('os').path.isdir('docs/paperB') else '')+'cert_modularity.json'),"w"),indent=1)
    P("  certificate written: docs/paperB/cert_modularity.json")
else:
    P("  NONE found in this family -> modularity non-definability stays OPEN")

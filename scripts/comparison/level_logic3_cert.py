"""Paper B, milestone 3(i): completeness of S4.2Grz w.r.t. sameness frames,
checked frame-by-frame up to SIX elements.
Finite rooted S4.2Grz frames = finite BOUNDED posets (bottom=root, top by
directedness+finiteness).  Six-element bounded posets = bottom + (a poset on 4
points) + top: 16 of them, several NOT lattices (e.g. the butterfly).
Test: is each a p-morphic image of a rooted generated subframe of a sameness
frame F(C)?  Sources: all posets on <=4 points, groups C6,C8,C12,V4,S3,Q8,A4,
D4,C2xC4,C3xC3,C2^3, parallel pair.  If all 16 pass, Log(sameness frames)
agrees with S4.2Grz on every frame of size <= 6."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns)
poset_cat,all_posets,group_cat,cyclic,klein,sym3,quat8,width,height=[ns[k] for k in
   ("poset_cat","all_posets","group_cat","cyclic","klein","sym3","quat8","width","height")]
P=lambda *a,**k: print(*a,**k,flush=True)

# ---- extra groups ----
def alt4():
    Ps=[p for p in it.permutations(range(4)) if sum(1 for i in range(4) for j in range(i+1,4) if p[i]>p[j])%2==0]
    nm={p:''.join(map(str,p)) for p in Ps}
    return [nm[p] for p in Ps],{(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(4))] for p in Ps for q in Ps},nm[(0,1,2,3)]
def dihedral4():   # symmetries of a square as permutations of 4 vertices
    r=(1,2,3,0); s=(0,3,2,1)
    def pm(p,q): return tuple(p[q[i]] for i in range(4))
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
    mul={(f"{a}|{b}",f"{c}|{d}"):f"{m1[(a,c)]}|{m2[(b,d)]}" for a in e1 for b in e2 for c in e1 for d in e2}
    return el,mul,f"{i1}|{i2}"

# ---- targets: all 6-element bounded posets ----
def bounded6():
    out=[]
    for R in all_posets(4):
        el=['B']+[str(i) for i in range(4)]+['T']
        strict={('B',str(i)) for i in range(4)}|{(str(i),'T') for i in range(4)}|{(str(a),str(b)) for (a,b) in R}
        leq={(x,x) for x in el}|strict; ch=True
        while ch:
            ch=False
            for (a,b) in list(leq):
                for (c,d) in list(leq):
                    if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
        # is it a lattice?
        def lub(x,y):
            ub=[z for z in el if (x,z) in leq and (y,z) in leq]
            return [z for z in ub if all((z,w) in leq for w in ub)]
        islat=all(len(lub(x,y))==1 for x in el for y in el)
        out.append((f"bnd6[{sorted(R)}]",(el,leq),islat))
    return out

def dims(t):
    el,leq=t
    w=max(len(A) for r in range(1,len(el)+1) for A in it.combinations(el,r)
          if all((x,y) not in leq and (y,x) not in leq for x,y in it.combinations(A,2)))
    h=max(len(Cc) for r in range(1,len(el)+1) for Cc in it.permutations(el,r)
          if all((Cc[i],Cc[i+1]) in leq for i in range(r-1)))
    return w,h

def pmorphic_image(S, W, target):
    telems,tleq=target
    U=sorted([u for u in S if W<=u],key=len)
    tbot=[t for t in telems if all((t,x) in tleq for x in telems)][0]
    ttop=[t for t in telems if all((x,t) in tleq for x in telems)][0]
    top=max(U,key=len); f={}
    def ok_forth(x,v):
        for u,fu in f.items():
            if u<=x and (fu,v) not in tleq: return False
            if x<=u and (v,fu) not in tleq: return False
        return True
    def rec(i):
        if i==len(U):
            if set(f.values())!=set(telems): return False
            return all(any(x<=x2 and f[x2]==v2 for x2 in U)
                       for x in U for v2 in telems if (f[x],v2) in tleq)
        x=U[i]
        for v in ([tbot] if i==0 else [ttop] if x==top else telems):
            if ok_forth(x,v):
                f[x]=v
                if rec(i+1): return True
                del f[x]
        return False
    return dict(f) if rec(0) else None

sources=[(f"poset{n}",poset_cat(n,R)) for n in range(1,5) for R in all_posets(n)]
C2,C3,C4=cyclic(2),cyclic(3),cyclic(4)
for nm,g in [("C6",cyclic(6)),("C8",cyclic(8)),("C12",cyclic(12)),("V4",klein()),("S3",sym3()),("Q8",quat8()),
             ("A4",alt4()),("D4",dihedral4()),("C2xC4",product(C2,C4)),("C3xC3",product(C3,C3)),("C2^3",product(C2,product(C2,C2)))]:
    sources.append((nm,group_cat(*g)))
sources.append(("parallel pair",Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},
      {('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},{0:'x',1:'y'})))
SS=[(name,[frozenset(w) for w in all_samenesses(C)[0]]) for name,C in sources]
P(f"sources: {len(SS)}  (max |Same| = {max(len(S) for _,S in SS)})")

def five():
    def mk(name,el,strict):
        leq={(x,x) for x in el}|set(strict); ch=True
        while ch:
            ch=False
            for (a,b) in list(leq):
                for (c,d) in list(leq):
                    if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
        return (name,(el,leq),True)
    return [mk("N5",['0','a','b','c','1'],[('0','a'),('a','b'),('b','1'),('0','c'),('c','1')]),
            mk("1+2^2",['0','m','a','b','1'],[('0','m'),('m','a'),('m','b'),('a','1'),('b','1')]),
            mk("2^2+1",['0','a','b','m','1'],[('0','a'),('0','b'),('a','m'),('b','m'),('m','1')])]
targets=five()+bounded6(); P(f"targets (3 five-element + 16 six-element): {len(targets)}  (lattices: {sum(1 for _,_,l in targets if l)}, non-lattices: {sum(1 for _,_,l in targets if not l)})")
results=[]; certs=[]
import json
for tname,tgt,islat in targets:
    tw,th=dims(tgt); hit=None
    for name,S in SS:
        for W in S:
            U=[u for u in S if W<=u]
            if len(U)<6 or height(U)<th or width(U)<tw: continue
            f=pmorphic_image(S,W,tgt)
            if f:
                hit=f"{name}(|Same|={len(S)})"
                certs.append({"target":tname,"target_elements":tgt[0],
                              "target_strict":sorted([list(p) for p in tgt[1] if p[0]!=p[1]]),
                              "source":name,"source_size":len(S),"root":"|".join(sorted(W)),
                              "source_elements":["|".join(sorted(u)) for u in S],
                              "source_leq":[["|".join(sorted(a)),"|".join(sorted(b))] for a in S for b in S if a<=b],
                              "pmorphism":{"|".join(sorted(k)):v for k,v in f.items()}})
                break
        if hit: break
    results.append((tname,islat,tw,th,hit))
    P(f"  {'lattice ' if islat else 'NOT lat.'} w={tw} h={th}  {tname:<40} <- {hit if hit else 'NONE'}")
json.dump(certs,open((('docs/paperB/' if __import__('os').path.isdir('docs/paperB') else '')+'certificates.json'),'w'),indent=1)
P(f'certificates written: docs/paperB/certificates.json ({len(certs)} p-morphisms)')
ok=sum(1 for r in results if r[4]); P(f"\np-morphic images realized: {ok}/{len(results)}")
P("=> " + ("Log(sameness frames) agrees with S4.2Grz on ALL frames of size <= 6." if ok==len(results)
          else "candidates for a genuine separation (not realized in this family): "+str([r[0] for r in results if not r[4]])))

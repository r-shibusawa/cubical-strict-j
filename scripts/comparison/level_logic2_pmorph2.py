"""Fast, pruned p-morphic-image test (replaces the unbounded run).
Family: groups C6,C8,C12,V4,S3,Q8,A4 ; all posets on <=4 points ; parallel pair.
Pruning: a p-morphism f:↑W ->> T satisfies f(↑x)=↑f(x), hence
   height(↑W) >= height(T)  and  width(↑W) >= width(T);
roots failing these are skipped before any search."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns)
poset_cat,all_posets,group_cat,cyclic,klein,sym3,quat8,width,height=[ns[k] for k in
   ("poset_cat","all_posets","group_cat","cyclic","klein","sym3","quat8","width","height")]
P=lambda *a,**k: print(*a,**k,flush=True)

def alt4():
    Ps=[p for p in it.permutations(range(4)) if sum(1 for i in range(4) for j in range(i+1,4) if p[i]>p[j])%2==0]
    nm={p:''.join(map(str,p)) for p in Ps}
    return [nm[p] for p in Ps],{(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(4))] for p in Ps for q in Ps},nm[(0,1,2,3)]
def poset(elems, strict):
    leq={(x,x) for x in elems}|set(strict); ch=True
    while ch:
        ch=False
        for (a,b) in list(leq):
            for (c,d) in list(leq):
                if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
    return elems,leq
TARGETS={"N5":poset(['0','a','b','c','1'],[('0','a'),('a','b'),('b','1'),('0','c'),('c','1')]),
         "1+2^2":poset(['0','m','a','b','1'],[('0','m'),('m','a'),('m','b'),('a','1'),('b','1')]),
         "2^2+1":poset(['0','a','b','m','1'],[('0','a'),('0','b'),('a','m'),('b','m'),('m','1')])}
def tdims(t):
    el,leq=t
    w=max(len(A) for r in range(1,len(el)+1) for A in it.combinations(el,r)
          if all((x,y) not in leq and (y,x) not in leq for x,y in it.combinations(A,2)))
    h=max(len(Cc) for r in range(1,len(el)+1) for Cc in it.permutations(el,r)
          if all((Cc[i],Cc[i+1]) in leq for i in range(r-1)))
    return w,h
TD={k:tdims(v) for k,v in TARGETS.items()}

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
    return rec(0)

sources=[(f"poset{n}",poset_cat(n,R)) for n in range(1,5) for R in all_posets(n)]
for nm,g in [("C6",cyclic(6)),("C8",cyclic(8)),("C12",cyclic(12)),("V4",klein()),("S3",sym3()),("Q8",quat8()),("A4",alt4())]:
    sources.append((nm,group_cat(*g)))
sources.append(("parallel pair",Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},
      {('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},{0:'x',1:'y'})))
P(f"targets: { {k:f'width {v[0]}, height {v[1]}' for k,v in TD.items()} }")
hits={t:[] for t in TARGETS}; tested=0
for name,C in sources:
    S=[frozenset(w) for w in all_samenesses(C)[0]]; tested+=1
    for tname,tgt in TARGETS.items():
        tw,th=TD[tname]
        for W in S:
            U=[u for u in S if W<=u]
            if len(U)<5 or height(U)<th or width(U)<tw: continue     # necessary conditions
            if pmorphic_image(S,W,tgt):
                hits[tname].append(f"{name}(|Same|={len(S)}, |root|={len(W)})"); break
    P(f"  done {name:<14} |Same|={len(S):>2}   hits so far: { {k:len(v) for k,v in hits.items()} }")
P(f"\nsources tested: {tested}")
for t in TARGETS:
    P(f"  {t:<6} p-morphic image of a rooted generated subframe of: {hits[t] if hits[t] else 'NONE'}")

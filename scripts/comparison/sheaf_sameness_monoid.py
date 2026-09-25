"""Sheaf sameness on ONE-OBJECT categories (monoids M, groups G):
sieves on the unique object = right ideals I (I*M ⊆ I); pullback along h: h*(I)={g : h g ∈ I}.
Compare Top(M) (Grothendieck topologies) with Same(M) (2-of-3 submonoids)."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/sheaf_sameness.py").read().split("cases=[")[0]
ns={}; exec(src,ns); profile=ns["profile"]
def right_ideals(el,mul):
    out=[]
    for r in range(len(el)+1):
        for I in it.combinations(el,r):
            I=frozenset(I)
            if all(mul[(i,m)] in I for i in I for m in el): out.append(I)
    return out
def topologies_monoid(el,mul,e):
    ideals=right_ideals(el,mul); M=frozenset(el)
    pull=lambda I,h: frozenset(g for g in el if mul[(h,g)] in I)
    tops=[]
    for r in range(len(ideals)):
        for J in it.combinations(ideals,r+1):
            J=frozenset(J)
            if M not in J: continue
            if not all(pull(I,h) in J for I in J for h in el): continue            # stability
            if not all((R in J) or not all(pull(R,h) in J for h in I) for I in J for R in ideals): continue  # transitivity
            tops.append(J)
    return tops
def group_cat(el,mul,e): return Cat([0],{(0,0):list(el)},{(a,b):mul[(a,b)] for a in el for b in el},{0:e})
def cyclic(n): el=[str(i) for i in range(n)]; return el,{(a,b):str((int(a)+int(b))%n) for a in el for b in el},'0'
def monoids(n):
    el=list(range(n)); e=0; out=[]; seen=set(); cells=[(a,b) for a in el for b in el if a!=e and b!=e]
    for vals in it.product(el,repeat=len(cells)):
        mul={(a,b):(b if a==e else a if b==e else None) for a in el for b in el}
        for (a,b),v in zip(cells,vals): mul[(a,b)]=v
        if all(mul[(mul[(a,b)],c)]==mul[(a,mul[(b,c)])] for a in el for b in el for c in el):
            canon=min(tuple(p.index(mul[(p[a],p[b])]) for a in el for b in el) for p in [tuple([0]+list(q)) for q in it.permutations(el[1:])])
            if canon in seen: continue
            seen.add(canon); out.append(mul)
    return out
P=lambda *a,**k: print(*a,**k,flush=True)
P(f"{'one-object cat':<18}|Top|  chain w h  dist   ||  |Same|  chain w h  mod dist   (right ideals)")
rows=[]
for nm,(el,mul,e) in [("C2",cyclic(2)),("C3",cyclic(3)),("C4",cyclic(4)),("C6",cyclic(6))]:
    rows.append((nm,el,mul,e))
for n in (2,3):
    for k,mul in enumerate(monoids(n)):
        el=[str(i) for i in range(n)]; m={(str(a),str(b)):str(v) for (a,b),v in mul.items()}
        rows.append((f"monoid{n}#{k}",el,m,'0'))
for nm,el,mul,e in rows:
    T=topologies_monoid(el,mul,e); tp=profile(T,lambda a,b:a<=b)
    S=[frozenset(w) for w in all_samenesses(group_cat(el,mul,e))[0]]; sp=profile(S,lambda a,b:a<=b)
    ideals=len(right_ideals(el,mul))
    P(f"{nm:<18}{len(T):>4}   {str(tp['chain']):<5} {tp['width']} {tp['height']}  {str(tp['distributive']):<5} || {len(S):>5}   {str(sp['chain']):<5} {sp['width']} {sp['height']}  {str(sp['modular']):<5}{str(sp['distributive']):<5} ({ideals})")

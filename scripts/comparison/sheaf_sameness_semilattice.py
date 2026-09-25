"""Paper C milestone 2b: finite lattices L viewed as MONOIDS under meet (identity = top).
Compute Top(L) (Grothendieck topologies on the one-object category; sieves = ideals of L)
and Same(L); identify the lattice Top(L) by its invariants and Hasse diagram."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/sheaf_sameness_monoid.py").read().split("P=lambda")[0]
ns={}; exec(src,ns); topologies_monoid,group_cat,profile=[ns[k] for k in ("topologies_monoid","group_cat","profile")]
def lattice_monoid(name,el,leq):          # meet-monoid: a*b = a ∧ b, identity = top
    def meet(a,b):
        lb=[x for x in el if (x,a) in leq and (x,b) in leq]; return [x for x in lb if all((y,x) in leq for y in lb)][0]
    top=[x for x in el if all((y,x) in leq for y in el)][0]
    return name,[str(x) for x in el],{(str(a),str(b)):str(meet(a,b)) for a in el for b in el},str(top)
def closure(el,strict):
    leq={(x,x) for x in el}|set(strict); ch=True
    while ch:
        ch=False
        for (a,b) in list(leq):
            for (c,d) in list(leq):
                if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
    return leq
L={}
for n in (2,3,4,5,6): L[f"{n}-chain"]=(list(range(n)),closure(range(n),[(i,i+1) for i in range(n-1)]))
L["2^2"]=([0,1,2,3],closure(range(4),[(0,1),(0,2),(1,3),(2,3)]))
L["1+2^2 (bottom,square)"]=([0,1,2,3,4],closure(range(5),[(0,1),(1,2),(1,3),(2,4),(3,4)]))
L["2^2+1 (square,top)"]=([0,1,2,3,4],closure(range(5),[(0,1),(0,2),(1,3),(2,3),(3,4)]))
L["M3"]=([0,1,2,3,4],closure(range(5),[(0,1),(0,2),(0,3),(1,4),(2,4),(3,4)]))
L["N5"]=([0,1,2,3,4],closure(range(5),[(0,1),(1,2),(2,4),(0,3),(3,4)]))
L["2x3"]=([0,1,2,3,4,5],closure(range(6),[(0,1),(1,2),(0,3),(3,4),(4,5),(1,4),(2,5)]))
L["2^2+2 (square,2 on top)"]=([0,1,2,3,4,5],closure(range(6),[(0,1),(0,2),(1,3),(2,3),(3,4),(4,5)]))
L["2^3"]=(list(range(8)),{(a,b) for a in range(8) for b in range(8) if a&b==a})
def hasse(elems,leq):     # covering pairs count + a compact description: level sizes
    lv={}; order=sorted(elems,key=lambda a:sum(1 for b in elems if (b,a) in leq))
    for a in order: lv[a]=1+max([lv[b] for b in order if (b,a) in leq and b!=a and b in lv],default=0)
    import collections; c=collections.Counter(lv.values()); return [c[i] for i in sorted(c)]
print(f"{'L (as meet-monoid)':<26}|L| |Top(L)| chain w h dist  levels(Top)     || |Same(L)| chain w h  levels(Same)",flush=True)
for name,(el,leq) in L.items():
    nm,E,mul,e=lattice_monoid(name,el,leq)
    T=topologies_monoid(E,mul,e); tp=profile(T,lambda a,b:a<=b)
    S=[frozenset(w) for w in all_samenesses(group_cat(E,mul,e))[0]]; sp=profile(S,lambda a,b:a<=b)
    tl=hasse(T,{(a,b) for a in T for b in T if a<=b}); sl=hasse(S,{(a,b) for a in S for b in S if a<=b})
    print(f"{name:<26}{len(el):>3} {len(T):>7}  {str(tp['chain']):<5} {tp['width']} {tp['height']} {str(tp['distributive']):<5} {str(tl):<15} || {len(S):>6}   {str(sp['chain']):<5} {sp['width']} {sp['height']}  {sl}",flush=True)

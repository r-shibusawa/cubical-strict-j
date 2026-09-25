"""Paper C milestone 2: all monoids of order 4 (up to isomorphism):
Top(M) (Grothendieck topologies via right ideals) vs Same(M) (2-of-3 submonoids).
Questions: is Top(M) always a chain? how do the two invariants relate?"""
import sys, itertools as it, collections; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/sheaf_sameness_monoid.py").read().split("P=lambda")[0]
ns={}; exec(src,ns)
topologies_monoid,right_ideals,group_cat,profile=[ns[k] for k in ("topologies_monoid","right_ideals","group_cat","profile")]
def monoids4():
    n=4; el=list(range(n)); e=0; out=[]; seen=set(); cells=[(a,b) for a in el for b in el if a!=e and b!=e]
    for vals in it.product(el,repeat=len(cells)):
        mul={(a,b):(b if a==e else a if b==e else None) for a in el for b in el}
        for (a,b),v in zip(cells,vals): mul[(a,b)]=v
        if not all(mul[(mul[(a,b)],c)]==mul[(a,mul[(b,c)])] for a in el for b in el for c in el): continue
        canon=min(tuple(p.index(mul[(p[a],p[b])]) for a in el for b in el) for p in [tuple([0]+list(q)) for q in it.permutations(el[1:])])
        if canon in seen: continue
        seen.add(canon); out.append(mul)
    return out
Ms=monoids4(); print(f"monoids of order 4 up to iso: {len(Ms)}",flush=True)
stats=collections.Counter(); pairs=collections.Counter(); nonchain=[]
for k,mul in enumerate(Ms):
    el=[str(i) for i in range(4)]; m={(str(a),str(b)):str(v) for (a,b),v in mul.items()}
    T=topologies_monoid(el,m,'0'); tp=profile(T,lambda a,b:a<=b)
    S=[frozenset(w) for w in all_samenesses(group_cat(el,m,'0'))[0]]; sp=profile(S,lambda a,b:a<=b)
    stats[(len(T),tp['chain'])]+=1; pairs[(len(T),len(S))]+=1
    if not tp['chain']: nonchain.append((k,len(T),tp['width'],tp['height'],tp['distributive'],len(S),sp['chain'],mul))
print("\n(|Top|, Top is chain) -> count:",dict(sorted(stats.items())))
print("(|Top|,|Same|) -> count:",dict(sorted(pairs.items())))
print(f"\nmonoids with NON-chain Top(M): {len(nonchain)}")
for k,t,w,h,d,s,sc,mul in nonchain[:6]:
    tbl=[[mul[(a,b)] for b in range(4)] for a in range(4)]
    print(f"  #{k}: |Top|={t} width={w} height={h} dist={d} | |Same|={s} chain={sc} | table rows={tbl}")

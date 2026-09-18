"""Extended realization survey for Paper B milestone 2: does N5 (or the two
'square+point' lattices) occur as Same(C)?  Family: all posets on <=5 points,
cyclic groups incl. C8/C12/C16, V4, S3, all monoids of order <=3, free triangle,
parallel pair."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
import importlib.util
spec=importlib.util.spec_from_file_location("ll2","scripts/comparison/level_logic2.py")
# reuse helpers without running its main: exec only the defs
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns)
invariant,NAMES,poset_cat,all_posets,group_cat,cyclic,klein,sym3=[ns[k] for k in
    ("invariant","NAMES","poset_cat","all_posets","group_cat","cyclic","klein","sym3")]

found={}
def record(src,C):
    S,_=all_samenesses(C); inv=invariant(S)
    if inv[0]<=5: found.setdefault(inv,[]).append(src)

# posets on <=5 points
for n in range(1,6):
    Ps=all_posets(n)
    for R in Ps: record(f"poset{n}:{sorted(R)}",poset_cat(n,R))
    print(f"posets on {n} points: {len(Ps)}")
# groups
for nm,n in [("C8",8),("C12",12),("C16",16),("C9",9)]: record(nm,group_cat(*cyclic(n)))
record("V4",group_cat(*klein())); record("S3",group_cat(*sym3()))
# all monoids of order <=3 (one-object categories, not necessarily groups)
def monoids(n):
    el=list(range(n)); e=0; out=[]; seen=set()
    cells=[(a,b) for a in el for b in el if a!=e and b!=e]
    for vals in it.product(el,repeat=len(cells)):
        mul={(a,b):(b if a==e else a if b==e else None) for a in el for b in el}
        for (a,b),v in zip(cells,vals): mul[(a,b)]=v
        if all(mul[(mul[(a,b)],c)]==mul[(a,mul[(b,c)])] for a in el for b in el for c in el):
            canon=min(tuple(mul[(p[a],p[b])] and p.index(mul[(p[a],p[b])]) if False else p.index(mul[(p[a],p[b])]) for a in el for b in el) for p in [tuple([0]+list(q)) for q in it.permutations(el[1:])])
            if canon in seen: continue
            seen.add(canon); out.append(mul)
    return out
for n in (2,3):
    Ms=monoids(n)
    for k,mul in enumerate(Ms):
        record(f"monoid{n}#{k}",group_cat([str(i) for i in range(n)],{(str(a),str(b)):str(v) for (a,b),v in mul.items()},'0'))
    print(f"monoids of order {n}: {len(Ms)}")
record("parallel pair",Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},
      {('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},{0:'x',1:'y'}))

print("\n=== lattices with <=5 elements realized as Same(C) ===")
for inv in sorted(found,key=lambda k:(k[0],k[1],k[2])):
    print(f"  {NAMES.get(inv,str(inv)):<32} <- {found[inv][0]}" + (f"  (+{len(found[inv])-1} more)" if len(found[inv])>1 else ""))
print("  NOT realized in this (larger) family:",[NAMES[k] for k in NAMES if k not in found])

"""Paper B, milestone 2.
(a) CORRESPONDENCE: on the frame F(C)=(Same(C),⊆)
      bw_n (bounded width)  valid  <=>  width(Same(C)) <= n     [bw_1 = .3]
      bd_n (bounded depth)  valid  <=>  height(Same(C)) <= n
    Frame conditions: bw_n = no (n+1)-antichain inside any up-set ↑w;
                      bd_n = no strictly ascending chain of n+1 points from any w.
    Since ↑⊥ = Same(C), both reduce to global width / height.  We check the
    general frame condition AND the global invariant, and assert they agree.
(c) REALIZATION SURVEY: which lattices with <= 5 elements occur as Same(C)?
    Family: all posets on <=4 points, small groups, free triangle, parallel pair.
    In particular: is the pentagon N_5 a sameness lattice?
"""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses

# ---------- lattice helpers on a family S of frozensets (order = ⊆) ----------
def up(S,w): return [u for u in S if w<=u]
def is_antichain(A): return all(not(a<=b) and not(b<=a) for a,b in it.combinations(A,2))
def width(S):
    best=1
    S=sorted(S,key=len)
    def rec(start,cur):
        nonlocal best
        best=max(best,len(cur))
        for i in range(start,len(S)):
            x=S[i]
            if all(not(x<=y) and not(y<=x) for y in cur): rec(i+1,cur+[x])
    rec(0,[]); return best
def height(S):
    S=sorted(S,key=len); h={}
    for x in S: h[x]=1+max([h[y] for y in S if y<x],default=0)
    return max(h.values())
def bw(S,n):   # no (n+1)-antichain in any ↑w
    return all(not any(is_antichain(A) for A in it.combinations(up(S,w),n+1)) for w in S)
def bd(S,n):   # no chain of n+1 points starting at w
    return all(height(up(S,w))<=n for w in S)
def join(S,a,b):
    ups=[w for w in S if a<=w and b<=w]; m=ups[0]
    for w in ups[1:]: m=m&w
    return m
def modular(S):
    return all(join(S,a,x&b)==join(S,a,x)&b for a in S for b in S if a<=b for x in S)
def distributive(S):
    return all(a&join(S,b,x)==join(S,a&b,a&x) for a in S for b in S for x in S)
def invariant(S):
    S=[frozenset(w) for w in S]; bot=min(S,key=len); top=max(S,key=len)
    atoms=sum(1 for x in S if x!=bot and not any(bot<y<x for y in S))
    coat=sum(1 for x in S if x!=top and not any(x<y<top for y in S))
    return (len(S),width(S),height(S),modular(S),distributive(S),atoms,coat)
NAMES={ (1,1,1,True,True,0,0):"1", (2,1,2,True,True,1,1):"2-chain", (3,1,3,True,True,1,1):"3-chain",
        (4,1,4,True,True,1,1):"4-chain", (4,2,3,True,True,2,2):"2^2 (Boolean)",
        (5,1,5,True,True,1,1):"5-chain", (5,3,3,True,False,3,3):"M3", (5,2,4,False,False,2,2):"N5",
        (5,2,4,True,True,1,2):"1+2^2 (bottom then square)", (5,2,4,True,True,2,1):"2^2+1 (square then top)"}

# ---------- categories ----------
def group_cat(elems, mul, e):
    return Cat([0],{(0,0):list(elems)},{(a,b):mul[(a,b)] for a in elems for b in elems},{0:e})
def cyclic(n):
    el=[str(i) for i in range(n)]; return el,{(a,b):str((int(a)+int(b))%n) for a in el for b in el},'0'
def klein():
    t={('e','e'):'e',('e','a'):'a',('e','b'):'b',('e','c'):'c',('a','e'):'a',('a','a'):'e',('a','b'):'c',('a','c'):'b',
       ('b','e'):'b',('b','a'):'c',('b','b'):'e',('b','c'):'a',('c','e'):'c',('c','a'):'b',('c','b'):'a',('c','c'):'e'}
    return ['e','a','b','c'],t,'e'
def sym3():
    P=list(it.permutations(range(3))); nm={p:''.join(map(str,p)) for p in P}
    return [nm[p] for p in P],{(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(3))] for p in P for q in P},nm[(0,1,2)]
def quat8():
    bm={('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),('i','1'):(1,'i'),('j','1'):(1,'j'),('k','1'):(1,'k'),
        ('i','i'):(-1,'1'),('j','j'):(-1,'1'),('k','k'):(-1,'1'),('i','j'):(1,'k'),('j','k'):(1,'i'),('k','i'):(1,'j'),
        ('j','i'):(-1,'k'),('k','j'):(-1,'i'),('i','k'):(-1,'j')}
    el=[(s,b) for s in (1,-1) for b in '1ijk']; nm=lambda x:('' if x[0]==1 else '-')+x[1]; mul={}
    for x in el:
        for y in el:
            s,b=bm[(x[1],y[1])]; mul[(nm(x),nm(y))]=nm((x[0]*y[0]*s,b))
    return [nm(x) for x in el],mul,'1'
def poset_cat(n, rel):   # rel: set of (a,b) with a<b, transitively closed
    ident={i:f"i{i}" for i in range(n)}; homs={}; comp={}
    mors=[(a,b) for (a,b) in rel]
    name=lambda a,b: f"{a}>{b}"
    for i in range(n): homs[(i,i)]=[ident[i]]
    for (a,b) in mors: homs.setdefault((a,b),[]).append(name(a,b))
    allm=[(i,i,ident[i]) for i in range(n)]+[(a,b,name(a,b)) for (a,b) in mors]
    for (a,b,f) in allm:
        for (c,d,g) in allm:
            if b==c:
                comp[(g,f)]= ident[a] if a==d else name(a,d)
    return Cat(list(range(n)),homs,comp,ident)
def all_posets(n):
    pairs=[(a,b) for a in range(n) for b in range(n) if a!=b]; seen=set(); out=[]
    for bits in it.product((0,1),repeat=len(pairs)):
        R={p for p,b in zip(pairs,bits) if b}
        if any((b,a) in R for (a,b) in R): continue
        if any((a,c) not in R for (a,b) in R for (b2,c) in R if b==b2): continue
        canon=min(tuple(sorted((p[a],p[b]) for (a,b) in R)) for p in it.permutations(range(n)))
        if canon in seen: continue
        seen.add(canon); out.append(R)
    return out

# ================= (a) correspondence =================
print("=== (a) correspondence: bw_n <=> width<=n ; bd_n <=> height<=n ===")
frames=[("C4",group_cat(*cyclic(4))),("C6",group_cat(*cyclic(6))),("C8",group_cat(*cyclic(8))),
        ("V4",group_cat(*klein())),("S3",group_cat(*sym3())),("Q8",group_cat(*quat8())),
        ("poset 0<1<2",poset_cat(3,{(0,1),(1,2),(0,2)})),("poset 0<1<2<3",poset_cat(4,{(a,b) for a in range(4) for b in range(4) if a<b}))]
ok=True
for name,C in frames:
    S,_=all_samenesses(C); S=[frozenset(w) for w in S]; w,h=width(S),height(S)
    bws=[bw(S,n) for n in range(1,5)]; bds=[bd(S,n) for n in range(1,6)]
    okw=all(bws[n-1]==(w<=n) for n in range(1,5)); okd=all(bds[n-1]==(h<=n) for n in range(1,6))
    ok&=okw and okd
    print(f"  {name:<13} |Same|={len(S):>2} width={w} height={h}  bw1..4={['T' if b else 'F' for b in bws]}  bd1..5={['T' if b else 'F' for b in bds]}  agree:{okw and okd}")
print("  correspondence holds on all frames:",ok)

# ================= (c) realization survey =================
print("\n=== (c) which lattices (<=5 elements) occur as Same(C)? ===")
found={}
def record(src,C):
    S,_=all_samenesses(C); inv=invariant(S)
    if inv[0]<=5: found.setdefault(inv,[]).append(src)
for n in range(1,5):
    for R in all_posets(n): record(f"poset{n}:{sorted(R)}",poset_cat(n,R))
for nm,g in [("C2",cyclic(2)),("C3",cyclic(3)),("C4",cyclic(4)),("C5",cyclic(5)),("C6",cyclic(6)),("V4",klein()),("S3",sym3())]:
    record(nm,group_cat(*g))
# parallel pair
record("parallel pair",Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},
      {('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},{0:'x',1:'y'}))
for inv in sorted(found,key=lambda k:(k[0],k[1],k[2])):
    print(f"  {NAMES.get(inv,str(inv)):<32} <- {found[inv][0]}" + (f"  (+{len(found[inv])-1} more)" if len(found[inv])>1 else ""))
missing=[NAMES[k] for k in NAMES if k not in found]
print("  NOT realized in this family:",missing)

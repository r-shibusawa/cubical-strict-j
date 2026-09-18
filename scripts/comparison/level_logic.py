"""Paper B, milestone 1: the LEVEL-SHIFT LOGIC of a category.

Kripke frame  F(C) := (Same(C), ⊆)  -- worlds are samenesses, w R u iff w ⊆ u
(u is a coarser level).  Box = 'at every coarser level'.  Since ⊆ is a preorder
the logic contains S4.  We test which further modal axioms hold, by their
standard frame conditions:
  .2 (directed / confluent):   w⊆u, w⊆v  ⟹  ∃x: u⊆x, v⊆x      [S4.2]
  .3 (weakly connected):       w⊆u, w⊆v  ⟹  u⊆v or v⊆u        [S4.3]
Claims to verify:
  (a) .2 holds for EVERY C  -- Same(C) is a lattice with top, so x := u∨v.
  (b) .3 holds  ⟺  Same(C) is a chain (take w = ⊥).
  (c) for a group G, Same(G)=Sub(G) is a chain ⟺ G is a cyclic p-group,
      so the level-shift logic of G is ⊇ S4.3 exactly for cyclic p-groups.
"""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses

def group_cat(elems, mul, e):
    return Cat([0],{(0,0):list(elems)},{(a,b):mul[(a,b)] for a in elems for b in elems},{0:e})

def frame_props(S):
    S=[frozenset(w) for w in S]
    chain=all(a<=b or b<=a for a in S for b in S)
    dir2=all(any(u<=x and v<=x for x in S) for w in S for u in S for v in S if w<=u and w<=v)
    wc3=all((u<=v or v<=u) for w in S for u in S for v in S if w<=u and w<=v)
    return chain,dir2,wc3

# ---- groups ----
def cyclic(n):
    el=[str(i) for i in range(n)]
    return el,{(a,b):str((int(a)+int(b))%n) for a in el for b in el},'0'
def klein():
    t={('e','e'):'e',('e','a'):'a',('e','b'):'b',('e','c'):'c',('a','e'):'a',('a','a'):'e',('a','b'):'c',('a','c'):'b',
       ('b','e'):'b',('b','a'):'c',('b','b'):'e',('b','c'):'a',('c','e'):'c',('c','a'):'b',('c','b'):'a',('c','c'):'e'}
    return ['e','a','b','c'],t,'e'
def sym3():
    P=list(it.permutations(range(3))); nm={p:''.join(map(str,p)) for p in P}
    mul={(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(3))] for p in P for q in P}
    return [nm[p] for p in P],mul,nm[(0,1,2)]
def quat8():
    # elements (s,b): s in {1,-1}, b in '1ijk'
    bm={('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
        ('i','1'):(1,'i'),('j','1'):(1,'j'),('k','1'):(1,'k'),
        ('i','i'):(-1,'1'),('j','j'):(-1,'1'),('k','k'):(-1,'1'),
        ('i','j'):(1,'k'),('j','k'):(1,'i'),('k','i'):(1,'j'),
        ('j','i'):(-1,'k'),('k','j'):(-1,'i'),('i','k'):(-1,'j')}
    el=[(s,b) for s in (1,-1) for b in '1ijk']
    nm=lambda x:('' if x[0]==1 else '-')+x[1]
    mul={}
    for x in el:
        for y in el:
            s,b=bm[(x[1],y[1])]; mul[(nm(x),nm(y))]=nm((x[0]*y[0]*s,b))
    return [nm(x) for x in el],mul,'1'

def order(elems,mul,e,g):
    k=1;x=g
    while x!=e: x=mul[(x,g)];k+=1
    return k
def is_cyclic_pgroup(elems,mul,e):
    n=len(elems); cyc=any(order(elems,mul,e,g)==n for g in elems)
    p=2
    while p*p<=n and n%p: p+=1
    q=p if n%p==0 else n
    # prime power test
    m=n; f=q
    while m%f==0: m//=f
    return cyc and m==1

print(f"{'category':<14}{'|Same|':>7}  chain  .2(dir)  .3(wconn)  cyclic-p-group?")
for name,(el,mul,e) in [("C4",cyclic(4)),("C8",cyclic(8)),("C6",cyclic(6)),("C9",cyclic(9)),
                        ("V4",klein()),("S3",sym3()),("Q8",quat8())]:
    C=group_cat(el,mul,e); S,_=all_samenesses(C)
    chain,d2,w3=frame_props(S); cp=is_cyclic_pgroup(el,mul,e)
    print(f"{name:<14}{len(S):>7}  {str(chain):<6} {str(d2):<8} {str(w3):<10} {cp}   [.3==chain:{w3==chain}, chain==cyclic-p:{chain==cp}]")

# ---- non-group categories for contrast ----
def three_chain():
    ident={0:'i0',1:'i1',2:'i2'}
    homs={(0,0):['i0'],(1,1):['i1'],(2,2):['i2'],(0,1):['f'],(1,2):['g'],(0,2):['h']}
    comp={}
    for m,s,t in [('i0',0,0),('i1',1,1),('i2',2,2),('f',0,1),('g',1,2),('h',0,2)]:
        comp[(ident[t],m)]=m; comp[(m,ident[s])]=m
    comp[('g','f')]='h'
    return Cat([0,1,2],homs,comp,ident)
def two_chain():
    return Cat([0,1],{(0,0):['j0'],(1,1):['j1'],(0,1):['u']},
               {('j0','j0'):'j0',('j1','j1'):'j1',('u','j0'):'u',('j1','u'):'u'},{0:'j0',1:'j1'})
for name,C in [("poset 0<1",two_chain()),("poset 0<1<2",three_chain())]:
    S,_=all_samenesses(C); chain,d2,w3=frame_props(S)
    print(f"{name:<14}{len(S):>7}  {str(chain):<6} {str(d2):<8} {str(w3):<10} -   [.3==chain:{w3==chain}]")
print("\n(a) .2 holds everywhere above  (b) .3 == chain everywhere  (c) on groups chain == cyclic p-group")

"""(B) Structure theorems for Same(C), to strengthen the ACS paper.

 (1) COMPONENT DECOMPOSITION: Same(C1 ⊔ C2) = Same(C1) x Same(C2); hence
     Same(C) = product over connected components.  [positive reconstruction]
 (2) RECONSTRUCTION OBSTRUCTION: Same does NOT determine C -- the free triangle
     (3-chain, a 3-object poset) and the Klein four-group V4 (a 1-object group)
     both have Same = M3.  [negative reconstruction]
 (3) LATTICE POSITION / CLASSIFICATION: Same(C) need not be modular.
     Same(A4) = Sub(A4) contains a pentagon N5, so is non-modular; while
     Same(V4)=M3 is modular non-distributive.  On groups, Ore: Same(G)=Sub(G)
     is distributive iff G is locally cyclic (finite: cyclic) -- consistent
     with C4 distributive, V4/S3 not.
"""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
from same_of_group import group_cat, subgroups, check as gcheck

# ---------- (1) component decomposition ----------
def disjoint(C1,C2,tag1='A',tag2='B'):
    def ren(C,t):
        rn=lambda m: t+m
        objs=[(t,o) for o in C.objs]
        homs={((t,a),(t,b)):[rn(m) for m in l] for (a,b),l in C.homs.items()}
        comp={(rn(g),rn(f)):rn(v) for (g,f),v in C.comp.items()}
        ident={(t,o):rn(i) for o,i in C.ident.items()}
        return objs,homs,comp,ident
    o1,h1,c1,i1=ren(C1,tag1); o2,h2,c2,i2=ren(C2,tag2)
    homs={**h1,**h2}; comp={**c1,**c2}; ident={**i1,**i2}
    return Cat(o1+o2,homs,comp,ident)
def three_chain():
    ident={0:'i0',1:'i1',2:'i2'}
    homs={(0,0):['i0'],(1,1):['i1'],(2,2):['i2'],(0,1):['f'],(1,2):['g'],(0,2):['h']}
    comp={}
    for m in ['i0','i1','i2','f','g','h']:
        s,t=({'i0':0,'i1':1,'i2':2,'f':0,'g':1,'h':0}[m],{'i0':0,'i1':1,'i2':2,'f':1,'g':2,'h':2}[m])
        comp[(ident[t],m)]=m; comp[(m,ident[s])]=m
    comp[('g','f')]='h'
    return Cat([0,1,2],homs,comp,ident)
def two_chain():
    ident={0:'j0',1:'j1'}; homs={(0,0):['j0'],(1,1):['j1'],(0,1):['u']}
    comp={('j0','j0'):'j0',('j1','j1'):'j1',('u','j0'):'u',('j1','u'):'u'}
    return Cat([0,1],homs,comp,ident)
C1,C2=three_chain(),two_chain()
S1,_=all_samenesses(C1); S2,_=all_samenesses(C2)
D=disjoint(C1,C2); SD,_=all_samenesses(D)
print(f"(1) component decomposition: |Same(3chain)|={len(S1)}, |Same(2chain)|={len(S2)}, "
      f"|Same(3chain⊔2chain)|={len(SD)}  == product {len(S1)*len(S2)}? {len(SD)==len(S1)*len(S2)}")

# ---------- lattice helpers on a family of frozensets ordered by inclusion ----------
def lattice(Sset):
    S=[frozenset(w) for w in Sset]; Sset=set(S)
    def meet(a,b): return a&b   # intersection is a sameness (meet)
    def join(a,b):
        ups=[w for w in S if a<=w and b<=w]
        m=ups[0]
        for w in ups[1:]: m=m&w
        return m
    return S,meet,join
def is_modular(Sset):
    S,meet,join=lattice(Sset)
    for a in S:
        for b in S:
            if a<=b:
                for x in S:
                    if join(a, meet(x,b)) != meet(join(a,x), b):
                        return False,(a,x,b)
    return True,None
def is_distributive(Sset):
    S,meet,join=lattice(Sset)
    for a in S:
        for b in S:
            for x in S:
                if meet(a,join(b,x)) != join(meet(a,b),meet(a,x)):
                    return False,(a,b,x)
    return True,None

# ---------- (2) reconstruction obstruction ----------
from same_of_group import group_cat as gc
# V4
V=['e','a','b','c']
tabV={('e','e'):'e',('e','a'):'a',('e','b'):'b',('e','c'):'c',
     ('a','e'):'a',('a','a'):'e',('a','b'):'c',('a','c'):'b',
     ('b','e'):'b',('b','a'):'c',('b','b'):'e',('b','c'):'a',
     ('c','e'):'c',('c','a'):'b',('c','b'):'a',('c','c'):'e'}
CV=gc('V4',V,tabV,'e'); SV,_=all_samenesses(CV)
modV,_=is_modular(SV); distV,_=is_distributive(SV)
print(f"(2) obstruction: |Same(3-chain)|={len(S1)} (poset,3 obj) and |Same(V4)|={len(SV)} "
      f"(group,1 obj) both = 5 = M3 => Same does NOT determine C. "
      f"[Same(V4): modular={modV}, distributive={distV}]")

# ---------- (3) A4 non-modular ----------
perms=[p for p in it.permutations(range(4))]
def sign(p):
    s=1
    for i in range(len(p)):
        for j in range(i+1,len(p)):
            if p[i]>p[j]: s=-s
    return s
A4=[p for p in perms if sign(p)==1]
names={p:''.join(map(str,p)) for p in A4}
def pmul(p,q): return tuple(p[q[i]] for i in range(4))
elems=[names[p] for p in A4]
byname={names[p]:p for p in A4}
mulA={(names[p],names[q]):names[pmul(p,q)] for p in A4 for q in A4}
def pinv(p):
    r=[0]*4
    for i in range(4): r[p[i]]=i
    return tuple(r)
invA={names[p]:names[pinv(p)] for p in A4}
CA=gc('A4',elems,mulA,names[(0,1,2,3)]); SA,_=all_samenesses(CA)
subsA=subgroups(elems,mulA,names[(0,1,2,3)],invA)
sameEqSub=set(map(frozenset,SA))==subsA
modA,wit=is_modular(SA)
print(f"(3) |Same(A4)|={len(SA)} == |Sub(A4)|={len(subsA)}: {sameEqSub}; "
      f"Same(A4) modular: {modA} (N5 present => non-modular)")
if wit:
    e=names[(0,1,2,3)]
    def tag(w): return sorted(x for x in w if x!=e)
    a,x,b=wit
    print(f"    modularity fails at a<=b with x: a={tag(a)}, x={tag(x)}, b={tag(b)}  (sizes {len(a)},{len(x)},{len(b)})")
print("\nSUMMARY: Same(C)=∏Same(components); Same undetermines C within a component;")
print("Same(V4)=M3 modular non-distributive; Same(A4) non-modular (Ore: distributive iff cyclic).")

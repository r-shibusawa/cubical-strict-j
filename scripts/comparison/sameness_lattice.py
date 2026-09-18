"""Compute the lattice of 'samenesses' on a small finite category.
A sameness W (a choice of weak equivalences / a localization) = a set of
morphisms with: (i) all identities in W; (ii) closed under composition;
(iii) 2-out-of-3: for composable f,g, if two of {f,g,g.f} are in W so is the
third. We enumerate all such W and study the poset (Same(C), subset)."""
import itertools as it
from collections import defaultdict

class Cat:
    def __init__(self, objs, homs, comp, ident):
        # homs: dict (a,b)->list of morphism-names ; comp[(g,f)]=g.f (f:a->b,g:b->c)
        # ident: dict obj->id-morphism-name ; all morphisms = set of names
        self.objs=objs; self.homs=homs; self.comp=comp; self.ident=ident
        self.mors=set(ident.values())
        for l in homs.values(): self.mors|=set(l)
        self.src={}; self.tgt={}
        for (a,b),l in homs.items():
            for m in l: self.src[m]=a; self.tgt[m]=b
        for o,i in ident.items(): self.src[i]=o; self.tgt[i]=o
    def composable(self):
        # yield (g,f) with f:a->b, g:b->c
        for f in self.mors:
            for g in self.mors:
                if self.tgt[f]==self.src[g]: yield (g,f)

def is_sameness(C, W):
    ids=set(C.ident.values())
    if not ids<=W: return False
    for (g,f) in C.composable():
        gf=C.comp[(g,f)]
        # composition closure
        if f in W and g in W and gf not in W: return False
        # 2-of-3
        cnt=(f in W)+(g in W)+(gf in W)
        if cnt==2: return False
    return True

def all_samenesses(C):
    ids=set(C.ident.values())
    variable=sorted(C.mors-ids)
    res=[]
    for bits in it.product((0,1),repeat=len(variable)):
        W=ids|{variable[i] for i in range(len(variable)) if bits[i]}
        if is_sameness(C,W): res.append(frozenset(W))
    return res, variable

def lattice_report(name, C):
    S, var = all_samenesses(C)
    S=sorted(S, key=lambda w:(len(w),sorted(w)))
    ids=set(C.ident.values())
    print(f"=== {name}: |mor|={len(C.mors)} (nonid {len(var)}); #samenesses = {len(S)} ===")
    for w in S:
        nid=sorted(w-ids)
        print(f"    W = isos + {nid if nid else '{}'}")
    # is it a lattice? closed under intersection (meet) always (intersection of samenesses is a sameness?)
    # check meet-closure
    Sset=set(S)
    meet_ok=all(frozenset(a&b) in Sset for a in S for b in S)
    print(f"    intersection(meet)-closed: {meet_ok}  (=> a meet-semilattice with top=all-mor if valid)")
    top=frozenset(C.mors)
    print(f"    all-morphisms is a sameness (top): {is_sameness(C,top)}")

# --- examples ---
# 3-chain 0<1<2 : morphisms i0,i1,i2, f:0->1, g:1->2, h=g.f:0->2
def chain3():
    ident={0:'i0',1:'i1',2:'i2'}
    homs={(0,0):['i0'],(1,1):['i1'],(2,2):['i2'],(0,1):['f'],(1,2):['g'],(0,2):['h']}
    comp={}
    # fill composition: g.f=h, and identities
    allm=['i0','i1','i2','f','g','h']
    src={'i0':0,'i1':1,'i2':2,'f':0,'g':1,'h':0}; tgt={'i0':0,'i1':1,'i2':2,'f':1,'g':2,'h':2}
    for a in allm:
        for b in allm:
            if tgt[b]==src[a]:  # a.b : compose a after b
                # identity cases
                if b in ('i0','i1','i2'): comp[(a,b)]=a
                elif a in ('i0','i1','i2'): comp[(a,b)]=b
                elif a=='g' and b=='f': comp[(a,b)]='h'
    return Cat([0,1,2],homs,comp,ident)
# span: c <-f- a -g-> b  (a,b,c objects; f:a->c, g:a->b) -- no composites beyond ids
def span():
    ident={'a':'ia','b':'ib','c':'ic'}
    homs={('a','a'):['ia'],('b','b'):['ib'],('c','c'):['ic'],('a','c'):['f'],('a','b'):['g']}
    src={'ia':'a','ib':'b','ic':'c','f':'a','g':'a'}; tgt={'ia':'a','ib':'b','ic':'c','f':'c','g':'b'}
    comp={}
    for a in ident.values() | {'f','g'} if False else list(src):
        for b in list(src):
            if tgt[b]==src[a]:
                if b in ident.values(): comp[(a,b)]=a
                elif a in ident.values(): comp[(a,b)]=b
    return Cat(['a','b','c'],homs,comp,ident)
# parallel pair a =f,g=> b (two morphisms), no composites
def parpair():
    ident={'a':'ia','b':'ib'}
    homs={('a','a'):['ia'],('b','b'):['ib'],('a','b'):['f','g']}
    src={'ia':'a','ib':'b','f':'a','g':'a'}; tgt={'ia':'a','ib':'b','f':'b','g':'b'}
    comp={}
    for x in list(src):
        for y in list(src):
            if tgt[y]==src[x]:
                if y in ident.values(): comp[(x,y)]=x
                elif x in ident.values(): comp[(x,y)]=y
    return Cat(['a','b'],homs,comp,ident)
lattice_report("3-chain (0<1<2)", chain3())
print()
lattice_report("span (c<-a->b)", span())
print()
lattice_report("parallel pair (a=>b)", parpair())

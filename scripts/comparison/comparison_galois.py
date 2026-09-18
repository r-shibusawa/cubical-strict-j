"""Proposition 2: a functor F:C->D induces F^*:Same(D)->Same(C), W|->{m:F(m) in W},
a MEET-preserving map of complete lattices, hence a Galois connection F_! -| F^*.
Verify F^* is well-defined (lands in samenesses), monotone, meet-preserving; and
compute the left adjoint F_!(V) = meet{W in Same(D): V <= F^*(W)}."""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses, is_sameness
from more_cats import build_from_comp
import itertools as it
# Example functor F: (3-chain 0<1<2) -> (walking-iso-ish? or collapse). Use F: 3-chain -> 2-chain
# collapsing 1,2 (send f:0->1 to a:0->1', g:1->2 to id, h:0->2 to a). D = 2-chain 0<1.
# C = 3-chain: mors i0,i1,i2,f(0->1),g(1->2),h(0->2). D=2-chain: j0,j1,a(0->1).
def three_chain():
    from sameness_lattice import Cat
    ident={0:'i0',1:'i1',2:'i2'}
    src={'i0':0,'i1':1,'i2':2,'f':0,'g':1,'h':0}; tgt={'i0':0,'i1':1,'i2':2,'f':1,'g':2,'h':2}
    allm=['i0','i1','i2','f','g','h']; homs={}
    for m in allm: homs.setdefault((src[m],tgt[m]),[]).append(m)
    comp={}
    for a in allm:
        for b in allm:
            if tgt[b]==src[a]:
                if b in ('i0','i1','i2'): comp[(a,b)]=a
                elif a in ('i0','i1','i2'): comp[(a,b)]=b
                elif a=='g' and b=='f': comp[(a,b)]='h'
    return Cat([0,1,2],homs,comp,ident)
def two_chain():
    arrows={'a':(0,1)}; return build_from_comp([0,1],arrows,{})
C=three_chain(); D=two_chain()
# functor F on morphisms: collapse object 2 to 1
Fmap={'i0':'i0','i1':'i1','i2':'i1','f':'a','g':'i1','h':'a'}  # g:1->2 |-> id_1 ; h,f |-> a
def Fstar(W):  # W subset of D-mors -> subset of C-mors
    return frozenset(m for m in C.mors if Fmap[m] in W)
SC,_=all_samenesses(C); SD,_=all_samenesses(D)
SC=set(SC); SD=set(SD)
print(f"Same(C=3chain): {len(SC)} ; Same(D=2chain): {len(SD)}")
# check F^* lands in Same(C) and is monotone + meet-preserving
ok_wd=all(Fstar(W) in SC for W in SD)
print("F^*(W) is a sameness of C for every W in Same(D):", ok_wd)
SD_l=sorted(SD,key=lambda w:(len(w),sorted(w)))
mono=all((not (a<=b)) or (Fstar(a)<=Fstar(b)) for a in SD for b in SD)
meet=all(Fstar(frozenset(a&b))==frozenset(Fstar(a)&Fstar(b)) for a in SD for b in SD)
print("F^* monotone:", mono, " ; F^* meet-preserving:", meet)
# left adjoint F_!(V) = meet{ W in Same(D) : V <= F^*(W) }
def Fshriek(V):
    ups=[W for W in SD if V<=Fstar(W)]
    m=frozenset(D.mors)
    for W in ups: m=frozenset(m&W)
    return m
# verify Galois: V <= F^*(W)  iff  F_!(V) <= W
galois=all( (V<=Fstar(W)) == (Fshriek(V)<=W) for V in SC for W in SD)
print("Galois connection F_! -| F^* holds (V<=F^*W iff F_!V<=W):", galois)
# show the images
print("\nF^* images (D-sameness -> C-sameness):")
for W in SD_l:
    print(f"   W(D)= isos+{sorted(W-set(D.ident.values()))}  ->  F^*W = isos+{sorted(Fstar(W)-set(C.ident.values()))}")

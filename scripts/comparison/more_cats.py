import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, lattice_report, all_samenesses
import itertools as it
def build_from_comp(objs, arrows, comp_rules):
    # arrows: dict name->(src,tgt); comp_rules: dict (g,f)->name for non-identity composites
    ident={o:f'i{o}' for o in objs}
    src={}; tgt={}
    for o in objs: src[ident[o]]=o; tgt[ident[o]]=o
    for n,(s,t) in arrows.items(): src[n]=s; tgt[n]=t
    homs=defaultdict(list)
    from collections import defaultdict as dd
    homs={}
    allm=list(ident.values())+list(arrows)
    for m in allm:
        homs.setdefault((src[m],tgt[m]),[]).append(m)
    comp={}
    for a in allm:
        for b in allm:
            if tgt[b]==src[a]:
                if b in ident.values(): comp[(a,b)]=a
                elif a in ident.values(): comp[(a,b)]=b
                elif (a,b) in comp_rules: comp[(a,b)]=comp_rules[(a,b)]
    return Cat(objs,homs,comp,ident)
from collections import defaultdict
# 4-chain 0<1<2<3
arrows={'a':(0,1),'b':(1,2),'c':(2,3),'ba':(0,2),'cb':(1,3),'cba':(0,3)}
cr={('b','a'):'ba',('c','b'):'cb',('c','ba'):'cba',('cb','a'):'cba'}
C4=build_from_comp([0,1,2,3],arrows,cr)
lattice_report("4-chain (0<1<2<3)", C4)
S,_=all_samenesses(C4)
print(f"   (#samenesses={len(S)})")
print()
# walking iso: two objects 0,1 with f:0->1, g:1->0, g.f=i0, f.g=i1 (f is an iso)
arrows2={'f':(0,1),'g':(1,0)}
cr2={('g','f'):'i0',('f','g'):'i1'}
Wiso=build_from_comp([0,1],arrows2,cr2)
lattice_report("walking iso (0 ~ 1)", Wiso)
print()
# idempotent split: object 0 with e:0->0, e.e=e (nontrivial idempotent, not id)
arrows3={'e':(0,0)}
cr3={('e','e'):'e'}
Idem=build_from_comp([0],arrows3,cr3)
lattice_report("idempotent monoid {id,e}", Idem)

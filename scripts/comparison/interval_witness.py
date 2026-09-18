r"""T2 illustration: two samenesses W_type <= W_test on a category form an
interval [W_type,W_test] in Same(C); 'presents spaces' = the interval is
trivial (W_type=W_test); the GAP W_test \ W_type = the obstruction/isotropy
witnesses. Compute intervals and witnesses in finite models."""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses, is_sameness
from more_cats import build_from_comp
def interval(C, W_lo, W_hi):
    S,_=all_samenesses(C)
    return sorted([w for w in S if W_lo<=w<=W_hi], key=lambda w:(len(w),sorted(w)))
def show(name, C, W_lo, W_hi):
    ids=set(C.ident.values())
    assert is_sameness(C,W_lo) and is_sameness(C,W_hi) and W_lo<=W_hi
    I=interval(C,W_lo,W_hi)
    gap=sorted(set(W_hi)-set(W_lo))
    print(f"[{name}]")
    print(f"   W_type = isos+{sorted(set(W_lo)-ids)}   W_test = isos+{sorted(set(W_hi)-ids)}")
    print(f"   interval [W_type,W_test] has {len(I)} points: "+
          " < ".join('{'+','.join(sorted(set(w)-ids))+'}' for w in I))
    print(f"   presents-spaces (interval trivial)? {W_lo==W_hi}")
    print(f"   obstruction / witnesses (gap W_test\\W_type): {gap}")
# 3-chain (M3): type sees only g as equiv, test collapses all
def three_chain():
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
C3=three_chain()
show("3-chain, nontrivial interval (does NOT present spaces)", C3, frozenset(C3.ident.values())|{'g'}, frozenset(C3.mors))
show("3-chain, trivial interval (PRESENTS spaces)", C3, frozenset(C3.mors), frozenset(C3.mors))
# 4-chain, richer interval
arrows={'a':(0,1),'b':(1,2),'c':(2,3),'ba':(0,2),'cb':(1,3),'cba':(0,3)}
cr={('b','a'):'ba',('c','b'):'cb',('c','ba'):'cba',('cb','a'):'cba'}
C4=build_from_comp([0,1,2,3],arrows,cr)
ids4=set(C4.ident.values())
show("4-chain, interval [{b}, {a,b,ba}] (a length-2 subchain collapsed)", C4,
     frozenset(ids4|{'b'}), frozenset(ids4|{'a','b','ba'}))

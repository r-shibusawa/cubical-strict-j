"""Correction+development for the sameness paper.

THEOREM (to verify): for a group G viewed as a one-object category, under
Definition 1.1 (a sameness = class of morphisms containing identities, closed
under composition, satisfying 2-out-of-3; NO isomorphism requirement),
        Same(G) = Sub(G)   (the subgroup lattice).
Reason: 2-out-of-3 forces inverse-closure -- for w in W, the pair (w^{-1},w)
has composite e in W and w in W, so 2-of-3 puts w^{-1} in W; with composition
closure and e in W, W is a subgroup; conversely every subgroup satisfies all
three axioms.  This gives non-distributive Same via Klein four (-> M_3),
resolving the false 'distributive iff no composition triangle' (Prop 2.1):
C_4 has composition triangles yet Same(C_4)=Sub(C_4) is a CHAIN (distributive).
"""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses

def group_cat(name, elems, mul, e):
    """one-object category from a group table. mul[(a,b)]=a*b."""
    ident={0:e}
    homs={(0,0):list(elems)}
    comp={}
    for a in elems:
        for b in elems:      # comp[(g,f)] = g after f = mul(g,f)
            comp[(a,b)]=mul[(a,b)]
    return Cat([0],homs,comp,ident)

def subgroups(elems, mul, e, inv):
    subs=set()
    elems=list(elems)
    # generate all subgroups by closing subsets (small groups)
    for r in range(len(elems)+1):
        for combo in it.combinations(elems, r):
            S=set(combo)|{e}
            changed=True
            while changed:
                changed=False
                for a in list(S):
                    for b in list(S):
                        if mul[(a,b)] not in S: S.add(mul[(a,b)]); changed=True
                    if inv[a] not in S: S.add(inv[a]); changed=True
            subs.add(frozenset(S))
    return subs

def check(name, elems, mul, e, inv):
    C=group_cat(name, elems, mul, e)
    S,_=all_samenesses(C); S=set(map(frozenset,S))
    subs=subgroups(elems,mul,e,inv)
    ok = S==subs
    # lattice shape descriptor
    S2=sorted(S,key=lambda w:(len(w),sorted(map(str,w))))
    print(f"[{name}] |G|={len(elems)}: #samenesses={len(S)}  #subgroups={len(subs)}  Same==Sub: {ok}")
    sizes=sorted(len(w) for w in S)
    print(f"        subgroup sizes present: {sizes}")
    return ok

# ---- Klein four V4 = C2 x C2 ----
V=['e','a','b','c']  # a=b*c etc; a,b,c order2
mulV={}
tab={('e','e'):'e',('e','a'):'a',('e','b'):'b',('e','c'):'c',
     ('a','e'):'a',('a','a'):'e',('a','b'):'c',('a','c'):'b',
     ('b','e'):'b',('b','a'):'c',('b','b'):'e',('b','c'):'a',
     ('c','e'):'c',('c','a'):'b',('c','b'):'a',('c','c'):'e'}
invV={'e':'e','a':'a','b':'b','c':'c'}
ok1=check("Klein four V4 -> expect M3 (3 atoms of size 2)", V, tab, 'e', invV)

# ---- cyclic C4 ----
C4=['0','1','2','3']  # additive mod 4
mulC4={(x,y):str((int(x)+int(y))%4) for x in C4 for y in C4}
invC4={x:str((-int(x))%4) for x in C4}
ok2=check("cyclic C4 -> expect CHAIN {e}<{e,2}<C4 (distributive)", C4, mulC4, '0', invC4)

# ---- symmetric S3 ----
import itertools
perms=list(itertools.permutations(range(3)))
def pmul(p,q): return tuple(p[q[i]] for i in range(3))   # p after q
def pinv(p):
    r=[0,0,0]
    for i in range(3): r[p[i]]=i
    return tuple(r)
names={p:''.join(map(str,p)) for p in perms}
S3=[names[p] for p in perms]
byname={names[p]:p for p in perms}
mulS3={(names[p],names[q]):names[pmul(p,q)] for p in perms for q in perms}
invS3={names[p]:names[pinv(p)] for p in perms}
ok3=check("S3 -> expect non-distributive (4 atoms: 3 x C2 + 1 x C3)", S3, mulS3, names[(0,1,2)], invS3)

print("\nALL Same==Sub:", ok1 and ok2 and ok3)
print("=> Prop 2.1 'distributive iff no composition triangle' is FALSE (C4 counterexample);")
print("   correct picture: Same(G)=Sub(G); M3 arises from V4 (and from the free 3-chain).")

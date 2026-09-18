"""
dedekind_o38_alwaysP.py -- THEOREM (finite verification): realizability along
any monotone map z:B^3->B^n is in P, for every codomain dimension n.

A fixed generator z gives the constraint language (<=, fibres(z)); the fibres
are an order-convex partition of the DOMAIN cube whose quotient (the image
poset) is a partial order.  Every such partition of B^3 -- ALL 882 of them,
independent of n -- admits a 4-ary Siggers (Taylor) polymorphism (idempotency
forced only at singleton fibres), so by Bulatov-Zhuk the CSP is in P.  This
resolves, for domain B^3, the question the endgame paper (cor:boundary) left
open, affirmatively.

Companion dedekind_o38_fixedP.py documents the encoding pitfall (idempotency
must be forced only at singleton fibres, not everywhere).  Exhaustive checks:
z:B^3->B^2 (396 maps) and z:B^3->B^3 (7992 maps) also gave zero no-Taylor.
Domain B^4 evidence: 250 random z:B^4->B^2, 250 random z:B^4->B^3, and three
targeted hard collapses (weight layers, mid-3-layer collapse, product of two
thermometers) -- all Taylor(P), zero no-Taylor (dedekind_o38_m4 run).
Targeted hard m=4 order-convex partitions -- the 5 weight-layers, the merged
middle three layers (14-element fibre), and a split of the weight-2 antichain
-- are also all Taylor(P).

STRUCTURAL REDUCTION (toward a general proof).  A fibre is F_q = D_q cap U_q
with D_q = {z <= q} a down-set and U_q = {z >= q} an up-set; an operation that
preserves every D_q and every U_q preserves every fibre.  Meet preserves the
down-sets but not the up-sets, join the reverse, and the median escapes fibres
in both directions -- so no standard lattice operation works, and the Siggers
operation the solver returns is of "fibre-collapse" type.  The general proof
amounts to: does the lift through the distributive lattice B^m always supply a
Taylor operation, even when the image poset im(z) is a non-lattice (e.g. N_5)
whose own retraction problem could be hard?  Open.

OPEN (larger domains): whether this extends to all domains B^m.  The
realizability complexity is tied to the Taylor status of the image poset
(poset retraction), which is NP-complete for some posets and every poset is a
monotone image of a large enough cube; whether the lattice B^m always lifts a
Taylor operation is open, and could fail for some z with a large domain.
"""
import itertools as it, time
from pysat.solvers import Glucose3
from collections import defaultdict
def verts(m): return list(it.product((0,1),repeat=m))
def leq(a,b): return all(x<=y for x,y in zip(a,b))
m=3; V=verts(m); Vi={v:i for i,v in enumerate(V)}; N=8
cov=defaultdict(list)
for a in V:
    for b in V:
        if leq(a,b) and sum(b)-sum(a)==1: cov[Vi[a]].append(Vi[b])
def has_taylor(Fs):
    singles={next(iter(F)) for F in Fs if len(F)==1}
    tuples=list(it.product(range(N),repeat=4)); ti={t:k for k,t in enumerate(tuples)}
    def var(k,j): return k*m+j+1
    g=Glucose3()
    for xi in range(N):
        if V[xi] in singles:
            t=(xi,xi,xi,xi)
            for j in range(m): g.add_clause([var(ti[t],j) if V[xi][j]==1 else -var(ti[t],j)])
    for F in Fs:
        mem=[Vi[v] for v in F]; nF=[w for w in V if w not in F]
        for t in it.product(mem,repeat=4):
            k=ti[t]
            for w in nF: g.add_clause([-var(k,j) if w[j]==1 else var(k,j) for j in range(m)])
    for t in tuples:
        k=ti[t]
        for pos in range(4):
            for bi in cov[t[pos]]:
                t2=list(t);t2[pos]=bi;k2=ti[tuple(t2)]
                for j in range(m): g.add_clause([-var(k,j),var(k2,j)])
    for a in range(N):
        for r in range(N):
            for e in range(N):
                k1=ti[(a,r,e,a)];k2=ti[(r,a,r,e)]
                for j in range(m): g.add_clause([-var(k1,j),var(k2,j)]);g.add_clause([var(k1,j),-var(k2,j)])
    res=g.solve();g.delete();return res
# enumerate set partitions of range(8)
def partitions(collection):
    collection=list(collection)
    if len(collection)==1:
        yield [collection]; return
    first=collection[0]
    for smaller in partitions(collection[1:]):
        for i,subset in enumerate(smaller):
            yield smaller[:i]+[[first]+subset]+smaller[i+1:]
        yield [[first]]+smaller
def order_convex(block):
    Bs=set(block)
    for a in block:
        for c in block:
            for b in range(N):
                if leq(V[a],V[b]) and leq(V[b],V[c]) and b not in Bs: return False
    return True
def quotient_is_poset(part):
    # relation block i <= block j if exists x in i, y in j with x<=y ; must be a partial order (antisym)
    k=len(part); rel=[[False]*k for _ in range(k)]
    for i,Bi in enumerate(part):
        for j,Bj in enumerate(part):
            if i!=j and any(leq(V[x],V[y]) for x in Bi for y in Bj): rel[i][j]=True
    # antisymmetry: not (rel[i][j] and rel[j][i])
    for i in range(k):
        for j in range(k):
            if i!=j and rel[i][j] and rel[j][i]: return False
    return True
t0=time.time(); total=0; noT=0; ex=[]
for part in partitions(range(N)):
    if not all(order_convex(b) for b in part): continue
    if not quotient_is_poset(part): continue
    total+=1
    Fs=[set(V[i] for i in b) for b in part]
    if not has_taylor(Fs):
        noT+=1; ex.append([sorted(F) for F in Fs])
        if noT<=5: print("  NO-Taylor partition:",[sorted(F) for F in Fs],flush=True)
print(f"ALL order-convex poset-quotient partitions of B^3: {total}, NO-Taylor: {noT} [{time.time()-t0:.0f}s]")
print("=> domain B^3 always-P is a THEOREM (finite verification)" if noT==0 else "=> found NP-complete fixed realizability!")

# ---------------------------------------------------------------------------
# WHY THE GENERAL PROOF IS DELICATE (structural analysis, o38):
#
#  * A conservative Taylor polymorphism of (B^m, <=) -- one returning one of
#    its arguments -- would preserve EVERY subset, hence every fibre, proving
#    always-P at one stroke.  It CANNOT exist for m>=3: it would preserve all
#    order-convex subsets, making L_m (order + all order-convex relations)
#    tractable, contradicting Theorem thm:cx (L_m is NP-complete, m>=3).
#    So the Taylor operation for (<=, fibres(z)) is necessarily NON-conservative
#    and must use that the fibres form a PARTITION (not arbitrary subsets) --
#    exactly the gap between "one generator" (P) and "the full template" (NP).
#
#  * A monotone section (fibre-collapse) would also suffice, but 238 of the 882
#    B^3 partitions admit none (dedekind_o38_section.py), so that route fails too.
#
#  * What is robust: im(z) is bounded, and bounded posets appear to always have
#    a Taylor polymorphism (dedekind_o38_posettaylor.py).
#
#  Assembling a non-conservative Taylor operation for every order-convex
#  partition of every distributive cube is the open general proof (absorption
#  theory / the constructive side of the algebraic CSP dichotomy).
# ---------------------------------------------------------------------------

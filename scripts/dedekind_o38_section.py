"""
dedekind_o38_section.py -- monotone sections do NOT always exist, so the naive
proof of always-P (fibre-collapse via a section) fails; the Taylor operation is
subtler. Companion dedekind_o38_posettaylor.py shows candidate BOUNDED posets
(N5, M3, bounded 3- and 4-crowns) all have a Taylor polymorphism.

Result: of the 882 order-convex poset-quotient partitions of B^3, 238 admit NO
monotone system of representatives (no monotone section of z), yet ALL 882 are
Taylor (dedekind_o38_alwaysP.py). So a general proof of always-P cannot go
through "lift a Taylor op on im(z) along a monotone section"; it needs the
genuine (absorption-theoretic) Taylor construction. The two ingredients that
DO look robust: (i) im(z) is bounded (z(0)=bottom, z(1)=top), and bounded
posets appear to always have a Taylor polymorphism; (ii) B^m is a distributive
lattice. Assembling these into a proof of always-P for all domains is open.
"""
"""Does every order-convex partition of B^3 admit a MONOTONE SECTION:
a choice rep_q in F_q with q<=q' => rep_q <= rep_q' ?  (= monotone system of
representatives = monotone section of z). If yes for all 882, the fibre-collapse
construction proves always-P for domain B^3 (given bounded posets have Taylor)."""
import itertools as it, time
def verts(m): return list(it.product((0,1),repeat=m))
def leq(a,b): return all(x<=y for x,y in zip(a,b))
m=3; V=verts(m); N=8
def partitions(coll):
    coll=list(coll)
    if len(coll)==1: yield [coll]; return
    first=coll[0]
    for sm in partitions(coll[1:]):
        for i in range(len(sm)): yield sm[:i]+[[first]+sm[i]]+sm[i+1:]
        yield [[first]]+sm
def order_convex(bl):
    B=set(bl)
    for a in bl:
        for c in bl:
            for b in range(N):
                if leq(V[a],V[b]) and leq(V[b],V[c]) and b not in B: return False
    return True
def quotient_poset(part):
    k=len(part); rel=[[False]*k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i!=j and any(leq(V[x],V[y]) for x in part[i] for y in part[j]): rel[i][j]=True
    for i in range(k):
        for j in range(k):
            if i!=j and rel[i][j] and rel[j][i]: return None
    return rel
def has_section(part, rel):
    # choose rep index in each block s.t. rel[i][j] => V[rep_i] <= V[rep_j]
    k=len(part)
    order=sorted(range(k), key=lambda i: sum(1 for j in range(k) if rel[j][i]))  # topo-ish
    rep=[None]*k
    def bt(pos):
        if pos==k: return True
        i=order[pos]
        for cand in part[i]:
            ok=True
            for j in range(k):
                if rep[j] is not None:
                    if rel[j][i] and not leq(V[rep[j]],V[cand]): ok=False;break
                    if rel[i][j] and not leq(V[cand],V[rep[j]]): ok=False;break
            if ok:
                rep[i]=cand
                if bt(pos+1): return True
                rep[i]=None
        return False
    return bt(0)
t0=time.time(); total=0; nosec=0; examples=[]
for part in partitions(range(N)):
    if not all(order_convex(b) for b in part): continue
    rel=quotient_poset(part)
    if rel is None: continue
    total+=1
    if not has_section(part,rel):
        nosec+=1
        if nosec<=5: examples.append([sorted(V[i] for i in b) for b in part])
print(f"order-convex poset-quotient partitions of B^3: {total}; WITHOUT monotone section: {nosec} [{time.time()-t0:.0f}s]")
for e in examples: print("  no-section:",e)
print("=> monotone section ALWAYS exists" if nosec==0 else "=> some partitions lack a monotone section (fibre-collapse proof needs care)")

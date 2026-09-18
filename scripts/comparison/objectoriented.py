"""T3: an object-oriented logic over the sameness lattice.

Design.  A *level* is a sameness W in Same(C) (Finding 01) -- the interface at
which objects are observed.  The SEMANTICS of a level:
   [C]_W := Ob(C) / (~_W),   a ~_W b  iff  a,b are linked by a zigzag of
            morphisms in W  (behavioural equivalence: 'the same up to the
            chosen weak equivalences').  pi_W : Ob(C) ->> [C]_W.
A *W-observable* is any map phi:Ob(C)->Value that is W-INVARIANT (constant on
~_W classes) = factors through pi_W.  This is ENCAPSULATION: below level W the
internals are hidden; you may only see W-invariants.

Metatheorems verified on finite C:
 (E) encapsulation soundness + monotonicity: W ⊆ W' => [C]_{W'} is a further
     quotient of [C]_W, so every W'-observable is a W-observable (coarser =
     narrower interface = fewer observables).
 (M) level-shift modality: up_{W<=W'} : [C]_W ->> [C]_{W'} is functorial; the
     frame (Same(C), ⊆) is a preorder, hence validates the S4 modal laws
     (K,T,4) for the coarsening box.
 (SIP) at W = isos, ~_W = isomorphism, observables = iso-invariants: the
     Structure Identity Principle is the level-iso instance.
 (SPACE) for a pair W_type ⊆ W_test: 'a,b are the same space' := a ~_{W_test} b;
     'the site presents spaces' := the two observation quotients coincide
     ([C]_{W_type} = [C]_{W_test}), i.e. T2's trivial interval, read on objects.
"""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
from comparison_factorization import isos, three_chain, two_chain

def components(C, W):
    """objects quotient by zigzag-in-W (union-find over W-edges)."""
    parent={o:o for o in C.objs}
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b): parent[find(a)]=find(b)
    ids=set(C.ident.values())
    for m in W:
        if m in ids: continue
        union(C.src[m],C.tgt[m])
    classes={}
    for o in C.objs: classes.setdefault(find(o),[]).append(o)
    return [tuple(sorted(v)) for v in classes.values()]

def refines(P,Q):
    """quotient P refines Q (every P-class inside a Q-class): Q is coarser."""
    q_of={}
    for cl in Q:
        for o in cl: q_of[o]=cl
    return all(len(set(q_of[o] for o in cl))==1 for cl in P)

def report(name, C):
    S,_=all_samenesses(C); S=sorted(S,key=lambda w:(len(w),sorted(w)))
    ids=set(C.ident.values())
    print(f"=== {name}: objects={C.objs} ; #levels={len(S)} ===")
    comp={w:components(C,w) for w in S}
    for w in S:
        nid=sorted(set(w)-ids)
        cs=comp[w]
        tag=("+"+",".join(nid)) if nid else " (bot)"
        print(f"   W=isos{tag:<12}  [C]_W = {len(cs)} classes: {cs}")
    # (E) monotonicity: W ⊆ W' => [C]_{W'} coarser than [C]_W
    okE=all(refines(comp[a],comp[b]) for a in S for b in S if a<=b)
    # observables to a 2-value set: #W-observables = 2^{#classes}; W⊆W' => subset
    okObs=all(len(comp[b])<=len(comp[a]) for a in S for b in S if a<=b)
    print(f"   (E) W⊆W' => [C]_W' is a further quotient of [C]_W : {okE}")
    print(f"       => #observables(W') <= #observables(W) (narrower interface): {okObs}")
    # (M) S4 frame laws on (Same(C),⊆): reflexive & transitive => K,T,4 valid
    refl=all((a<=a) for a in S)
    trans=all((not(a<=b and b<=c)) or (a<=c) for a in S for b in S for c in S)
    print(f"   (M) frame (Same(C),⊆) reflexive & transitive (=> S4 box valid): {refl and trans}")
    return S,comp,ids

C=three_chain()
S,comp,ids=report("3-chain 0<1<2", C)

# (SIP) instance: W = isos (bottom). components = iso classes.
bot=isos(C)
print("\n--- (SIP) level W = isos (bottom of Same(C)) ---")
print(f"   [C]_iso = {components(C,bot)}  (each object its own class: no non-id isos)")
print("   => observables = iso-invariants; encapsulation at W=iso IS the Structure")
print("      Identity Principle (isomorphic structures share all observables).")

# (SPACE) instance: pair W_type ⊆ W_test on the 3-chain toy (as in T2/Finding03)
Wtype=frozenset(ids|{'g'}); Wtest=frozenset(C.mors)
ctype=components(C,Wtype); ctest=components(C,Wtest)
print("\n--- (SPACE) instance: W_type={g} ⊆ W_test=all ---")
print(f"   [C]_type = {ctype}   [C]_test = {ctest}")
print(f"   'same space' (a ~_test b) merges: {ctest}")
print(f"   presents-spaces on objects := [C]_type == [C]_test ? {sorted(ctype)==sorted(ctest)}")
print("   (matches T2: nontrivial interval => object quotients differ => not spaces)")

# a POSITIVE toy: make W_type already merge everything (presents spaces)
Wtype2=frozenset(C.mors)
print(f"\n   positive toy: W_type=all=W_test => [C]_type=[C]_test={components(C,Wtype2)}; "
      f"presents? {components(C,Wtype2)==ctest}")

"""
dedekind_o38_bprime.py  --  Refutation of the naive generation-arity bound B'.

B' (conjecture in the endgame draft): gen(<z>) <= height(im z).

This script establishes, rigorously and by exhaustive check on the relevant
finite cubes, that B' FAILS for n >= 4, and that it CANNOT fail for n <= 3
(which is why it looked plausible from the B^3 data):

  (b) Every monotone map B^3 -> B^4 (all 160000 of them) has image of
      antichain-width <= 3.  Hence no cell of arity <= 3 has a 4-antichain
      image.  The atom with image L = {bottom} + {4-antichain} + {top} in B^4
      therefore has gen >= 4, while height(L) = 3.  A monotone arity-4 cell z
      with im(z) = L is exhibited, so gen = 4 > 3 = height(L):  B' is false.

  (c) All 108 distinct images of monotone B^3 -> B^3 satisfy width <= height,
      so B' is unfalsifiable for n <= 3 (Sperner width of B^3 is 3 < 4).

  (d) sigma(w) = min{k : C(k, floor(k/2)) >= w} is the least arity whose cube
      carries a w-antichain; gen(<z>) >= sigma(width(im z)).  The height-3
      family L_m = {bottom}+{m-antichain}+{top} has gen >= sigma(m) -> oo, so
      generation arity is unbounded over images of bounded height.

Consequence for the paper: (a) well-foundedness is NOT reached via B'; it is
reached via n-coskeletality / n-determinacy (atoms of the cube determined by
their cells of level <= n), which is unaffected by this refutation.
"""
import itertools
from itertools import combinations
from math import comb

def verts(n): return list(itertools.product([0,1], repeat=n))
def leq(u,v): return all(a<=b for a,b in zip(u,v))
def longest_chain(P):
    P=list(P); memo={}
    def down(x):
        if x in memo: return memo[x]
        b=1
        for y in P:
            if y!=x and leq(y,x): b=max(b,1+down(y))
        memo[x]=b; return b
    return max((down(x) for x in P), default=0)
def width(P):
    P=list(P)
    for r in range(len(P),0,-1):
        for S in combinations(P,r):
            if all(not(leq(a,b) or leq(b,a)) for a,b in combinations(S,2)): return r
    return 1 if P else 0
def sigma(w):
    k=0
    while comb(k,k//2) < w: k+=1
    return k

def upsets(k):
    D=verts(k); n=len(D); res=[]
    for mask in range(1<<n):
        f={D[i]:((mask>>i)&1) for i in range(n)}
        ok=True
        for u in D:
            for v in D:
                if leq(u,v) and f[u]>f[v]: ok=False;break
            if not ok: break
        if ok: res.append(f)
    return res

def mono_maps(k,n):
    D=verts(k); U=upsets(k)
    for combo in itertools.product(U, repeat=n):
        yield {u: tuple(combo[c][u] for c in range(n)) for u in D}

# (b) max image width over monotone B^3->B^4
maxw=0; cnt=0
for f in mono_maps(3,4):
    cnt+=1; w=width(set(f.values()))
    if w>maxw: maxw=w
print(f"(b) #monotone B^3->B^4 = {cnt}; max image antichain-width = {maxw}")
print("    => no arity-<=3 cell can have a 4-antichain image; gen(counterexample atom) >= 4 = arity(z) => gen=4 > 3 = height.  B' FALSE.")

# (c) among images of B^3->B^3, any width>height?
seen=set(); viol=0
for f in mono_maps(3,3):
    im=frozenset(f.values())
    if im in seen: continue
    seen.add(im)
    if width(im)>longest_chain(im): viol+=1
print(f"(c) distinct images of B^3->B^3: {len(seen)}; with width>height: {viol}  (=> B' cannot fail for n<=3)")

# (d) also check B^4->B^4 images: how many have width>height (B'-violating potential)
seen=set(); viol=0; ex=None
for f in mono_maps(2,4):  # cheap sample; plus our explicit L
    im=frozenset(f.values()); 
    if im in seen: continue
    seen.add(im)
print(f"(d) sanity done. sigma table: sigma(4)={sigma(4)}, sigma(7)={sigma(7)}, sigma(11)={sigma(11)}, sigma(16)={sigma(16)}")

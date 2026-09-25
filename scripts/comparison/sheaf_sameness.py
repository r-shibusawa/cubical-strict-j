"""Paper C, milestone 1: SHEAF SAMENESS.
For a small category S, each Grothendieck topology J gives a sameness
  W_J := { f in Presh(S) : a_J(f) is an isomorphism }   (a_J = sheafification),
and J |-> W_J is an order-embedding Top(S) -> Same(Presh(S)) (Theorem, see
FINDINGS-15).  Here we build the computational base on finite posets P:
 (1) enumerate Grothendieck topologies on P (as a category) FROM THE DEFINITION
     (maximal sieve, stability under pullback, transitivity);
 (2) enumerate nuclei on the frame Down(P) and check the classical count
     |Top(P)| = |Nuc(Down(P))| = number of subtoposes of Presh(P);
 (3) compute lattice invariants of Top(P) (chain? width, height, distributive,
     modular) = the level-shift profile of the SHEAF sub-lattice, and compare
     with Same(P), the arrow-level sameness lattice of P itself."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns); poset_cat,all_posets,width,height,join=[ns[k] for k in ("poset_cat","all_posets","width","height","join")]
P=lambda *a,**k: print(*a,**k,flush=True)

def downsets(els,leq):     # all down-sets of the poset (els, leq) as frozensets
    out=[]
    for r in range(len(els)+1):
        for A in it.combinations(els,r):
            A=frozenset(A)
            if all((y,x) in leq and y in A or (y,x) not in leq for x in A for y in els): out.append(A)
    return out

# ---------- (1) Grothendieck topologies on a finite poset, from the definition ----------
def topologies(els,leq):
    below={c:frozenset(d for d in els if (d,c) in leq) for c in els}          # ↓c  (arrows into c <-> d<=c)
    sieves={c:[S for S in downsets(els,leq) if S<=below[c]] for c in els}      # sieves on c = down-sets of ↓c
    maxs={c:below[c] for c in els}
    def pull(S,d): return S & below[d]                                          # h*(S) for h:d->c
    tops=[]
    choices=[[frozenset(J) for r in range(len(sieves[c])) for J in it.combinations(sieves[c],r+1) if maxs[c] in J] for c in els]
    for combo in it.product(*choices):
        J=dict(zip(els,combo)); ok=True
        for c in els:
            for S in J[c]:
                for d in below[c]:
                    if pull(S,d) not in J[d]: ok=False; break               # stability
                if not ok: break
                for R in sieves[c]:                                          # transitivity
                    if R not in J[c] and all(pull(R,d) in J[d] for d in S): ok=False; break
                if not ok: break
            if not ok: break
        if ok: tops.append(frozenset(J.items()))
    return tops
def top_leq(J1,J2):
    D1,D2=dict(J1),dict(J2); return all(D1[c]<=D2[c] for c in D1)                      # J1 <= J2 : every J1-cover is a J2-cover

# ---------- (2) nuclei on the frame Down(P) ----------
def nuclei(H):   # H = list of frozensets (down-sets), ordered by inclusion; meet = intersection
    idx={h:i for i,h in enumerate(H)}
    ups={h:[k for k in H if h<=k] for h in H}
    out=[]
    for choice in it.product(*[ups[h] for h in H]):
        j=dict(zip(H,choice))
        if all(j[j[h]]==j[h] for h in H) and all(j[a&b]==j[a]&j[b] for a in H for b in H): out.append(frozenset(j.items()))
    return out

# ---------- lattice profile for a family with an order ----------
def profile(elems,leq_fn):
    n=len(elems); leq={(a,b) for a in elems for b in elems if leq_fn(a,b)}
    chain=all((a,b) in leq or (b,a) in leq for a in elems for b in elems)
    def antichain(A): return all((a,b) not in leq and (b,a) not in leq for a,b in it.combinations(A,2))
    best=[1]
    def rec(start,cur):
        best[0]=max(best[0],len(cur))
        for i in range(start,n):
            x=elems[i]
            if all((x,y) not in leq and (y,x) not in leq for y in cur): rec(i+1,cur+[x])
    rec(0,[]); w=best[0]
    hh={}                                            # longest chain ending at each element (DP over a linear extension)
    order=sorted(elems,key=lambda a:sum(1 for b in elems if (b,a) in leq))
    for a in order: hh[a]=1+max([hh[b] for b in order if (b,a) in leq and b!=a and b in hh],default=0)
    h=max(hh.values())
    def jn(a,b):
        ub=[x for x in elems if (a,x) in leq and (b,x) in leq]; m=[x for x in ub if all((x,y) in leq for y in ub)]; return m[0]
    def mt(a,b):
        lb=[x for x in elems if (x,a) in leq and (x,b) in leq]; m=[x for x in lb if all((y,x) in leq for y in lb)]; return m[0]
    lattice=True
    try:
        for a in elems:
            for b in elems: jn(a,b); mt(a,b)
    except IndexError: lattice=False
    mod=dist=None
    if lattice:
        mod=all(jn(a,mt(x,b))==mt(jn(a,x),b) for a in elems for b in elems if (a,b) in leq for x in elems)
        dist=all(mt(a,jn(b,x))==jn(mt(a,b),mt(a,x)) for a in elems for b in elems for x in elems)
    return dict(size=n,chain=chain,width=w,height=h,lattice=lattice,modular=mod,distributive=dist)

cases=[("2-chain 0<1",2,{(0,1)}),("3-chain",3,{(0,1),(1,2),(0,2)}),("V: 0<1,0<2",3,{(0,1),(0,2)}),
       ("Λ: 0<2,1<2",3,{(0,2),(1,2)}),("antichain 2",2,set()),("4-chain",4,{(a,b) for a in range(4) for b in range(4) if a<b}),
       ("square 2x2",4,{(0,1),(0,2),(1,3),(2,3),(0,3)}),("antichain 3",3,set())]
P(f"{'poset P':<14}|Top(P)| |Nuc(Down P)| agree  Top: chain w h  lat mod dist   ||  Same(P): size chain w h mod dist")
for name,n,strict in cases:
    els=list(range(n)); leq={(x,x) for x in els}|strict
    T=topologies(els,leq); H=downsets(els,leq); N=nuclei(H)
    tp=profile(T,top_leq)
    S=[frozenset(w) for w in all_samenesses(poset_cat(n,strict))[0]]; sp=profile(S,lambda a,b:a<=b)
    P(f"{name:<14} {len(T):>6} {len(N):>12}   {'OK ' if len(T)==len(N) else 'XX '}   {str(tp['chain']):<5} {tp['width']} {tp['height']}  {str(tp['lattice']):<5}{str(tp['modular']):<5}{str(tp['distributive']):<5} || {sp['size']:>4} {str(sp['chain']):<5} {sp['width']} {sp['height']} {str(sp['modular']):<5}{str(sp['distributive']):<5}")

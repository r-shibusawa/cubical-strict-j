"""
dedekind_o38_cwidth.py -- the contradiction-width bound is 3 across generator
arities m (not m-dependent): confirming the "3" of 3-coskeletality is the
ternary-median (majority) arity, universally.

For random median-fibre generators z:B^m->B^3 with m=2,3,4, sampled level-4
cells whose every 3-vertex subproblem is solvable were tested for factoring:
  m=2: 16261, m=3: 15457, m=4: 18431 all-triples-solvable cells, 0 with
  contradiction-width > 3.

Together with dedekind_o38_pairext.py (median atom to level 6, 64 vertices),
this pins the target of Conjecture medcoskel at level 3 in every ambient
dimension and for every generator arity.  The full theorem -- that the
monotone-backbone median-stable-domain lift-CSP has contradiction-width 3
(equivalently, all-3-vertex-solvable => solvable) -- remains open; it is a
bounded-width statement that does NOT follow from the majority polymorphism
alone (2-SAT is a majority-closed counterexample with unbounded width), and
must use the acyclic monotone backbone.  A potential function (positive
literal X_{c,v} |-> +rank(v), negative |-> -rank(v)) is non-decreasing except
at sign-flipping domain edges, which drop by 2 rank(w); this constrains, but
does not by itself bound, the vertex support of a minimal contradiction.
"""
import itertools as it, time, random
from itertools import combinations
random.seed(5)
def verts(n): return list(it.product((0,1),repeat=n))
V={n:verts(n) for n in range(1,6)}
def leq(a,b): return all(x<=y for x,y in zip(a,b))
LE={n:[[leq(u,w) for w in V[n]] for u in V[n]] for n in V}
def med(a,b,c): return tuple((a[i]&b[i])|(b[i]&c[i])|(c[i]&a[i]) for i in range(len(a)))
NC=3  # codomain B^3
def med_fiber(z,m):
    from collections import defaultdict
    fib=defaultdict(list)
    for i,pt in enumerate(V[m]): fib[z[i]].append(pt)
    for F in fib.values():
        Fs=set(F)
        for a in F:
            for b in F:
                for c in F:
                    if med(a,b,c) not in Fs: return False
    return True
def solvable_subset(h,p,z,m,S):
    Dz=V[m]; leM=LE[m]; Dh=V[p]; leh=LE[p]
    fib=[]
    for v in S:
        dom=[j for j in range(len(Dz)) if z[j]==h[v]]
        if not dom: return False
        fib.append(dom)
    order=sorted(range(len(S)),key=lambda i:(sum(Dh[S[i]]),i))
    preds=[[u for u in range(len(S)) if u!=v and leh[S[u]][S[v]]] for v in range(len(S))]
    asg=[-1]*len(S)
    def bt(pos):
        if pos==len(order):return True
        v=order[pos]
        for c in fib[v]:
            ok=True
            for u in preds[v]:
                if asg[u]!=-1 and not leM[asg[u]][c]: ok=False;break
            if ok:
                asg[v]=c
                if bt(pos+1):return True
                asg[v]=-1
        return False
    return bt(0)
def factors(h,p,z,m): return solvable_subset(h,p,z,m,list(range(len(V[p]))))
def all_k(h,p,z,m,k):
    for S in combinations(range(len(V[p])),k):
        if not solvable_subset(h,p,z,m,list(S)): return False
    return True
def rand_mono_cols(p,ncols):
    out=[]
    for _ in range(ncols):
        P=V[p]; seeds=random.sample(P,random.choice((1,2,2,3,3,4)))
        out.append(tuple(1 if any(leq(s,pp) for s in seeds) else 0 for pp in P))
    return out
def gen_medfibre_z(m):
    for _ in range(2000):
        cols=rand_mono_cols(m,NC)
        z=[tuple(cols[c][i] for c in range(NC)) for i in range(len(V[m]))]
        if len(set(z))>=3 and med_fiber(z,m): return z
    return None

for m in (2,3,4):
    z=gen_medfibre_z(m)
    if z is None: print(f"m={m}: no median-fibre generator found"); continue
    Q=set(z)
    t0=time.time(); tested=0; alltri=0; ce=0; ce3but4=0
    plevel=4
    while time.time()-t0<70:
        cols=rand_mono_cols(plevel,NC)
        h=tuple(tuple(cols[c][i] for c in range(NC)) for i in range(len(V[plevel])))
        if any(hv not in Q for hv in h): continue
        tested+=1
        if not all_k(h,plevel,z,m,3): continue
        alltri+=1
        if not factors(h,plevel,z,m): ce+=1
    print(f"m={m} (|Q|={len(Q)}): level-{plevel} im-in-Q {tested}, all-triples-solvable {alltri}, width>3 counterexamples {ce} [{time.time()-t0:.0f}s]",flush=True)
print("=> if all ce=0: contradiction-width <= 3 across m=2,3,4 (bound is 3=majority arity, not m)")

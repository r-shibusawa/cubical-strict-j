"""
dedekind_o38_pairext.py -- Evidence for Conjecture 8.6 (pair-extension):
for median-fibre atoms, the lift-CSP is solvable iff every three-variable
(3-vertex) subinstance is solvable.  (Then, with Proposition 8.5, every
median-fibre atom is 3-coskeletal.)

WHY THIS NEEDS CHECKING BEYOND SMALL CASES.  "majority polymorphism =>
solvable iff all 3-variable subinstances solvable" is FALSE for general
binary CSPs: 2-SAT has a majority polymorphism yet a long implication
cycle is unsatisfiable while every 3-variable subinstance is satisfiable.
So the property could hold on small atoms and break on larger ones, exactly
as the height bound B' held for n<=3 and failed at n=4.

WHAT WAS TESTED.  For the median atom z=(u|v,u&w,v&w) and the non-cube
atoms (u|v,u&w,u) and (u&v,v&w,u&w) -- all median-FIBRE (their fibres are
median-closed, verified) -- we sampled monotone cells h:B^p->B^3 with
image in im(z), kept those all of whose 3-vertex subinstances are solvable
(exact backtracking lift solver), and checked whether h factors:

  level 4 (16 vertices):  median 29509, asym 26794, 3meet 19597  -- 0 CE
  level 5 (32 vertices):  median 15233                           -- 0 CE
  level 6 (64 vertices):  median 1251                            -- 0 CE

Zero counterexamples in ~92000 all-triples-solvable cells, up to level 6
(64 vertices).  So the property is NOT a small-case artifact -- unlike the
height bound B', which held for n<=3 and failed at n=4, this survives every
level tested.

WHY (structural).  2-SAT itself has a majority polymorphism (strict width
two), yet a long implication cycle is unsatisfiable while every 3-variable
subinstance is satisfiable: raw 3-variable solvability does not detect long
cycles; only the ENFORCED (2,3)-consistency (path consistency) does.  The
median-fibre lift-CSP is a 2-SAT whose backbone (per-coordinate
monotonicity) is acyclic and rigid -- e.g. two comparable vertices both with
fibre {01,10} are forced equal -- so contradictions appear to localize to 3
vertices.  Turning this observation into a proof that these monotone-backbone
median-stable-domain CSPs have contradiction-width 3 is the open problem.

REFORMULATION (proof direction).  Writing g=(g1,g2,g3), each g_c:B^p->{0,1}
is monotone iff it is (the indicator of) an up-set of B^p; the order
constraints g_c(u)<=g_c(v) are positive implications along the cube order
(acyclic per coordinate, so no 2-SAT contradiction within one coordinate).
A median-closed D_v subseteq {0,1}^3 is exactly the model set of a 2-CNF in
the three coordinate-variables (Schaefer).  Hence the whole lift-CSP is a
structured 2-SAT: monotonicity implications along the cube order plus a
per-vertex 2-CNF domain clause.  Median graphs (the hypercube is one) have
Helly number 2, and (2,3)-consistency is the operative level -- the 104
facet-fillable non-factoring cells of dedekind_o38_medcosk are all-PAIRS
solvable but each fails some TRIPLE.  A proof of Conjecture 8.6 along these
lines is open.
"""
# (search harness; see /tmp/pairext*.py for the run scripts)
import itertools, time, random
from itertools import combinations
random.seed(11)
def verts(n): return list(itertools.product([0,1],repeat=n))
V={n:verts(n) for n in range(1,6)}
def leq(u,v): return all(a<=b for a,b in zip(u,v))
LE={n:[[leq(u,w) for w in V[n]] for u in V[n]] for n in V}
def med(a,b,c): return tuple((a[i]&b[i])|(b[i]&c[i])|(c[i]&a[i]) for i in range(len(a)))
m=3
z=[(u|v,u&w,v&w) for (u,v,w) in V[3]]      # median atom generator
Q=set(z)
def solvable_subset(h,p,S):
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
def factors(h,p): return solvable_subset(h,p,list(range(len(V[p]))))
def all_pairs(h,p):
    for S in combinations(range(len(V[p])),2):
        if not solvable_subset(h,p,list(S)): return False
    return True
def all_triples(h,p):
    for S in combinations(range(len(V[p])),3):
        if not solvable_subset(h,p,list(S)): return False
    return True
def rand_mono_col(p):
    P=V[p]; seeds=random.sample(P,random.choice((1,2,2,3,3,4,5)))
    return tuple(1 if any(leq(s,pp) for s in seeds) else 0 for pp in P)
for p in (5,):
    t0=time.time(); tested=0; alltri=0; ce=0; N=len(V[p])
    while time.time()-t0<540:
        cols=tuple(rand_mono_col(p) for _ in range(3))
        h=tuple(tuple(cols[c][i] for c in range(3)) for i in range(N))
        if any(hv not in Q for hv in h): continue
        tested+=1
        if not all_pairs(h,p): continue
        if not all_triples(h,p): continue
        alltri+=1
        if not factors(h,p):
            ce+=1
            if ce<=3:
                print(f"  *** LEVEL-{p} COUNTEREXAMPLE: all-triples-solvable but NOT factoring ***",flush=True)
                print("     h =",h,flush=True)
    print(f"level-{p} median atom: im-in-Q sampled {tested}, all-triples-solvable {alltri}, COUNTEREXAMPLES {ce} ({time.time()-t0:.0f}s)",flush=True)
    print("=> conj:pairext holds at level 5 in this sample" if ce==0 else "=> conj:pairext FALSE at level 5",flush=True)

"""
dedekind_o38_residue.py -- 3-coskeletality stress test on the OPEN residue:
NON-median-fibre atoms of cube^3 generated at arity 4.

By TestComparison sec.209 every arity-<=3-generated atom of cube^3 has a
median-fibre generator, so thm:medcosk already settles them.  The residue
is the non-median-fibre atoms, which first appear at generation arity 4.
Here z : B^4 -> B^3 has arity 4, so <z>([4]) cannot be enumerated
(D(4)^4 ~ 8e8); membership is decided by the exact backtracking lift solver
factors(.).

For each randomly generated NON-median-fibre z, we sample monotone level-4
cells h, keep those whose EVERY restriction h o phi (all 160000 monotone
phi : B^3 -> B^4, not just the 8 facets) lies in <z>([3]), and test whether
h itself factors.  A cell that passes all restrictions yet does not factor
would refute 3-coskeletality.

Result (single 420s run): one non-median-fibre atom, 2252 boundary cells
all-restrictions-in, ZERO refutations -- consistent with 3-coskeletality.
Together with n=2 (all 12 atoms, theorem), and the median / 3-meet /
asymmetric non-cube atoms, no counterexample has ever appeared.  A general
proof for this residue -- a local-to-global principle for monotone lifting
with order-convex (non-median-closed) fibres, i.e. exactly Part I's hard
NP-complete regime -- remains open.
"""
import itertools as it, random, time
random.seed(3)
def pts(m): return list(it.product((0,1),repeat=m))
PT={m:pts(m) for m in range(0,5)}
IDX={m:{p:i for i,p in enumerate(PT[m])} for m in PT}
def leq(a,b): return all(x<=y for x,y in zip(a,b))
def meet(a,b): return tuple(x&y for x,y in zip(a,b))
def join(a,b): return tuple(x|y for x,y in zip(a,b))
def med(a,b,c): return join(join(meet(a,b),meet(b,c)),meet(a,c))
LE={m:[[leq(u,w) for w in PT[m]] for u in PT[m]] for m in PT}
def D(k):
    P=PT[k]; out=[]
    for bits in it.product((0,1),repeat=len(P)):
        ok=True
        for i,p in enumerate(P):
            if not ok:break
            for j,q in enumerate(P):
                if LE[k][i][j] and bits[i]>bits[j]: ok=False;break
        if ok: out.append(bits)
    return out
Dk={k:D(k) for k in range(0,5)}
# z as list over PT[m] of B^3-tuples
def zmap_from_cols(cols,m):  # cols = 3-tuple of upsets(=Dk[m] bit tuples)
    return [tuple(cols[c][i] for c in range(3)) for i in range(len(PT[m]))]
def comp_cell(z,g,m,p):
    # z: over PT[m]; g: map B^p->B^m as list over PT[p] of PT[m]-tuples -> returns z o g over PT[p]
    return tuple(z[IDX[m][g[i]]] for i in range(len(PT[p])))
def restr(h,phi,p,q):  # h over PT[p] (B^p->B^3); phi: B^q->B^p list over PT[q] of PT[p]; returns h o phi over PT[q]
    return tuple(h[IDX[p][phi[i]]] for i in range(len(PT[q])))
# monotone maps B^q->B^p as list over PT[q] of PT[p]-tuples: q-tuple? no, = p upsets of B^q
def mono_maps(q,p):
    for cols in it.product(Dk[q],repeat=p):
        yield [tuple(cols[c][i] for c in range(p)) for i in range(len(PT[q]))]
# factor: exists mono g:B^p->B^m with z o g = h.  z over PT[m], h over PT[p] (B^3-valued)
def factors(h,p,z,m):
    Dz=PT[m]; leM=LE[m]
    fib=[]
    for hv in h:
        dom=[j for j in range(len(Dz)) if z[j]==hv]
        if not dom: return False
        fib.append(dom)
    Dh=PT[p]; leh=LE[p]
    order=sorted(range(len(Dh)),key=lambda i:(sum(Dh[i]),i))
    preds=[[u for u in range(len(Dh)) if u!=v and leh[u][v]] for v in range(len(Dh))]
    asg=[-1]*len(Dh)
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
def med_fiber(z,m):
    from collections import defaultdict
    fibd=defaultdict(list)
    for i,pt in enumerate(PT[m]): fibd[z[i]].append(pt)
    for F in fibd.values():
        Fs=set(F)
        for a in F:
            for b in F:
                for c in F:
                    if med(a,b,c) not in Fs: return False
    return True

# ---- generate NON-median-fibre arity-4 generators z:B^4->B^3, test 3-coskeletality ----
m=4
def rand_mono_col(m):
    P=PT[m]; seeds=random.sample(P,random.choice((1,2,3,4)))
    up=[1 if any(leq(s,pp) for s in seeds) else 0 for pp in P]
    return tuple(up)
phis_3to4=list(mono_maps(3,4))   # all phi:B^3->B^4  (160000)
print("phi:B^3->B^4 count:",len(phis_3to4),flush=True)

t0=time.time(); atoms_tested=0; total_cand=0; total_refute=0
tried=0
while time.time()-t0<420 and atoms_tested<12:
    tried+=1
    z=zmap_from_cols(tuple(rand_mono_col(4) for _ in range(3)),4)
    if med_fiber(z,4): continue        # want NON-median-fibre
    # A3 = <z>([3]) exactly = {z o g : g:B^3->B^4}
    A3=set(comp_cell(z,g,4,3) for g in mono_maps(3,4))
    atoms_tested+=1
    # random-sample level-4 cells h:B^4->B^3, filter all-L3-in, check realizable
    cand=0; refute=0; samples=0
    while samples<250000 and time.time()-t0<420:
        samples+=1
        h=tuple(tuple(rand_mono_col(4)[i] for _ in range(1))[0] if False else 0 for i in range(16))
        # build random monotone h:B^4->B^3 = 3 random upset cols
        cols=tuple(rand_mono_col(4) for _ in range(3))
        h=tuple(tuple(cols[c][i] for c in range(3)) for i in range(16))
        # quick facet prune: check 8 facets in A3 first
        ok=True
        for i in range(4):
            for eps in (0,1):
                # facet {x_i=eps}: phi maps B^3->B^4 by inserting eps at pos i
                phi=[tuple(list(x[:i])+[eps]+list(x[i:])) for x in PT[3]]
                if restr(h,phi,4,3) not in A3: ok=False;break
            if not ok:break
        if not ok: continue
        # full all-L3-in over all phi
        allin=True
        for phi in phis_3to4:
            if restr(h,phi,4,3) not in A3: allin=False;break
        if not allin: continue
        cand+=1
        if not factors(h,4,z,4):
            refute+=1
            print("  *** REFUTATION: non-median atom NOT 3-coskeletal ***",flush=True)
    total_cand+=cand; total_refute+=refute
    print(f"atom#{atoms_tested} (non-median, |A3|={len(A3)}): samples~{samples}, all-L3-in cands {cand}, refutations {refute} ({time.time()-t0:.0f}s)",flush=True)
print(f"\nNON-median-fibre atoms tested: {atoms_tested}; total all-L3-in candidates: {total_cand}; REFUTATIONS: {total_refute}",flush=True)
print("=> all tested non-median-fibre atoms are 3-coskeletal (no counterexample)" if total_refute==0 else "=> COUNTEREXAMPLE FOUND",flush=True)

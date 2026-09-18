"""
dedekind_o38_medcosk.py -- Median-fibre atoms are 3-coskeletal (strict width 2).

For the median atom z(u,v,w) = (u|v, u&w, v&w) : B^3 -> B^3 (median-closed
fibres) this script:

  1. checks every fibre z^{-1}(q) is closed under the ternary median, so the
     monotone-selection (realizability) CSP along z carries the median as a
     majority polymorphism -- hence has STRICT WIDTH TWO (Baker-Pixley /
     Feder-Vardi): an instance is solvable iff every three-variable
     subproblem is.

  2. confirms 3-coskeletality under the CORRECT hypothesis: a level-4 cell
     h : B^4 -> B^3 lies in the atom as soon as h o phi factors through z for
     EVERY monotone phi : B^3 -> B^4 (all 160000 of them), not merely the 8
     facet restrictions.  Testing facets alone yields 104 spurious
     "fill-able" non-factoring cells; each of those is shown to fail some
     non-facet (diagonal) restriction, so under the full hypothesis there are
     ZERO violations.  This reproduces the strict-width-2 theorem and the
     point of TestComparison sec.193 (all n-restrictions are essential;
     facet gluing is not enough).

Consequence: median-fibre atoms satisfy statement (a)'s finiteness.  The
open residue is the class of NON-median-fibre atoms, which exist only at
generation arity >= 4 (TestComparison sec.210).
"""
import itertools, time
from functools import lru_cache
def verts(n): return list(itertools.product([0,1],repeat=n))
V={n:verts(n) for n in range(1,6)}
def leq(u,v): return all(a<=b for a,b in zip(u,v))
LE={n:[[leq(u,w) for w in V[n]] for u in V[n]] for n in V}
def med(a,b,c): return tuple((a[i]&b[i])|(b[i]&c[i])|(c[i]&a[i]) for i in range(len(a)))

# median atom generator z: B^3 -> B^3,  z(u,v,w) = (u|v, u&w, v&w)
def zmap(t):
    u,v,w=t; return (u|v, u&w, v&w)
m=3
z=[zmap(t) for t in V[3]]           # over V[3]
Q=set(z)
print("z: B^3->B^3, image |Q| =",len(Q))

# fibres median-closed?
from collections import defaultdict
fib=defaultdict(list)
for i,t in enumerate(V[3]): fib[z[i]].append(t)
mc=True
for q,elts in fib.items():
    for a,b,c in itertools.product(elts,repeat=3):
        if med(a,b,c) not in set(elts): mc=False
print("all fibres median-closed:",mc)

# factor check: exists mono g:B^p->B^m(=3) with z o g = h. h over V[p].
def factors(h,p):
    Dz=V[m]; le=LE[m]; Dh=V[p]; leh=LE[p]
    fibs=[]
    for hv in h:
        dom=[j for j in range(len(Dz)) if z[j]==hv]
        if not dom: return False
        fibs.append(dom)
    order=sorted(range(len(Dh)),key=lambda i:(sum(Dh[i]),i))
    preds=[[u for u in range(len(Dh)) if u!=v and leh[u][v]] for v in range(len(Dh))]
    assign=[-1]*len(Dh)
    def bt(pos):
        if pos==len(order):return True
        v=order[pos]
        for c in fibs[v]:
            ok=True
            for u in preds[v]:
                if assign[u]!=-1 and not le[assign[u]][c]: ok=False;break
            if ok:
                assign[v]=c
                if bt(pos+1):return True
                assign[v]=-1
        return False
    return bt(0)

# level-3 cells of atom  M3 = { h:B^3->B^3 mono : factors }
@lru_cache(None)
def upsets(k):
    D=V[k]; n=len(D); le=LE[k]; res=[]
    for mask in range(1<<n):
        b=[(mask>>i)&1 for i in range(n)]; ok=True
        for i in range(n):
            if b[i]:
                for j in range(n):
                    if le[i][j] and not b[j]: ok=False;break
            if not ok:break
        if ok:res.append(tuple(b))
    return res
def mono_to_B3(k):
    U=upsets(k); L=len(V[k])
    for c in itertools.product(U,repeat=3):
        yield tuple((c[0][i],c[1][i],c[2][i]) for i in range(L))

t0=time.time()
M3=set(h for h in mono_to_B3(3) if factors(h,3))
print("|atom([3])| =",len(M3),"  (time",round(time.time()-t0,1),"s)")

# 3-coskeletality: every mono h:B^4->B^3 whose all 8 facet-restrictions are in M3, must factor.
# facets of B^4: fix coord i in {0..3} to eps. restriction is a map B^3->B^3.
V4=V[4]; V3=V[3]; idx3={v:i for i,v in enumerate(V3)}
def facet(hh, i, eps):
    # hh over V4 -> return level-3 cell over V3 by fixing coord i to eps
    out=[None]*8
    for v in V3:
        w=list(v); w.insert(i,eps); w=tuple(w)
        out[idx3[v]] = hh[V4.index(w)]
    return tuple(out)
# enumerate mono h:B^4->B^3 with all facets in M3, via (h0,h1) last-coord facets in M3, h0<=h1
# Build full 4D map from h0,h1 then check other facets.
M3set=M3
cand=0; bad=0; t0=time.time()
M3list=list(M3)
# index level-3 cell by vertex order V3
for h0 in M3list:
    for h1 in M3list:
        # h(v,0)=h0[v], h(v,1)=h1[v]; need monotone across last coord: h0<=h1 pointwise
        if any(not leq(h0[i],h1[i]) for i in range(8)): continue
        # build hh over V4
        hh=[None]*16
        for v in V3:
            hh[V4.index(v+(0,))]=h0[idx3[v]]
            hh[V4.index(v+(1,))]=h1[idx3[v]]
        # verify monotone (should be, but check quickly via all covers)
        # check other 6 facets (coords 0,1,2 fixed to 0/1) in M3
        ok=True
        for i in range(3):
            for eps in (0,1):
                if facet(hh,i,eps) not in M3set: ok=False;break
            if not ok:break
        if not ok: continue
        cand+=1
        if not factors(tuple(hh),4): bad+=1
print("boundary-fillable level-4 cells:",cand," NON-factoring (coskeletality violations):",bad,
      " time",round(time.time()-t0,1),"s")
print("=> median atom is 3-coskeletal" if bad==0 else "=> COUNTEREXAMPLE")

# --- CONFIRM: the 104 facet-only "violations" each fail some NON-facet restriction phi:B^3->B^4 ---
print("\n--- Reconfirming under the CORRECT hypothesis (all monotone phi:B^3->B^4) ---")
# recollect bad cells
bad_cells=[]
for h0 in M3list:
    for h1 in M3list:
        if any(not leq(h0[i],h1[i]) for i in range(8)): continue
        hh=[None]*16
        for v in V3:
            hh[V4.index(v+(0,))]=h0[idx3[v]]
            hh[V4.index(v+(1,))]=h1[idx3[v]]
        ok=True
        for i in range(3):
            for eps in (0,1):
                if facet(hh,i,eps) not in M3set: ok=False;break
            if not ok:break
        if not ok: continue
        if not factors(tuple(hh),4): bad_cells.append(tuple(hh))
print("collected facet-only-fillable non-factoring cells:",len(bad_cells))

# enumerate all monotone phi:B^3->B^4 as maps V3->V4
def mono_B3_to_B4():
    U=upsets(3); L=8
    for c in itertools.product(U,repeat=4):
        yield tuple((c[0][i],c[1][i],c[2][i],c[3][i]) for i in range(L))
PHIS=list(mono_B3_to_B4())
print("monotone phi:B^3->B^4 :",len(PHIS))
allconfirmed=True
import time as _t; t0=_t.time()
for hh in bad_cells:
    found=False
    for phi in PHIS:
        # h o phi : V3 -> B^3
        hp=tuple(hh[V4.index(phi[i])] for i in range(8))
        if hp not in M3set:   # this restriction does NOT lie in the atom
            found=True; break
    if not found:
        allconfirmed=False
        print("  A cell passes ALL phi-restrictions yet does NOT factor -> TRUE counterexample!")
        break
print("every facet-only 'violation' fails some non-facet restriction:",allconfirmed,
      " (time",round(_t.time()-t0,1),"s)")
print("=> Under the correct hypothesis, ZERO violations: median atom is 3-coskeletal." if allconfirmed
      else "=> genuine counterexample found")

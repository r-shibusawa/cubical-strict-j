"""
dedekind_o38_fixedP.py -- fixed-generator cubical realizability is in P for all
tested monotone maps z (median- AND non-median-fibre), supporting the endgame
paper's cor:boundary.

CORRECTION / CAUTION: an earlier version forced idempotency s(x,x,x,x)=x at ALL
points when searching for a Siggers polymorphism of (<=, fibres(z)).  That is
WRONG: it silently assumes every singleton is a relation of the language (the
full order-convex template L_m), which makes the search report "no Siggers"
(NP-complete) spuriously.  A polymorphism of (<=, fibres) need only be
idempotent where a SINGLETON fibre forces it.  With idempotency restricted to
singleton fibres (full_idem=False), all 500 non-median-fibre z tested have a
4-ary Siggers polymorphism => CSP(<=, fibres(z)) is in P (Bulatov-Zhuk).

Sanity that the corrected test still DETECTS NP-completeness: (<=, ALL
singletons, middle-6) -- a genuine core = the L_3 template -- returns no
Siggers (NP), while (<=, all singletons) alone returns Siggers (P, median
majority).  So the test is not vacuous.

Takeaway: NP-completeness needs the FULL order-convex template (all singletons
= pinning power); a single generator's fibres form only a PARTITION into
order-convex classes, which always admits a Taylor operation.  "Realizability
along any fixed monotone map is in P" is the clean affirmative resolution of
the question the endgame paper left open, now strongly supported.
"""
import itertools as it
from pysat.solvers import Glucose3
from collections import defaultdict
def verts(m): return list(it.product((0,1),repeat=m))
def leq(a,b): return all(x<=y for x,y in zip(a,b))
def med(a,b,c): return tuple((a[i]&b[i])|(b[i]&c[i])|(c[i]&a[i]) for i in range(len(a)))
m=3; V=verts(m); Vi={v:i for i,v in enumerate(V)}; N=8
covers=defaultdict(list)
for a in V:
    for b in V:
        if leq(a,b) and sum(b)-sum(a)==1: covers[Vi[a]].append(Vi[b])
def has_siggers(Fs, full_idem=False):
    """Siggers polymorphism preserving order + each fibre in Fs.
       Idempotency is FORCED ONLY where required: at singleton fibres (and,
       if full_idem, everywhere)."""
    singles={next(iter(F)) for F in Fs if len(F)==1}
    tuples=list(it.product(range(N),repeat=4)); ti={t:k for k,t in enumerate(tuples)}
    def var(k,j): return k*m+j+1
    g=Glucose3()
    for xi in range(N):
        if full_idem or V[xi] in singles:
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
            for bi in covers[t[pos]]:
                t2=list(t);t2[pos]=bi;k2=ti[tuple(t2)]
                for j in range(m): g.add_clause([-var(k,j),var(k2,j)])
    for a in range(N):
        for r in range(N):
            for e in range(N):
                k1=ti[(a,r,e,a)];k2=ti[(r,a,r,e)]
                for j in range(m): g.add_clause([-var(k1,j),var(k2,j)]);g.add_clause([var(k1,j),-var(k2,j)])
    res=g.solve();g.delete();return res
mid6=set(V)-{(0,0,0),(1,1,1)}
# z with image 3-chain: fibres = {000}, mid6, {111}
Fs_mid=[{(0,0,0)}, mid6, {(1,1,1)}]
print("z=(3-chain, middle-6 fibre):")
print("   full-idem (WRONG): Siggers =", has_siggers(Fs_mid, full_idem=True))
print("   correct (idem only at singletons {000},{111}): Siggers =", has_siggers(Fs_mid, full_idem=False))
# atom-triangle z: e.g. z:B^3->B^2 fibres {000}, atom3, coatom-ish?, {111}
atom3={(1,0,0),(0,1,0),(0,0,1)}
# z:B^3->B^2: 000->00, weight1->01, weight2->11? then weight2 all ->11 = coatom-triangle+? weight2={110,101,011}->? and 111->11 too. fibre of 11 = {110,101,011,111}. fibre of 01={100,010,001}=atom3. fibre 00={000}.
Fs_atom=[{(0,0,0)}, atom3, {(1,1,0),(1,0,1),(0,1,1),(1,1,1)}]
print("z=(B^3->B^2, atom-triangle fibre + up(coatoms+top)):")
print("   full-idem (WRONG): Siggers =", has_siggers(Fs_atom, full_idem=True))
print("   correct: Siggers =", has_siggers(Fs_atom, full_idem=False))
# also: middle-6 ALONE as the only unary relation (no singletons) -- is it a core? 
print("middle-6 alone (no singleton fibres), correct idem: Siggers =", has_siggers([mid6], full_idem=False))

print("\n=== SANITY: can the corrected test DETECT NP-completeness? ===")
# L_3 = order + ALL order-convex relations + all singletons (a core) is NP-complete (endgame thm).
# Feed ALL singletons as fibres (forces full idem = a core) + a hard order-convex relation.
allsingles=[{v} for v in V]
mid6=set(V)-{(0,0,0),(1,1,1)}
print("all-singletons + middle-6 (a core, should be NP=no Siggers):",
      has_siggers(allsingles+[mid6], full_idem=False))
print("all-singletons only (=order core, HAS median majority, P):",
      has_siggers(allsingles, full_idem=False))

print("\n=== re-run: are ALL non-median-fibre z P under CORRECT encoding? ===")
import random,time
random.seed(2)
def med_closed(F): return all(med(a,b,c) in F for a in F for b in F for c in F)
def rand_col():
    seeds=random.sample(V,random.choice((1,2,2,3,3,4)))
    return tuple(1 if any(leq(sd,pp) for sd in seeds) else 0 for pp in V)
def fibres_of(z):
    d=defaultdict(set)
    for i,pt in enumerate(V): d[z[i]].add(pt)
    return list(d.values())
tested=0; NP=0; t0=time.time(); seen=set()
while time.time()-t0<120 and tested<500:
    cols=tuple(rand_col() for _ in range(3))
    z=tuple(tuple(cols[c][i] for c in range(3)) for i in range(8))
    if z in seen: continue
    seen.add(z)
    if len(set(z))<2: continue
    Fs=fibres_of(z)
    if all(med_closed(F) for F in Fs): continue
    tested+=1
    if not has_siggers(Fs, full_idem=False):
        NP+=1
        if NP<=3: print("   genuine NP z fibres:",[sorted(F) for F in Fs])
print(f"non-median-fibre z (correct encoding): tested {tested}, genuinely NP-complete {NP} [{time.time()-t0:.0f}s]")

"""Theorem D check: for a finite monoid M,
   Top(M)  ≅  { D ⊆ M : D two-sided ideal, D·D = D }   ordered by REVERSE inclusion,
via J ↦ ⋂J and D ↦ J_D = {right ideals I ⊇ D}.  Also for a finite meet-semilattice L
(as monoid): Same(L) ≅ L^op via a ↦ ↑a.  Verified on all 35 monoids of order 4, the
groups/monoids of order ≤3, and the lattice-monoids of sheaf_sameness_semilattice.py."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
srcm=open("scripts/comparison/sheaf_sameness_monoid.py").read().split("P=lambda")[0]
ns={}; exec(srcm,ns); topologies_monoid,right_ideals,group_cat,monoids,cyclic=[ns[k] for k in ("topologies_monoid","right_ideals","group_cat","monoids","cyclic")]
srcs=open("scripts/comparison/sheaf_sameness_semilattice.py").read().split("def hasse")[0].split("print(")[0]
ns2={}; exec(srcs,ns2); L,lattice_monoid=ns2["L"],ns2["lattice_monoid"]
src4=open("scripts/comparison/sheaf_sameness_monoid4.py").read().split("Ms=monoids4()")[0]
ns4={}; exec(src4,ns4); monoids4=ns4["monoids4"]

def idem_two_sided(el,mul):
    out=[]
    for I in right_ideals(el,mul):
        if all(mul[(m,i)] in I for i in I for m in el) and frozenset(mul[(a,b)] for a in I for b in I)==I: out.append(I)
    return out
def check(name,el,mul,e):
    T=topologies_monoid(el,mul,e); D=idem_two_sided(el,mul)
    mins={J:frozenset.intersection(*J) for J in T}
    bij = len(T)==len(D) and set(mins.values())==set(D)
    rev = all((mins[J1]>=mins[J2])==(J1<=J2) for J1 in T for J2 in T)     # J1 ⊆ J2  iff  ⋂J1 ⊇ ⋂J2
    return len(T),len(D),bij and rev
tot=ok=0
def report(name,el,mul,e):
    global tot,ok
    t,d,good=check(name,el,mul,e); tot+=1; ok+=good
    return f"{name:<22} |Top|={t:>2} |idempotent 2-sided ideals|={d:>2}  bijection&order-reversing: {good}"
print("--- groups and monoids of order <= 3 ---",flush=True)
for nm,(el,mul,e) in [("C2",cyclic(2)),("C3",cyclic(3)),("C4",cyclic(4)),("C6",cyclic(6))]: print(report(nm,el,mul,e))
for n in (2,3):
    for k,mul in enumerate(monoids(n)):
        el=[str(i) for i in range(n)]; print(report(f"monoid{n}#{k}",el,{(str(a),str(b)):str(v) for (a,b),v in mul.items()},'0'))
print("--- all 35 monoids of order 4 ---",flush=True)
bad=[]
for k,mul in enumerate(monoids4()):
    el=[str(i) for i in range(4)]; m={(str(a),str(b)):str(v) for (a,b),v in mul.items()}
    t,d,good=check(f"m4#{k}",el,m,'0'); tot+=1; ok+=good
    if not good: bad.append(k)
print(f"order-4: {35-len(bad)}/35 agree; failures: {bad}")
print("--- lattices as meet-monoids: Top(L) ≅ Down(L)^op and Same(L) ≅ L^op ---",flush=True)
for name,(els,leq) in L.items():
    nm,E,mul,e=lattice_monoid(name,els,leq)
    t,d,good=check(nm,E,mul,e); tot+=1; ok+=good
    # Same(L) ≅ L^op via a ↦ ↑a
    S=set(frozenset(w) for w in all_samenesses(group_cat(E,mul,e))[0])
    up={str(a):frozenset(str(b) for b in els if (a,b) in leq) for a in els}
    same_ok = set(up.values())==S and all((up[str(a)]<=up[str(b)])==((b,a) in leq) for a in els for b in els)
    ndown=sum(1 for r in range(len(els)+1) for A in it.combinations(els,r) if all((y,x) not in leq or y in A for x in A for y in els))
    print(f"{name:<22} |Top|={t:>2} = |Down(L)|={ndown:>2}  idempotent-ideal bijection: {good}   Same(L)≅L^op via a↦↑a: {same_ok}")
print(f"\nTheorem D verified on {ok}/{tot} monoids")

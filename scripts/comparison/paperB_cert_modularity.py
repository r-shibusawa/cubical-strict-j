"""Regenerate docs/paperB/cert_modularity.json in self-contained form:
Same(C2^3) (Fano-plane lattice, modular) ->> Same(A4) (non-modular), with the
source and target posets stored so the certificate can be verified from the
JSON alone (verify_certificates.py)."""
import sys, itertools as it, json; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
src=open("scripts/comparison/level_logic2.py").read().split("# ================= (a) correspondence")[0]
ns={}; exec(src,ns); group_cat,cyclic,height,width=[ns[k] for k in ("group_cat","cyclic","height","width")]
def alt4():
    Ps=[p for p in it.permutations(range(4)) if sum(1 for i in range(4) for j in range(i+1,4) if p[i]>p[j])%2==0]
    nm={p:''.join(map(str,p)) for p in Ps}
    return [nm[p] for p in Ps],{(nm[p],nm[q]):nm[tuple(p[q[i]] for i in range(4))] for p in Ps for q in Ps},nm[(0,1,2,3)]
def product(g1,g2):
    e1,m1,i1=g1; e2,m2,i2=g2; el=[f"{a}.{b}" for a in e1 for b in e2]
    return el,{(f"{a}.{b}",f"{c}.{d}"):f"{m1[(a,c)]}.{m2[(b,d)]}" for a in e1 for b in e2 for c in e1 for d in e2},f"{i1}.{i2}"
C2=cyclic(2)
S=[frozenset(w) for w in all_samenesses(group_cat(*product(C2,product(C2,C2))))[0]]   # Sub(C2^3), 16
T=[frozenset(w) for w in all_samenesses(group_cat(*alt4()))[0]]                       # Sub(A4), 10
sid=lambda u:"|".join(sorted(u)); tid=lambda u:"|".join(sorted(u))
tel=[tid(t) for t in T]; tleq={(tid(a),tid(b)) for a in T for b in T if a<=b}
def pmorph(S,W):
    U=sorted([u for u in S if W<=u],key=len); top=max(U,key=len); f={}
    tbot=[t for t in tel if all((t,x) in tleq for x in tel)][0]; ttop=[t for t in tel if all((x,t) in tleq for x in tel)][0]
    def ok(x,v): return all(((fu,v) in tleq) if u<=x else True for u,fu in f.items()) and all(((v,fu) in tleq) if x<=u else True for u,fu in f.items())
    def rec(i):
        if i==len(U):
            if set(f.values())!=set(tel): return False
            return all(any(x<=x2 and f[x2]==v2 for x2 in U) for x in U for v2 in tel if (f[x],v2) in tleq)
        x=U[i]
        for v in ([tbot] if i==0 else [ttop] if x==top else tel):
            if ok(x,v):
                f[x]=v
                if rec(i+1): return True
                del f[x]
        return False
    return dict(f) if rec(0) else None
W=min(S,key=len); f=pmorph(S,W); assert f, "no p-morphism found"
cert={"target":"Sub(A4)","target_elements":tel,"target_strict":sorted([list(p) for p in tleq if p[0]!=p[1]]),
      "source":"Sub(C2^3)","source_size":len(S),"root":sid(W),
      "source_elements":[sid(u) for u in S],"source_leq":[[sid(a),sid(b)] for a in S for b in S if a<=b],
      "pmorphism":{sid(k):v for k,v in f.items()}}
json.dump([cert],open((('docs/paperB/' if __import__('os').path.isdir('docs/paperB') else '')+'cert_modularity.json'),"w"),indent=1)
print("cert_modularity.json regenerated (self-contained); |source|=",len(S),"|target|=",len(T))

"""
dedekind_o38_medcontract.py -- Rules out cellwise strict contractions of the
median atom A = <(u|v, u&w, v&w)> in cube^3, the open core (b).

The wedge cone works for constant-free atoms (thm:conedescent) but the median
atom is not constant-free, and the question is whether SOME natural cellwise
strict contraction of A (hence of its intrinsic chain stratum Ch(A)) exists --
in particular a MEDIAN-based one, since A is median-fibre.

Findings (K=3):
  * meet-cone / join-cone LEAVE the atom (12024 / 10488 of 32618 slides on Ch),
    so they do not map A->A: no strict contraction.
  * BUT wherever a cone stays in the atom it stays in Ch(A) (leaves_Ch = 0):
    the sole obstruction to contracting Ch(A) is leaving A, i.e. non-constant-
    freeness -- Ch-preservation is automatic.
  * The atom cells are NOT median-closed (median of three atom cells leaves the
    atom: 3720/216000 at level 2, 8964 at level 3), matching that the median is
    not a polymorphism of the atom (only of its fibres).
  * No median-cone med(c, d, E) toward any sorted center E keeps the homotopy
    inside A (0 of all centers tried).

Conclusion: no meet/join/median cellwise strict contraction of the median atom
exists.  Its type-level contractibility (test-contractible, Betti [1,0,0]) must
come from a non-strict (Kan-filling / fibrant-replacement) argument -- the known
hard core of statement (b).  This experiment rules out the cellwise-cone route,
so that effort is not wasted elsewhere.
"""
import itertools as it, time
t0=time.time()
def pts(m): return list(it.product((0,1),repeat=m))
PT={m:pts(m) for m in range(0,5)}
IDX={m:{p:i for i,p in enumerate(PT[m])} for m in PT}
def comp(phi,a,ks,kt): return tuple(phi[IDX[ks][tuple(ai[j] for ai in a)]] for j in range(len(PT[kt])))
def rest(cell,u,j,k): return tuple(comp(c,u,j,k) for c in cell)
def D(k):
    P=PT[k]; out=[]
    for bits in it.product((0,1),repeat=len(P)):
        ok=True
        for i,p in enumerate(P):
            if not ok: break
            for jj,q in enumerate(P):
                if all(a<=b for a,b in zip(p,q)) and bits[i]>bits[jj]: ok=False;break
        if ok: out.append(bits)
    return out
Dk={k:D(k) for k in range(0,4)}
def leq(a,b): return all(x<=y for x,y in zip(a,b))
def comparable(a,b): return leq(a,b) or leq(b,a)
def o_stat(j,m):
    P=PT[m]
    if j<=0: return tuple(1 for _ in P)
    if j>m: return tuple(0 for _ in P)
    return tuple(1 if sum(p)>=j else 0 for p in P)
def sortsub(q): return tuple(o_stat(j,q) for j in range(1,q+1))
def atom_cells(z,m,k): return set(rest(z,u,m,k) for u in it.product(Dk[k],repeat=m))
def chain_stratum(z,m,K):
    cells={k:atom_cells(z,m,k) for k in range(K+1)}
    sortedcells={q:set(c for c in cells[q] if rest(c,sortsub(q),q,q)==c) for q in range(K+1)}
    ch={k:set() for k in range(K+1)}
    for k in range(K+1):
        for q in range(k+1):
            for s in sortedcells[q]:
                if q==0: ch[k].add(rest(s,(),0,k)); continue
                for u in it.product(Dk[k],repeat=q):
                    if all(comparable(a,b) for a,b in it.combinations(u,2)):
                        inst=rest(s,u,q,k)
                        if inst in cells[k]: ch[k].add(inst)
    return cells,ch,sortedcells
def meet(c,d): return tuple(tuple(x&y for x,y in zip(cc,dd)) for cc,dd in zip(c,d))
def join(c,d): return tuple(tuple(x|y for x,y in zip(cc,dd)) for cc,dd in zip(c,d))

u3=tuple(p[0] for p in PT[3]); v3=tuple(p[1] for p in PT[3]); w3=tuple(p[2] for p in PT[3])
def mt(*xs):
    o=xs[0]
    for x in xs[1:]: o=tuple(a&b for a,b in zip(o,x))
    return o
def jn(*xs):
    o=xs[0]
    for x in xs[1:]: o=tuple(a|b for a,b in zip(o,x))
    return o
A=(jn(u3,v3), mt(u3,w3), mt(v3,w3)); m=3; K=3
cells,ch,sortedcells=chain_stratum(A,m,K)
print("Ch(A) sizes:",{k:len(ch[k]) for k in ch},"cells:",{k:len(cells[k]) for k in cells},f"[{time.time()-t0:.0f}s]")

# a "cone toward s" (s a fixed cell, level-indexed): op maps c -> c OP s|_level, with sliding through d.
# preserves Ch iff for ALL up-sets d of B^k, (c OP dcell(d,s)) in Ch whenever it's in cells, where dcell interpolates.
# Simpler faithful test: the STRICT contraction via OP toward s exists iff the "partial cone" homotopy stays in Ch.
# We test the endpoint retraction r_s(c)=c OP s AND the sliding-preservation for the standard meet/join cone.
def dbroadcast(d,ncod): return tuple(tuple(d[i] for _ in range(ncod)) for i in range(len(d)))
def cone_preserves(OP):
    for k in range(1,K+1):
        chk=ch[k]; cellsk=cells[k]
        for c in chk:
            for d in Dk[k]:
                hd=OP(c,dbroadcast(d,len(c[0])))
                if hd in cellsk and hd not in chk:
                    return False
    return True
print("meet-cone preserves Ch(A):",cone_preserves(meet),f"[{time.time()-t0:.0f}s]")
print("join-cone preserves Ch(A):",cone_preserves(join),f"[{time.time()-t0:.0f}s]")

# retraction toward a fixed sorted center s (per level via chain-instantiation): r(c)=meet/join(c, s_k)
# test which sorted centers s give a Ch-preserving retraction that is also idempotent-contracting
def instantiate(s,qsel,k):
    for u in it.product(Dk[k],repeat=qsel):
        if all(comparable(a,b) for a,b in it.combinations(u,2)):
            cand=rest(s,u,qsel,k)
            if cand in cells[k]: return cand
    return None
def retr_preserves(OP,center):  # center: dict level->cell
    for k in range(1,K+1):
        ck=center.get(k)
        if ck is None: return False
        for c in ch[k]:
            hc=OP(c,ck)
            if hc in cells[k] and hc not in ch[k]: return False
    return True
good=[]
for qsel in range(0,K+1):
    for s in sortedcells[qsel]:
        center={}
        ok=True
        for k in range(1,K+1):
            inst=instantiate(s,qsel,k) if qsel>0 else rest(s,(),0,k)
            if inst is None: ok=False;break
            center[k]=inst
        if not ok: continue
        for OP,nm in [(meet,"meet"),(join,"join")]:
            if retr_preserves(OP,center):
                # does it strictly reduce toward a point? check image size shrinks
                good.append((nm,qsel))
from collections import Counter
print("Ch-preserving retractions toward a sorted center (op,arity):",Counter(good),f"[{time.time()-t0:.0f}s]")

print("\n=== STRICT test (no skip): H(c,d) must LAND IN Ch(A) for all c in Ch, all d ===")
def cone_strict(OP):
    leaves_atom=0; leaves_ch=0; tot=0
    for k in range(1,K+1):
        chk=ch[k]; cellsk=cells[k]
        for c in chk:
            for d in Dk[k]:
                tot+=1
                hd=OP(c,dbroadcast(d,len(c[0])))
                if hd not in cellsk: leaves_atom+=1
                elif hd not in chk: leaves_ch+=1
    return leaves_atom,leaves_ch,tot
for OP,nm in [(meet,"meet"),(join,"join")]:
    la,lc,tot=cone_strict(OP)
    print(f"  {nm}-cone: leaves_atom={la}, leaves_Ch(but in atom)={lc}, total={tot}  -> strict-contracts Ch(A): {la==0 and lc==0}")

# also: does meet-cone at least keep A INTO A (contracts the whole atom)?
def cone_on_atom(OP):
    la=0; tot=0
    for k in range(1,K+1):
        cellsk=cells[k]
        for c in cellsk:
            for d in Dk[k]:
                tot+=1
                if OP(c,dbroadcast(d,len(c[0]))) not in cellsk: la+=1
    return la,tot
for OP,nm in [(meet,"meet"),(join,"join")]:
    la,tot=cone_on_atom(OP)
    print(f"  {nm}-cone on whole atom A: leaves_atom={la}/{tot} -> maps A->A: {la==0}")

print("\n=== median-closure of the atom cells, and a median homotopy staying in A ===")
def med3(c,d,e): return join(join(meet(c,d),meet(d,e)),meet(e,c))
# 1) are atom cells median-closed? (coordinatewise median of any 3 atom cells)
import random
random.seed(1)
for k in range(1,K+1):
    L=list(cells[k]); bad=0; tot=0
    trials=L if len(L)<=60 else random.sample(L,60)
    for a in trials:
        for b in trials:
            for c in trials:
                tot+=1
                if med3(a,b,c) not in cells[k]: bad+=1
    print(f"  level {k}: median of atom cells leaves atom {bad}/{tot}")

# 2) median-cone toward interior center E: H(c,d)=med(c, dbroadcast(d), E); does it stay in A (and Ch)?
#    test for E ranging over cells; count centers E s.t. H stays in A for all c in Ch, all d.
def medcone_stays_inA(E_by_level):
    for k in range(1,K+1):
        Ek=E_by_level.get(k)
        if Ek is None: return False
        for c in ch[k]:
            for d in Dk[k]:
                if med3(c,dbroadcast(d,len(c[0])),Ek) not in cells[k]: return False
    return True
# build E per level by chain-instantiating each sorted cell
stay=[]
for qsel in range(0,K+1):
    for s in sortedcells[qsel]:
        E={}; ok=True
        for k in range(1,K+1):
            inst=instantiate(s,qsel,k) if qsel>0 else rest(s,(),0,k)
            if inst is None: ok=False;break
            E[k]=inst
        if ok and medcone_stays_inA(E): stay.append((qsel,s))
print("  median-cone centers keeping H in A (arity of center):",[q for q,_ in stay][:20],"count",len(stay))

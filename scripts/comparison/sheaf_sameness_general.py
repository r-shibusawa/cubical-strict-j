"""Theorem D' (finite categories): Top(S) ≅ { idempotent two-sided ideals of S }^op.
A two-sided ideal = set D of morphisms closed under pre- and post-composition;
idempotent: every d in D is a composite of two morphisms of D (D∘D = D).
Bijection: J ↦ (⋂ J(c))_c ;  D ↦ J_D(c) = { sieves S on c : S ⊇ D(c) }.
Verified from the definition of Grothendieck topology on small categories with
several objects, parallel arrows, and non-trivial endomorphisms."""
import sys, itertools as it; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses
def arrows_into(C,c): return [m for m in C.mors if C.tgt[m]==c]
def sieves(C,c):
    A=arrows_into(C,c); out=[]
    for r in range(len(A)+1):
        for S in it.combinations(A,r):
            S=frozenset(S)
            if all(C.comp[(s,g)] in S for s in S for g in C.mors if C.tgt[g]==C.src[s]): out.append(S)   # closed under precomposition
    return out
def pull(C,S,h):   # h: d -> c ; h*(S) = { g into d : h∘g ∈ S }
    d=C.src[h]; return frozenset(g for g in arrows_into(C,d) if C.comp[(h,g)] in S)
def topologies(C):
    Sv={c:sieves(C,c) for c in C.objs}; maxs={c:frozenset(arrows_into(C,c)) for c in C.objs}
    choices=[[frozenset(J) for r in range(len(Sv[c])) for J in it.combinations(Sv[c],r+1) if maxs[c] in J] for c in C.objs]
    tops=[]
    for combo in it.product(*choices):
        J=dict(zip(C.objs,combo)); ok=True
        for c in C.objs:
            for S in J[c]:
                if not all(pull(C,S,h) in J[C.src[h]] for h in arrows_into(C,c)): ok=False; break
                for R in Sv[c]:
                    if R not in J[c] and all(pull(C,R,h) in J[C.src[h]] for h in S): ok=False; break
                if not ok: break
            if not ok: break
        if ok: tops.append(frozenset((c,J[c]) for c in C.objs))
    return tops
def idem_ideals(C):
    M=sorted(C.mors); out=[]
    for r in range(len(M)+1):
        for D in it.combinations(M,r):
            D=frozenset(D)
            two=all(C.comp[(g,d)] in D for d in D for g in C.mors if C.tgt[d]==C.src[g]) and all(C.comp[(d,g)] in D for d in D for g in C.mors if C.tgt[g]==C.src[d])
            if not two: continue
            if all(any(C.comp[(a,b)]==d for a in D for b in D if C.tgt[b]==C.src[a]) for d in D): out.append(D)
    return out
def check(name,C):
    T=topologies(C); D=idem_ideals(C)
    least={J:frozenset().union(*[frozenset.intersection(*[S for (c,Jc) in J if c==o for S in [frozenset.intersection(*Jc)]]) for o in C.objs]) for J in T}
    # least[J] = union over objects of the least covering sieve on that object = the ideal ⋂J
    bij=len(T)==len(D) and set(least.values())==set(D)
    rev=all((least[J1]>=least[J2])==(all(dict(J1)[c]<=dict(J2)[c] for c in C.objs)) for J1 in T for J2 in T)
    print(f"{name:<34} |Top|={len(T):>3}  |idempotent 2-sided ideals|={len(D):>3}  bijection & order-reversing: {bij and rev}",flush=True)
    return bij and rev
def poset(n,strict):
    ident={i:f"i{i}" for i in range(n)}; leq={(a,a) for a in range(n)}|set(strict); ch=True
    while ch:
        ch=False
        for (a,b) in list(leq):
            for (c,d) in list(leq):
                if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
    homs={}; comp={}; name=lambda a,b: ident[a] if a==b else f"{a}>{b}"
    for (a,b) in leq: homs.setdefault((a,b),[]).append(name(a,b))
    for (a,b) in leq:
        for (c,d) in leq:
            if b==c: comp[(name(c,d),name(a,b))]=name(a,d)
    return Cat(list(range(n)),homs,comp,ident)
cases=[("2-chain",poset(2,[(0,1)])),("3-chain",poset(3,[(0,1),(1,2)])),("V",poset(3,[(0,1),(0,2)])),("Λ",poset(3,[(0,2),(1,2)])),
       ("square 2x2",poset(4,[(0,1),(0,2),(1,3),(2,3)]))]
# parallel pair, span, walking iso
cases.append(("parallel pair x⇉y",Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},{('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},{0:'x',1:'y'})))
cases.append(("walking iso",Cat([0,1],{(0,0):['e0'],(1,1):['e1'],(0,1):['u'],(1,0):['w']},{('e0','e0'):'e0',('e1','e1'):'e1',('u','e0'):'u',('e1','u'):'u',('w','e1'):'w',('e0','w'):'w',('w','u'):'e0',('u','w'):'e1'},{0:'e0',1:'e1'})))
# C2 acting on object 0 with an arrow to object 1 (f∘a = f): a non-trivial endomorphism in a 2-object category
cases.append(("C2 ⟶ pt (f∘a=f)",Cat([0,1],{(0,0):['e','a'],(1,1):['id1'],(0,1):['f']},
   {('e','e'):'e',('e','a'):'a',('a','e'):'a',('a','a'):'e',('f','e'):'f','f'and('f','a'):'f',('id1','f'):'f',('id1','id1'):'id1'},{0:'e',1:'id1'})))
# idempotent endo: object 0 with End={id,p}, p∘p=p, plus arrow f:0->1 with f∘p=f
cases.append(("idempotent p on 0, f∘p=f",Cat([0,1],{(0,0):['e','p'],(1,1):['id1'],(0,1):['f']},
   {('e','e'):'e',('e','p'):'p',('p','e'):'p',('p','p'):'p',('f','e'):'f',('f','p'):'f',('id1','f'):'f',('id1','id1'):'id1'},{0:'e',1:'id1'})))
# monoid sanity: the semilattice 2^2 as one-object category
cases.append(("monoid 2^2 (meet)",Cat([0],{(0,0):['1','0','a','b']},{(x,y):({('1',y):y,(x,'1'):x}.get(('1',y)) if x=='1' else ({('a','a'):'a',('b','b'):'b',('a','b'):'0',('b','a'):'0'}.get((x,y),'0') if y!='1' else x)) for x in ['1','0','a','b'] for y in ['1','0','a','b']},{0:'1'})))
ok=sum(check(n,C) for n,C in cases); print(f"\nTheorem D' verified on {ok}/{len(cases)} categories")

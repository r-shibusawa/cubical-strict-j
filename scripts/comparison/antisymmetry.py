"""Antisymmetry relative to a sameness .
W_cyc(C) = {f : x -> y  with Hom(y, x) nonempty}  (morphisms inside strongly connected classes)
W_obj(C) = {f : x -> y  with x isomorphic to y}
Checks on small categories: both are samenesses; {ids} <= Iso <= W_obj <= W_cyc <= Mor;
acyclic  <=> W_cyc = {ids};  EI (all endomorphisms invertible) <=> W_cyc = Iso."""
import sys, itertools as it
sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, is_sameness, all_samenesses
from more_cats import build_from_comp

def isos(C):
    out=set()
    for f in C.mors:
        for g in C.mors:
            if C.src[g]==C.tgt[f] and C.tgt[g]==C.src[f] and C.comp[(g,f)]==C.ident[C.src[f]] and C.comp[(f,g)]==C.ident[C.src[g]]:
                out.add(f)
    return out
def hom_nonempty(C,a,b): return any(C.src[m]==a and C.tgt[m]==b for m in C.mors)
def W_cyc(C): return {f for f in C.mors if hom_nonempty(C,C.tgt[f],C.src[f])}
def W_obj(C):
    I=isos(C); return {f for f in C.mors if C.src[f]==C.tgt[f] or any(C.src[i]==C.src[f] and C.tgt[i]==C.tgt[f] for i in I)}
def is_EI(C): return all(f in isos(C) for f in C.mors if C.src[f]==C.tgt[f])
def is_acyclic(C):
    ids=set(C.ident.values())
    return all(f in ids for f in W_cyc(C))

# --- test categories (finite) ---
def chain3():
    arrows={'a':(0,1),'b':(1,2),'ba':(0,2)}; return build_from_comp([0,1,2],arrows,{('b','a'):'ba'})
def square():
    arrows={'a':(0,1),'b':(1,3),'c':(0,2),'d':(2,3),'ba':(0,3)}
    return build_from_comp([0,1,2,3],arrows,{('b','a'):'ba',('d','c'):'ba'})
def walking_iso():
    arrows={'u':(0,1),'v':(1,0)}; return build_from_comp([0,1],arrows,{('v','u'):'id0',('u','v'):'id1'}) if False else _walking_iso()
def _walking_iso():
    objs=[0,1]; ident={0:'id0',1:'id1'}
    homs={(0,0):[],(1,1):[],(0,1):['u'],(1,0):['v']}
    comp={('id0','id0'):'id0',('id1','id1'):'id1',('u','id0'):'u',('id1','u'):'u',('v','id1'):'v',('id0','v'):'v',('v','u'):'id0',('u','v'):'id1'}
    return Cat(objs,homs,comp,ident)
def retract_cycle():
    """objects x,y ; u: x->y, v: y->x with v u = id_x, u v = e (idempotent on y): x is a retract of y (EI? e is a non-invertible endomorphism)"""
    objs=['x','y']; ident={'x':'1x','y':'1y'}
    homs={('x','x'):[],('y','y'):['e'],('x','y'):['u'],('y','x'):['v']}
    M=['1x','1y','e','u','v']; src={'1x':'x','1y':'y','e':'y','u':'x','v':'y'}; tgt={'1x':'x','1y':'y','e':'y','u':'y','v':'x'}
    def mul(g,f):  # g after f
        if f in ('1x','1y'): return g
        if g in ('1x','1y'): return f
        t={('v','u'):'1x',('u','v'):'e',('e','e'):'e',('e','u'):'u',('v','e'):'v'}
        return t[(g,f)]
    comp={(g,f):mul(g,f) for g in M for f in M if tgt[f]==src[g]}
    return Cat(objs,homs,comp,ident)
def monoid_cat(name,table,idx0=0):
    n=len(table); objs=['*']; ident={'*':'m0'}
    homs={('*','*'):['m%d'%i for i in range(n) if i!=idx0]}
    comp={('m%d'%a,'m%d'%b):'m%d'%table[a][b] for a in range(n) for b in range(n)}
    return Cat(objs,homs,comp,ident)
C2=[[0,1],[1,0]]; E2=[[0,1],[1,1]]; N3=[[0,1,2],[1,2,2],[2,2,2]]  # group C2; {1,e}; {1,t,t^2=t^3}

tests=[('chain 0<1<2',chain3()),('square poset',square()),('walking iso',_walking_iso()),('retract cycle x<->y, vu=1, uv=e',retract_cycle()),
       ('group C2',monoid_cat('C2',C2)),('monoid {1,e}',monoid_cat('E2',E2)),('monoid {1,t,t^2}',monoid_cat('N3',N3))]
for name,C in tests:
    ids=set(C.ident.values()); I=isos(C); Wc=W_cyc(C); Wo=W_obj(C)
    S,_=all_samenesses(C)
    print("%-32s |Same|=%2d  W_cyc sameness:%s W_obj sameness:%s  chain ids<=Iso<=W_obj<=W_cyc<=Mor: %s  acyclic:%s (W_cyc=ids:%s)  EI:%s (W_cyc=Iso:%s)"%(
        name,len(S),is_sameness(C,Wc),is_sameness(C,Wo),ids<=I<=Wo<=Wc<=C.mors,is_acyclic(C),Wc==ids,is_EI(C),Wc==I))

# --- W_endo (identities + all endomorphisms), Aut (identities + automorphisms), W_ret (mutual retracts)
def W_endo(C): return set(C.ident.values())|{f for f in C.mors if C.src[f]==C.tgt[f]}
def Aut(C): return {f for f in isos(C) if C.src[f]==C.tgt[f]}|set(C.ident.values())
def retract_of(C,x,y):
    """x is a retract of y: s: x->y, r: y->x with r s = id_x"""
    for s in C.mors:
        if C.src[s]==x and C.tgt[s]==y:
            for r in C.mors:
                if C.src[r]==y and C.tgt[r]==x and C.comp[(r,s)]==C.ident[x]: return True
    return False
def W_ret(C): return {f for f in C.mors if retract_of(C,C.src[f],C.tgt[f]) and retract_of(C,C.tgt[f],C.src[f])}
print("\n--- W_endo, Aut, W_ret ---")
for name,C in tests:
    I=isos(C); We=W_endo(C); A=Aut(C); Wr=W_ret(C); Wo=W_obj(C); Wc=W_cyc(C)
    S,_=all_samenesses(C)
    print("%-32s W_endo sameness:%s Aut sameness:%s W_ret sameness:%s | Aut=Iso&W_endo:%s  W_obj=Iso v W_endo(in Same):%s  W_obj<=W_ret<=W_cyc:%s  Iso<=W_endo:%s"%(
        name,is_sameness(C,We),is_sameness(C,A),is_sameness(C,Wr),A==I&We,
        Wo==min((W for W in S if I<=W and We<=W),key=len) if any(I<=W and We<=W for W in S) else None,
        Wo<=Wr<=Wc, I<=We))

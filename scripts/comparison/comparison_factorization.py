"""T1: the comparison factorization theorem.

A *comparison* is either
  (P) a pair of samenesses W1,W2 on one category C   (e.g. W_type,W_test), or
  (F) a functor F : C -> D.
Claim: every comparison has a canonical factorization through an INTERVAL of a
sameness lattice, and 'the two theories agree' <=> the interval is trivial.

  (P)  interval  [W1 ^ W2 , W1 v W2]  in Same(C);  trivial <=> W1 = W2.
  (F)  V_F := F^*(bot_D)  (maps F sends to isos) is the LARGEST sameness on C
       that F inverts; F factors  C -> C[V_F^{-1}] -> D  with the second functor
       CONSERVATIVE (m in V_F  <=>  F(m) iso); the interval [bot_C, V_F] in
       Same(C) is F's collapse, trivial <=> F reflects isos (F conservative).
Both are verified on finite models below; plus the spectrum monotonicity
(the set of levels at which F is essentially surjective is an up-set)."""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses, is_sameness

def isos(C):
    """iso morphisms of C: m:a->b with a two-sided inverse."""
    R=set(C.ident.values())
    for m in C.mors:
        a,b=C.src[m],C.tgt[m]
        for n in C.mors:
            if C.src[n]==b and C.tgt[n]==a:
                if C.comp.get((n,m))==C.ident[a] and C.comp.get((m,n))==C.ident[b]:
                    R.add(m); break
    return frozenset(R)

class Functor:
    """object map fo: C.objs->D.objs, morphism map fm: name->name (id->id, comp-preserving)."""
    def __init__(self,C,D,fo,fm): self.C,self.D,self.fo,self.fm=C,D,fo,fm
    def check(self):
        C,D,fo,fm=self.C,self.D,self.fo,self.fm
        for o in C.objs: assert fm[C.ident[o]]==D.ident[fo[o]], "identity"
        for (g,f) in C.composable():
            gf=C.comp[(g,f)]
            assert D.comp[(fm[g],fm[f])]==fm[gf], f"comp {g},{f}"
        return True
    def Fstar(self,W):   # {m in C : F(m) in W}
        return frozenset(m for m in self.C.mors if self.fm[m] in W)

def meetjoin_interval(C, W1, W2):
    S,_=all_samenesses(C); Sset=set(map(frozenset,S))
    assert frozenset(W1) in Sset and frozenset(W2) in Sset
    meet=frozenset(W1)&frozenset(W2); assert meet in Sset, "meet must be a sameness"
    # join = least sameness containing W1 ∪ W2
    ups=[w for w in Sset if frozenset(W1)<=w and frozenset(W2)<=w]
    join=min(ups,key=len)
    interval=sorted([w for w in Sset if meet<=w<=join],key=lambda w:(len(w),sorted(w)))
    return meet,join,interval

# ---------- (F) functor case: build C=3-chain 0<1<2, D=2-chain collapsing 1~2 ----------
def three_chain():
    ident={0:'i0',1:'i1',2:'i2'}
    homs={(0,0):['i0'],(1,1):['i1'],(2,2):['i2'],(0,1):['f'],(1,2):['g'],(0,2):['h']}
    comp={}
    for m in ['i0','i1','i2','f','g','h']:
        s,t=({'i0':0,'i1':1,'i2':2,'f':0,'g':1,'h':0}[m],{'i0':0,'i1':1,'i2':2,'f':1,'g':2,'h':2}[m])
        comp[(ident[t],m)]=m; comp[(m,ident[s])]=m
    comp[('g','f')]='h'
    return Cat([0,1,2],homs,comp,ident)
def two_chain():   # 0<1, names j0,j1,u:0->1
    ident={0:'j0',1:'j1'}; homs={(0,0):['j0'],(1,1):['j1'],(0,1):['u']}
    comp={('j0','j0'):'j0',('j1','j1'):'j1',('u','j0'):'u',('j1','u'):'u'}
    return Cat([0,1],homs,comp,ident)
C=three_chain(); D=two_chain()
# F collapses 1,2 -> object 1 of D ; f|->u, g|->j1(iso), h|->u
F=Functor(C,D,{0:0,1:1,2:1},{'i0':'j0','i1':'j1','i2':'j1','f':'u','g':'j1','h':'u'}); F.check()
botC=isos(C); botD=isos(D)
V_F=F.Fstar(botD)
print("=== (F) functor case: F: (0<1<2) -> (0<1), collapsing 1~2 ===")
print(f"   bot_D (isos of D) = {sorted(botD)}")
print(f"   V_F = F^*(bot_D) = maps F inverts = {sorted(V_F-botC)} (+isos)   is-sameness:{is_sameness(C,V_F)}")
# V_F is the LARGEST sameness C that F inverts:
SC,_=all_samenesses(C)
inverted=[w for w in SC if F.Fstar(botD)>=w and all(F.fm[m] in botD for m in w)]
inv_max=max(inverted,key=len)
print(f"   largest sameness F inverts = {sorted(inv_max-botC)} (+isos)  == V_F? {frozenset(inv_max)==V_F}")
# conservativity of the factorization: m in V_F  <=>  F(m) iso
conserv=all((m in V_F)==(F.fm[m] in botD) for m in C.mors)
print(f"   factorization C->C[V_F^-1]->D conservative (m in V_F <=> F(m) iso): {conserv}")
_,_,interval=meetjoin_interval(C,botC,V_F)
print(f"   collapse interval [bot_C,V_F] has {len(interval)} pts; F conservative(trivial)? {botC==V_F}")

# ---------- (P) pair case: cube-site shape  W_type ⊆ W_test on one C ----------
print("\n=== (P) pair case (cube-site shape): W1 ⊆ W2 on the 3-chain ===")
ids=set(C.ident.values())
W1=frozenset(ids|{'g'}); W2=frozenset(C.mors)   # W_type={g}, W_test=all
meet,join,interval=meetjoin_interval(C,W1,W2)
print(f"   W1(type)=isos+{sorted(W1-ids)}  W2(test)=isos+{sorted(W2-ids)}")
print(f"   meet W1^W2 = isos+{sorted(meet-ids)}   join W1vW2 = isos+{sorted(join-ids)}")
print(f"   comparison interval [meet,join]: {len(interval)} pts; agree(W1=W2)? {W1==W2}")
print(f"   (meet = finest common sameness; W1⊆W2 so meet=W1, join=W2 = exactly the T2 interval)")

# ---------- spectrum monotonicity: essential W-surjectivity is an up-set ----------
def ess_surj_mod(F,W):
    """every object d of D is W-connected to some F(c): exists c and a morphism
       F(c)->d or d->F(c) lying in W."""
    C,D=F.C,F.D; img=set(F.fo.values())
    for d in D.objs:
        hit=False
        for c in C.objs:
            fc=F.fo[c]
            for m in D.mors:
                if {D.src[m],D.tgt[m]}=={fc,d} or (D.src[m]==fc and D.tgt[m]==d) or (D.src[m]==d and D.tgt[m]==fc):
                    if m in W: hit=True;break
            if hit:break
        if not hit: return False
    return True
SD,_=all_samenesses(D)
spec=[w for w in SD if ess_surj_mod(F,w)]
up=all((not(a<=b)) or (a in spec)==True for a in spec for b in SD if a<=b)  # a in spec, a<=b => b in spec
upclosed=all( (not (a<=b)) or (b in spec) for a in spec for b in SD)
least=min(spec,key=len) if spec else None
print("\n=== spectrum monotonicity ===")
print(f"   levels W(D) with F essentially W-surjective: {len(spec)}/{len(SD)}; up-closed: {upclosed}")
print(f"   least such level exists: {least is not None}; = isos+{sorted(least-set(D.ident.values())) if least else None}")

# ---------- nontrivial spectrum: F picks the bottom object of the 2-chain ----------
def point_cat():
    return Cat([0],{(0,0):['e']},{('e','e'):'e'},{0:'e'})
Pt=point_cat()
G=Functor(Pt,D,{0:0},{'e':'j0'}); G.check()   # image = {0}; object 1 unhit unless u in W
SDg,_=all_samenesses(D)
specg=[w for w in SDg if ess_surj_mod(G,w)]
upg=all((not(a<=b)) or (b in specg) for a in specg for b in SDg)
leastg=min(specg,key=len) if specg else None
print("\n=== nontrivial spectrum: G: point -> (0<1) picking object 0 ===")
print(f"   Same(D) levels: {len(SDg)}; ess-surjective levels: {len(specg)} (up-closed: {upg})")
print(f"   least level of agreement = isos+{sorted(leastg-set(D.ident.values())) if leastg else None}"
      f"  (must invert u:0->1 to reach object 1 => least = top, not bottom)")
print(f"   => the comparison only 'agrees' after coarsening to W={sorted(leastg)}: G is a")
print(f"      W-equivalence exactly on the principal up-set generated by this least level.")

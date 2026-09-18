"""Development for ACS: Same(-) is a functor.  For F:C->D, G:D->E finite:
  (GF)^*  = F^* o G^*        (contravariant, immediate from preimage)
  (GF)_!  = G_! o F_!        (covariant; left adjoints compose)
verified exhaustively on a composable chain of finite functors.  Together:
  Same : Cat -> (complete lattices, Galois connections),  C |-> Same(C),
  F |-> (F_! -| F^*),  a genuine categorical construction, not one observation.
Also records the faithfulness counterexample fixing Thm 4.3."""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses, is_sameness
from comparison_factorization import Functor

def Fstar(F,W): return frozenset(m for m in F.C.mors if F.fm[m] in W)
def Fshriek(F,V):
    SD,_=all_samenesses(F.D); SD=list(map(frozenset,SD))
    V=frozenset(V)
    ups=[W for W in SD if V<=Fstar(F,W)]
    # least element of ups (meet of all; exists since meet-closed)
    m=ups[0]
    for W in ups[1:]: m=m&W
    m=frozenset(m)
    assert m in set(SD)
    return m

# chain of categories C=(0<1<2) -> D=(0<1) -> E=(*)
def three_chain():
    ident={0:'i0',1:'i1',2:'i2'}
    homs={(0,0):['i0'],(1,1):['i1'],(2,2):['i2'],(0,1):['f'],(1,2):['g'],(0,2):['h']}
    comp={}
    for m in ['i0','i1','i2','f','g','h']:
        s,t=({'i0':0,'i1':1,'i2':2,'f':0,'g':1,'h':0}[m],{'i0':0,'i1':1,'i2':2,'f':1,'g':2,'h':2}[m])
        comp[(ident[t],m)]=m; comp[(m,ident[s])]=m
    comp[('g','f')]='h'
    return Cat([0,1,2],homs,comp,ident)
def two_chain():
    ident={0:'j0',1:'j1'}; homs={(0,0):['j0'],(1,1):['j1'],(0,1):['u']}
    comp={('j0','j0'):'j0',('j1','j1'):'j1',('u','j0'):'u',('j1','u'):'u'}
    return Cat([0,1],homs,comp,ident)
def point():
    return Cat([0],{(0,0):['e']},{('e','e'):'e'},{0:'e'})
C,D,E=three_chain(),two_chain(),point()
F=Functor(C,D,{0:0,1:1,2:1},{'i0':'j0','i1':'j1','i2':'j1','f':'u','g':'j1','h':'u'}); F.check()
G=Functor(D,E,{0:0,1:0},{'j0':'e','j1':'e','u':'e'}); G.check()
GF=Functor(C,E,{o:G.fo[F.fo[o]] for o in C.objs},{m:G.fm[F.fm[m]] for m in C.mors}); GF.check()

SE,_=all_samenesses(E); SE=list(map(frozenset,SE))
SC,_=all_samenesses(C); SC=list(map(frozenset,SC))
# (GF)^* = F^* o G^*
ok_star=all(Fstar(GF,W)==Fstar(F,Fstar(G,W)) for W in SE)
# (GF)_! = G_! o F_!
ok_shriek=all(Fshriek(GF,V)==Fshriek(G,Fshriek(F,V)) for V in SC)
# identity functor gives identity maps
idC=Functor(C,C,{o:o for o in C.objs},{m:m for m in C.mors}); idC.check()
ok_id=all(Fstar(idC,W)==frozenset(W) for W in SC) and all(Fshriek(idC,V)==frozenset(V) for V in SC)

print(f"(GF)^* = F^* o G^*  (contravariant functoriality): {ok_star}")
print(f"(GF)_! = G_! o F_!  (covariant functoriality)   : {ok_shriek}")
print(f"id^*=id and id_!=id                              : {ok_id}")
print(f"=> Same : Cat -> Galois connections of complete lattices is a functor: "
      f"{ok_star and ok_shriek and ok_id}")

# ---- faithfulness counterexample fixing Thm 4.3 ----
# C = free cat on two parallel arrows X =f,g=> Y ; D = walking arrow X -u-> Y.
Cpar=Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['f','g']},
         {('x','x'):'x',('y','y'):'y',('f','x'):'f',('g','x'):'g',('y','f'):'f',('y','g'):'g'},
         {0:'x',1:'y'})
Darr=Cat([0,1],{(0,0):['x'],(1,1):['y'],(0,1):['u']},
         {('x','x'):'x',('y','y'):'y',('u','x'):'u',('y','u'):'u'},{0:'x',1:'y'})
Fpar=Functor(Cpar,Darr,{0:0,1:1},{'x':'x','y':'y','f':'u','g':'u'}); Fpar.check()
# full? surjective on each hom. ess-surj? bijective on objects. conservative? only id isos.
def isos(C):
    R=set(C.ident.values())
    for m in C.mors:
        a,b=C.src[m],C.tgt[m]
        for n in C.mors:
            if C.src[n]==b and C.tgt[n]==a and C.comp.get((n,m))==C.ident[a] and C.comp.get((m,n))==C.ident[b]:
                R.add(m)
    return R
full=all(set(Fpar.fm[m] for m in Cpar.homs.get((a,b),[]))>=set(Darr.homs.get((Fpar.fo[a],Fpar.fo[b]),[]))
         for a in Cpar.objs for b in Cpar.objs)
faithful=all(not(Fpar.fm[m1]==Fpar.fm[m2] and m1!=m2 and Cpar.src[m1]==Cpar.src[m2] and Cpar.tgt[m1]==Cpar.tgt[m2])
             for m1 in Cpar.mors for m2 in Cpar.mors)
cons=(isos(Cpar)==set(Cpar.ident.values()) and isos(Darr)==set(Darr.ident.values()))
print(f"\nThm 4.3 fix -- parallel-pair functor X=f,g=>Y  ->  X-u->Y :")
print(f"   full={full}, essentially surjective=True(bijective on objects), conservative={cons}, faithful={faithful}")
print(f"   => full+ess-surj+conservative but NOT faithful, hence NOT an equivalence:")
print(f"      'W-equivalence' MUST include W-faithfulness (conservativity does not supply it).")

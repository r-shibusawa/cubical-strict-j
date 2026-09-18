"""Verify the reviewer's counterexample: the canonical factorization
C -> C[V_F^{-1}] -> D need NOT be conservative (fixes false Thm 6.2), and the
groupoid generalisation Same(groupoid)=wide subgroupoids (strengthens Thm 3.1)."""
import sys; sys.path.insert(0,'scripts/comparison')
from sameness_lattice import Cat, all_samenesses, is_sameness
from comparison_factorization import Functor, isos

# ---------- D: A a retract of B (r i = id_A, i r = e != id_B, e idempotent) ----------
# morphisms: idA,idB, i:A->B, r:B->A, e=ir:B->B
Dhoms={(0,0):['idA'],(1,1):['idB','e'],(0,1):['i'],(1,0):['r']}
Dcomp={}
# fill composition: comp[(g,f)] = g after f
def setc(g,f,val): Dcomp[(g,f)]=val
# units
for m,s,t in [('idA',0,0),('idB',1,1),('e',1,1),('i',0,1),('r',1,0)]:
    setc(m, {0:'idA',1:'idB'}[s], m); setc({0:'idA',1:'idB'}[t], m, m)
setc('r','i','idA')      # r i = idA
setc('i','r','e')        # i r = e
setc('e','i','i')        # e i = (ir)i = i(ri)=i
setc('r','e','r')        # r e = r(ir)=(ri)r=r
setc('e','e','e')        # e e = ir ir = i(ri)r = ir = e
setc('e','idB','e'); setc('idB','e','e')
D=Cat([0,1],Dhoms,Dcomp,{0:'idA',1:'idB'})
# validate associativity + units on all composable triples
def valid(C):
    for f in C.mors:
        for g in C.mors:
            if C.tgt[f]!=C.src[g]: continue
            assert (g,f) in C.comp, f"missing {g},{f}"
            for h in C.mors:
                if C.tgt[g]!=C.src[h]: continue
                assert C.comp[(h,C.comp[(g,f)])]==C.comp[(C.comp[(h,g)],f)], f"assoc {h},{g},{f}"
    return True
print("D valid category:", valid(D), "| isos(D)=", sorted(isos(D)), "(e is not iso)")

# ---------- C: free-ish on f:X->Y, g:Z->X, v:Z->Y  (objects X=0,Y=1,Z=2) ----------
Choms={(0,0):['ix'],(1,1):['iy'],(2,2):['iz'],(0,1):['f'],(2,0):['g'],(2,1):['fg','v']}
Ccomp={}
def sc(g,f,val): Ccomp[(g,f)]=val
for m,s,t in [('ix',0,0),('iy',1,1),('iz',2,2),('f',0,1),('g',2,0),('fg',2,1),('v',2,1)]:
    sc(m,{0:'ix',1:'iy',2:'iz'}[s],m); sc({0:'ix',1:'iy',2:'iz'}[t],m,m)
sc('f','g','fg')   # f after g = fg
C=Cat([0,1,2],Choms,Ccomp,{0:'ix',1:'iy',2:'iz'})
print("C valid category:", valid(C))

# ---------- F: C -> D ----------
F=Functor(C,D,{0:0,1:1,2:1},{'ix':'idA','iy':'idB','iz':'idB','f':'i','g':'r','v':'idB','fg':'e'})
F.check()
VF=frozenset(m for m in C.mors if F.fm[m] in isos(D))
print("V_F = {m: F(m) iso} =", sorted(VF), "| is a sameness of C:", is_sameness(C,VF))
print("   f,g in V_F?", 'f' in VF, 'g' in VF, "| v in V_F?", 'v' in VF)
# the localization morphism alpha = g . v^{-1} . f : X->X has F(alpha)=r.idB.i = r i = idA (iso)
comp_img = D.comp[('r', D.comp[('idB','i')])]
print("F(alpha) = r . idB^{-1} . i =", comp_img, "(=idA, an isomorphism)")

# ---------- witness that alpha is NOT iso in C[V_F^{-1}]: a functor H:C->FinSet inverting v ----------
# H(X)=H(Y)=H(Z)={0,1}; H(v)=identity (bijection => descends to localization);
# H(f)=const0 ; H(g)=const0 ; then H(alpha)=H(g) o H(v)^{-1} o H(f) is constant, not bijective.
HX=HY=HZ=[0,1]
Hf=lambda x:0        # X->Y constant
Hg=lambda x:0        # Z->X constant
Hv=lambda x:x        # Z->Y identity bijection
Hfg=lambda x:Hf(Hg(x))   # must equal H(f o g); functoriality on the one relation f.g=fg
# check H well-defined on the relation: H(fg) := Hf∘Hg
Halpha=lambda x: Hg(Hv_inv(Hf(x))) if False else Hg(Hf(x))  # v^{-1}=id so H(alpha)=Hg∘Hf
vals=sorted(set(Halpha(x) for x in HX))
print("witness functor H inverts v (H(v) bijection); H(alpha) image =", vals,
      "=> H(alpha) NOT bijective => alpha NOT iso in C[V_F^{-1}].")
print("CONCLUSION: F-bar sends a non-iso (alpha) to an iso => F-bar is NOT conservative. Thm 6.2 false.\n")

# ---------- groupoid theorem: Same(G) = wide subgroupoids ----------
# walking-iso groupoid: objects 0,1 ; iso u:0->1, u':1->0, uu'=id1, u'u=id0
Ghoms={(0,0):['e0'],(1,1):['e1'],(0,1):['u'],(1,0):['w']}
Gcomp={}
def gc(g,f,val): Gcomp[(g,f)]=val
for m,s,t in [('e0',0,0),('e1',1,1),('u',0,1),('w',1,0)]:
    gc(m,{0:'e0',1:'e1'}[s],m); gc({0:'e0',1:'e1'}[t],m,m)
gc('w','u','e0')  # w u = e0
gc('u','w','e1')  # u w = e1
G=Cat([0,1],Ghoms,Gcomp,{0:'e0',1:'e1'})
SG,_=all_samenesses(G)
print("Same(walking-iso groupoid): #samenesses =", len(SG),
      "=> {e0,e1}(discrete wide) and whole G ; both wide subgroupoids:", len(SG)==2)
# every sameness of a groupoid is inverse-closed (2-of-3) + wide (all ids) + comp-closed = wide subgroupoid
for W in SG:
    for m in W:
        # inverse present?
        inv=[n for n in G.mors if G.comp.get((n,m))==G.ident[G.src[m]] and G.comp.get((m,n))==G.ident[G.tgt[m]]]
        assert any(n in W for n in inv), "inverse must be in W"
    assert set(G.ident.values())<=W  # wide
print("   verified: every sameness of the groupoid is a wide subgroupoid (inverse-closed + all objects).")

# ---------- the counterexample fails calculus of (left) fractions for V_F ----------
# Left calculus of fractions (Gabriel-Zisman) requires: for s:A->B in Sigma and
# any a:A->C in C, there exist t:C->D in Sigma and h:B->D with h s = t a.
# Take s=v:Z->Y in Sigma, a=g:Z->X.  Need t:X->D in Sigma, h:Y->D with h v = t g.
Sigma={'iz','ix','iy','v'}   # V_F on C
def hom(C,a,b): return C.homs.get((a,b),[])
def left_fractions_ok(C,Sigma):
    for s in Sigma:
        if s in C.ident.values(): continue
        A,B=C.src[s],C.tgt[s]
        for a in C.mors:
            if C.src[a]!=A: continue
            Cc=C.tgt[a]
            # need t:Cc->D in Sigma, h:B->D with C.comp[(h,s)]==C.comp[(t,a)]
            found=False
            for t in Sigma:
                if C.src[t]!=Cc: continue
                Dd=C.tgt[t]
                for h in C.mors:
                    if C.src[h]==B and C.tgt[h]==Dd:
                        if C.comp.get((h,s))==C.comp.get((t,a)): found=True
            if not found:
                return False,(s,a)
    return True,None
ok,wit=left_fractions_ok(C,Sigma)
print(f"\nV_F=<v> admits left calculus of fractions in C: {ok}"
      + ("" if ok else f"  (fails: no completion for s=v, a=g -- no morphism Y->X exists)"))
print("=> the counterexample violates the calculus-of-fractions hypothesis, consistent")
print("   with THEOREM: if V_F admits a calculus of fractions then F-bar IS conservative.")

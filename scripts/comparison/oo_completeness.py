"""Machine check of the (corrected) completeness theorem for the identity/
encapsulation fragment of OO(C), as reformulated after review.

LANGUAGE (fixed finite lattice L of levels, constants X0, observable symbols Phi):
  atoms   a ≡_W b      ('eq',W,a,b)
          φ obs_W      ('obs',φ,W)
          φ(a) ≐ φ(b)  ('val',φ,a,b)      -- 'φ takes equal values at a,b'
RULES (closure):  ≡_W equivalence + coarsen;  ≐_φ equivalence;
  (encapsulate) φ obs_W, a≡_W b ⟹ φ(a)≐φ(b);   (restrict) φ obs_W', W≤W' ⟹ φ obs_W.
MODELS: X ⊇ X0; monotone family E_W of equivalences on X; functions φ^M : X→V_φ.
  ⊨ a≡_W b iff (a,b)∈E_W;  ⊨ φ(a)≐φ(b) iff φ^M(a)=φ^M(b);
  ⊨ φ obs_W iff φ^M constant on every E_W-class.
COUNTERMODELS (the proof):
  M0 (for eq/val goals): X=X0, E_W = derivable ≡_W, V_φ = X/≐_φ, φ^M(a)=[a].
  M1 (for goal φ obs_W0): M0 + fresh x,y with (x,y)∈E_W iff W ≥ W0,
      φ^M(x)≠φ^M(y) fresh, ψ^M(x)=ψ^M(y) for ψ≠φ.
We verify, on exhaustive-ish random instances: M0/M1 satisfy Γ and refute the
non-derivable goal; and every derivable atom holds in M0 and M1 (soundness spot check)."""
import itertools as it, random
random.seed(7)

def lattice(name):
    if name=="3-chain": el=['0','1','2']; leq={(a,b) for a in el for b in el if el.index(a)<=el.index(b)}
    elif name=="2^2":
        el=['b','l','r','t']; leq={(x,x) for x in el}|{('b','l'),('b','r'),('b','t'),('l','t'),('r','t')}
    elif name=="M3":
        el=['0','a','b','c','1']; leq={(x,x) for x in el}|{('0',m) for m in 'abc'}|{(m,'1') for m in 'abc'}|{('0','1')}
    return el,leq

def closure(G,L,X0,Phi):
    el,leq=L; D=set(G); ch=True
    while ch:
        ch=False; new=set()
        for W in el:
            for a in X0: new.add(('eq',W,a,a))
        for φ in Phi:
            for a in X0: new.add(('val',φ,a,a))
        for t in list(D):
            if t[0]=='eq':
                _,W,a,b=t; new.add(('eq',W,b,a))
                for u in list(D):
                    if u[0]=='eq' and u[1]==W and u[2]==b: new.add(('eq',W,a,u[3]))
                for W2 in el:
                    if (W,W2) in leq: new.add(('eq',W2,a,b))
                for u in list(D):
                    if u[0]=='obs' and u[2]==W: new.add(('val',u[1],a,b))
            elif t[0]=='val':
                _,φ,a,b=t; new.add(('val',φ,b,a))
                for u in list(D):
                    if u[0]=='val' and u[1]==φ and u[2]==b: new.add(('val',φ,a,u[3]))
            elif t[0]=='obs':
                _,φ,W=t
                for W2 in el:
                    if (W2,W) in leq: new.add(('obs',φ,W2))
                for u in list(D):
                    if u[0]=='eq' and u[1]==W: new.add(('val',φ,u[2],u[3]))
        if not new<=D: D|=new; ch=True
    return D

def holds(M,atom):
    X,E,F=M
    if atom[0]=='eq': return (atom[2],atom[3]) in E[atom[1]]
    if atom[0]=='val': return F[atom[1]][atom[2]]==F[atom[1]][atom[3]]
    φ,W=atom[1],atom[2]
    return all(F[φ][a]==F[φ][b] for (a,b) in E[W])
def is_model(M,L):     # E_W equivalences, monotone
    X,E,F=M; el,leq=L
    for W in el:
        R=E[W]
        if not all((x,x) in R for x in X): return False
        if not all((b,a) in R for (a,b) in R): return False
        if not all((a,c) in R for (a,b) in R for (b2,c) in R if b==b2): return False
    return all(E[W]<=E[W2] for W in el for W2 in el if (W,W2) in leq)

def M0(D,L,X0,Phi):
    el,_=L; E={W:{(a,b) for a in X0 for b in X0 if ('eq',W,a,b) in D} for W in el}
    F={}
    for φ in Phi:
        cls={}
        for a in X0: cls[a]=frozenset(b for b in X0 if ('val',φ,a,b) in D)
        F[φ]=cls
    return (list(X0),E,F)
def M1(D,L,X0,Phi,φ0,W0):
    X,E,F=M0(D,L,X0,Phi); el,leq=L
    X=X+['x','y']; E={W:set(E[W])|{('x','x'),('y','y')}|({('x','y'),('y','x')} if (W0,W) in leq else set()) for W in el}
    F={ψ:dict(F[ψ]) for ψ in Phi}
    for ψ in Phi:
        if ψ==φ0: F[ψ]['x']='*1'; F[ψ]['y']='*2'
        else: F[ψ]['x']=F[ψ]['y']='*'
    return (X,E,F)

X0=['a','b','c']; Phi=['φ','ψ']
tot=0; bad=0
for lname in ["3-chain","2^2","M3"]:
    L=lattice(lname); el,leq=L
    atoms=[('eq',W,a,b) for W in el for a in X0 for b in X0 if a!=b]+[('obs',φ,W) for φ in Phi for W in el]+[('val',φ,a,b) for φ in Phi for a in X0 for b in X0 if a!=b]
    Gs=[set()]+[set(random.sample(atoms,k)) for k in range(1,7) for _ in range(40)]
    for G in Gs:
        D=closure(G,L,X0,Phi)
        for goal in atoms:
            if goal in D: continue
            tot+=1
            M=M1(D,L,X0,Phi,goal[1],goal[2]) if goal[0]=='obs' else M0(D,L,X0,Phi)
            ok=is_model(M,L) and all(holds(M,g) for g in G) and not holds(M,goal) and all(holds(M,d) for d in D if d[0]!='obs' or True)
            if not ok: bad+=1; print("FAIL",lname,sorted(G),goal)
    print(f"{lname:<8} instances={len(Gs)}  non-derivable goals checked so far={tot}  failures={bad}")
print(f"\nTOTAL non-derivable goals: {tot}; countermodel failures: {bad}")
print("=> completeness construction (M0 for ≡/≐ goals, M1 with two fresh individuals for obs goals) verified" if bad==0 else "=> PROOF BROKEN")

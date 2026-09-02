"""O27: fold-locus decomposition of the five-chain atom T.

T = <z>, z = (u^v^w, u^v, u^(v|w)).  Facts to verify:
  (1) m = (u^(v|w), v, w) is idempotent with z o m = z, so
      M := <m> = image of an idempotent = retract of cube^3,
      and M(k) = {(p,b,c) : p <= b|c} with
      q : M ->> T, (p,b,c) |-> (p, p^b, p^b^c)   [decreasing]
      presenting T as a quotient of the REGULAR M.
  (2) The fold locus S = <cells of M with a distinct q-partner>
      -- if the generator e = m is NOT in S, then
      T = q(S) u_S M is a genuine pushout along a mono
      (fold-locus pushout), reducing T's regularity to S, q(S).
Checks: Stab(z), idempotents, partner analysis of e at levels
0..4, folded generators, structure of folded cells.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def meet(a,b): return tuple(x & y for x,y in zip(a,b))
def join(a,b): return tuple(x | y for x,y in zip(a,b))
def leq(a,b): return all(x <= y for x,y in zip(a,b))

def var(k, i):
    pts,_ = F(k)
    return tuple(p[i] for p in pts)

def zmap(t):  # z o (t1,t2,t3): components of z applied to a triple
    t1,t2,t3 = t
    return (meet(meet(t1,t2),t3), meet(t1,t2), meet(t1, join(t2,t3)))

def emap(t):  # m o (t1,t2,t3) = (t1 ^ (t2|t3), t2, t3)
    t1,t2,t3 = t
    return (meet(t1, join(t2,t3)), t2, t3)

def comp_cell(mu, rho, ks, kt):
    """cell mu at level ks (triple over F(ks)) composed with
    rho: [kt]->[ks] i.e. ks-tuple over F(kt) -> triple over F(kt)"""
    return tuple(compose(c, rho, ks, kt) for c in mu)

k = 3
pts3, D3 = F(k)
u, v, w = var(3,0), var(3,1), var(3,2)
z = (meet(meet(u,v),w), meet(u,v), meet(u, join(v,w)))
m = (meet(u, join(v,w)), v, w)
assert zmap(m) == z, "z o m = z"
assert emap(m) == m, "m idempotent"

# --- Stab(z) ---
stab = [t for t in itertools.product(D3, repeat=3) if zmap(t) == z]
print(f"|Stab(z)| = {len(stab)}")
idem = [t for t in stab if comp_cell(t, t, 3, 3) == t]
print(f"idempotents in Stab: {len(idem)}")
for t in idem:
    orbit = set(comp_cell(t, s, 3, 3) for s in stab)
    print(f"  idem, e o Stab size = {len(orbit)}, e==m: {t == m}")

# --- M and q at levels 0..4 ---
def M_cells(kk):
    _, D = F(kk)
    return [(p,b,c) for p in D for b in D for c in D if leq(p, join(b,c))]

def qmap(cell):
    p,b,c = cell
    return (p, meet(p,b), meet(meet(p,b),c))

from collections import defaultdict
e_cell = m  # generator of M, at level 3, in (p,b,c) form: p=u^(v|w),b=v,c=w
for kk in range(0, 4):
    cells = M_cells(kk)
    classes = defaultdict(list)
    for cell in cells:
        classes[qmap(cell)].append(cell)
    folded = {im: cs for im, cs in classes.items() if len(cs) > 1}
    nf = sum(len(cs) for cs in folded.values())
    print(f"level {kk}: |M| = {len(cells)}, q-classes = {len(classes)}, "
          f"folded classes = {len(folded)}, folded cells = {nf}")
    if kk == 3:
        img_e = qmap(e_cell)
        print(f"  generator e: fiber size = {len(classes[img_e])}",
              "UNFOLDED" if len(classes[img_e]) == 1 else
              f"FOLDED partners={classes[img_e]}")
        folded3 = folded
print("done stage 1", flush=True)

# --- folded generators at level 3: folded mu with mu o rho = e ---
# mu generates M iff e in instances of mu; necessary: mu's q-class
# folded.  Search rho in D3^3 for each folded mu.
gen_folded = []
allfold3 = [c for cs in folded3.values() for c in cs]
print(f"checking {len(allfold3)} folded level-3 cells for generator property...")
for mu in allfold3:
    # prune: vertex image of mu must cover vertex image of e
    for rho in itertools.product(D3, repeat=3):
        if comp_cell(mu, rho, 3, 3) == e_cell:
            gen_folded.append(mu); break
print(f"folded level-3 generators (mu o rho = e): {len(gen_folded)}")

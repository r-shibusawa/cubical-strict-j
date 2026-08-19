"""Theorem P'' on the reflection-generated mixed subgroups of B_4 that
own NO nontrivial reflection-free normal subgroup (O18, section 76).

The E-machine of section 40 needs the reflections to act freely on E_G,
i.e. to survive in G = H/V; V = 1 always achieves this (a nontrivial V is
only a convenience -- it merges the strata and shrinks the certificate
search).  So we run the exact Boolean certificate with V = 1 on the
32 exceptional groups (conjugacy representatives) and on a control set.

Prediction of Theorem P'': all of them are reflection-generated, hence
CERTIFIED (survivors = 0).
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from boolean_certificates4 import certify, ELEMS, ID, mm, inv, close, hfc, n

idx = {e: i for i, e in enumerate(ELEMS)}
NE = len(ELEMS)

def act(e, v):
    p, s = e
    return sum(((((v >> p[i]) & 1) ^ s[i]) << i) for i in range(n))

# --- lattice via multiplication table (fast) ---
MULT = [[idx[mm(ELEMS[a], ELEMS[b])] for b in range(NE)] for a in range(NE)]
IDi = idx[ID]
INVi = [next(b for b in range(NE) if MULT[a][b] == IDi) for a in range(NE)]
def closei(gens):
    S = {IDi}; dq = deque([IDi])
    while dq:
        x = dq.popleft()
        for g in gens:
            y = MULT[x][g]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
subsi = {frozenset([IDi]): []}
frontier = list(subsi.items())
while frontier:
    new = []
    for H, gens in frontier:
        for g in range(NE):
            if g in H: continue
            H2 = closei(gens + [g])
            if H2 not in subsi:
                subsi[H2] = gens + [g]; new.append((H2, gens + [g]))
    frontier = new
subs = {frozenset(ELEMS[a] for a in H): [ELEMS[g] for g in gens]
        for H, gens in subsi.items()}
print(f"subgroups of B_4: {len(subs)}", flush=True)
REFLi = [hfc(ELEMS[a]) for a in range(NE)]

def refl(H): return [a for a in H if REFLi[a]]
def fixedi(S):
    return any(all(act(ELEMS[a], v) == v for a in S) for v in range(1 << n))

targets = []
for H, gens in subsi.items():
    R = refl(H)
    if not R or fixedi(R): continue
    if closei(R) != H: continue
    Vs = [M for M in subsi
          if M <= H and len(M) > 1 and not any(REFLi[a] for a in M)
          and all(MULT[MULT[g][a]][INVi[g]] in M for g in H for a in M)]
    if not Vs:
        targets.append((H, gens))
print(f"reflection-generated mixed with NO nontrivial reflection-free "
      f"normal subgroup: {len(targets)}")

# conjugacy representatives
seen = set(); reps = []
for H, gens in targets:
    key = min(tuple(sorted(MULT[MULT[g][a]][INVi[g]] for a in H))
              for g in range(NE))
    if key in seen: continue
    seen.add(key); reps.append((H, gens))
print(f"conjugacy classes: {len(reps)}")

ok = True
for i, (H, gens) in enumerate(reps):
    R = refl(H)
    r = certify([ELEMS[a] for a in sorted(H)], [],
                f"noV-{i} (|H|={len(H)}, #R={len(R)})")
    if r is False: ok = False
print()
print("THEOREM P'' on the V-less reflection-generated mixed groups:",
      "CONFIRMED (all certified)" if ok else "FAILED")


# --- control: the three HARD degenerate mixed classes of section 75 ---
# (mixed, <R> proper and fixed-type).  Theorem P'' predicts they are NOT
# certified (survivors > 0), and the closed form of section 75 puts them
# on the AGREE side -- the certificate machine must not certify them.
print()
print("control: the hard degenerate mixed classes (section 75)")
hard = []
seen2 = set()
for H, gens in subsi.items():
    R = refl(H)
    if not R or fixedi(H): continue
    D = closei(R)
    if D == H or not fixedi(D): continue
    key = min(tuple(sorted(MULT[MULT[g][a]][INVi[g]] for a in H))
              for g in range(NE))
    if key in seen2: continue
    seen2.add(key); hard.append((H, gens, D))
print(f"  degenerate mixed classes: {len(hard)}")
import itertools as _it
def orbits_i(H):
    par = list(range(n))
    def f(i):
        while par[i] != i: par[i] = par[par[i]]; i = par[i]
        return i
    for a in H:
        p, _ = ELEMS[a]
        for i in range(n):
            ra, rb = f(i), f(p[i])
            if ra != rb: par[ra] = rb
    gr = {}
    for i in range(n): gr.setdefault(f(i), []).append(i)
    return sorted(tuple(v) for v in gr.values())
def restrict_i(a, B):
    p, s = ELEMS[a]
    q = list(range(n)); t = [0]*n
    for i in B: q[i] = p[i]; t[i] = s[i]
    return idx[(tuple(q), tuple(t))]
def is_product_i(H):
    orb = orbits_i(H)
    for r in range(1, len(orb)):
        for sel in _it.combinations(range(len(orb)), r):
            A = [i for k in sel for i in orb[k]]
            if all(restrict_i(a, A) in H for a in H): return True
    return False
def is_median_i(H):
    orb = orbits_i(H); k = len(orb); parts = []
    for asg in _it.product(range(k), repeat=k):
        if any(asg[i] > max(asg[:i], default=-1) + 1 for i in range(k)):
            continue
        gr = {}
        for i, b in enumerate(asg): gr.setdefault(b, []).extend(orb[i])
        P = [sorted(v) for v in gr.values()]
        if all(len(b) % 2 for b in P) and any(len(b) >= 3 for b in P):
            parts.append(P)
    for eps in range(1 << n):
        d = idx[(tuple(range(n)), tuple((eps >> i) & 1 for i in range(n)))]
        sgs = [ELEMS[MULT[MULT[d][a]][INVi[d]]][1] for a in H]
        for P in parts:
            if all(len(set(s[i] for i in b)) == 1 for s in sgs for b in P):
                return True
    return False
nh = 0
for H, gens, D in hard:
    if is_product_i(H) or is_median_i(H): continue
    nh += 1
    certify([ELEMS[a] for a in sorted(H)], [],
            f"hard-{nh} (|H|={len(H)}, |<R>|={len(D)})")
print(f"  irreducible (non-product, non-median) hard classes: {nh}")

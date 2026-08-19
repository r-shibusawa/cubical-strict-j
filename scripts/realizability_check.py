"""Unified realizability theorem: machine verification (O20).

THEOREM.  A character psi: H -> Z/2 is realizable as a twisted
element (T o sigma_h = ~^psi(h) T) over a reversal site iff psi
vanishes on the stabilizers of the psi-twisted H-action
(h |-> sigma_h o rho^psi(h)) at every middle point of the site
(Boolean: vertices; Kleene: proper middle points = vertices, via
the top-dominant extension; De Morgan: the full literal middle
level, via the weight extension).

Verifies the De Morgan case at n = 2 exhaustively: for every
subgroup of B_2 and every character, the closed-form middle-level
parity criterion coincides with brute-force enumeration over
DM(2) (25 characters, zero mismatches expected).
"""
import sys, itertools as it
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT

n = 2
N2, leq2, rho2 = build(2)
dm = monotone_masks(N2, leq2)
notf = {m: NOT(m, N2, rho2) for m in dm}
ELEMS = []
for p in it.permutations(range(n)):
    for s in it.product((0, 1), repeat=n):
        ELEMS.append((p, s))
ID = (tuple(range(n)), (0,) * n)

def mm(a, b):
    (p1, s1), (p2, s2) = a, b
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i] ^ s2[p1[i]] for i in range(n)))

def close(g):
    S = {ID} | set(g)
    while True:
        new = {mm(a, b) for a in S for b in S} - S
        if not new:
            return frozenset(S)
        S |= new

def sub_pt(e, p):
    pm, s = e
    c = [(p >> i) & 1 for i in range(2 * n)]
    d = [0] * (2 * n)
    for i in range(n):
        vx, vnx = c[2 * pm[i]], c[2 * pm[i] + 1]
        if s[i]:
            vx, vnx = vnx, vx
        d[2 * i], d[2 * i + 1] = vx, vnx
    return sum(b << i for i, b in enumerate(d))

def rho_pt(p):
    c = [(p >> i) & 1 for i in range(2 * n)]
    d = []
    for i in range(n):
        d += [1 - c[2 * i + 1], 1 - c[2 * i]]
    return sum(b << i for i, b in enumerate(d))

def SUB(m, e):
    r = 0
    for p in range(N2):
        if (m >> sub_pt(e, p)) & 1:
            r |= 1 << p
    return r

mid = [p for p in range(N2) if bin(p).count('1') == n]

def brute(H, psi):
    return any(all(SUB(T, h) == (notf[T] if psi[h] else T) for h in H)
               for T in dm)

def closed(H, psi):
    idx = {p: i for i, p in enumerate(mid)}
    parent = list(range(len(mid))); par = [0] * len(mid)
    def find(i):
        r = i; acc = 0
        while parent[r] != r:
            acc ^= par[r]; r = parent[r]
        return r, acc
    for h in H:
        if h == ID:
            continue
        for p in mid:
            q = sub_pt(h, p)
            rq = rho_pt(p) if psi[h] else p
            (ri, pi), (rj, pj) = find(idx[q]), find(idx[rq])
            if ri == rj:
                if (pi ^ pj) != psi[h]:
                    return False
            else:
                parent[ri] = rj; par[ri] = pi ^ pj ^ psi[h]
    return True

subs = {frozenset([ID])}
frontier = {frozenset([ID])}
while frontier:
    new = set()
    for Hf in frontier:
        for e in ELEMS:
            if e in Hf:
                continue
            H2 = close(set(Hf) | {e})
            if H2 not in subs:
                new.add(H2)
    subs |= new
    frontier = new
mism = tested = 0
for Hf in subs:
    H = sorted(Hf)
    gens = []
    span = {ID}
    for e in H:
        if e in span:
            continue
        gens.append(e); span = set(close(gens))
        if len(span) == len(H):
            break
    for bits in it.product((0, 1), repeat=len(gens)):
        psi = {ID: 0}
        for g, b in zip(gens, bits):
            psi[g] = b
        ok = True
        while ok and len(psi) < len(H):
            prog = False
            for a in list(psi):
                for b in list(psi):
                    c = mm(a, b); v = psi[a] ^ psi[b]
                    if c in psi:
                        if psi[c] != v:
                            ok = False; break
                    else:
                        psi[c] = v; prog = True
                if not ok:
                    break
            if not prog:
                break
        if not ok or len(psi) < len(H):
            continue
        tested += 1
        if brute(H, psi) != closed(H, psi):
            mism += 1
print(f"characters tested={tested}, mismatches={mism}")
assert mism == 0
print("UNIFIED REALIZABILITY CRITERION VERIFIED (DM, n=2)")

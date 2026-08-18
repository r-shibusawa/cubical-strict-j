"""Theorem R verification: the stage-zero rigidity discriminant (O17).

THEOREM R (uniform in the site).  Let H <= B_n be a two-stratum mixed
subgroup, J its join model, eps: H -> Z/2 the strata-swap character.
  (a) An interior invariant cell with twist delta is stage-zero
      slide-reachable to an end iff  eps o delta = 0.  Proof: a
      homotopy to a constant end forces its own twist character to
      vanish (the w=1 face is constant), so its w=0 face has an
      UNTWISTED T-component; a function cannot be both psi-twisted
      (psi != 0) and untwisted -- pointwise contradiction.  Conversely
      when psi = 0 the slide T4 = T & ~w with w-constant remaining
      coordinates is an invariant homotopy to the D-end.
  (b) Rigid cells exist over the Boolean site iff some nonzero
      psi in eps o Hom(H,H) vanishes on all vertex stabilizers
      (signed-XOR realizability) and the remaining coordinate system
      is consistent.  Over De Morgan/Kleene, realizability is the
      C3 parity condition instead: this unifies the De Morgan
      delta-certificates and the Boolean XOR phenomenon.

This script closes the loop on the n = 3 census: for each of the 12
two-stratum subgroups with |H| >= 8 it computes eps o Hom(H,H), the
vertex-stabilizer condition, and the strata-swapper structure, and
checks the prediction against the recorded rigidity table of
boolean_fate.py (9 rigid / 3 slide-null).  Empirical sharpening at
n = 3: rigid  <=>  H contains a strata-swapping element at all
(the three null groups have eps == 0 identically).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from delta_obstruction import make_group_tools, locus_pattern, \
    act_on_pattern, match_pattern

n = 3
ELEMS, ID, mm, close, cycles, has_fixed_cell = make_group_tools(n)

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
targets = []
for Hf in sorted(subs, key=len):
    refl = [h for h in Hf if has_fixed_cell(h)]
    if len(refl) != 2:
        continue
    Hsub = close(refl)
    parent = list(range(3)); par = [0] * 3
    def findp(i):
        r = i; acc = 0
        while parent[r] != r:
            acc ^= par[r]; r = parent[r]
        return r, acc
    okc = True
    for (p, s) in Hsub:
        for i in range(3):
            (ri, pi), (rj, pj) = findp(i), findp(p[i])
            if ri == rj:
                if (pi ^ pj) != (s[i] & 1):
                    okc = False; break
            else:
                parent[ri] = rj; par[ri] = pi ^ pj ^ (s[i] & 1)
        if not okc:
            break
    if okc:
        continue
    targets.append(Hf)
big = [Hf for Hf in targets if len(Hf) >= 8]

# rigidity table established by boolean_fate.py
ACTUAL = {0: False, 1: True, 2: False, 3: True, 4: True, 5: True,
          6: True, 7: False, 8: True, 9: True, 10: True, 11: True}

all_ok = True
for idx, Hf in enumerate(big):
    H = sorted(Hf)
    refl = [h for h in H if has_fixed_cell(h)]
    h1, h2 = refl
    m1, m2 = len(cycles(h1)), len(cycles(h2))
    pat1 = locus_pattern(h1, n, cycles)
    pat2 = locus_pattern(h2, n, cycles)
    eps = {}
    for h in H:
        a1 = match_pattern(act_on_pattern(h, pat1, n), pat1, m1)
        a2 = match_pattern(act_on_pattern(h, pat2, n), pat2, m2)
        eps[h] = 0 if (a1 is not None and a2 is not None) else 1
    gens = []
    span = {ID}
    for e in H:
        if e in span:
            continue
        gens.append(e); span = set(close(gens))
        if len(span) == len(H):
            break
    homs = []
    for imgs in itertools.product(H, repeat=len(gens)):
        d = {ID: ID}
        for g, im in zip(gens, imgs):
            d[g] = im
        ok = True
        while ok and len(d) < len(H):
            prog = False
            for a in list(d):
                for b in list(d):
                    c = mm(a, b); v = mm(d[a], d[b])
                    if c in d:
                        if d[c] != v:
                            ok = False; break
                    else:
                        d[c] = v; prog = True
                if not ok:
                    break
            if not prog:
                break
        if ok and len(d) == len(H) and \
           all(d[mm(a, b)] == mm(d[a], d[b]) for a in H for b in H):
            homs.append(d)

    def t_exists(psi):
        for p in range(8):
            for h in H:
                pm, s = h
                q = 0
                for i in range(3):
                    q |= ((((p >> pm[i]) & 1) ^ s[i]) << i)
                if q == p and psi[h] == 1:
                    return False
        return True

    realizable = [d for d in homs
                  if any(eps[d[h]] for h in H)
                  and t_exists({h: eps[d[h]] for h in H})]
    pred = bool(realizable)
    swap_free = all(eps[h] == 0 for h in H)
    ok = (pred == ACTUAL[idx]) and (swap_free == (not ACTUAL[idx]))
    all_ok &= ok
    print(f"#{idx} |H|={len(H)}: eps==0 identically: {swap_free}; "
          f"realizable nonzero twists: {len(realizable)}; "
          f"predict rigid={pred}, actual={ACTUAL[idx]} "
          f"{'MATCH' if ok else '*** MISMATCH ***'}")
print("\nTHEOREM R VERIFIED ON ALL 12 GROUPS" if all_ok else "\nFAILED")

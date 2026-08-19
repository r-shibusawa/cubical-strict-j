"""Decisive tests for the arrangement dichotomy conjecture (O20):

  H~(E(T)/M; F2) != 0  <=>  some elementary abelian 2-subgroup
                            of M has empty fixed set on T.

(1) V = (Z/2)^2 acting on T = three 2-point orbits E/<e1>,
    E/<e2>, E/<e1e2>: every ELEMENT has fixed points, but V has
    none.  Quillen-stratification predicts NONacyclic; the
    'free-involution' heuristic would predict acyclic.
(2) S3 on 3 over F3 (is el fully acyclic or does odd homology
    survive? -- relevant to the test-side geometry).
(3) All 34 cube classes (n<=4): does every mixed
    reflection-generated N contain a fixed-point-free
    elementary abelian 2-subgroup?  (Conjecture side check:
    nonvanishing observed <=> such a subgroup exists.)
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')

def rank2(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

def betti_p(T, M, top, p):
    reps = []; ind = []
    for k in range(top + 1):
        m = k + 1; size = T ** m
        arr = [-1] * size; rp = []
        for code in range(size):
            if arr[code] >= 0: continue
            t = []; c = code
            for _ in range(m): t.append(c % T); c //= T
            oid = len(rp); rp.append(code)
            for g in M:
                c2 = 0
                for j in range(m - 1, -1, -1): c2 = c2 * T + g[t[j]]
                arr[c2] = oid
        reps.append(rp); ind.append(arr)
    def dmat(k):
        # rows of d_k as dicts col->coeff mod p (simplicial boundary)
        rows = []
        for code in reps[k]:
            m = k + 1
            t = []; c = code
            for _ in range(m): t.append(c % T); c //= T
            row = {}
            for i in range(m):
                u = t[:i] + t[i+1:]; c2 = 0
                for j in range(len(u) - 1, -1, -1): c2 = c2 * T + u[j]
                col = ind[k-1][c2]
                row[col] = (row.get(col, 0) + (-1)**i) % p
            rows.append({c: v for c, v in row.items() if v})
        return rows
    def rankp(rows):
        rows = [dict(r) for r in rows if r]
        piv = {}; r = 0
        for row in rows:
            while row:
                c = min(row)
                if c in piv:
                    lead = piv[c]; f = row[c] * pow(lead[c], -1, p) % p
                    for cc, vv in lead.items():
                        row[cc] = (row.get(cc, 0) - f * vv) % p
                        if row[cc] == 0: del row[cc]
                else:
                    piv[c] = row; r += 1; break
        return r
    r = {k: rankp(dmat(k)) for k in range(1, top + 1)}
    return [len(reps[k]) - r[k] - r[k+1] for k in range(1, top)]

def close_perms(gens, T):
    idp = tuple(range(T))
    def comp(a, b): return tuple(a[b[i]] for i in range(T))
    S = {idp} | set(gens); dq = deque(S)
    while dq:
        x = dq.popleft()
        for y in list(S):
            for z in (comp(x, y), comp(y, x)):
                if z not in S: S.add(z); dq.append(z)
    return sorted(S)

# (1) V on three 2-orbits: T = {0,1, 2,3, 4,5}
# e1 acts: swaps orbit2 and orbit3, fixes orbit1? NO --
# T = E/<e1> + E/<e2> + E/<e1e2>: e1 fixes E/<e1> pointwise? cosets
# {<e1>, e2<e1>}: e1 * <e1> = <e1> (fix), e1 * e2<e1> = e2<e1> wait
# e1e2<e1> = e2 e1 <e1> = e2<e1> (abelian) -> e1 fixes BOTH cosets of
# E/<e1>?! coset action: e1 acts trivially on E/<e1> ✓ (index 2,
# abelian). On E/<e2>: cosets {<e2>, e1<e2>}: e1 swaps them ✓.
e1 = (0,1, 3,2, 5,4)   # fixes orbit1 pointwise, swaps within 2,3
e2 = (1,0, 2,3, 5,4)   # swaps orbit1, fixes orbit2, swaps orbit3
V6 = close_perms([e1, e2], 6)
assert len(V6) == 4
fpf = not any(all(g[t] == t for g in V6) for t in range(6))
print(f"(1) V=(Z/2)^2 on 2+2+2: |M|={len(V6)} V-fixed-point-free={fpf}; "
      f"every element has fixed pts: "
      f"{all(any(g[t]==t for t in range(6)) for g in V6 if g != tuple(range(6)))}",
      flush=True)
b2 = betti_p(6, V6, 6, 2)
print(f"    H~(F2) deg1..5 = {b2}", flush=True)

# (2) S3 on 3 over F3
S3 = close_perms([(1,0,2),(0,2,1)], 3)
b3 = betti_p(3, S3, 7, 3)
print(f"(2) S3 on 3: H~(F3) deg1..6 = {b3}", flush=True)

# (3) cube classes: fpf elementary abelian 2-subgroups?
from strata_retract import build
for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    REFL = []
    for a in range(NE):
        p, s = ELEMS[a]
        seen = [False]*n; ok = a != ID
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]
            if sg & 1: ok = False
        REFL.append(ok)
    subs = {frozenset([ID]): []}
    fr = list(subs.items())
    while fr:
        new = []
        for H, gens in fr:
            for g in range(NE):
                if g in H: continue
                H2 = close(gens + [g])
                if H2 not in subs:
                    subs[H2] = gens + [g]; new.append((H2, gens + [g]))
        fr = new
    classes = {}
    for H in subs:
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, H)
    cnt = have = 0
    for H in classes.values():
        R = [a for a in H if REFL[a]]
        if not R or close(R) != H: continue
        if any(all(ACT[a][v] == v for a in R)
               for v in range(1 << n)): continue
        cnt += 1
        # search elem-ab 2-subgroups (up to rank 3) with empty Fix
        invs = [a for a in H if a != ID and MUL[a][a] == ID]
        found = False
        for a in invs:
            if not any(ACT[a][v] == v for v in range(1 << n)):
                found = True; break
        if not found:
            for a, b in itertools.combinations(invs, 2):
                if MUL[a][b] != MUL[b][a]: continue
                E = [ID, a, b, MUL[a][b]]
                if not any(all(ACT[g][v] == v for g in E)
                           for v in range(1 << n)):
                    found = True; break
        have += found
    print(f"(3) n={n}: {have}/{cnt} classes have a fixed-point-free "
          f"elementary abelian 2-subgroup", flush=True)

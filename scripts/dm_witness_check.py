"""DM/Kleene realizability of the (R)-class reduction witnesses
(O21).  For the tree8a class (N <= B_4, order 8, invariant plane
P = {(a, ~a, b, ~b)} with residual res ~ K), a one-step V-witness
is exactly a pair (f, g) of free-algebra elements with

    (f, g) o sigma_h = res(c^{-1} h c) . (f, g)   (all h in N)

for some c in N (the pattern stabilization is automatic).  On the
De Morgan site, elements are monotone functions on the literal
cube L_4 = {0,1}^8; on the Kleene site, monotone functions on the
unmixed subposet U_4.  Existence is decided exactly as a 2-SAT
instance: parity equalities from equivariance (~ acts by
(~f)(p) = 1 - f(rho p)) plus monotonicity implications.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

n = 4
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
from collections import Counter
def cyc(a):
    p, s = ELEMS[a]
    seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        sg = s[i]; j = p[i]; seen[i] = True; ln = 1
        while j != i:
            seen[j] = True; ln += 1; sg ^= s[j]; j = p[j]
        out.append((ln, sg & 1))
    return tuple(sorted(out))
SIG8a = (8, {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):2,
             ((2,0),(2,0)):3, ((4,0),):2})
SIG8b = (8, {((1,0),(1,0),(1,0),(1,0)):1,
             ((1,0),(1,0),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):3,
             ((1,1),(1,1),(2,0)):1, ((2,0),(2,0)):2})
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
found = {}
for H in classes.values():
    R = [a for a in H if REFL[a]]
    if not R or close(R) != H: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    sig = (len(H), dict(Counter(cyc(a) for a in H)))
    if sig == SIG8a: found['tree8a'] = sorted(H)
    if sig == SIG8b: found['tree8b'] = sorted(H)
print("matched:", sorted(found), flush=True)

# ---------- literal cube machinery ----------
def lit_pts(m):
    return list(itertools.product((0,1), repeat=2*m))
def rho_pt(p, m):
    q = list(p)
    for i in range(m): q[2*i], q[2*i+1] = 1-q[2*i+1], 1-q[2*i]
    return tuple(q)
def hstar(h, p, m):
    """point map of the substitution x_i -> (~)^eps x_{pi(i)}:
    pair i of the new point = pair pi(i) of p, swapped iff eps."""
    perm, sgn = ELEMS[h]
    q = [0]*(2*m)
    for i in range(m):
        j = perm[i]
        if sgn[i]:
            q[2*i], q[2*i+1] = p[2*j+1], p[2*j]
        else:
            q[2*i], q[2*i+1] = p[2*j], p[2*j+1]
    return tuple(q)
def unmixed(p, m):
    """Kleene: no (0,0)-pair together with a (1,1)-pair"""
    has00 = any(p[2*i]==0 and p[2*i+1]==0 for i in range(m))
    has11 = any(p[2*i]==1 and p[2*i+1]==1 for i in range(m))
    return not (has00 and has11)

def solve(N, site):
    """exists exact res(c^-1 h c)-equivariant pair (f,g) on the
    tree8a plane pattern, for some c?  2-SAT per c."""
    V = 1 << n
    # the invariant plane and residual: recompute
    loci = {}
    for a in N:
        if REFL[a]:
            L = frozenset(v for v in range(V) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [L for L in loci if not any(L < L2 for L2 in loci)]
    # plane with setwise stabilizer = N and |L| = 4 (tree8a) or 8
    planes = [L for L in maximal
              if all(frozenset(ACT[g][v] for v in L) == L for g in N)]
    # pattern coordinates: find pattern of L: classes of equal/negated
    # bits across the locus --> embedding iota: square -> cube
    results = {}
    for L in planes:
        Ls = sorted(L)
        d = len(Ls).bit_length() - 1   # dim of locus
        # find d free bit-classes: bits as functions on L
        cols = []
        for b in range(n):
            colv = tuple((v >> b) & 1 for v in Ls)
            cols.append(colv)
        # pick representative independent columns and relations
        # (each column = one of the free coords or its negation or const)
        # determine free coords greedily
        free = []; expr = {}   # bit b -> (index into free, negated?)
        for b in range(n):
            c0 = cols[b]
            if all(x == c0[0] for x in c0):
                expr[b] = ('const', c0[0]); continue
            done = False
            for k,(fb,) in enumerate([(f,) for f in free]):
                if cols[fb] == c0: expr[b] = ('eq', k); done=True; break
                if tuple(1-x for x in cols[fb]) == c0:
                    expr[b] = ('neg', k); done=True; break
            if not done:
                expr[b] = ('eq', len(free)); free.append(b)
        if len(free) != d: continue
        # residual action res(h) on the free coords as signed perm of d
        # via vertex action on L in (a_1..a_d)-coordinates
        def coords(v):
            return tuple((v >> fb) & 1 for fb in free)
        cmap = {coords(v): v for v in Ls}
        def res_elem(h):
            # signed perm on d letters: image of unit vectors
            base = cmap[tuple(0 for _ in range(d))]
            img0 = coords(ACT[h][base])
            out = []
            for i in range(d):
                e = tuple(1 if j==i else 0 for j in range(d))
                imi = coords(ACT[h][cmap[e]])
                diff = [j for j in range(d) if imi[j] != img0[j]]
                assert len(diff) == 1
                out.append((diff[0], img0[diff[0]] ^ 0 ^ (0 if imi[diff[0]]==1-img0[diff[0]] and img0[diff[0]]==0 else 0)))
            # sign of letter i: img0[target] (1 means negated)
            return [(j, img0[j]) for (j, _s) in out], img0
        # sanity: res is a group hom to signed perms; encode action on
        # the PAIR (f_1..f_d) of algebra elements:
        #   res(h): f_i' = (~)^{s_j} f_j arrangement
        m = n
        pts = [p for p in lit_pts(m) if site=='DM' or unmixed(p, m)]
        pindex = {p: i for i, p in enumerate(pts)}
        nv = d * len(pts)          # variables f_i(p)
        def vid(i, p): return i * len(pts) + pindex[p]
        import sys as _s
        ok_any = False
        for c in N:
            ci = INV[c]
            # build 2-SAT: implication graph over 2*nv literals
            adj = [[] for _ in range(2*nv)]
            def lit(x, neg): return 2*x + (1 if neg else 0)
            def imp(a, b):
                adj[a].append(b)
                adj[b ^ 1].append(a ^ 1)
            def equal(a, b):   # literal a == literal b
                imp(a, b); imp(b, a)
            bad = False
            # monotonicity: p <= q => f_i(p) -> f_i(q)
            for p in pts:
                for q in pts:
                    if p != q and all(x<=y for x,y in zip(p,q)):
                        for i in range(d):
                            imp(lit(vid(i,p),False), lit(vid(i,q),False))
            # equivariance: for each h in N, each point p:
            #   f_i(hstar(h,p)) == [res(c^-1 h c) applied]_i (p)
            for h in N:
                hh = MUL[MUL[ci][h]][c]
                mp, sg = res_elem(hh)
                # res: new_i = (~)^{sg[target]} f_target ... derive:
                # vertex action: coords(ACT[hh][v]): a'_j = ...
                # We use: sigma_hh o iota = iota o r_hh where r_hh acts
                # on square coords; then condition:
                #   f_i o sigma_h = component_i of r_{c^{-1}hc}(f)
                # component: determine directly from vertex data:
                # find perm tau, signs eps with
                # coords(ACT[hh][cmap[a]])_j = a_{tau(j)} xor eps_j
                base0 = coords(ACT[hh][cmap[tuple(0 for _ in range(d))]])
                tau = [None]*d; eps = list(base0)
                for i in range(d):
                    e = tuple(1 if j==i else 0 for j in range(d))
                    imi = coords(ACT[hh][cmap[e]])
                    diff = [j for j in range(d) if imi[j] != base0[j]]
                    assert len(diff) == 1
                    tau[i] = diff[0]
                # invert: new coord j comes from old coord tau^{-1}(j)
                inv_tau = [0]*d
                for i in range(d): inv_tau[tau[i]] = i
                for p in pts:
                    hp = hstar(h, p, m)
                    for jco in range(d):
                        src = inv_tau[jco]
                        # f_jco(hstar p) == (~)^{eps_jco} f_src(p)
                        if eps[jco]:
                            rp = rho_pt(p, m)
                            if rp not in pindex: bad = True; break
                            equal(lit(vid(jco,hp),False),
                                  lit(vid(src,rp),True))
                        else:
                            equal(lit(vid(jco,hp),False),
                                  lit(vid(src,p),False))
                    if bad: break
                if bad: break
            if bad: continue
            # 2-SAT via Tarjan SCC (iterative)
            NLIT = 2*nv
            index = [0]*NLIT; low = [0]*NLIT; onstk = [False]*NLIT
            comp = [-1]*NLIT; idx_counter = [1]; stk = []; ncomp = [0]
            import sys as s2
            for s0 in range(NLIT):
                if index[s0]: continue
                work = [(s0, 0)]
                while work:
                    v0, pi = work[-1]
                    if pi == 0:
                        index[v0] = low[v0] = idx_counter[0]
                        idx_counter[0] += 1
                        stk.append(v0); onstk[v0] = True
                    recurse = False
                    for k in range(pi, len(adj[v0])):
                        w = adj[v0][k]
                        if not index[w]:
                            work[-1] = (v0, k+1)
                            work.append((w, 0)); recurse = True; break
                        elif onstk[w]:
                            low[v0] = min(low[v0], index[w])
                    if recurse: continue
                    if low[v0] == index[v0]:
                        while True:
                            w = stk.pop(); onstk[w] = False
                            comp[w] = ncomp[0]
                            if w == v0: break
                        ncomp[0] += 1
                    work.pop()
                    if work:
                        u0, _ = work[-1]
                        low[u0] = min(low[u0], low[v0])
                sat = all(comp[2*x] != comp[2*x+1] for x in range(nv))
            sat = all(comp[2*x] != comp[2*x+1] for x in range(nv))
            if sat:
                ok_any = True
                results[tuple(Ls)] = ('WITNESS EXISTS', ELEMS[c])
                break
        if not ok_any:
            results[tuple(Ls)] = ('no witness (all c)',)
    return results

for name in sorted(found):
    N = found[name]
    for site in ('DM', 'KL'):
        res = solve(N, site)
        for L, verdict in res.items():
            print(f"{name} [{site}] plane {list(L)}: {verdict}",
                  flush=True)

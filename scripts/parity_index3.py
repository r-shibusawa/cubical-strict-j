"""Classification program, step 2: combinatorial criteria + the n=3 table.

Criteria (proved in TestComparison §33):
  (C1) h has a fixed nonempty cell  <=>  every cycle of h has even
       sign-sum  (cycle-wise propagation; odd forces m = ~m).
  (C2) fixed layer of H nonempty  <=>  the slot union-find with sign
       parity has no odd loop.
  (C3) character chi: H -> Z/2 realizable by monotone phi
       <=>  the middle-level constraint graph (edges q ~ M_h q with
       parity chi(h), M_h = sigma_h* if chi(h)=0 else sigma_h*.rho)
       is parity-consistent.  (Weight rule handles everything off
       the middle antichain; exactness theorem.)
Cross-check n=2 against the census-based table, then produce n=3.
"""
import sys, itertools
sys.path.insert(0, 'scripts')

def run(n, crosscheck=False):
    N = 1 << (2*n)
    def coords(p): return [(p>>i)&1 for i in range(2*n)]
    def frompt(c): return sum(b<<i for i,b in enumerate(c))
    # elements of B_n
    ELEMS = []
    for perm in itertools.permutations(range(n)):
        for signs in itertools.product((0,1), repeat=n):
            ELEMS.append((perm, signs))
    def point_map(perm, signs):
        mp = []
        for p in range(N):
            c = coords(p)
            d = [0]*(2*n)
            for i in range(n):
                src = perm[i]
                a, b = c[2*src], c[2*src+1]
                if signs[i]: a, b = b, a
                d[2*i], d[2*i+1] = a, b
            mp.append(frompt(d))
        return mp
    PM = {e: point_map(*e) for e in ELEMS}
    rho = []
    for p in range(N):
        c = coords(p)
        d = []
        for i in range(n):
            d += [1-c[2*i+1], 1-c[2*i]]
        rho.append(frompt(d))
    W = [sum(coords(p)) for p in range(N)]
    MID = [p for p in range(N) if W[p] == n]
    ID = (tuple(range(n)), (0,)*n)

    def mm(e1, e2):
        """Algebraic composite h1∘h2 as a substitution: component i of
        h1∘h2 = (¬)^{s1[i]} (h2-component at perm1[i])
              = (¬)^{s1[i] ^ s2[perm1[i]]} x_{perm2[perm1[i]]}."""
        (p1, s1), (p2, s2) = e1, e2
        perm = tuple(p2[p1[i]] for i in range(n))
        signs = tuple(s1[i] ^ s2[p1[i]] for i in range(n))
        return (perm, signs)
    # sanity: algebraic mul matches point-map composition
    import random as _r
    for _ in range(20):
        a, b = _r.choice(ELEMS), _r.choice(ELEMS)
        assert PM[mm(a,b)] == [PM[a][PM[b][p]] for p in range(N)], (a,b)

    # (C1) fixed-cell criterion per element
    def fixed_cell(e):
        perm, signs = e
        seen = [False]*n
        for i in range(n):
            if seen[i]: continue
            j, ssum = i, 0
            while True:
                seen[j] = True
                ssum += signs[j]
                j = perm[j]
                if j == i: break
            if ssum % 2 == 1: return False
        return True

    # (C2) fixed layer of H
    def fixed_layer(H):
        parent = list(range(n)); par = [0]*n
        def find(i):
            path=[]
            while parent[i]!=i: path.append(i); i=parent[i]
            p=0
            for j in reversed(path):
                p^=par[j]; parent[j]=i; par[j]=p
            return i,0 if not path else (i, par[path[0]]) if False else (i, p if False else par[path[0]] if path else 0)
        # simpler: rebuild find cleanly
        parent = list(range(n)); rank_par = [0]*n
        def find2(i):
            if parent[i]==i: return i,0
            r,p = find2(parent[i])
            parent[i]=r; rank_par[i]^=p
            return r, rank_par[i]
        def union(i,j,parity):
            ri,pi = find2(i); rj,pj = find2(j)
            if ri==rj: return (pi^pj)==parity
            parent[ri]=rj; rank_par[ri]=pi^pj^parity
            return True
        ok = True
        for (perm, signs) in H:
            for i in range(n):
                if not union(i, perm[i], signs[i]): ok=False
        return ok

    # (C3) character realizability via middle-level parity union-find
    def realizable(H, chi):
        idx = {p:k for k,p in enumerate(MID)}
        parent = list(range(len(MID))); pr = [0]*len(MID)
        def find2(i):
            if parent[i]==i: return i,0
            r,p = find2(parent[i])
            parent[i]=r; pr[i]^=p
            return r, pr[i]
        def union(i,j,parity):
            ri,pi = find2(i); rj,pj = find2(j)
            if ri==rj: return (pi^pj)==parity
            parent[ri]=rj; pr[ri]=pi^pj^parity
            return True
        for e in H:
            c = chi[e]
            mp = PM[e]
            for p in MID:
                q = mp[p] if c==0 else mp[rho[p]]
                if W[q] != n:  # can only happen if something is off
                    return False
                if not union(idx[p], idx[q], c): return False
        return True

    # subgroups via closure of <=3 generators (dedup)
    def close(gens):
        S = {ID} | set(gens)
        changed = True
        while changed:
            changed = False
            new = set()
            for a in S:
                for b in S:
                    c = mm(a,b)
                    if c not in S: new.add(c)
            if new: S |= new; changed = True
        return frozenset(S)
    subs = {frozenset([ID])}
    frontier = {frozenset([ID])}
    while frontier:
        newsubs = set()
        for H in frontier:
            for e in ELEMS:
                if e in H: continue
                H2 = close(set(H) | {e})
                if H2 not in subs:
                    newsubs.add(H2)
        subs |= newsubs
        frontier = newsubs
    subs = sorted(subs, key=lambda H: (len(H), sorted(H)))
    print(f"n={n}: |B_n|={len(ELEMS)}, subgroups found: {len(subs)}")

    rows = []
    for H in subs:
        anyfix = any(fixed_cell(e) for e in H if e != ID)
        flayer = fixed_layer(list(H))
        if not anyfix and len(H) > 1: iso = 'free'
        elif flayer: iso = 'fixed-layer'
        elif anyfix: iso = 'MIXED'
        else: iso = 'trivial'
        if len(H) == 1: iso = 'trivial'
        # characters: Hom(H, Z/2) via generators (propagate, check)
        Hl = sorted(H)
        # find a small generating set greedily
        gens = []
        gen_span = {ID}
        for e in Hl:
            if e in gen_span: continue
            gens.append(e)
            gen_span = set(close(set(gens)))
            if len(gen_span) == len(H): break
        chis = []
        for bits in itertools.product((0,1), repeat=len(gens)):
            chi = {ID: 0}
            for g, b in zip(gens, bits): chi[g] = b
            ok, frontier = True, set(chi)
            while ok and len(chi) < len(H):
                progressed = False
                for a in list(chi):
                    for b in list(chi):
                        c = mm(a,b); v = chi[a]^chi[b]
                        if c in chi:
                            if chi[c] != v: ok = False; break
                        else:
                            chi[c] = v; progressed = True
                    if not ok: break
                if not ok or not progressed: break
            if ok and len(chi) == len(H) and                all(chi[mm(a,b)] == (chi[a]^chi[b]) for a in Hl for b in Hl):
                chis.append(chi)
        nreal = sum(1 for chi in chis if realizable(H, chi))
        ntriv = sum(1 for chi in chis if realizable(H, chi) and any(chi[h] for h in H))
        rows.append((len(H), iso, len(chis), nreal, ntriv))
    from collections import Counter
    summary = Counter((iso, ntriv>0) for (_o, iso, _c, _r, ntriv) in rows)
    print("summary {(isotropy, has-nontrivial-realizable-char): count}:")
    for k,v in sorted(summary.items()): print("  ", k, v)
    mixed = [(o,c,r,t) for (o,iso,c,r,t) in rows if iso=='MIXED']
    print(f"MIXED subgroups: {len(mixed)}; with ONLY trivial realizable char: "
          f"{sum(1 for (_o,_c,r,_t) in mixed if r==1)} / {len(mixed)}")
    for (o,c,r,t) in sorted(set(mixed)):
        print(f"  order={o} chars={c} realizable={r} nontrivial={t}")

run(2)
print()
run(3)

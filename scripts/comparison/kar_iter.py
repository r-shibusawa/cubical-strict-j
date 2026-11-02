"""Transfer-function version: C = P(G)/(e_v e_v = e_v) for a set of idempotent loops e_v, G finite acyclic.
Morphisms = reduced words of tokens: edge (d,c) or loop ('L',v).  Marks = vertices v (object (v,id) of Kar C) and loops
('L',v) (object (v,e_v) of Kar C).  For a set E of marks, a_E X = Ran along the full subcategory of Kar C on E.
Common marks E ^ F = marks m with id_m in D_E and D_F: the marks of E n F and the loops ('L',v) with v in one set and
('L',v) in the other.  Test: least n with (a_E a_F)^n X an (E ^ F)-sheaf is at most a+1, a = max alternation of marks
(F-mark then E-mark, positions non-decreasing) along reduced paths with no mark in E ^ F."""
import random, itertools as it, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)

def reduce_word(w):
    out = []
    for t in w:
        if out and t[0] == 'L' and out[-1] == t: continue
        out.append(t)
    return tuple(out)

def all_morphisms(n, E, loops):
    """all reduced words (source-to-target order) from each vertex: returns dict tgt -> list of (src, word)."""
    res = {c: [] for c in range(n)}
    # BFS over words: state (current vertex, word)
    for s in range(n):
        frontier = [(s, ())]
        while frontier:
            new = []
            for (v, w) in frontier:
                res[v].append((s, w))
                if v in loops and (not w or w[-1] != ('L', v)): new.append((v, w + (('L', v),)))
                for (d, c) in E:
                    if d == v: new.append((c, w + ((d, c),)))
            frontier = new
    return res

def marks_along(s, w):
    """sequence of marks visited: starting vertex, then for each token: loop mark or next vertex."""
    seq = [('V', s)]; v = s
    for t in w:
        if t[0] == 'L': seq.append(('L', v)); seq.append(('V', v))
        else: v = t[1]; seq.append(('V', v))
    return seq

def apply(X, s, w, x):
    """X(w): X(target) -> X(source); x in X(target); w from s. apply tokens from the end."""
    for t in reversed(w):
        if t[0] == 'L': x = X['loop'][t[1]][x]
        else: x = X['res'][t][x]
    return x

def ran(X, Emarks, n, M):
    """a_E X. Objects of comma cat at c: (m, w) with m in Emarks, w: m -> c in Kar: if m = ('V',s): any word from s;
    if m = ('L',s): word from s starting with ('L',s).  Value X(m): X(s) or image of loop map."""
    def Xm(m):
        s = m[1]
        if m[0] == 'V': return list(X['el'][s])
        return sorted(set(X['loop'][s].values()))
    def objs(c):
        o = []
        for (s, w) in M[c]:
            for m in Emarks:
                if m[1] != s: continue
                if m[0] == 'V': o.append((m, w))
                elif w and w[0] == ('L', s): o.append((m, w))
        return sorted(o, key=repr)
    def hom(m2, m1):
        """morphisms g: m2 -> m1 in Kar: words from s2 to s1 with e1 g e2 = g."""
        s2, s1 = m2[1], m1[1]
        out = []
        for (s, w) in M[s1]:
            if s != s2: continue
            if m2[0] == 'L' and not (w and w[0] == ('L', s2)): continue
            if m1[0] == 'L' and not (w and w[-1] == ('L', s1)): continue
            out.append(w)
        return out
    Y = {'el': {}, 'res': {}, 'loop': {}}
    for c in range(n):
        o = objs(c); fams = []
        for vals in it.product(*[Xm(m) for (m, w) in o]):
            z = dict(zip(o, vals)); ok = True
            for (m, w) in o:
                for m2 in Emarks:
                    for g in hom(m2, m):
                        key = (m2, reduce_word(g + w))
                        if z[key] != apply(X, m2[1], g, z[(m, w)]): ok = False; break
                    if not ok: break
                if not ok: break
            if ok: fams.append(tuple(sorted(z.items(), key=repr)))
        Y['el'][c] = fams
    def restr(c, tok, f):
        z = dict(f); d = tok[1] if tok[0] == 'L' else tok[0]
        return tuple(sorted(((k, z[(k[0], reduce_word(k[1] + (tok,)))]) for k in objs(d)), key=repr))
    for (d, c) in X['res']:
        Y['res'][(d, c)] = {f: restr(c, (d, c), f) for f in Y['el'][c]}
    for v in X['loop']:
        Y['loop'][v] = {f: restr(v, ('L', v), f) for f in Y['el'][v]}
    unit = {c: {x: tuple(sorted((((m, w), apply(X, m[1], w, x)) for (m, w) in objs(c)), key=repr)) for x in X['el'][c]} for c in range(n)}
    return Y, unit

def is_sheaf(X, Emarks, n, M):
    Y, unit = ran(X, Emarks, n, M)
    return all(len(set(unit[c].values())) == len(X['el'][c]) == len(Y['el'][c]) for c in range(n))

def common_marks(Em, Fm):
    c = set(Em & Fm)
    for m in Em | Fm:
        v = m[1]
        if (('V', v) in Em and ('L', v) in Fm) or (('L', v) in Em and ('V', v) in Fm): c.add(('L', v))
    return c

def max_alt(n, M, Em, Fm):
    common = common_marks(Em, Fm); best = 0
    for c in range(n):
        for (s, w) in M[c]:
            seq = marks_along(s, w)
            if any(m in common for m in seq): continue
            k = 0; ph = 0
            for m in seq:
                if ph == 0 and m in Fm: ph = 1
                if ph == 1 and m in Em: ph = 0; k += 1
            best = max(best, k)
    return best

stats = {}; bad = []
for trial in range(250):
    n = random.randint(3, 6)
    E = [(i, j) for i in range(n) for j in range(i + 1, n) if random.random() < (0.9 if j == i + 1 else 0.15)]
    loops = {v for v in range(n) if random.random() < 0.4}
    M = all_morphisms(n, E, loops)
    if max(len(M[c]) for c in range(n)) > 9: continue
    marks = [('V', v) for v in range(n)] + [('L', v) for v in loops]
    Em = {m for m in marks if random.random() < 0.45}; Fm = {m for m in marks if random.random() < 0.45}
    if not Em or not Fm: continue
    X = {'el': {v: list(range(random.randint(1, 2))) for v in range(n)}, 'res': {}, 'loop': {}}
    for (d, c) in E: X['res'][(d, c)] = {x: random.choice(X['el'][d]) for x in X['el'][c]}
    for v in loops:
        # random idempotent map on X(v)
        img = random.choice(X['el'][v]); m = {x: (x if random.random() < 0.5 else img) for x in X['el'][v]}
        m[img] = img; X['loop'][v] = m
    a = max_alt(n, M, Em, Fm)
    Y = X; nmin = None
    for k in range(0, 6):
        if is_sheaf(Y, common_marks(Em, Fm), n, M): nmin = k; break
        Z, _ = ran(Y, Fm, n, M); Y, _ = ran(Z, Em, n, M)
        if max(len(Y['el'][c]) for c in range(n)) > 2000: break
    key = (a, nmin); stats[key] = stats.get(key, 0) + 1
    if nmin is None or nmin > a + 1: bad.append((n, E, sorted(loops), sorted(Em), sorted(Fm), a, nmin))
print("(a, n_min) -> count:")
for k in sorted(stats, key=lambda t: (t[0], -1 if t[1] is None else t[1])): print(" ", k, stats[k])
print("violations:", len(bad))
for b in bad[:3]: print(" ", b)

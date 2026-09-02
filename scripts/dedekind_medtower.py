"""O28 stage 7f: the median tower -- does 5-ary majority give a
strict subatom flat at levels <= 3?  (F(5) enumeration avoided:
truth-table composition only.)"""
import itertools, random, time
random.seed(31)

def pts(m): return list(itertools.product((0,1), repeat=m))
PT = {m: pts(m) for m in range(0, 7)}
IDX = {m: {p: i for i, p in enumerate(PT[m])} for m in PT}

def comp(phi, a, ks, kt):
    """phi: table over PT[ks]; a: ks-tuple of tables over PT[kt]"""
    return tuple(phi[IDX[ks][tuple(ai[j] for ai in a)]]
                 for j in range(len(PT[kt])))
def rest(cell, u, j, k):
    return tuple(comp(c, u, j, k) for c in cell)

def var(i, m): return tuple(p[i] for p in PT[m])
def med(m): return tuple(1 if sum(p) > m//2 else 0 for p in PT[m])

def D(k):
    """monotone functions on PT[k] -- only for k <= 3"""
    out = []
    for bits in itertools.product((0,1), repeat=len(PT[k])):
        ok = True
        for i, p in enumerate(PT[k]):
            for jj, q in enumerate(PT[k]):
                if all(a <= b for a, b in zip(p, q)) and \
                   bits[i] > bits[jj]: ok = False; break
            if not ok: break
        if ok: out.append(bits)
    return out
D1, D2, D3 = D(1), D(2), D(3)

x1, x2, x3 = var(0,3), var(1,3), var(2,3)
A = (tuple(a|b for a,b in zip(x1,x2)),
     tuple(a&b for a,b in zip(x1,x3)),
     tuple(a&b for a,b in zip(x2,x3)))
y = [var(i,5) for i in range(5)]
u5 = (y[1], y[0], med(5))
A5 = rest(A, u5, 3, 5)

def cells(z, m, k, Dk):
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))
t0 = time.time()
e1 = cells(A,3,1,D1) == cells(A5,5,1,D1)
e2 = cells(A,3,2,D2) == cells(A5,5,2,D2)
print(f"5-ary median lift: level-1 equal {e1}, level-2 equal {e2} "
      f"({time.time()-t0:.0f}s)", flush=True)
l3A = cells(A,3,3,D3)
samp = set()
for _ in range(120000):
    u = tuple(random.choice(D3) for _ in range(5))
    samp.add(rest(A5, u, 5, 3))
print(f"A(3) exact {len(l3A)}; A5(3) sampled {len(samp)}; "
      f"subset of A(3): {samp <= l3A}; unhit {len(l3A - samp)}",
      flush=True)
# also: the LEVEL-3 median pair inside A5? A5' = A5 o (3-ary med
# pattern lifted)?  and: is A5 strictly smaller: is A in <A5>?
# strictness hint: search v: [3]->[5] with A5 o v = A (sampled)
hit = False
for _ in range(200000):
    v = tuple(tuple(random.choice(D3)) for _ in range(5))
    if rest(A5, v, 5, 3) == A: hit = True; break
print(f"A recovered from A5 by sampled substitution: {hit} "
      f"(False = strictness hint)", flush=True)

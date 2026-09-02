"""O27 stage 7: the subatom family of cube^3.

(1) Census: all subatoms <c> of cube^3 from generators of level
    <= 3, fingerprinted by their cell sets at levels <= 2 (fast),
    refining collisions at level 3 if needed.
(2) Level-4 probe: sample c in D(4)^3 (random + structured
    suspects) and test whether <c> equals a level-<=3 subatom
    (compare level-<=2 fingerprints; novel fingerprint = ALARM =
    rank-collapse failure candidate).
Cells and maps at the vertex level (complete for identities):
a cell c in D(l)^3 = a monotone map 2^l -> 2^3, encoded as a
tuple of 2^l values in 0..7.  Instances at level k: c o r for
r in Mon(2^k, 2^l).
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {}
for k in range(0, 5):
    D[k] = [to_int(f) for f in F(k)[1]]

def monmaps(k, l):
    """monotone maps 2^k -> 2^l as value tuples (len 2^k, vals in
    0..2^l-1), via l-tuples of D(k)"""
    out = set()
    for comps in itertools.product(D[k], repeat=l):
        vals = []
        for x in range(1 << k):
            v = 0
            for i in range(l):
                v |= ((comps[i] >> x) & 1) << i
            vals.append(v)
        out.add(tuple(vals))
    return sorted(out)

MM = {}
def mm(k, l):
    if (k, l) not in MM: MM[(k, l)] = monmaps(k, l)
    return MM[(k, l)]

def cellmap(c, l):
    """c = triple over D(l) -> value tuple 2^l -> 2^3"""
    return tuple((((c[0] >> x) & 1) | (((c[1] >> x) & 1) << 1)
                  | (((c[2] >> x) & 1) << 2)) for x in range(1 << l))

def fingerprint(cm, l, maxk=2):
    """cell sets of <c> at levels 0..maxk; cm = value tuple"""
    fp = []
    for k in range(0, maxk + 1):
        cells = set()
        for r in mm(k, l):
            cells.add(tuple(cm[y] for y in r))
        fp.append(frozenset(cells))
    return tuple(fp)

# (1) census from levels <= 3
seen = {}
for l in range(0, 4):
    for c in itertools.product(D[l], repeat=3):
        cm = cellmap(c, l)
        fp = fingerprint(cm, l)
        if fp not in seen:
            seen[fp] = (l, cm)
    print(f"cube^3 subatoms from generators of level <= {l}: "
          f"{len(seen)}", flush=True)

# (2) level-4 probe
random.seed(0)
novel = []
samples = []
# random samples
for _ in range(300):
    samples.append(tuple(random.choice(D[4]) for _ in range(3)))
# structured suspects: essentially-4-var combinations
pts4 = F(4)[0]
x1 = to_int(tuple(p[0] for p in pts4)); x2 = to_int(tuple(p[1] for p in pts4))
x3 = to_int(tuple(p[2] for p in pts4)); x4 = to_int(tuple(p[3] for p in pts4))
AND, OR = (lambda a,b: a&b), (lambda a,b: a|b)
sus = [
  (x1&(x2|x3), x2&(x3|x4), x3&(x4|x1)),
  (x1&(x2|(x3&x4)), x2&(x1|(x3&x4)), (x3&x4)|(x1&x2)),
  ((x1&x2)|(x3&x4), (x1&x3)|(x2&x4), (x1&x4)|(x2&x3)),
  (x1|(x2&x3&x4), x2|(x1&x3&x4), (x3&x4)|(x1&x2&(x3|x4))),
  (x1&(x2|x3|x4), (x1&x2)|(x3&x4), x1&x2&(x3|x4)),
]
samples.extend(sus)
for c in samples:
    cm = cellmap(c, 4)
    fp = fingerprint(cm, 4)
    if fp not in seen:
        novel.append(c)
print(f"level-4 samples tested: {len(samples)}, "
      f"NOVEL subatom fingerprints: {len(novel)}", flush=True)
for c in novel[:5]:
    print("  novel:", c)

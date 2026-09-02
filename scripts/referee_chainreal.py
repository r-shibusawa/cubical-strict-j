"""Referee check 3 (thm:chext obs (i) for ATOM presentations):
if c = z o v is an ambient-chain cell of the atom <z> (pairwise
comparable components), is there a CHAIN-VALUED v' with z o v' = c?
(This is what is needed so that the image of an ambient-chain cell of
B under the presentation map is a chain instance x.v' in Ch(X).)
Search for violations at cell levels m <= 2, generators z in D(k)^n.
"""
import sys, itertools, random
sys.path.insert(0, '/Users/shibusawa/Dev/DIT/FormalizedMathematics/scripts')
from dedekind_site import F, compose

def leq(a, b): return all(x <= y for x, y in zip(a, b))
def chain_tuple(t):
    return all(leq(a, b) or leq(b, a)
               for a, b in itertools.combinations(t, 2))

def run(k, n, gens, mmax=2):
    viol = 0; nchain = 0
    for z in gens:
        for m in range(mmax + 1):
            Dm = F(m)[1]
            subs = list(itertools.product(Dm, repeat=k))
            chain_subs = [v for v in subs if chain_tuple(v)] if k > 1 \
                else subs
            # realizable chain cells via chain-valued subs:
            reach = {tuple(compose(c, v, k, m) for c in z)
                     for v in chain_subs}
            for v in subs:
                c = tuple(compose(cc, v, k, m) for cc in z)
                if n > 1 and not chain_tuple(c): continue
                nchain += 1
                if c not in reach:
                    viol += 1
                    print(f"VIOLATION k={k} n={n} m={m}: z={z} "
                          f"c={c} (via v={v}) not chain-realizable")
                    break
    return viol, nchain

random.seed(11)
for (k, n, sample) in [(2, 2, None), (2, 3, 400), (3, 2, 400),
                       (3, 3, 250)]:
    Dk = F(k)[1]
    allg = list(itertools.product(Dk, repeat=n))
    gens = random.sample(allg, sample) if sample and len(allg) > sample \
        else allg
    v, c = run(k, n, gens)
    print(f"(k={k},n={n}) gens={len(gens)}: chain cells checked={c}, "
          f"violations={v}", flush=True)

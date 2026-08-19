"""Degenerate-group search at n = 4 (O18, paper 18).

Samples subgroups of B_4, keeps the MIXED DEGENERATE ones (the
normal closure N of the reflections has a common fixed cell), and
searches for an H-equivariant consensus pattern with d < n classes
whose negated classes are all odd -- the hypothesis of the one-step
equivariant retraction.  The run (seed 11) finds five degenerate
groups admitting NO such pattern: the one-step retraction provably
fails for them, and the two-step covering argument of the criterion
paper (retract at the level of N, then quotient by the free H/N)
is genuinely needed.
"""
import itertools as it, collections, random
n=4
ELEMS=[]
for p in it.permutations(range(n)):
    for s in it.product((0,1),repeat=n):
        ELEMS.append((p,s))
ID=(tuple(range(n)),(0,)*n)
def mm(a,b):
    (p1,s1),(p2,s2)=a,b
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i]^s2[p1[i]] for i in range(n)))
def inv(e):
    p,s=e
    q=[0]*n;t=[0]*n
    for i in range(n): q[p[i]]=i
    for i in range(n): t[i]=s[q[i]]
    return (tuple(q),tuple(t))
def hfc(e):
    if e==ID: return False
    p,s=e; seen=[False]*n
    for i in range(n):
        if seen[i]:continue
        seen[i]=True;j=p[i];sg=s[i]
        while j!=i: seen[j]=True;sg^=s[j];j=p[j]
        if sg&1: return False
    return True
def close(g):
    S={ID}|set(g)
    dq=collections.deque(S)
    while dq:
        x=dq.popleft()
        for y in list(S):
            for z in (mm(x,y),mm(y,x)):
                if z not in S: S.add(z);dq.append(z)
    return S
def cf(H):
    parent=list(range(n)); par=[0]*n
    def findp(i):
        r=i;acc=0
        while parent[r]!=r: acc^=par[r]; r=parent[r]
        return r,acc
    for (p,s) in H:
        for i in range(n):
            (ri,pi),(rj,pj)=findp(i),findp(p[i])
            if ri==rj:
                if (pi^pj)!=(s[i]&1): return False
            else:
                parent[ri]=rj; par[ri]=pi^pj^(s[i]&1)
    return True
def all_patterns():
    out=[]
    def parts(elems):
        if not elems: yield []
        else:
            x=elems[0]
            for rest in parts(elems[1:]):
                for i in range(len(rest)):
                    yield rest[:i]+[[x]+rest[i]]+rest[i+1:]
                yield [[x]]+rest
    for P in parts(list(range(n))):
        blocks=[sorted(b) for b in P]
        if len(blocks)==n: continue
        freeslots=[i for b in blocks for i in b if i!=b[0]]
        for bits in it.product((0,1),repeat=len(freeslots)):
            eps={}
            for b in blocks: eps[b[0]]=0
            for sl,v in zip(freeslots,bits): eps[sl]=v
            lam={i:bi for bi,b in enumerate(blocks) for i in b}
            out.append((blocks,lam,eps))
    return out
PATTERNS=all_patterns()
def valid_structure(H):
    for blocks,lam,eps in PATTERNS:
        ok=True; negated=set()
        for (p,s) in H:
            cmap={}; csgn={}
            for i in range(n):
                c=lam[i]; tgt=lam[p[i]]; sg=eps[p[i]]^s[i]^eps[i]
                if c in cmap:
                    if cmap[c]!=tgt or csgn[c]!=sg: ok=False;break
                else:
                    cmap[c]=tgt; csgn[c]=sg
            if not ok: break
            if len(set(cmap.values()))!=len(blocks): ok=False;break
            for c,sg in csgn.items():
                if sg: negated.add(cmap[c])
        if not ok: continue
        if all(len(blocks[c])%2==1 for c in negated):
            return (blocks, negated)
    return None
random.seed(11)
seen=set(); degen=0; nostruct=[]
for trial in range(6000):
    k=random.choice([2,2,3])
    gens=random.sample(ELEMS,k)
    Hf=frozenset(close(gens))
    if Hf in seen: continue
    seen.add(Hf)
    H=sorted(Hf)
    refl=[h for h in H if hfc(h)]
    if not refl: continue
    if cf([h for h in H if h!=ID]): continue
    Ncl=close([mm(mm(g,r),inv(g)) for g in H for r in refl])
    if not cf([h for h in Ncl if h!=ID]): continue
    degen+=1
    if valid_structure(H) is None:
        nostruct.append([list(map(list,h)) for h in H])
print("STRICT d<n: sampled degenerate=%d; without structure=%d"%(degen,len(nostruct)))
if nostruct:
    import json
    open("/tmp/nostruct_strict.json","w").write(json.dumps(nostruct[:10]))
    for H in nostruct[:3]:
        print("  example |H|=",len(H))

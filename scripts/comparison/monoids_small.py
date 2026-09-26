"""Backtracking enumeration of all monoids of order n (identity = 0) up to isomorphism.
Associativity is checked incrementally on fully-defined triples."""
import itertools as it, sys

def monoids(n):
    T=[[None]*n for _ in range(n)]
    for a in range(n): T[0][a]=a; T[a][0]=a
    cells=[(a,b) for a in range(1,n) for b in range(1,n)]
    found=[]; seen=set()
    def assoc_ok(a,b):
        # check all triples involving the newly set cell (a,b) where everything needed is defined
        for c in range(n):
            # (a b) c = a (b c)
            ab=T[a][b]; bc=T[b][c]
            if bc is not None and T[ab][c] is not None and T[a][bc] is not None and T[ab][c]!=T[a][bc]: return False
            # (c a) b = c (a b)
            ca=T[c][a]
            if ca is not None and T[ca][b] is not None and T[c][ab] is not None and T[ca][b]!=T[c][ab]: return False
            # (a c) ? : triples (x,y,z) where the cell (a,b) appears as (x y) with x=a,y=b handled; as (y z): x arbitrary, y=a, z=b handled (second). Others don't involve (a,b) directly but could involve it as an outer product: (x y) z with (x y)=a? handled when those cells set later.
        return True
    def full_check():
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    if T[T[a][b]][c]!=T[a][T[b][c]]: return False
        return True
    def rec(i):
        if i==len(cells):
            if not full_check(): return
            key=min(tuple(tuple(s[T[si[a]][si[b]]] for b in range(n)) for a in range(n))
                    for s in [(0,)+p for p in it.permutations(range(1,n))] for si in [tuple(s.index(k) for k in range(n))])
            if key not in seen:
                seen.add(key); found.append([row[:] for row in T])
            return
        a,b=cells[i]
        for v in range(n):
            T[a][b]=v
            if assoc_ok(a,b): rec(i+1)
            T[a][b]=None
    rec(0)
    return found

if __name__=='__main__':
    import time
    for n in range(1,int(sys.argv[1]) if len(sys.argv)>1 else 5):
        t=time.time(); M=monoids(n); print(n,len(M),"%.1fs"%(time.time()-t))

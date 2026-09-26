"""Checks for the factorisation lemmas P and P'.
(P)  for idempotent ideals X,Y,Z and c in Y.Z: the class of (x,y,c) in X(x)Y(x)Z depends only on (xy,c).
(P') for c in X.Y in the first slot: the class of (c,y,z) depends only on (c,yz).
(A)  when I = D n E is idempotent: T_4 = E(x)D(x)E(x)D has |T_4| = |I(x)I| and mu_4 : T_4 -> T_3 bijective ... (tower data)."""
import itertools as it, sys
from monoids_small import monoids
from topjoin_monoid import idem_two_sided
from tensor_multi import multitensor

def prod(T,A,B): return frozenset(T[a][b] for a in A for b in B)

def check(nmax):
    P_fail=P2_fail=0; tested=0
    for n in range(2,nmax+1):
        for i,T in enumerate(monoids(n)):
            ideals=[D for D in idem_two_sided(T) if D and len(D)<n]  # proper, nonempty
            for X in ideals:
                for Y in ideals:
                    for Z in ideals:
                        uf=multitensor(T,[X,Y,Z]); tested+=1
                        YZ=prod(T,Y,Z); XY=prod(T,X,Y)
                        # (P): group tuples by (xy, c) for c in YZ
                        rep={}
                        for x in X:
                            for y in Y:
                                for c in Z:
                                    if c in YZ:
                                        k=(T[x][y],c); r=uf.find((x,y,c))
                                        if k in rep and rep[k]!=r: P_fail+=1; print("P fails",n,i,sorted(X),sorted(Y),sorted(Z),k); break
                                        rep[k]=r
                        rep={}
                        for c in X:
                            if c not in XY: continue
                            for y in Y:
                                for z in Z:
                                    k=(c,T[y][z]); r=uf.find((c,y,z))
                                    if k in rep and rep[k]!=r: P2_fail+=1; print("P' fails",n,i,sorted(X),sorted(Y),sorted(Z),k); break
                                    rep[k]=r
    print("triples tested",tested,"P failures",P_fail,"P' failures",P2_fail)

if __name__=='__main__':
    check(int(sys.argv[1]) if len(sys.argv)>1 else 5)

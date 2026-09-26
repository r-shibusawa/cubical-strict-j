"""Three-fold multiplicativity test: for idempotent two-sided ideals A,B,C of a finite monoid,
are A(x)B(x)C -> AB(x)C and A(x)B(x)C -> A(x)BC bijections?  (Two-fold A(x)B -> AB is NOT.)"""
import sys, itertools as it
from monoids_small import monoids
from topjoin_monoid import idem_two_sided
from tensor_multi import mult_map_bijective

def run(nmin,nmax):
    fails=0; total=0
    for n in range(nmin,nmax+1):
        for i,Tm in enumerate(monoids(n)):
            ideals=[D for D in idem_two_sided(Tm) if D]
            for A in ideals:
                for B in ideals:
                    for C in ideals:
                        total+=1
                        l=mult_map_bijective(Tm,[A,B,C],0); r=mult_map_bijective(Tm,[A,B,C],1)
                        if not (l[0] and r[0]):
                            fails+=1; print("FAIL monoid%d#%d A=%s B=%s C=%s left=%s right=%s"%(n,i,sorted(A),sorted(B),sorted(C),l,r),flush=True)
        print("order",n,"done; triples so far",total,"fails",fails,flush=True)
    print("TOTAL triples",total,"fails",fails,flush=True)

if __name__=='__main__':
    run(int(sys.argv[1]),int(sys.argv[2]))

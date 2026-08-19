"""el(cube^3/A4-type) via the master collage formula (O20).

  el = hocolim( * <- B(Z/3) -> B(A4-type) )
(the four lines form one orbit with trivial residual, so the
stratified sieve quotient is contractible; the comma is the Borel
construction of the transitive action on the four lines, i.e.,
B(Z/3)).  Since H~*(B Z/3; F2) = 0, the F2-cohomology of el equals
that of B(A4-type): computed = [1, 0, 1, 2, 1] in degrees 0..4,
matching the invariant-theory prediction (H^2 spanned by
x^2+xy+y^2 etc.).  This machine-verifies the non-domination
hypothesis for the A4-type base: el is non-contractible while
el(Sigma/N) is contractible.
"""
import sys, itertools as it, collections
sys.path.insert(0,'scripts')
import el_betti as eb

# A4-type as signed perms, indexed
n=3
ELEMS=[]
for p in it.permutations(range(n)):
    for s in it.product((0,1),repeat=n):
        ELEMS.append((p,s))
ID=(tuple(range(n)),(0,)*n)
def mm(a,b):
    (p1,s1),(p2,s2)=a,b
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i]^s2[p1[i]] for i in range(n)))
def close(g):
    S={ID}|set(g)
    dq=collections.deque(S)
    while dq:
        x=dq.popleft()
        for y in list(S):
            for z in (mm(x,y),mm(y,x)):
                if z not in S: S.add(z);dq.append(z)
    return S
nb=((0,1,2),(1,1,0)); n011=((0,1,2),(0,1,1)); rot=((1,2,0),(0,0,0))
A4=sorted(close([nb,n011,rot]))
gi={h:i for i,h in enumerate(A4)}
mulA={(gi[a],gi[b]):gi[mm(a,b)] for a in A4 for b in A4}
GA=list(range(12))
# Z/3 = <rot> inside
Z3elems=[ID,rot,mm(rot,rot)]
gz={h:i for i,h in enumerate(Z3elems)}
mulZ={(gz[a],gz[b]):gz[mm(a,b)] for a in Z3elems for b in Z3elems}
GZ=list(range(3))
inc={gz[h]:gi[h] for h in Z3elems}   # Z/3 -> A4

D=5
print("building bar complexes (D=%d)..."%D, flush=True)
barA=eb.bar_complex(GA,mulA,D)
barZ=eb.bar_complex(GZ,mulZ,D)
print("H^*(B Z/3; F2):", barZ[0].betti()[:D], flush=True)
print("H^*(B A4-12; F2):", barA[0].betti()[:D], flush=True)
# el(cube^3/A4) = hocolim( * <- B(Z/3) -> B(A4) )
# A = point complex
Apt = eb.Cx([1]+[0]*D, [[0] if k==0 else [] for k in range(D)])
# fix: point complex dims [1,0,0,...]; d[0] = [0] (one column, zero map)
Apt = eb.Cx([1]+[0]*D, [[0]]+[[] for _ in range(D-1)])
# cochain maps: C^*(pt) -> C^*(BZ3): unit in degree 0
fcols=[[ (1<<0) ]]+[[] for _ in range(D)]
fmap=eb.Map(fcols)
# C^*(BA4) -> C^*(BZ3): restriction along inclusion
gmap=eb.induced_map(GZ,mulZ,GA,mulA,inc,barZ,barA,D)
X = eb.pushout_cx(Apt, barA[0], barZ[0], fmap, gmap)
print("H^*(el(cube^3/A4-type); F2):", X.betti()[:D], flush=True)

import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

# DM(4) on generators d,a,t,s : L_4 = {0,1}^8, 256 points
N, leq, rho = build(4)
D = gen(0,4,N); A = gen(1,4,N); T = gen(2,4,N); S = gen(3,4,N)
def nt(m): return NOT(m,N,rho)
def F(d,a,t): return (d & nt(t)) | (a & t) | (d & a)

lhs = F(D, A, T & S)
rhs = F(D, F(D,A,T), S)
print("flow identity F(d,a,t∧s) == F(d,F(d,a,t),s):", lhs == rhs)

# dual (for Z_A / t-raising toward t=1): G(d,a,t) with roles swapped =
# F(a,d,¬t); t-raising t∨s should compose dually:
lhs2 = F(D, A, T | S)
rhs2 = F(F(D,A,T), A, S)   # candidate: flow from the a-side
print("dual identity F(d,a,t∨s) == F(F(d,a,t),a,s):", lhs2 == rhs2)

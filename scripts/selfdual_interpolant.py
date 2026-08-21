"""The self-dual interpolant (O21).

  chi (u,v,t) = (u & ~t) | (t & v) | (u & v)
  chi*(u,v,t) = ~chi(~u,~v,t) = (u | t) & (~t | v) & (u | v)
  I(u,v,t)    = mu(chi, chi*, u),  mu(a,b,c) = ab | ac | bc

Claims (as identities of the free De Morgan algebra F_DM(3) on
u, v, t -- hence valid in every quotient variety, i.e. on the
Kleene and Boolean sites too):
  (1) I(u,v,0) = u        (2) I(u,v,1) = v
  (3) I(~u,~v,t) = ~I(u,v,t)      [self-duality in (u,v)]

Free DM algebra model: elements = monotone {0,1}-functions on the
literal cube L_3 = {0,1}^6 (coordinate pairs (x, x')); generator
x_i = projection to 2i, its negation uses rho = swap within each
pair: (~f)(p) = 1 - f(rho p).  Two terms are equal in F_DM iff
they agree on all of L_3.  We also verify monotonicity of I.
"""
import itertools

PAIRS = 3
PTS = list(itertools.product((0,1), repeat=2*PAIRS))
def rho(p): 
    q = list(p)
    for i in range(PAIRS): q[2*i], q[2*i+1] = 1-q[2*i+1], 1-q[2*i]
    return tuple(q)
def gen(i):  return {p: p[2*i] for p in PTS}
def neg(f):  return {p: 1 - f[rho(p)] for p in PTS}
def AND(f,g): return {p: f[p] & g[p] for p in PTS}
def OR(f,g):  return {p: f[p] | g[p] for p in PTS}
def const(c): return {p: c for p in PTS}

u, v, t = gen(0), gen(1), gen(2)
def chi(u,v,t):  return OR(OR(AND(u,neg(t)), AND(t,v)), AND(u,v))
def chis(u,v,t): return neg(chi(neg(u),neg(v),t))
def mu(a,b,c):   return OR(OR(AND(a,b), AND(a,c)), AND(b,c))
def I(u,v,t):    return mu(chi(u,v,t), chis(u,v,t), u)

# (1),(2): substitute t = 0/1 -- as algebra maps: evaluate I at points
# with the t-pair forced; implement substitution by precomposition:
# t := const 0 means replace gen(2) by const(0) in the term tree; easiest:
# rebuild I as a function of abstract arguments:
I0 = I(u, v, const(0)); I1 = I(u, v, const(1))
print("I(u,v,0) == u :", I0 == u)
print("I(u,v,1) == v :", I1 == v)
Idual = I(neg(u), neg(v), t)
print("I(~u,~v,t) == ~I(u,v,t):", Idual == neg(I(u,v,t)))
# monotonicity of I (it is an element of F_DM(3) built by the
# operations, hence automatically monotone; verify anyway)
mono = all(I(u,v,t)[p] <= I(u,v,t)[q]
           for p in PTS for q in PTS
           if all(a <= b for a,b in zip(p,q)))
print("I monotone on L_3:", mono)
# also: chi alone is NOT self-dual (the reason I is needed)
print("chi self-dual (expected False):",
      chi(neg(u),neg(v),t) == neg(chi(u,v,t)))

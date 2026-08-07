import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

# (i) Z_D and Z_A are substitution-closed (equational: automatic), but
# verify the *class-level* disjointness and end-membership once more at
# level 1-2, plus: id-cell (generators) not in Z; ends inside Z_D/Z_A.
for n in (1, 2):
    N, leq, rho = build(n)
    dm = monotone_masks(N, leq)
    notf = {m: NOT(m, N, rho) for m in dm}
    FULL = (1 << N) - 1
    def F(d, a, t): return (d & notf[t]) | (a & t) | (d & a)
    both = 0; d_at_t1 = 0; a_at_t0 = 0
    for t in dm:
        for d in dm:
            for a in dm:
                F1, F2 = F(d, a, t), F(d, notf[a], t)
                zd, za = F1 == F2, F1 == notf[F2]
                if zd and za: both += 1
                if zd and t == FULL: d_at_t1 += 1
                if za and t == 0: a_at_t0 += 1
    print(f"level {n}: Z_D∩Z_A={both}, Z_D∩{{t=1}}={d_at_t1}, Z_A∩{{t=0}}={a_at_t0}")
# (ii) generators (id-cell) not in Z, any level via DM(3) generic:
N, leq, rho = build(3)
D, A, T = gen(0,3,N), gen(1,3,N), gen(2,3,N)
notf3 = lambda m: NOT(m, N, rho)
F1 = (D & notf3(T)) | (A & T) | (D & A)
F2 = (D & notf3(T)) | (notf3(A) & T) | (D & notf3(A))
print("id-cell in Z_D:", F1 == F2, " in Z_A:", F1 == notf3(F2))

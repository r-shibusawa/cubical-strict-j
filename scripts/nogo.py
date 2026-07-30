#!/usr/bin/env python3
"""No-go theorem and median coherence: the verification record.

(1) Forcing census over DM(2): unique fillers (singleton fibers)
    force values on 42 of the 54 non-singleton fibers via 121
    endo-substitutions, with 142 pairwise conflicts; the printed
    core is m = -x /\ y /\ -y, whose transports under x:=y and
    x:=x/\-x are the top and the bottom of one two-element fiber.
(2) Exhaustive search: backtracking with propagation over all
    2^38 * 4^16 sections against the same 121 substitutions finds
    no natural section (independent re-proof).
(3) Median identities: the fiber-coordinate formula for chi and the
    four face identities of the iterated median cylinder
    Xi = chi_l(chi_k(a,b), cyl c) verified exactly on a rank-two
    fiber of DM(2).
See docs/NoGo.md for the recorded outputs; the ad-hoc scripts are
reproduced in the repository history (2026-07-31/08-01).
"""

#!/usr/bin/env python3
"""The reversal quotient L = interval/(x ~ -x): verification record.

(1) Freeness: 0 self-dual elements in DM(m) and KL(m) for m <= 3
    (the one-line proof: the all-(0,1) point is fixed by the point
    involution while Boolean values are not).
(2) No rescue terms: no t in DM(x,z) or KL(x,z) is reversal-
    compatible, restricts to the generator at z=0, and is constant
    at z=1 - the cartesian connection trick has no symmetric analogue.
(3) Reachability census: symmetric squares number 60 (De Morgan),
    32 (Kleene), 8 (Boolean); the face graph on symmetric lines
    leaves the [x]-component isolated in all three theories, while
    the connection-degenerate line connects symmetrically to the
    constants ((x /\ -x) /\ -z is exactly symmetric).
(4) L-cell census: 62 squares over the generator, 44 z-varying,
    12 contracting it non-symmetrically.
See docs/ReversalQuotient.md for recorded outputs; the ad-hoc
scripts are reproduced in the repository history (2026-08-01/02).
"""

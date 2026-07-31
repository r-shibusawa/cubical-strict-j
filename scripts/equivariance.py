#!/usr/bin/env python3
"""Reversal is unrepairable: the verification record.

(1) Automorphism groups: Aut of the 2-cube is the hyperoctahedral
    group of order 8 in both the De Morgan (coordinate permutations
    of the literal cube commuting with the negation involution) and
    Kleene (all poset automorphisms of the unmixed poset) cases.
(2) Freeness/el: 0 self-dual cells through m <= 3 (see
    scripts/reversal.py), whence N el(I^k/H) = BH for
    reversal-containing H - the overshoot witness.
(3) Non-automatic equivariance: (-x) /\ e != -(x /\ e), so the
    connection-contraction argument yields symmetric-group
    equivariance only.
(4) Crown no-go certificates: for (n,a,b) = (3,2,4) the crown-region
    constraint problems - 768 points (De Morgan), 312 points
    (Kleene), domains of size 4, order constraints from the product
    of the crown subposet with the negative-literal cube - are
    exhaustively UNSAT; fiber incomparability and three-branch
    disjointness checked directly. The Boolean case stabilizes
    (arbitrary vertex actions admit a set-level section).
See docs/Unrepairable.md for recorded outputs; ad-hoc scripts are
in the repository history (2026-08-02/03).
"""

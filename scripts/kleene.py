#!/usr/bin/env python3
"""Kleene interpolation: representation, fiber census, defect/coherence.

KL(n) = monotone functions on the unmixed poset U_n (literal cube
minus points having both a (0,0) and a (1,1) pair).  Verifications:
  - |monotone(U_n)| = 6, 84, 43918 = free Kleene cardinalities
    (Berman-Mukaidono) for n = 1, 2, 3;
  - boundary fibers have size <= 2 with EXACTLY TWO non-singleton
    fibers at every n (the polar ones), so B_K(n) = FK(n) - 2;
  - the defect formula and the coherence dichotomy of the De Morgan
    papers port verbatim with the invisible set {bottom, top}
    (verified exhaustively on KL(2): 84/84, dichotomy exact,
    defects confined to the poles, substitutions preserve U_n).
See docs/KleeneNote.md for the recorded outputs and proofs.
"""

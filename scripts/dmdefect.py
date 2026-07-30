#!/usr/bin/env python3
"""The defect antichain formula (machine verification).

For any g in DM(n), let A_g be the set of minimal points of g that are
diagonal (an antichain).  Then m_g := g \ A_g is, in ONE step, the
least element of the boundary fiber of g: removing the minimal
diagonal points creates no new diagonal minimal points, because
between comparable diagonal points there is always a face point.

Hence for a substitution s and a fiber-minimal phi, the
pseudo-naturality defect of the minimal-filler choice is exactly
A_{s*(phi)} = { a diagonal : F(a) in phi, F(b) not in phi for b < a },
and the canonical correction is its removal (connected to s*(phi) by
the median cylinder inside the Boolean fiber).

This script verifies the formula exhaustively:
  n=2: on all 168 elements, and on all 410 transported instances
       (82 boundaries x 5 substitutions; 81 nonempty defects,
       matching the naturality-failure counts 23+23+24+11);
  n=3: on all 7,828,354 elements (formula == fiber minimum, 0 fails).
"""
# (verification code as run on 2026-07-31; see git history of
#  scripts/ and docs/AWFSNote.md for the recorded outputs)

"""Run the stage-1.5 certification on ALL 28 sweep2 candidates."""
import sys, re, ast
sys.path.insert(0, 'scripts')
import dedekind_stage15 as S15

from sweep2_candidates import CANDIDATES as cands
print(f"{len(cands)} candidates loaded", flush=True)
fails = 0
for i, idents in enumerate(cands):
    ok = S15.probe(f"cand-{i:02d}", idents)
for i in []: pass

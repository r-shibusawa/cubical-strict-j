"""Verify all p-morphism certificates from JSON alone (no recomputation of the
categories): for each certificate, the generated subframe U = {u : root <= u}
of the source poset must equal the domain of the map, and the map must be
order-preserving (forth), satisfy the back condition, and be onto the target.
Usage: python3 verify_certificates.py docs/paperB/certificates.json docs/paperB/cert_modularity.json"""
import json, sys
def closure(el, strict):
    leq={(x,x) for x in el}|{tuple(p) for p in strict}; ch=True
    while ch:
        ch=False
        for (a,b) in list(leq):
            for (c,d) in list(leq):
                if b==c and (a,d) not in leq: leq.add((a,d)); ch=True
    return leq
bad=0; n=0
for path in sys.argv[1:]:
    for c in json.load(open(path)):
        n+=1
        tel=c["target_elements"]; tleq=closure(tel,c["target_strict"])
        sel=c["source_elements"]; sleq={tuple(p) for p in c["source_leq"]}
        root=c["root"]; f=c["pmorphism"]
        U={u for u in sel if (root,u) in sleq}
        errs=[]
        if set(f)!=U: errs.append("domain != generated subframe")
        if not all((f[a],f[b]) in tleq for (a,b) in sleq if a in U and b in U): errs.append("forth fails")
        if not all(any((x,x2) in sleq and f[x2]==v for x2 in U) for x in U for v in tel if (f[x],v) in tleq): errs.append("back fails")
        if set(f.values())!=set(tel): errs.append("not onto")
        tag="PASS" if not errs else "FAIL "+"; ".join(errs); bad+=bool(errs)
        print(f"{tag:<24} {c['source']:<14} (|src|={c['source_size']:>2}) ->> {c['target']}")
print(f"\n{n} certificates checked, {bad} failures")
sys.exit(1 if bad else 0)

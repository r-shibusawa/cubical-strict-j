"""Experiment: joins of topologies on finite posets inside Same(Presh(P)).

For a finite poset P the topologies are the subsets Y (rigid): Sh_Y = presheaves
X with X ~= a_Y X, where a_Y X(p) = lim_{y in Y, y <= p} X(y) (right Kan extension
of the restriction to Y), and W_Y = {f : f_y bijective for all y in Y}.
The join topology of Y, Y' is Y n Y'.  Question: is W_Y v W_{Y'} = W_{Y n Y'}?
Sufficient: the alternating chain X -> a_Y X -> a_{Y'} a_Y X -> ... reaches a
(Y n Y')-sheaf after finitely many steps (each step is a unit, in W_Y or W_{Y'}).
This script builds random finite presheaves and reports the number of steps.
"""
import itertools as it, random, sys

def posets_on(n):
    pairs=[(i,j) for i in range(n) for j in range(n) if i<j]
    seen=set(); out=[]
    for bits in it.product([0,1],repeat=len(pairs)):
        rel={(i,i) for i in range(n)}|{p for p,b in zip(pairs,bits) if b}
        if all(((a,c) in rel) for (a,b) in rel for (b2,c) in rel if b==b2):
            key=min(tuple(sorted((s[a],s[b]) for (a,b) in rel)) for s in it.permutations(range(n)))
            if key not in seen: seen.add(key); out.append(rel)
    return out

class Presheaf:
    def __init__(self,P,leq,val,res):
        self.P=P; self.leq=leq; self.val=val; self.res=res
    def check(self):
        for p in self.P:
            for q in self.P:
                if self.leq(q,p):
                    for x in self.val[p]: assert self.res[(q,p)][x] in self.val[q]
                    for r in self.P:
                        if self.leq(r,q):
                            for x in self.val[p]:
                                assert self.res[(r,p)][x]==self.res[(r,q)][self.res[(q,p)][x]]
        return True

def random_presheaf(P,leq,rng,maxsize=3):
    U=list(range(6)); R={u:rng.choice(U) for u in U}
    h={p:sum(1 for q in P if leq(q,p) and q!=p) for p in P}   # strictly monotone height
    def Rpow(k,u):
        for _ in range(k): u=R[u]
        return u
    val={p:set(rng.sample(U,rng.randint(0,maxsize))) for p in P}
    for p in P:
        for q in P:
            if leq(q,p) and q!=p:
                val[q]|={Rpow(h[p]-h[q],x) for x in val[p]}
    val={p:sorted(v) for p,v in val.items()}
    res={(q,p):{x:Rpow(h[p]-h[q],x) for x in val[p]} for p in P for q in P if leq(q,p)}
    X=Presheaf(P,leq,val,res); X.check(); return X

def ran(X,Y):
    P,leq=X.P,X.leq; val={}
    for p in P:
        Yp=sorted(y for y in Y if leq(y,p)); elems=[]
        for choice in it.product(*[X.val[y] for y in Yp]):
            f=dict(zip(Yp,choice))
            if all(X.res[(y,y2)][f[y2]]==f[y] for y in Yp for y2 in Yp if leq(y,y2)):
                elems.append(tuple(sorted(f.items())))
        val[p]=elems
    res={}
    for p in P:
        for q in P:
            if leq(q,p):
                Yq={y for y in Y if leq(y,q)}
                res[(q,p)]={e:tuple((y,x) for (y,x) in e if y in Yq) for e in val[p]}
    Z=Presheaf(P,leq,val,res); Z.check(); return Z

def unit_bijective(X,Y):
    Z=ran(X,Y)
    for p in X.P:
        Yp=[y for y in Y if X.leq(y,p)]
        img={tuple(sorted((y,X.res[(y,p)][x]) for y in Yp)) for x in X.val[p]}
        if len(img)!=len(X.val[p]) or len(img)!=len(Z.val[p]): return False
    return True

def main(seed=1,trials=25,maxn=4,maxsteps=8):
    rng=random.Random(seed); worst=0; results={}
    for n in range(1,maxn+1):
        for rel in posets_on(n):
            P=list(range(n)); leq=lambda q,p,rel=rel:(q,p) in rel
            subsets=[frozenset(s) for r in range(n+1) for s in it.combinations(P,r)]
            for _ in range(trials):
                X=random_presheaf(P,leq,rng)
                for Y in subsets:
                    for Y2 in subsets:
                        Z=X; k=0
                        while not unit_bijective(Z,Y&Y2):
                            Z=ran(Z,Y if k%2==0 else Y2); k+=1
                            if k>maxsteps: break
                        if k>maxsteps:
                            print("NO STABILIZATION", n, sorted(rel), sorted(Y), sorted(Y2), X.val); return
                        worst=max(worst,k); results[(n,k)]=results.get((n,k),0)+1
    print("all alternating chains reach a (Y n Y')-sheaf; worst number of steps:", worst)
    for key in sorted(results): print("  n=%d steps=%d : %d cases"%(key[0],key[1],results[key]))

if __name__=='__main__':
    main()

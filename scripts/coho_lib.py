import numpy as np

def lead_of(v):
    for w in range(len(v)-1,-1,-1):
        if v[w]: return (w<<6)+int(v[w]).bit_length()-1
    return -1

class F2Space:
    def __init__(self): self.piv={}
    def reduce(self,v):
        v=v.copy()
        while True:
            l=lead_of(v)
            if l<0: return None
            if l in self.piv: v=v^self.piv[l]
            else: return l,v
    def add(self,v):
        r=self.reduce(v)
        if r: self.piv[r[0]]=r[1];return True
        return False

def bits(nvar): return (nvar+63)//64
def setbit(v,i): v[i>>6]^=np.uint64(1<<(i&63))
def getbit(v,i): return int((v[i>>6]>>np.uint64(i&63))&np.uint64(1))

def kernel_basis(eqspace,nvar,W):
    rows=dict(eqspace.piv)
    leads=sorted(rows.keys())
    # full RREF: ascending; eliminate lower pivot bits from each row
    for l in leads:
        v=rows[l]
        changed=True
        while changed:
            changed=False
            for b in leads:
                if b>=l: break
                if getbit(v,b):
                    v=v^rows[b];changed=True
        rows[l]=v
    free=[i for i in range(nvar) if i not in rows]
    out=[]
    for f in free:
        v=np.zeros(W,dtype=np.uint64);setbit(v,f)
        for l in leads:
            r=rows[l].copy();setbit(r,l)
            dot=int(sum(int(t).bit_count() for t in np.bitwise_and(r,v)))&1
            if dot: setbit(v,l)
        out.append(v)
    return out

def cocycle_data(mul,m):
    nvar=m*m; W=bits(nvar)
    eq=F2Space()
    for g in range(m):
        for h in range(m):
            for k in range(m):
                v=np.zeros(W,dtype=np.uint64)
                for i in (h*m+k, mul[g][h]*m+k, g*m+mul[h][k], g*m+h):
                    setbit(v,i)
                if v.any(): eq.add(v)
    kernel=kernel_basis(eq,nvar,W)
    cob=[]
    for j in range(m):
        v=np.zeros(W,dtype=np.uint64)
        for g in range(m):
            for h in range(m):
                val=(1 if h==j else 0)^(1 if mul[g][h]==j else 0)^(1 if g==j else 0)
                if val: setbit(v,g*m+h)
        cob.append(v)
    return nvar,W,kernel,cob

def is_cocycle(v,mul,m):
    for g in range(m):
        for h in range(m):
            for k in range(m):
                s=getbit(v,h*m+k)^getbit(v,mul[g][h]*m+k)^getbit(v,g*m+mul[h][k])^getbit(v,g*m+h)
                if s: return False
    return True

def cup(c1,c2,m,W):
    v=np.zeros(W,dtype=np.uint64)
    for g in range(m):
        for h in range(m):
            if c1[g]&c2[h]: setbit(v,g*m+h)
    return v

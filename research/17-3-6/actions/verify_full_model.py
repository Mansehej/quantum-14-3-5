#!/usr/bin/env python3
"""Independently verify a CryptoMiniSat model for the complete [[17,3,6]] instance."""
from __future__ import annotations
import argparse,itertools,json
from pathlib import Path
N=17;K=3

def parse_assignment(path:Path):
    vals={};sat=False
    for line in path.read_text(errors='replace').splitlines():
        if line.startswith('s ') and 'SATISFIABLE' in line and 'UNSAT' not in line:sat=True
        if line.startswith('v '):
            for z in line[2:].split():
                v=int(z)
                if v:vals[abs(v)]=v>0
    if not sat:raise ValueError('no SAT model')
    if any(v not in vals for v in range(1,179)):raise ValueError('original variables missing')
    return vals

def rank(rows,width):
    b=[0]*width;r=0
    for x in rows:
        while x:
            p=x.bit_length()-1
            if b[p]:x^=b[p]
            else:b[p]=x;r+=1;break
    return r

def nullspace(rows,width):
    a=rows[:];piv=[];r=0
    for c in range(width):
        s=next((i for i in range(r,len(a)) if (a[i]>>c)&1),None)
        if s is None:continue
        a[r],a[s]=a[s],a[r]
        for i in range(len(a)):
            if i!=r and ((a[i]>>c)&1):a[i]^=a[r]
        piv.append(c);r+=1
    free=[c for c in range(width) if c not in set(piv)];out=[]
    for f in free:
        x=1<<f
        for row,p in zip(a[:r],piv):
            if (row>>f)&1:x|=1<<p
        out.append(x)
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('solver_output',type=Path);ap.add_argument('--json',default='verified.json',type=Path);a=ap.parse_args();model=parse_assignment(a.solver_output)
    edge={};q=1
    for i in range(N):
        for j in range(i+1,N):edge[(i,j)]=q;q+=1
    pv={}
    for r in range(K):
        for i in range(K,N):pv[(r,i)]=q;q+=1
    G=[[0]*N for _ in range(N)]
    for (i,j),v in edge.items():G[i][j]=G[j][i]=int(model[v])
    P=[[0]*N for _ in range(K)]
    for r in range(K):
        P[r][r]=1
        for i in range(K,N):P[r][i]=int(model[pv[(r,i)]])
    prows=[sum(P[r][i]<<i for i in range(N)) for r in range(K)];assert rank(prows,N)==3
    checked=0;minimum=99;bad=[]
    for w in range(6):
        for S in itertools.combinations(range(N),w):
            x=sum(1<<i for i in S)
            for lam in range(8):
                if not x and not lam:continue
                z=0
                for i in range(N):
                    bit=0
                    for j in S:bit^=G[i][j]
                    for r in range(K):bit^=((lam>>r)&1)&P[r][i]
                    z|=bit<<i
                wt=(x|z).bit_count();minimum=min(minimum,wt);checked+=1
                if wt<6:bad.append((x,z,lam,wt))
    if checked!=75215 or bad:raise AssertionError({'checked':checked,'bad':bad[:20]})
    ker=nullspace(prows,N);assert len(ker)==14;H=[]
    for x in ker:
        z=0
        for i in range(N):
            bit=0
            for j in range(N):bit^=G[i][j]&((x>>j)&1)
            z|=bit<<i
        H.append(x|(z<<N))
    assert rank(H,34)==14
    mask=(1<<N)-1
    def symp(u,v):return (((u&mask)&(v>>N)).bit_count()+((u>>N)&(v&mask)).bit_count())&1
    assert all(symp(u,v)==0 for u in H for v in H)
    out={'verified':True,'n':17,'k':3,'distance_at_least':minimum,'checked':checked,'Gamma':G,'P':P,'H_XZ_rows':[f"{''.join(str((h>>i)&1) for i in range(N))}|{''.join(str((h>>(N+i))&1) for i in range(N))}" for h in H]}
    a.json.write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independently verify a CryptoMiniSat model for a fixed-P graph instance."""
from __future__ import annotations
import argparse,itertools,json
N=17
EDGES=[(i,j) for i in range(N) for j in range(i+1,N)]

def parse_counts(s):
    c=[int(x) for x in s.replace(',',' ').split()]
    assert len(c)==8 and sum(c)==17
    return c

def parse_model(path):
    vals={}
    for line in open(path,errors='ignore'):
        if line.startswith('v '):
            for z in line[2:].split():
                v=int(z)
                if v:vals[abs(v)]=v>0
    return vals

def main():
    ap=argparse.ArgumentParser();ap.add_argument('solver_output');ap.add_argument('--counts',required=True);ap.add_argument('--json',default='verified.json');a=ap.parse_args()
    txt=open(a.solver_output,errors='ignore').read()
    if 's SATISFIABLE' not in txt:
        raise SystemExit('solver output is not SAT')
    vals=parse_model(a.solver_output);g=[vals.get(i+1,False) for i in range(136)]
    counts=parse_counts(a.counts);P=[v for v,n in enumerate(counts) for _ in range(n)]
    rows=[0]*N
    for e,(u,v) in enumerate(EDGES):
        if g[e]:rows[u]|=1<<v;rows[v]|=1<<u
    bad=[];minimum=99
    pwords=[sum((((lam&P[i]).bit_count()&1)<<i) for i in range(N)) for lam in range(8)]
    for w in range(6):
        for S in itertools.combinations(range(N),w):
            aa=sum(1<<i for i in S);ga=0
            for i in S:ga^=rows[i]
            for lam in range(8):
                if not aa and not lam:continue
                wt=(aa|(ga^pwords[lam])).bit_count();minimum=min(minimum,wt)
                if wt<6:bad.append({'support':S,'lambda':lam,'weight':wt})
    out={'verified':not bad,'minimum_weight':minimum,'bad_count':len(bad),'counts':counts,'P_columns':P,'Gamma_upper':[int(x) for x in g]}
    json.dump(out,open(a.json,'w'),indent=2);print(json.dumps(out,indent=2))
    if bad:raise SystemExit(1)
if __name__=='__main__':main()

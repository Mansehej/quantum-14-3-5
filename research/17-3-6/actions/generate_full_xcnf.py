#!/usr/bin/env python3
"""Generate the complete pure [[17,3,6]] graph-code XCNF instance."""
from __future__ import annotations
import argparse,itertools
from pathlib import Path
N=17;K=3;D=6

def build_original_variables():
    q=1;edge={}
    for i in range(N):
        for j in range(i+1,N):edge[(i,j)]=q;q+=1
    pv={}
    for r in range(K):
        for i in range(K,N):pv[(r,i)]=q;q+=1
    assert q-1==178
    return edge,pv,q

def edge_id(edge,i,j):
    return edge[(i,j) if i<j else (j,i)]

def generate(path:Path,smoke:int|None=None):
    edge,pv,next_var=build_original_variables();true_var=next_var;next_var+=1
    body=path.with_suffix(path.suffix+'.body');xors=0;cnf=1;ncons=0
    with body.open('w',encoding='ascii',buffering=1<<20) as out:
        out.write(f'c fixed true {true_var}\n{true_var} 0\n');stop=False
        for w in range(D):
            need=D-w
            for S in itertools.combinations(range(N),w):
                SS=set(S);outside=[i for i in range(N) if i not in SS]
                for lam in range(8):
                    if w==0 and lam==0:continue
                    ncons+=1;ys=[]
                    for i in outside:
                        y=next_var;next_var+=1;ys.append(y);lits=[y]+[edge_id(edge,i,j) for j in S];constant=0
                        for r in range(K):
                            if not ((lam>>r)&1):continue
                            if i<K:constant^=int(i==r)
                            else:lits.append(pv[(r,i)])
                        if constant==0:lits.append(true_var)
                        out.write('x'+' '.join(map(str,lits))+' 0\n');xors+=1
                    for omit in itertools.combinations(range(len(ys)),need-1):
                        om=set(omit);cl=[y for q,y in enumerate(ys) if q not in om];assert len(cl)==12
                        out.write(' '.join(map(str,cl))+' 0\n');cnf+=1
                    if smoke is not None and ncons>=smoke:stop=True;break
                if stop:break
            if stop:break
    nvars=next_var-1
    with path.open('w',encoding='ascii',buffering=1<<20) as dst:
        dst.write('c complete pure [[17,3,6]] graph-code search\n')
        dst.write('c vars 1..136 Gamma; 137..178 P rows columns 3..16\n')
        dst.write(f'c true {true_var}; constraints {ncons}\n')
        dst.write(f'p cnf {nvars} {xors+cnf}\n')
        with body.open() as src:
            while z:=src.read(1<<20):dst.write(z)
    body.unlink();return {'variables':nvars,'clauses':xors+cnf,'xor':xors,'cnf':cnf,'constraints':ncons}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);ap.add_argument('--smoke',type=int);a=ap.parse_args();print(generate(a.output,a.smoke))
if __name__=='__main__':main()

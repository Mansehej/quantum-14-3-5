#!/usr/bin/env python3
"""Generate an exact fixed-P XCNF instance for a pure [[17,3,6]] graph code."""
from __future__ import annotations
import argparse,itertools
from pathlib import Path
N=17;D=6

def parse_counts(text:str)->list[int]:
    c=[int(x) for x in text.replace(',', ' ').split()]
    if len(c)!=8 or sum(c)!=17 or min(c)<0:
        raise ValueError('counts must be 8 nonnegative integers summing to 17')
    return c

def columns(counts):
    return [v for v,n in enumerate(counts) for _ in range(n)]

def edge_id(i,j):
    if i>j:i,j=j,i
    return 1 + sum(16-u for u in range(i)) + (j-i-1)

def generate(out:Path,counts:list[int],smoke:int|None=None):
    P=columns(counts)
    pwords=[sum((((lam&P[i]).bit_count()&1)<<i) for i in range(N)) for lam in range(8)]
    if min(x.bit_count() for x in pwords[1:])<6:
        raise ValueError('logical type has distance below 6')
    true_var=137;next_var=138;body=out.with_suffix(out.suffix+'.body');xors=0;cnf=1;ncons=0
    with body.open('w',encoding='ascii',buffering=1<<20) as f:
        f.write(f'c fixed true {true_var}\n{true_var} 0\n')
        stop=False
        for w in range(D):
            need=D-w
            for S in itertools.combinations(range(N),w):
                SS=set(S);outside=[i for i in range(N) if i not in SS]
                for lam in range(8):
                    if w==0 and lam==0:continue
                    ncons+=1;ys=[]
                    for i in outside:
                        y=next_var;next_var+=1;ys.append(y);lits=[y]+[edge_id(i,j) for j in S]
                        constant=(lam&P[i]).bit_count()&1
                        if constant==0:lits.append(true_var)
                        f.write('x'+' '.join(map(str,lits))+' 0\n');xors+=1
                    for omit in itertools.combinations(range(len(ys)),need-1):
                        om=set(omit);cl=[y for q,y in enumerate(ys) if q not in om]
                        assert len(cl)==12
                        f.write(' '.join(map(str,cl))+' 0\n');cnf+=1
                    if smoke is not None and ncons>=smoke:stop=True;break
                if stop:break
            if stop:break
    nvars=next_var-1
    with out.open('w',encoding='ascii',buffering=1<<20) as g:
        g.write(f'c fixed-P pure [[17,3,6]] search counts={counts}\n')
        g.write('c original variables 1..136 = Gamma upper triangle lexicographic\n')
        g.write(f'c true variable {true_var}; constraints {ncons}\n')
        g.write(f'p cnf {nvars} {xors+cnf}\n')
        with body.open() as f:
            while z:=f.read(1<<20):g.write(z)
    body.unlink()
    return {'counts':counts,'P':P,'variables':nvars,'xor_clauses':xors,'cnf_clauses':cnf,'constraints':ncons}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);ap.add_argument('--counts',required=True);ap.add_argument('--smoke',type=int);a=ap.parse_args();print(generate(a.output,parse_counts(a.counts),a.smoke))
if __name__=='__main__':main()

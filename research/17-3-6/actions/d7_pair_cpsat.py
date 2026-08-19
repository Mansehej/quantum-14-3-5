#!/usr/bin/env python3
"""Exact CP-SAT feasibility test for the distance-seven parent pairing.

Necessary profile-6 situation:
- E is an extremal additive self-dual length-17 parent;
- e=XXX is the unique weight-three global-shadow word in one parent-shadow coset;
- V is one of the six forced type-0 translated logical cosets;
- e+V has the forced type-0 logical enumerator.

The variables are exact three-coordinate orbit split enumerators f, v, h.
All coefficients are integers. A FEASIBLE result is independently replayed
against every source equality and bound before being written.
"""
from __future__ import annotations

from itertools import product
from math import comb, factorial
import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model

N = 17
OUTSIDE = 14
SIZE = 2**17
W = [1,0,0,0,0,0,0,408,1530,3400,8160,17136,25704,28560,24480,15096,5661,936]
R0 = [0,0,0,0,0,0,112,352,1040,3680,9056,16576,24864,29120,24880,14816,5584,992]
U0 = [0,0,0,0,0,28,56,240,1320,3820,8496,16576,25424,28980,24600,14928,5640,964]
R1 = [0,0,0,0,0,0,112,336,1104,3632,8928,16800,24864,28896,25008,14864,5520,1008]
U1 = [0,0,0,1,0,21,56,261,1320,3785,8496,16611,25424,28959,24600,14935,5640,963]

ORBITS = sorted((ni, nx, 3-ni-nx) for ni in range(4) for nx in range(4-ni))
OI = {o:i for i,o in enumerate(ORBITS)}


def orbit_size(o: tuple[int,int,int]) -> int:
    a,b,c=o
    return factorial(3)//(factorial(a)*factorial(b)*factorial(c))*2**c


def patterns(o: tuple[int,int,int]):
    return [p for p in product(range(4), repeat=3)
            if (p.count(0),p.count(1),p.count(2)+p.count(3)) == o]

PATS = [patterns(o) for o in ORBITS]


def symp(a,b) -> int:
    return sum(((x&1)*((y>>1)&1)+((x>>1)&1)*(y&1))
               for x,y in zip(a,b)) & 1

FOURIER = [[0]*10 for _ in range(10)]
for ot in range(10):
    for os in range(10):
        vals={sum((-1)**symp(y,a) for y in PATS[ot]) for a in PATS[os]}
        assert len(vals)==1
        FOURIER[ot][os]=vals.pop()


def kraw(j:int,i:int,n:int=OUTSIDE) -> int:
    return sum((-1)**ell*3**(j-ell)*comb(i,ell)*comb(n-i,j-ell)
               for ell in range(j+1)
               if ell<=i and j-ell<=n-i)

KM = [[kraw(j,i) for i in range(15)] for j in range(15)]


def main() -> int:
    ap=argparse.ArgumentParser()
    ap.add_argument('--seconds',type=float,default=21600)
    ap.add_argument('--workers',type=int,default=4)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--output',type=Path,default=Path('d7_pair_cpsat_result.json'))
    args=ap.parse_args()

    model=cp_model.CpModel()
    f={};v={};h={}
    bounds={}
    for o,orb in enumerate(ORBITS):
        for i in range(15):
            w=i+3-orb[0]
            wt=i+3-orb[1]
            fu=min(W[w] if 0<=w<18 else 0,
                   U1[wt] if 0<=wt<18 else 0,
                   orbit_size(orb)*2048)
            vu=min(U0[w] if 0<=w<18 else 0,
                   R0[wt] if 0<=wt<18 else 0,
                   orbit_size(orb)*2048)
            f[o,i]=model.NewIntVar(0,fu,f'f_{o}_{i}')
            v[o,i]=model.NewIntVar(0,vu,f'v_{o}_{i}')
            h[o,i]=model.NewIntVar(0,fu,f'h_{o}_{i}')
            model.Add(h[o,i] <= f[o,i])
            bounds['f',o,i]=fu; bounds['v',o,i]=vu; bounds['h',o,i]=fu

    # E self-dual: M(f)=f.
    for ot in range(10):
        for j in range(15):
            terms=[SIZE*f[ot,j]]
            for os in range(10):
                ff=FOURIER[ot][os]
                if ff:
                    for i in range(15):
                        z=-ff*KM[j][i]
                        if z: terms.append(z*f[os,i])
            model.Add(sum(terms)==0)

    # V coset transform: M(v)=2h-f.
    for ot in range(10):
        for j in range(15):
            terms=[-2*SIZE*h[ot,j], SIZE*f[ot,j]]
            for os in range(10):
                ff=FOURIER[ot][os]
                if ff:
                    for i in range(15):
                        z=ff*KM[j][i]
                        if z: terms.append(z*v[os,i])
            model.Add(sum(terms)==0)

    # Ordinary enumerators before/after e=XXX translation.
    for block,enum,translated in [
        (f,W,False),(f,U1,True),(v,U0,False),(v,R0,True)
    ]:
        for weight in range(18):
            terms=[]
            for o,orb in enumerate(ORBITS):
                local=(3-orb[0]) if not translated else (3-orb[1])
                i=weight-local
                if 0<=i<=14: terms.append(block[o,i])
            model.Add(sum(terms)==enum[weight])

    # OA strength three: each exact local pattern occurs 2048 times.
    for o,orb in enumerate(ORBITS):
        total=orbit_size(orb)*2048
        model.Add(sum(f[o,i] for i in range(15))==total)
        model.Add(sum(v[o,i] for i in range(15))==total)

    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=args.seconds
    solver.parameters.num_search_workers=args.workers
    solver.parameters.random_seed=args.seed
    solver.parameters.log_search_progress=True
    solver.parameters.cp_model_presolve=True
    start=time.time()
    status=solver.Solve(model)
    elapsed=time.time()-start
    status_name=solver.StatusName(status)
    out={
        'format':'q1736-d7-parent-pair-cpsat-v1',
        'status':status_name,
        'seconds':elapsed,
        'workers':args.workers,
        'seed':args.seed,
        'conflicts':solver.NumConflicts(),
        'branches':solver.NumBranches(),
        'wall_time':solver.WallTime(),
    }
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        fv=[[solver.Value(f[o,i]) for i in range(15)] for o in range(10)]
        vv=[[solver.Value(v[o,i]) for i in range(15)] for o in range(10)]
        hv=[[solver.Value(h[o,i]) for i in range(15)] for o in range(10)]
        # Independent exact replay of every model family.
        residual=0
        for ot in range(10):
            for j in range(15):
                lhs=SIZE*fv[ot][j]-sum(
                    FOURIER[ot][os]*KM[j][i]*fv[os][i]
                    for os in range(10) for i in range(15))
                residual=max(residual,abs(lhs))
                lhs=-2*SIZE*hv[ot][j]+SIZE*fv[ot][j]+sum(
                    FOURIER[ot][os]*KM[j][i]*vv[os][i]
                    for os in range(10) for i in range(15))
                residual=max(residual,abs(lhs))
        for block,enum,translated in [(fv,W,False),(fv,U1,True),(vv,U0,False),(vv,R0,True)]:
            for weight in range(18):
                lhs=0
                for o,orb in enumerate(ORBITS):
                    local=(3-orb[0]) if not translated else (3-orb[1])
                    i=weight-local
                    if 0<=i<=14: lhs+=block[o][i]
                residual=max(residual,abs(lhs-enum[weight]))
        for o,orb in enumerate(ORBITS):
            total=orbit_size(orb)*2048
            residual=max(residual,abs(sum(fv[o])-total),abs(sum(vv[o])-total))
            for i in range(15):
                if not (0<=hv[o][i]<=fv[o][i]): residual=max(residual,1)
        out.update({'exact_residual':residual,'f':fv,'v':vv,'h':hv})
        if residual: raise AssertionError(f'CP-SAT solution failed exact replay: {residual}')
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    return 0 if status!=cp_model.MODEL_INVALID else 2

if __name__=='__main__':
    raise SystemExit(main())

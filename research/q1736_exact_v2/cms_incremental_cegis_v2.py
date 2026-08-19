#!/usr/bin/env python3
"""Incremental native-XOR construction search for one fixed logical type."""
from __future__ import annotations
import argparse,itertools,json,time,traceback,sys
from pathlib import Path
import pycryptosat
from q1736_core import N,D,EDGE_PAIRS,EDGE_TO_VAR,EDGE_VARIABLES,enumerate_p_types,columns_from_counts,verify_graph_candidate

def parity(x:int)->int:return x.bit_count()&1

def edge_var(i:int,j:int)->int:
    if i>j:i,j=j,i
    return EDGE_TO_VAR[(i,j)]

def pt_masks(columns):
    return tuple(sum(parity(lam&column)<<i for i,column in enumerate(columns)) for lam in range(8))

def support_masks(weight):
    for support in itertools.combinations(range(N),weight):
        yield sum(1<<i for i in support)

def gamma_rows(model):
    rows=[0]*N
    for variable,(i,j) in enumerate(EDGE_PAIRS,1):
        if model[variable]:rows[i]|=1<<j;rows[j]|=1<<i
    return tuple(rows)

def gamma_times(rows,x):return sum(parity(row&x)<<i for i,row in enumerate(rows))

def key(x,lam):return (x<<3)|lam

def add_condition(solver,columns,x,lam,next_variable):
    support=[i for i in range(N) if (x>>i)&1]
    outside=[i for i in range(N) if not ((x>>i)&1)]
    required=D-len(support);ys=[]
    for i in outside:
        y=next_variable;next_variable+=1;ys.append(y)
        solver.add_xor_clause([y,*[edge_var(i,j) for j in support]],bool(parity(lam&columns[i])))
    clause_size=len(ys)-required+1
    if clause_size!=12:raise AssertionError(clause_size)
    for clause in itertools.combinations(ys,clause_size):solver.add_clause(list(clause))
    return next_variable

def scan(rows,pt):
    violations=[];minimum=99;hist={}
    for weight in range(1,D):
        for x in support_masks(weight):
            gx=gamma_times(rows,x)
            for lam in range(8):
                value=(x|(gx^pt[lam])).bit_count();minimum=min(minimum,value)
                if value<D:
                    violations.append((D-value,weight,value,x,lam));hist[value]=hist.get(value,0)+1
    for lam in range(1,8):
        value=pt[lam].bit_count();minimum=min(minimum,value)
        if value<D:violations.append((D-value,0,value,0,lam));hist[value]=hist.get(value,0)+1
    violations.sort(reverse=True)
    return violations,minimum,hist

def solve_type(type_id,timeout,outdir,initial_weight=1,max_add=15000):
    outdir.mkdir(parents=True,exist_ok=True)
    entry=enumerate_p_types()[type_id]
    if entry['minimum_logical_weight']<D:
        result={'status':'FILTERED','type':entry};(outdir/f'type_{type_id:03d}.json').write_text(json.dumps(result,indent=2)+'\n');return result
    columns=columns_from_counts(entry['counts']);pt=pt_masks(columns);solver=pycryptosat.Solver(threads=1)
    next_variable=EDGE_VARIABLES+1;added=set();stats=[]
    for weight in range(1,initial_weight+1):
        for x in support_masks(weight):
            for lam in range(8):
                next_variable=add_condition(solver,columns,x,lam,next_variable);added.add(key(x,lam))
    started=time.monotonic();status='TIMEOUT';candidate=None;round_number=0
    while time.monotonic()-started<timeout:
        remaining=max(1.0,timeout-(time.monotonic()-started))
        sat,model=solver.solve(time_limit=min(remaining,120.0))
        round_number+=1
        if sat is False:status='UNSAT_NO_PROOF';break
        if sat is None:status='TIMEOUT';break
        rows=gamma_rows(model);violations,minimum,hist=scan(rows,pt)
        stats.append({'round':round_number,'elapsed_seconds':time.monotonic()-started,'violations':len(violations),'minimum_weight':minimum,'histogram':hist,'conditions_added':len(added),'variables':next_variable-1})
        (outdir/f'type_{type_id:03d}_progress.json').write_text(json.dumps({'type':entry,'stats':stats[-50:],'condition_keys':sorted(added)},indent=2)+'\n')
        if not violations:
            assignment={v:bool(model[v]) for v in range(1,EDGE_VARIABLES+1)}
            report=verify_graph_candidate(columns,assignment,exhaustive_normalizer=True);report['type']=entry;report['search_stats']=stats
            candidate_path=outdir/f'type_{type_id:03d}_VERIFIED_CANDIDATE.json';candidate_path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
            status='VERIFIED_SAT';candidate=str(candidate_path);break
        new=[]
        for _,_,_,x,lam in violations:
            encoded=key(x,lam)
            if encoded not in added:
                new.append((x,lam,encoded))
                if len(new)>=max_add:break
        if not new:status='STALLED_DUPLICATES';break
        for x,lam,encoded in new:
            next_variable=add_condition(solver,columns,x,lam,next_variable);added.add(encoded)
    condition_path=outdir/f'type_{type_id:03d}_conditions.json';condition_path.write_text(json.dumps({'type_id':type_id,'type':entry,'condition_keys':sorted(added)},separators=(',',':'))+'\n')
    result={'status':status,'type':entry,'elapsed_seconds':time.monotonic()-started,'rounds':round_number,'conditions_added':len(added),'condition_file':condition_path.name,'variables':next_variable-1,'stats':stats,'candidate':candidate}
    (outdir/f'type_{type_id:03d}.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--type-id',type=int,required=True);parser.add_argument('--timeout',type=float,default=180);parser.add_argument('--outdir',type=Path,required=True);parser.add_argument('--initial-weight',type=int,default=1);parser.add_argument('--max-add',type=int,default=15000);args=parser.parse_args()
    try:
        result=solve_type(args.type_id,args.timeout,args.outdir,args.initial_weight,args.max_add);print(json.dumps({'status':result['status'],'type_id':args.type_id,'rounds':result.get('rounds')},sort_keys=True));return 0
    except Exception as error:
        args.outdir.mkdir(parents=True,exist_ok=True);(args.outdir/f'type_{args.type_id:03d}_ERROR.json').write_text(json.dumps({'status':'ERROR','error':repr(error),'traceback':traceback.format_exc()},indent=2)+'\n');raise
if __name__=='__main__':raise SystemExit(main())

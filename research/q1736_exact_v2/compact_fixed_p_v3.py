#!/usr/bin/env python3
"""Compact exact CryptoMiniSat encoding for fixed-P [[17,3,6]] cases.

For a fixed X-support x, the graph syndrome g_i(x)=sum_j Gamma_ij x_j is
shared by all eight logical labels.  The label lambda only complements g_i by
the known constant <lambda,p_i>.  This removes a factor of eight in XOR
auxiliaries compared with the first complete encoding, without changing any
constraint.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, shutil, subprocess, time, traceback
from pathlib import Path
from q1736_core import D, EDGE_PAIRS, EDGE_TO_VAR, EDGE_VARIABLES, N, columns_from_counts, enumerate_p_types, parse_cms_model, verify_graph_candidate

def parity(value:int)->int:return value.bit_count()&1

def edge_variable(i:int,j:int)->int:
    if i>j:i,j=j,i
    return EDGE_TO_VAR[(i,j)]

def expected_counts()->tuple[int,int]:
    xor_count=sum(math.comb(N,w)*(N-w) for w in range(1,D))
    cnf_count=sum(math.comb(N,w)*8*math.comb(N-w,12) for w in range(1,D))
    if (xor_count,cnf_count)!=(117028,1534624):raise AssertionError((xor_count,cnf_count))
    return xor_count,cnf_count

def generate(columns,output:Path,metadata:Path):
    columns=tuple(columns);xor_expected,cnf_expected=expected_counts();total_variables=EDGE_VARIABLES+xor_expected;next_variable=EDGE_VARIABLES+1;xc=cc=0;digest=hashlib.sha256();output.parent.mkdir(parents=True,exist_ok=True)
    with output.open('wb',buffering=1024*1024) as handle:
        def emit(text:str):
            data=text.encode('ascii');handle.write(data);digest.update(data)
        emit(f'p cnf {total_variables} {xor_expected+cnf_expected}\n')
        universe=tuple(range(N))
        for weight in range(1,D):
            for support in itertools.combinations(universe,weight):
                support_set=frozenset(support);outside=[i for i in universe if i not in support_set];shared=[]
                for coordinate in outside:
                    variable=next_variable;next_variable+=1;shared.append((coordinate,variable))
                    terms=[edge_variable(coordinate,source) for source in support]
                    # CMS x-lines have RHS one.  Therefore -g XOR terms = 1
                    # is exactly g = XOR(terms).
                    emit('x'+' '.join(map(str,[-variable,*terms]))+' 0\n');xc+=1
                for lam in range(8):
                    y_literals=[-variable if parity(lam&columns[coordinate]) else variable for coordinate,variable in shared]
                    # At least 6-weight y's are true.  Since len(outside)-(6-weight)+1=12,
                    # every 12-subset must contain a true y literal.
                    for clause in itertools.combinations(y_literals,12):
                        emit(' '.join(map(str,clause))+' 0\n');cc+=1
    if next_variable-1!=total_variables or xc!=xor_expected or cc!=cnf_expected:raise AssertionError((next_variable-1,total_variables,xc,cc))
    record={'format':'compact fixed-P CMS XOR-CNF','p_columns':list(columns),'p_counts':[columns.count(v) for v in range(8)],'edge_variables':EDGE_VARIABLES,'shared_syndrome_variables':xor_expected,'variables':total_variables,'xor_clauses':xc,'cnf_clauses':cc,'clauses':xc+cc,'sha256':digest.hexdigest()}
    metadata.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');return record

def solve(cms:Path,instance:Path,timeout:int):
    started=time.monotonic();timed_out=False
    try:
        completed=subprocess.run([str(cms),'--verb=0','--printsol=1',str(instance)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=timeout,check=False);code=completed.returncode;output=completed.stdout
    except subprocess.TimeoutExpired as error:
        timed_out=True;code=124;output=error.stdout or '';output=output.decode(errors='replace') if isinstance(output,bytes) else output
    status='TIMEOUT' if timed_out else ('SAT' if code==10 and 'SATISFIABLE' in output and 'UNSATISFIABLE' not in output else ('UNSAT' if code==20 and 'UNSATISFIABLE' in output else 'UNKNOWN'))
    return {'status':status,'returncode':code,'elapsed_seconds':time.monotonic()-started,'output':output}

def atomic(path:Path,value):
    path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');tmp.replace(path)

def shard(cms:Path,shard_id:int,shards:int,timeout:int,work:Path,results:Path):
    all_types=enumerate_p_types();eligible=[entry for entry in all_types if entry['minimum_logical_weight']>=D];eligible.sort(key=lambda e:(-e['minimum_logical_weight'],e['maximum_logical_weight']-e['minimum_logical_weight'],e['counts'][0],e['type_id']));assigned=[e for pos,e in enumerate(eligible) if pos%shards==shard_id]
    summary={'format':'q1736-compact-fixed-P-v3','all_types':len(all_types),'eligible_types':len(eligible),'shard':shard_id,'shards':shards,'assigned':[e['type_id'] for e in assigned],'results':[],'candidate':None,'complete':False};atomic(results/f'shard_{shard_id:02d}.json',summary)
    for entry in assigned:
        tid=entry['type_id'];columns=columns_from_counts(entry['counts']);instance=work/f'type_{tid:03d}.cnf';meta=results/f'type_{tid:03d}_instance.json';log=results/f'type_{tid:03d}_solver.log'
        try:
            generation_started=time.monotonic();record=generate(columns,instance,meta);answer=solve(cms,instance,timeout);output=answer.pop('output');log.write_text(output);item={'type':entry,'instance':record,'generation_seconds':time.monotonic()-generation_started,'solver':answer,'status':answer['status'],'solver_log':log.name}
            if answer['status']=='SAT':
                report=verify_graph_candidate(columns,parse_cms_model(output),exhaustive_normalizer=True);report['type']=entry;candidate=results/f'type_{tid:03d}_VERIFIED_CANDIDATE.json';atomic(candidate,report);item['candidate']=candidate.name;summary['candidate']=candidate.name;shutil.copy2(instance,results/instance.name)
        except Exception as error:
            item={'type':entry,'status':'ERROR','error':repr(error),'traceback':traceback.format_exc()}
        finally:
            if instance.exists() and summary['candidate'] is None:instance.unlink()
        summary['results'].append(item);atomic(results/f'shard_{shard_id:02d}.json',summary)
        if summary['candidate']:break
    summary['complete']=summary['candidate'] is not None or len(summary['results'])==len(assigned);atomic(results/f'shard_{shard_id:02d}.json',summary)

def main():
    p=argparse.ArgumentParser();p.add_argument('--cms',type=Path,required=True);p.add_argument('--shard',type=int,required=True);p.add_argument('--shards',type=int,required=True);p.add_argument('--timeout',type=int,default=600);p.add_argument('--work',type=Path,required=True);p.add_argument('--results',type=Path,required=True);a=p.parse_args();a.work.mkdir(parents=True,exist_ok=True);a.results.mkdir(parents=True,exist_ok=True);shard(a.cms,a.shard,a.shards,a.timeout,a.work,a.results)
if __name__=='__main__':main()

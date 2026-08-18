#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,subprocess,sys,traceback
from pathlib import Path
from q1736_core import enumerate_p_types,D

def atomic(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);temporary=path.with_suffix(path.suffix+'.tmp');temporary.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');temporary.replace(path)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--shard',type=int,required=True);parser.add_argument('--shards',type=int,required=True);parser.add_argument('--timeout',type=int,default=180);parser.add_argument('--results',type=Path,required=True);args=parser.parse_args()
    types=[entry for entry in enumerate_p_types() if entry['minimum_logical_weight']>=D]
    types.sort(key=lambda entry:(entry['minimum_logical_weight'],-(entry['maximum_logical_weight']-entry['minimum_logical_weight']),-entry['counts'][0],-entry['type_id']))
    assigned=[entry for position,entry in enumerate(types) if position%args.shards==args.shard]
    output=args.results/f'shard_{args.shard:02d}';output.mkdir(parents=True,exist_ok=True)
    summary={'format':'q1736-incremental-cegis-v2','shard':args.shard,'shards':args.shards,'eligible_types':len(types),'assigned_type_ids':[entry['type_id'] for entry in assigned],'results':[],'sat_candidate':None,'complete':False};atomic(output/'summary.json',summary)
    script=Path(__file__).with_name('cms_incremental_cegis_v2.py')
    for entry in assigned:
        type_id=int(entry['type_id']);log=output/f'type_{type_id:03d}.log'
        try:
            completed=subprocess.run([sys.executable,str(script),'--type-id',str(type_id),'--timeout',str(args.timeout),'--outdir',str(output),'--initial-weight','1','--max-add','15000'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=args.timeout+90,check=False)
            log.write_text(completed.stdout);returncode=completed.returncode
        except subprocess.TimeoutExpired as error:
            value=error.stdout or '';value=value.decode(errors='replace') if isinstance(value,bytes) else value;log.write_text(value+'\nOUTER_TIMEOUT\n');returncode=124
        result_path=output/f'type_{type_id:03d}.json';status='TIMEOUT'
        if result_path.exists():
            try:status=json.loads(result_path.read_text()).get('status','UNKNOWN')
            except Exception:status='UNREADABLE'
        candidate=output/f'type_{type_id:03d}_VERIFIED_CANDIDATE.json'
        if candidate.exists():summary['sat_candidate']=candidate.name
        summary['results'].append({'type_id':type_id,'status':status,'returncode':returncode});atomic(output/'summary.json',summary)
        if candidate.exists():break
    summary['complete']=summary['sat_candidate'] is not None or len(summary['results'])==len(assigned);atomic(output/'summary.json',summary)
if __name__=='__main__':main()

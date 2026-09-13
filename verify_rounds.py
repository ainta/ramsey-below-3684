"""Serial concrete kernel verification, with durable progress and hard outer supervision.

Run under resource_guard.py. Shared support modules must already be compiled.
No unchecked producer result is used to discharge a Lean proposition.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--round',type=int,nargs='+',required=True)
    p.add_argument('--wait-for',type=Path)
    p.add_argument('--report',type=Path,required=True)
    p.add_argument('--reuse-chain-data',action='store_true')
    p.add_argument('--resume-from',type=Path,
        help='Reuse only a verified, unchanged prefix of an earlier progress report')
    a=p.parse_args();started=time.monotonic();done=[]
    deadline=datetime.fromisoformat(json.loads((ROOT/'verification_budget.json').read_text())[
        'verification_deadline_utc'].replace('Z','+00:00'))
    def check_deadline():
        if datetime.now(timezone.utc)>=deadline:
            raise SystemExit('Absolute one-week verification deadline reached')
    check_deadline()
    previous=[]
    if a.resume_from:
        if a.resume_from.resolve()==a.report.resolve():
            raise SystemExit('Resume output must be a new report, preserving the old evidence')
        earlier=json.loads(a.resume_from.read_text())
        assert earlier['rounds']==a.round,'Resume must use the same ordered round list'
        previous=earlier['modules']
        assert len({r['module'] for r in previous})==len(previous)
        # Validate the whole prefix before doing any new work. Older reports
        # record the compiler exit, source digest, and object timestamp; new
        # reports additionally pin the compiled bytes themselves.
        for row in previous:
            source=ROOT/'lean'/(row['module']+'.lean');obj=source.with_suffix('.olean')
            assert hashlib.sha256(source.read_bytes()).hexdigest()==row['source_sha256'],row['module']
            assert obj.is_file() and obj.stat().st_mtime>=source.stat().st_mtime,row['module']
            if 'object_sha256' in row:
                assert hashlib.sha256(obj.read_bytes()).hexdigest()==row['object_sha256'],row['module']
        print('VALIDATED RESUME PREFIX',len(previous),'modules',flush=True)
    if a.wait_for:
        print('WAITING FOR',a.wait_for,flush=True)
        while not a.wait_for.exists():check_deadline();time.sleep(1)
        status=json.loads(a.wait_for.read_text())['status']
        if status!='PASS_PROCESS':raise SystemExit('Predecessor did not pass: '+status)
    env=os.environ.copy();env['LEAN_PATH']=str(ROOT/'lean')
    def save(status):
        result=dict(status=status,rounds=a.round,elapsed_seconds=time.monotonic()-started,modules=done,
            resumed_from=str(a.resume_from) if a.resume_from else None,
            verification_deadline_utc=deadline.isoformat())
        temporary=a.report.with_suffix(a.report.suffix+'.tmp')
        temporary.write_text(json.dumps(result,indent=2)+'\n')
        temporary.replace(a.report)
    def build(module,phase,expected=None):
        check_deadline()
        source=ROOT/'lean'/(module+'.lean')
        digest=hashlib.sha256(source.read_bytes()).hexdigest()
        if expected is not None:assert expected==digest
        if len(done)<len(previous):
            row=previous[len(done)]
            assert row['module']==module and row['phase']==phase,'Not an identical build-plan prefix'
            done.append(dict(row,resumed=True))
            print('REUSE CHECKED',phase,module,flush=True)
            save('IN_PROGRESS_NOT_HEADLINE_THEOREM')
            return
        began=time.monotonic()
        print('CHECK',phase,module,flush=True)
        subprocess.run(['lean','+v4.32.1','-o',module+'.olean',module+'.lean'],cwd=ROOT/'lean',env=env,check=True)
        done.append(dict(module=module,phase=phase,source_sha256=digest,seconds=time.monotonic()-began,
            object_sha256=hashlib.sha256(source.with_suffix('.olean').read_bytes()).hexdigest()))
        save('IN_PROGRESS_NOT_HEADLINE_THEOREM')
    for rnd in a.round:
        data=json.loads((ROOT/f'lean/Kernel/ChainData/R{rnd:02d}.json').read_text())
        for module in data['modules'][2:]:
            if a.reuse_chain_data:
                source=ROOT/'lean'/(module+'.lean');obj=source.with_suffix('.olean')
                assert obj.stat().st_mtime>=source.stat().st_mtime
            else:build(module,'chain_data')
        build(f'Kernel/CheckedChainData/R{rnd:02d}','checked_chain_interface')
        for label in ['ChainChecks','OuterChecks']:
            manifest=json.loads((ROOT/f'lean/Kernel/{label}/R{rnd:02d}.json').read_text())
            if label=='OuterChecks':
                for module in manifest['base_modules'][2:]:build(module,'outer_data')
            for chunk in manifest['chunks']:build(chunk['module'],label,chunk['source_sha256'])
            for module in manifest['assemblies']:build(module,label+'_assembly')
        print('ROUND KERNEL CHECKS COMPLETE',rnd,flush=True)
    assert len(done)>=len(previous),'Resume prefix extends beyond the requested build plan'
    save('PASS_ALL_REQUESTED_ROUND_CHECKS_NOT_HEADLINE_THEOREM')

if __name__=='__main__':main()

"""Follow running kernel checks through the actual final Lean theorem.

This is an orchestrator, not a mathematical oracle. It waits only for
successful compiler results and then compiles the unconditional theorem.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from supervision_evidence import resource_passed

ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--dependency-project',type=Path,required=True)
    p.add_argument('--report',type=Path,required=True)
    a=p.parse_args();started=time.monotonic();compiled=[]
    raw=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.dependency_project,text=True).strip()
    env=os.environ.copy()
    env['LEAN_PATH']=os.pathsep.join([str(ROOT/'lean')]+[
        str((a.dependency_project/part).resolve()) if not Path(part).is_absolute() else part for part in raw.split(os.pathsep)])
    def read(path):
        try:return json.loads((ROOT/path).read_text())
        except (FileNotFoundError,json.JSONDecodeError):return None
    def wait_resource(path):
        print('WAIT RESOURCE',path,flush=True)
        while True:
            r=read(path)
            if r:
                if not resource_passed(r):raise SystemExit('Failed predecessor '+str(path))
                return r
            time.sleep(1)
    def wait_module(report,resource,module):
        print('WAIT MODULE',module,flush=True)
        while True:
            r=read(report)
            if r and any(x['module']==module for x in r['modules']):return
            resource_result=read(resource)
            if resource_result:
                raise SystemExit('Verification ended without '+module+': '+resource_result['status'])
            time.sleep(1)
    def build(module):
        print('ASSEMBLE',module,flush=True)
        began=time.monotonic()
        log=ROOT/'runs'/(module.replace('/','_')+'.final_compile.log')
        with log.open('w') as out:
            subprocess.run(['lean','+v4.32.1','-o',module+'.olean',module+'.lean'],
                cwd=ROOT/'lean',env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
        output=log.read_text();print(output,flush=True)
        assert 'sorryAx' not in output and 'Lean.ofReduceBool' not in output and 'error:' not in output
        source=ROOT/'lean'/(module+'.lean')
        compiled.append(dict(module=module,seconds=time.monotonic()-began,
            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),log=str(log.relative_to(ROOT))))
        a.report.write_text(json.dumps(dict(status='ASSEMBLY_IN_PROGRESS_NOT_HEADLINE_THEOREM',
            elapsed_seconds=time.monotonic()-started,modules=compiled),indent=2)+'\n')
    wait_resource('runs/chain_r00_full_second.resources.json')
    wait_resource('runs/outer_r00_full.resources.json')
    for m in read('lean/Kernel/ChainChecks/R00Assemblies.json')['modules']:build(m)
    for m in read('lean/Kernel/OuterChecks/R00Assemblies.json')['modules']:build(m)
    build('CertifiedRound/R00')
    for rnd in range(1,8):
        prefix='rounds_01_06_full' if rnd<7 else 'round_07_full'
        wait_module('runs/'+prefix+'.json','runs/'+prefix+'.resources.json',f'Kernel/OuterChecks/R{rnd:02d}Boundary')
        build(f'CertifiedRound/R{rnd:02d}')
    # Require the supervising processes themselves to have exited cleanly.
    wait_resource('runs/rounds_01_06_full.resources.json')
    wait_resource('runs/round_07_full.resources.json')
    build('RamseyBelow3684')
    output=(ROOT/'runs/RamseyBelow3684.final_compile.log').read_text()
    expected="'Compact3684.ramsey_le_368395' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert expected in output
    a.report.write_text(json.dumps(dict(status='PASS_UNCONDITIONAL_RAMSEY_THEOREM',
        theorem='Compact3684.ramsey_le_368395',base='73679/20000',base_decimal='3.68395',
        axioms=['propext','Classical.choice','Quot.sound'],
        dependency_builds_reused=True,elapsed_seconds=time.monotonic()-started,modules=compiled),indent=2)+'\n')
    print('PASS UNCONDITIONAL RAMSEY THEOREM BASE 3.68395',flush=True)

if __name__=='__main__':main()

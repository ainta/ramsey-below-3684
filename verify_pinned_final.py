"""Recheck the completed theorem against the exact original-repository sources."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--wait-for',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args();started=time.monotonic()
    print('WAITING FOR COMPLETE THEOREM',args.wait_for,flush=True)
    while True:
        try:predecessor=json.loads(args.wait_for.read_text());break
        except (FileNotFoundError,json.JSONDecodeError):time.sleep(1)
    if predecessor['status']!='PASS_PROCESS':raise SystemExit('Previous assembly did not pass')
    audit=json.loads((ROOT/'runs/dependency_provenance.json').read_text())
    assert audit['status']=='PASS_PINNED_DEPENDENCY_SOURCE_AUDIT_AND_OVERLAY'
    command=[sys.executable,'-u','build_support.py','--dependency-project',
        '/home/ainta/manuscripts/ramsey/claude_revision/lean',
        '--dependency-overlay','dependencies/upstream_overlay',
        '--output-root','dependencies/pinned_check_lean']
    print('RECHECK ALL GENERIC SUPPORT AGAINST PINNED UPSTREAM',flush=True)
    subprocess.run(command+['--report','runs/pinned_final_core.json'],cwd=ROOT,check=True)
    modules=(['InitialUniform','ReflectedInitial','CheckedCatalogSound','TerminalStrict']+
        [f'CertifiedRound/R{i:02d}' for i in range(8)]+['CertifiedRound','RamseyBelow3684'])
    log=ROOT/'runs/pinned_final_theorem.log'
    print('RECHECK ALL CLOSED ASSEMBLIES AGAINST PINNED UPSTREAM',flush=True)
    with log.open('w') as output:
        subprocess.run(command+['--report','runs/pinned_final_theorem.json','--modules']+modules,
            cwd=ROOT,stdout=output,stderr=subprocess.STDOUT,check=True)
    text=log.read_text();print(text,flush=True)
    assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text and 'error:' not in text
    expected="'Compact3684.ramsey_le_368395' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert expected in text
    result=dict(status='PASS_UNCONDITIONAL_RAMSEY_THEOREM_PINNED_UPSTREAM',
        theorem='Compact3684.ramsey_le_368395',base='73679/20000',base_decimal='3.68395',
        axioms=['propext','Classical.choice','Quot.sound'],
        upstream_commit=audit['upstream_commit'],mathlib_commit='520045ab14e26149ee970e2e617ca04b09bde5d6',
        unchanged_dependency_builds_reused=True,elapsed_seconds=time.monotonic()-started,
        final_source_sha256=hashlib.sha256((ROOT/'lean/RamseyBelow3684.lean').read_bytes()).hexdigest())
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS PINNED END-TO-END THEOREM',flush=True)

if __name__=='__main__':main()

"""Compare the actual Lean expression inventories across dependency versions."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def main():
    command=[sys.executable,'-u','build_support.py','--dependency-project',
             '/home/ainta/manuscripts/ramsey/claude_revision/lean']
    rows=[]
    for label,extra in [('cached',[]),('pinned',['--dependency-overlay','dependencies/upstream_overlay',
                                             '--output-root','dependencies/pinned_check_lean'])]:
        log=ROOT/f'runs/stable_exports_{label}.log'
        with log.open('w') as out:
            subprocess.run(command+extra+['--report',f'runs/stable_exports_{label}.json',
                '--modules','DependencyStableExports'],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,check=True)
        entries=[json.loads(line[len('STABLE_EXPORT '):]) for line in log.read_text().splitlines()
                 if line.startswith('STABLE_EXPORT ')]
        assert len(entries)==2
        rows.append(entries)
    assert rows[0]==rows[1],'Cached external consumer references a changed expression'
    result=dict(status='PASS_EXACT_STABLE_EXPORT_EXPRESSIONS',exports=[
        dict(name=r['name'],type_sha256=hashlib.sha256(r['type'].encode()).hexdigest(),
             value_sha256=hashlib.sha256(r['value'].encode()).hexdigest()) for r in rows[0]])
    (ROOT/'runs/stable_dependency_exports.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS EXACT TYPE AND VALUE COMPARISON FOR BOTH UNCHANGED EXPORTS',flush=True)

if __name__=='__main__':main()

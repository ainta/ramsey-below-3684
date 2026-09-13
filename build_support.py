"""Build every supporting module using an existing matching mathlib environment.

Only this experiment's directory is written. This is not a full Ramsey proof
build and deliberately does not claim otherwise.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--dependency-project',type=Path,required=True)
    p.add_argument('--modules',nargs='+')
    p.add_argument('--module-manifest',type=Path)
    p.add_argument('--dependency-overlay',type=Path)
    p.add_argument('--output-root',type=Path)
    p.add_argument('--report',type=Path,default=HERE/'runs/support_build.json')
    a=p.parse_args()
    path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=a.dependency_project,text=True).strip()
    env=os.environ.copy()
    env['LEAN_PATH']=str(HERE/'lean')+os.pathsep+path
    # lake's relative search paths are relative to the dependency project.
    env['LEAN_PATH']=os.pathsep.join(str((a.dependency_project/part).resolve())
        if not Path(part).is_absolute() else part for part in env['LEAN_PATH'].split(os.pathsep))
    if a.dependency_overlay:
        env['LEAN_PATH']=str(a.dependency_overlay.resolve())+os.pathsep+env['LEAN_PATH']
    if a.output_root:
        env['LEAN_PATH']=str(a.output_root.resolve())+os.pathsep+env['LEAN_PATH']
    began=time.monotonic()
    selected=a.modules or (json.loads(a.module_manifest.read_text())['modules'] if a.module_manifest else None)
    modules=selected or ['PrefixRange','ControlQuantization','TerminalNumeric','IntegerLog',
        'Ramsey3683Bootstrap/WeightedParameters','Ramsey3683Bootstrap/WeightedLocal',
        'Ramsey3683Bootstrap/WeightedMoment','Ramsey3683Bootstrap/WeightedEngine',
        'Ramsey3683Bootstrap/WeightedSchedules','Ramsey3683Bootstrap/WeightedSlack',
        'Ramsey3683Bootstrap/WeightedConcrete','Ramsey3683Bootstrap/WeightedUniform',
        'Ramsey3683Bootstrap/FiniteContinuation','Ramsey3683Bootstrap/Preparation',
        'Ramsey3683Bootstrap/GridSemantics','Ramsey3683Bootstrap/FinsetCut',
        'Ramsey3683Bootstrap/GridCell','Ramsey3683Bootstrap/GridDensity',
        'Ramsey3683Bootstrap/GridSeed','Ramsey3683Bootstrap/GridClosure',
        'Kernel/Log18','Kernel/LogInterval','Kernel/SeedGuard','Kernel/Codec','Kernel/Elementary',
        'Ramsey3683Bootstrap/Certificate','Kernel/ProfileGuard',
        'Ramsey3683Bootstrap/ReflectedProfile','Ramsey3683Bootstrap/ProfileCheck',
        'Kernel/ChainGuard','Ramsey3683Bootstrap/RunSemantics',
        'Ramsey3683Bootstrap/ChainColumns','Ramsey3683Bootstrap/ChainRuns',
        'Ramsey3683Bootstrap/ChainPaths','Ramsey3683Bootstrap/ChainSound',
        'Kernel/OuterGuard','Ramsey3683Bootstrap/OuterPaths',
        'Ramsey3683Bootstrap/OuterCover','Ramsey3683Bootstrap/RoundSound',
        'Kernel/ChainChecks','Ramsey3683Bootstrap/CheckedRoundInterface',
        'Kernel/PackedChain','Kernel/PackedOuter','Kernel/CheckedProfiles','Kernel/ChunkedChecks',
        'Kernel/CheckedLogChunk','Kernel',
        'Ramsey3683Bootstrap/MinimumDegreeCore','Ramsey3683Bootstrap/MaximumClique',
        'Ramsey3683Bootstrap/AllSpines','Ramsey3683Bootstrap/TerminalCore',
        'Ramsey3683Bootstrap/TerminalTransfer','TerminalTarget',
        'Ramsey3683Bootstrap','Compact3684']
    if a.output_root:
        selected_outputs={name+'.olean' for name in modules}
        for artifact in (HERE/'lean').rglob('*.olean'):
            rel=artifact.relative_to(HERE/'lean')
            if str(rel) in selected_outputs:continue
            link=a.output_root.resolve()/rel
            link.parent.mkdir(parents=True,exist_ok=True)
            if not link.exists():link.symlink_to(artifact)
    for name in modules:
        print('BUILD SUPPORT',name,flush=True)
        target=(a.output_root.resolve()/(name+'.olean')) if a.output_root else Path(name+'.olean')
        if a.output_root:target.parent.mkdir(parents=True,exist_ok=True)
        if a.output_root and target.is_symlink():
            # This derived local link may have been created by an earlier
            # narrower audit. Remove only the link, never its compiled target.
            target.unlink()
        subprocess.run(['lean','+v4.32.1','-o',str(target),name+'.lean'],
                       cwd=HERE/'lean',env=env,check=True)
    result=dict(status='PASS_SUPPORT_LIBRARY_NOT_RAMSEY_THEOREM',modules=modules,
                lean='4.32.1',mathlib='520045ab14e26149ee970e2e617ca04b09bde5d6',
                elapsed_seconds=time.monotonic()-began,headline_proved=False)
    a.report.write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

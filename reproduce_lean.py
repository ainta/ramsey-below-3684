"""Serial, isolated rebuild of a theorem's complete local import closure.

Run under resource_guard.py. Existing upstream/mathlib builds are explicit
external dependencies; no existing local proof objects enter LEAN_PATH.
The generator, JSON certificates, and old success reports are not premises.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'lean'
IMPORT=re.compile(r'^(?:(?:public|private)\s+)?import\s+(.+?)\s*(?:--.*)?$')


def import_closure(root_module):
    order=[];external=set();visiting=set();finished=set()
    def visit(name):
        if name in finished:return
        source=SOURCE/(name.replace('.','/')+'.lean')
        if not source.is_file():external.add(name);return
        if name in visiting:raise ValueError('Import cycle at '+name)
        visiting.add(name)
        # Only short import lines can match. Stream instead of loading a
        # multi-megabyte packed-integer data file into an extra string.
        with source.open() as stream:
            for line in stream:
                if len(line)>4096:continue
                match=IMPORT.fullmatch(line.strip())
                if match:
                    for dependency in match.group(1).split():
                        if dependency.startswith('--'):break
                        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',dependency):
                            raise ValueError('Unsupported import syntax: '+line)
                        visit(dependency)
        visiting.remove(name);finished.add(name);order.append(name)
    visit(root_module)
    if not order or order[-1]!=root_module:raise ValueError('Missing local root module')
    return order,sorted(external)


def digest(path):
    result=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(2**20),b''):result.update(block)
    return result.hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--module',default='RamseyBelow3684')
    parser.add_argument('--dependency-project',type=Path)
    parser.add_argument('--dependency-overlay',type=Path)
    parser.add_argument('--output-root',type=Path)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--plan-only',action='store_true')
    args=parser.parse_args();started=time.monotonic()
    modules,external=import_closure(args.module)
    if args.plan_only:
        args.report.write_text(json.dumps(dict(status='BUILD_PLAN_ONLY_NOT_CHECKED',
            root_module=args.module,modules=modules,external_modules=external),indent=2)+'\n')
        print('LOCAL IMPORT CLOSURE',len(modules),'modules;',len(external),'external imports',flush=True)
        return
    if not args.dependency_project or not args.output_root:
        parser.error('A build requires --dependency-project and a fresh --output-root')
    output=args.output_root.resolve()
    if not output.is_relative_to(ROOT/'runs') or output==ROOT/'runs':
        parser.error('The fresh output directory must be a proper child of this workspace runs directory')
    if output.exists():parser.error('Output already exists; preserve it and choose a fresh directory')
    output.mkdir(parents=True)
    raw=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=args.dependency_project,text=True).strip()
    dependencies=[str((args.dependency_project/p).resolve()) if not Path(p).is_absolute() else p
                  for p in raw.split(os.pathsep)]
    search=[str(output)]+([str(args.dependency_overlay.resolve())] if args.dependency_overlay else [])+dependencies
    if str(SOURCE) in search:raise ValueError('Existing local proof objects must not be a dependency')
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(search)
    done=[]
    def save(status):
        report=dict(status=status,root_module=args.module,modules=done,total_modules=len(modules),
            external_modules=external,external_dependency_builds_reused=True,
            existing_local_objects_reused=False,output_root=str(output),
            elapsed_seconds=time.monotonic()-started)
        temporary=args.report.with_suffix(args.report.suffix+'.tmp')
        temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(args.report)
    save('ISOLATED_REBUILD_IN_PROGRESS')
    for module in modules:
        relative=module.replace('.','/')
        source=SOURCE/(relative+'.lean');target=output/(relative+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        log=target.with_suffix('.compile.log');began=time.monotonic()
        print('REBUILD',len(done)+1,'/',len(modules),module,flush=True)
        with log.open('w') as stream:
            result=subprocess.run(['lean','+v4.32.1','-o',str(target),relative+'.lean'],cwd=SOURCE,
                env=env,stdout=stream,stderr=subprocess.STDOUT)
        text=log.read_text()
        if result.returncode or 'sorryAx' in text or 'Lean.ofReduceBool' in text or 'error:' in text:
            print(text,flush=True);save('FAILED_LOCAL_REBUILD');raise SystemExit(1)
        done.append(dict(module=module,source_sha256=digest(source),object_sha256=digest(target),
            seconds=time.monotonic()-began,log=str(log)))
        save('ISOLATED_REBUILD_IN_PROGRESS')
    if args.module=='RamseyBelow3684':
        expected="'Compact3684.ramsey_le_368395' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in text:raise SystemExit('Final theorem axiom inventory absent')
        save('PASS_ISOLATED_COMPLETE_LOCAL_RAMSEY_REBUILD')
    else:save('PASS_ISOLATED_SELECTED_LOCAL_IMPORT_CLOSURE')
    print('PASS',args.module,flush=True)


if __name__=='__main__':main()

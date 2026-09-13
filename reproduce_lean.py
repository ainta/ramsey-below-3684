"""Isolated rebuild of a theorem's complete local import closure.

Run under resource_guard.py. Existing upstream/mathlib builds are explicit
external dependencies; no existing local proof objects enter LEAN_PATH.
The generator, JSON certificates, and old success reports are not premises.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
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
EXTERNAL_ROOTS={'Mathlib','RamseyLean','Std','Lean','Init'}


def read_imports(source):
    with source.open(encoding='utf-8') as stream:
        for line in stream:
            if len(line)>4096:continue
            match=IMPORT.fullmatch(line.strip())
            if match:
                for dependency in match.group(1).split():
                    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',dependency):
                        raise ValueError('Unsupported import syntax: '+line)
                    yield dependency


def import_closure(root_module, source_root=None):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', root_module):
        raise ValueError('Invalid Lean module name: '+root_module)
    source_root=Path(source_root) if source_root is not None else SOURCE
    order=[];external=set();visiting=set();finished=set()
    def visit(name):
        if name in finished:return
        source=source_root/(name.replace('.','/')+'.lean')
        if not source.is_file():
            if name.split('.')[0] not in EXTERNAL_ROOTS:
                raise ValueError('Missing local Lean source: '+str(source)+
                    '\nInstall generated-lean-sources.tar.gz with prepare_sources.py first.')
            external.add(name);return
        if name in visiting:raise ValueError('Import cycle at '+name)
        visiting.add(name)
        for dependency in read_imports(source):visit(dependency)
        visiting.remove(name);finished.add(name);order.append(name)
    visit(root_module)
    if not order or order[-1]!=root_module:raise ValueError('Missing local root module')
    return order,sorted(external)


def parallel_build(modules, dependencies, build, record, jobs):
    """Submit a module only after all its local imports have succeeded."""
    pending=set(modules);finished=set();active={}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or active:
            for module in modules:
                if len(active)>=jobs:break
                if module in pending and dependencies[module]<=finished:
                    pending.remove(module)
                    active[pool.submit(build,module)]=module
            if not active:raise ValueError('No buildable module; import dependency cycle')
            ready,_=wait(active,return_when=FIRST_COMPLETED)
            for future in ready:
                module=active.pop(future)
                result=future.result()
                record(result)
                finished.add(module)


def external_search_paths(paths, modules, source=SOURCE):
    """Remove this package's cache and reject other caches of local proofs."""
    own={source.resolve(),(source/'.lake/build/lib/lean').resolve()}
    local_roots={m.split('.')[0] for m in modules}-EXTERNAL_ROOTS
    clean=[]
    for raw in paths:
        path=Path(raw).resolve()
        if path in own:continue
        for root in local_roots:
            if (path/root).exists() or (path/(root+'.olean')).exists():
                raise ValueError('Dependency path contains local proof objects: '+str(path))
        if str(path) not in clean:clean.append(str(path))
    return clean


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
    parser.add_argument('--jobs',type=int,default=1,help='Concurrent Lean processes (default: 1)')
    args=parser.parse_args();started=time.monotonic()
    if args.jobs<1:parser.error('--jobs must be positive')
    if args.report.exists():parser.error('Report already exists; choose a new --report')
    modules,external=import_closure(args.module)
    args.report.parent.mkdir(parents=True,exist_ok=True)
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
    raw=subprocess.check_output(['lake','+v4.32.1','env','printenv','LEAN_PATH'],cwd=args.dependency_project,text=True).strip()
    dependencies=[str((args.dependency_project/p).resolve()) if not Path(p).is_absolute() else p
                  for p in raw.split(os.pathsep)]
    search=[str(output)]+external_search_paths(
        ([str(args.dependency_overlay.resolve())] if args.dependency_overlay else [])+dependencies,modules)
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(search)
    output.mkdir(parents=True)
    done=[]
    def save(status):
        report=dict(status=status,root_module=args.module,modules=done,total_modules=len(modules),
            external_modules=external,external_dependency_builds_reused=True,
            existing_local_objects_reused=False,output_root=str(output),
            jobs=args.jobs,elapsed_seconds=time.monotonic()-started)
        temporary=args.report.with_suffix(args.report.suffix+'.tmp')
        temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(args.report)
    save('ISOLATED_REBUILD_IN_PROGRESS')
    def build(module):
        relative=module.replace('.','/')
        source=SOURCE/(relative+'.lean');target=output/(relative+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        log=target.with_suffix('.compile.log');began=time.monotonic()
        print('REBUILD',module,flush=True)
        with log.open('w') as stream:
            result=subprocess.run(['lean','+v4.32.1','-o',str(target),relative+'.lean'],cwd=SOURCE,
                env=env,stdout=stream,stderr=subprocess.STDOUT)
        text=log.read_text()
        if result.returncode or 'sorryAx' in text or 'Lean.ofReduceBool' in text or 'error:' in text:
            print(text,flush=True);raise RuntimeError('Lean check failed: '+module)
        return dict(module=module,source_sha256=digest(source),object_sha256=digest(target),
            seconds=time.monotonic()-began,log=str(log))
    def record(result):
        done.append(result)
        save('ISOLATED_REBUILD_IN_PROGRESS')
    local=set(modules)
    graph={m:set(read_imports(SOURCE/(m.replace('.','/')+'.lean')))&local for m in modules}
    try:parallel_build(modules,graph,build,record,args.jobs)
    except Exception:
        save('FAILED_LOCAL_REBUILD');raise
    if args.module=='RamseyBelow3684':
        expected="'Compact3684.ramsey_le_368395' depends on axioms: [propext, Classical.choice, Quot.sound]"
        text=(output/'RamseyBelow3684.compile.log').read_text()
        if expected not in text:
            save('FAILED_FINAL_AXIOM_AUDIT')
            raise SystemExit('Final theorem axiom inventory absent')
        save('PASS_ISOLATED_COMPLETE_LOCAL_RAMSEY_REBUILD')
    else:save('PASS_ISOLATED_SELECTED_LOCAL_IMPORT_CLOSURE')
    print('PASS',args.module,flush=True)


if __name__=='__main__':main()

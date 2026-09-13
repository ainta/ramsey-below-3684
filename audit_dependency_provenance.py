"""Check cached sources against the pinned upstream and rebuild the differences.

Only the three source differences are compiled into a private overlay. The
cached project and the pristine upstream checkout are never modified.
"""
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parent
CACHE=Path('/home/ainta/manuscripts/ramsey/claude_revision/lean')
UPSTREAM=ROOT/'dependencies/upstream_source'
OVERLAY=ROOT/'dependencies/upstream_overlay'
PIN='e53b8cf11d064daae70372b3a93b2556a5fee926'
EXPECTED=['RamseyLean/Descent.lean','RamseyLean/Numerics/Preliminary.lean','RamseyLean/Numerics.lean']

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(2**20),b''):h.update(block)
    return h.hexdigest()

def main():
    started=time.monotonic()
    pin=subprocess.check_output(['git','rev-parse','HEAD'],cwd=UPSTREAM,text=True).strip()
    assert pin==PIN
    common=[];different=[]
    for source in sorted((CACHE/'RamseyLean').rglob('*.lean')):
        rel=source.relative_to(CACHE)
        target=UPSTREAM/rel
        assert target.is_file(),str(rel)
        a,b=digest(source),digest(target)
        row=dict(module=str(rel),cached_source_sha256=a,upstream_source_sha256=b)
        common.append(row)
        if a!=b:different.append(str(rel))
    assert set(different)==set(EXPECTED),different
    raw=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=CACHE,text=True).strip()
    env=os.environ.copy()
    search=[(CACHE/part).resolve() if not Path(part).is_absolute() else Path(part) for part in raw.split(os.pathsep)]
    cachelib=next(part for part in search if (part/'RamseyLean/BookInduction.olean').is_file())
    replaced=[str(Path(module).with_suffix(''))+'.' for module in EXPECTED]
    # Lean resolves an entire top-level module namespace in one search root.
    # Snapshot byte-identical cached modules. Atomic replacement of a derived
    # link replaces only that link, never its external target. Keeping private
    # copies protects this audit from unrelated later builds in the cache.
    for artifact in (cachelib/'RamseyLean').rglob('*'):
        if not artifact.is_file():continue
        rel=artifact.relative_to(cachelib)
        if any(str(rel).startswith(stem) for stem in replaced):continue
        link=OVERLAY/rel;link.parent.mkdir(parents=True,exist_ok=True)
        if link.is_symlink() or not link.exists():
            temporary=link.with_name(link.name+'.snapshot-tmp')
            assert not temporary.exists()
            shutil.copy2(artifact,temporary)
            os.replace(temporary,link)
    env['LEAN_PATH']=os.pathsep.join([str(OVERLAY)]+[str(part) for part in search])
    records=[]
    for module in EXPECTED:
        target=(OVERLAY/module).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        began=time.monotonic();print('REBUILD PINNED UPSTREAM',module,flush=True)
        subprocess.run(['lean','+v4.32.1','-o',str(target),module],cwd=UPSTREAM,env=env,check=True)
        records.append(dict(module=module,seconds=time.monotonic()-began,source_sha256=digest(UPSTREAM/module)))
    result=dict(status='PASS_PINNED_DEPENDENCY_SOURCE_AUDIT_AND_OVERLAY',upstream_commit=PIN,
        cached_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=CACHE,text=True).strip(),
        common_sources=len(common),identical_sources=len(common)-len(different),recompiled=records,
        sources=common,elapsed_seconds=time.monotonic()-started,
        unchanged_sources_use_existing_compiled_caches=True,cached_artifacts_snapshotted=True,
        final_theorem_recheck_with_overlay_required=True)
    (ROOT/'runs/dependency_provenance.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS SOURCE AUDIT',len(common),'common modules; rebuilt',len(records),'differences',flush=True)

if __name__=='__main__':main()

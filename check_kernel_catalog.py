"""Build all generated log chunks serially and record real measured resources externally.

Run under resource_guard.py. This checks the catalog computation only; it
does not advertise completion of the Ramsey theorem or real-log soundness.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--manifest',type=Path,default=Path('lean/Kernel/LogCatalog/manifest.json'))
    p.add_argument('--report',type=Path,default=Path('runs/kernel_catalog.json'))
    p.add_argument('--wait-for',type=Path)
    p.add_argument('--skip-base',action='store_true',help='Reuse already built base modules for supervised development runs')
    args=p.parse_args()
    if args.wait_for is not None:
        print('Waiting for predecessor resource report:',args.wait_for,flush=True)
        while True:
            try:
                predecessor=json.loads(args.wait_for.read_text())
                break
            except (FileNotFoundError,json.JSONDecodeError):
                time.sleep(1)
        print('Predecessor finished:',predecessor['status'],flush=True)
    manifest=json.loads(args.manifest.read_text())
    base=Path('lean').resolve()
    env=os.environ.copy()
    env['LEAN_PATH']=str(base)
    started=time.monotonic()
    base_modules=manifest.get('base_modules',['Kernel/Log18']+(['Kernel/Codec'] if manifest.get('packed') else []))
    for module in base_modules:
        if args.skip_base:
            assert (base/(module+'.olean')).stat().st_mtime >= (base/(module+'.lean')).stat().st_mtime
        else:
            subprocess.run(['lean','+v4.32.1','-o',module+'.olean',module+'.lean'],cwd=base,env=env,check=True)
    records=[]
    for chunk in manifest['chunks']:
        name=chunk['module']
        source=base/(name+'.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest()==chunk['source_sha256']
        began=time.monotonic()
        subprocess.run(['lean','+v4.32.1','-o',name+'.olean',name+'.lean'],cwd=base,env=env,check=True)
        records.append(dict(module=name,entries=chunk['count'],seconds=time.monotonic()-began))
        report=dict(status='KERNEL_CATALOG_IN_PROGRESS',checked_entries=sum(r['entries'] for r in records),
                    total_entries=manifest['entries'],elapsed_seconds=time.monotonic()-started,
                    real_log_soundness=False,headline_proved=False,packed=manifest.get('packed',False),
                    base_modules_reused=args.skip_base,chunks=records)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
        print('PASS CHUNK',len(records),'/',len(manifest['chunks']),
              'seconds',round(records[-1]['seconds'],2),flush=True)
    kind=manifest.get('kind','CATALOG')
    report['status']='PASS_FULL_'+kind+'_KERNEL_COMPUTATION_NOT_RAMSEY_THEOREM'
    if 'source_catalog_sha256' in manifest:
        report['source_catalog_sha256']=manifest['source_catalog_sha256']
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS ALL',report['checked_entries'],kind,'ENTRIES',flush=True)

if __name__ == '__main__':
    main()

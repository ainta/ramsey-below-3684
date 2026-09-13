"""Supplement per-job supervision with aggregate RSS for this workspace only.

The sum counts shared resident pages once per process: it is not proportional
set size or machine-wide RAM. Earlier phases retain their per-job reports.
"""
import json
import argparse
import os
from pathlib import Path
import time

ROOT=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--report',type=Path,default=ROOT/'runs/aggregate_active_memory.json')
    parser.add_argument('--final-resource',type=Path,default=ROOT/'runs/final_assembly.resources.json')
    args=parser.parse_args()
    started=time.monotonic();peak=0;samples=0;own=os.getpid()
    while True:
        rss=0;processes=0
        for proc in Path('/proc').iterdir():
            if not proc.name.isdigit() or int(proc.name)==own:continue
            try:
                cwd=(proc/'cwd').resolve()
                if not cwd.is_relative_to(ROOT):continue
                for line in (proc/'status').read_text().splitlines():
                    if line.startswith('VmRSS:'):
                        rss+=int(line.split()[1]);processes+=1;break
            except (FileNotFoundError,ProcessLookupError,PermissionError):pass
        peak=max(peak,rss);samples+=1
        final=args.final_resource
        finished=final.exists()
        report=dict(status='FINISHED_MONITOR_WINDOW' if finished else 'MONITORING',
            elapsed_seconds=time.monotonic()-started,current_sampled_rss_kib=rss,
            peak_sampled_rss_kib=peak,processes=processes,samples=samples,sample_period_seconds=5,
            scope='processes with cwd anywhere beneath this workspace, including isolated dependency audits',
            shared_pages_counted_per_process=True,earlier_phases_not_included=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
        if finished or time.monotonic()-started>604800:return
        time.sleep(5)

if __name__=='__main__':main()

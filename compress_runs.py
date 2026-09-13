"""Untrusted lossless encoder; verify the resulting v4 certificate separately."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile
from verify_stream import lines

HERE = Path(__file__).resolve().parent

def compress(source, output):
    d = json.loads(source.read_text())
    assert d['format'] == 'bellman_dag_stream_v3'
    output.parent.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='pack_runs_', dir=HERE) as temp:
        tmp = Path(temp)
        cursor = count = 0
        with (tmp/'lengths').open('wb') as f:
            for r in lines(source.parent/d['record_file']):
                off, size = r.get('path', [cursor, 0])
                assert off == cursor
                f.write(struct.pack('<I', size))
                cursor += size
                count += 1
        assert cursor == d['edge_count'] and count == d['records_count']
        with gzip.open(source.parent/d['edge_file'], 'rb') as f, (tmp/'edges').open('wb') as g:
            shutil.copyfileobj(f, g, 2**20)
        assert (tmp/'edges').stat().st_size == 2*cursor
        subprocess.run(['g++', '-O3', '-std=c++17', str(HERE/'pack_runs.cpp'), '-o', str(tmp/'pack')], check=True)
        subprocess.run([str(tmp/'pack'), *[str(tmp/n) for n in ['lengths', 'edges', 'runs', 'offsets']]], check=True)
        d['run_count'] = (tmp/'runs').stat().st_size//4
        assert (tmp/'offsets').stat().st_size == 8*count
        d['format'] = 'bellman_dag_stream_v4_runs'
        record_name = output.name+'.records.gz'
        edge_name = output.name+'.runs.gz'
        with (tmp/'offsets').open('rb') as offsets, gzip.open(output.parent/record_name, 'wt', compresslevel=1) as g:
            for r in lines(source.parent/d['record_file']):
                off, = struct.unpack('<Q', offsets.read(8))
                if 'path' in r:
                    r['path'][0] = off
                g.write(json.dumps(r, separators=(',', ':'))+'\n')
        with (tmp/'runs').open('rb') as f, gzip.open(output.parent/edge_name, 'wb', compresslevel=1) as g:
            shutil.copyfileobj(f, g, 2**20)
        d.update(record_file=record_name, edge_file=edge_name)
        shutil.copyfile(source.parent/'initial_u.json', output.parent/'initial_u.json')
        output.write_text(json.dumps(d, separators=(',', ':')))
    print(json.dumps(dict(status='ENCODED_PENDING_VERIFICATION', records=count,
                         expanded_edges=cursor, runs=d['run_count'],
                         raw_path_bytes_before=2*cursor, raw_path_bytes_after=4*d['run_count']), indent=2))

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    compress(args.source, args.output)

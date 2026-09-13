"""Differential and rejection tests for arithmetic paths, NOT Ramsey proofs."""
import json
from pathlib import Path
import random
import struct
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SCALE = 10**18

def node(v, end, cost, off, size, rnd, row, col, base, kind):
    return (v.to_bytes(16, 'little', signed=True) + end.to_bytes(16, 'little', signed=True)
            + struct.pack('<qQ6i', cost, off, size, rnd, row, col, base, kind))

def main():
    checks = 0
    with tempfile.TemporaryDirectory(prefix='run_tests_', dir=HERE) as temp:
        p = Path(temp)
        for name in ['check_paths', 'check_runs', 'pack_runs']:
            subprocess.run(['g++', '-O2', '-std=c++17', str(HERE/(name+'.cpp')), '-o', str(p/name)], check=True)
        def run(name, *args, good=True):
            nonlocal checks
            q = subprocess.run([str(p/name), *map(str, args)], capture_output=True)
            assert (q.returncode == 0) == good, (name, q.stdout, q.stderr)
            checks += 1
        for seed in range(20):
            rng = random.Random(seed)
            records, edges, lengths, slots = [], [], [], {}
            for row in range(1, 61):
                for col in range(8):
                    cost = rng.randrange(1, 100)
                    size = 0 if col == 0 else rng.randrange(row)
                    total = need = 0
                    path = []
                    for k in range(size):
                        cc = rng.randrange(col if k == 0 else 8)
                        cv, cs = slots[row-k, cc]
                        total += cs*SCALE
                        need = max(need, cv+total)
                        path.append(cc)
                    end = max(need, 10**22)+rng.randrange(1, 1000)*SCALE
                    v = end+SCALE
                    records.append(node(v, end if col else v, cost, len(edges), size, 0, row, col, -1, 2 if col else 0))
                    lengths.append(size)
                    edges.extend(path)
                    slots[row, col] = v, cost
            (p/'nodes').write_bytes(b''.join(records))
            (p/'edges').write_bytes(struct.pack('<'+'H'*len(edges), *edges))
            (p/'lengths').write_bytes(struct.pack('<'+'I'*len(lengths), *lengths))
            run('check_paths', p/'nodes', p/'edges', p/'expanded_result', 2)
            run('pack_runs', p/'lengths', p/'edges', p/'runs', p/'offsets')
            offsets = struct.unpack('<'+'Q'*len(records), (p/'offsets').read_bytes())
            packed = [r[:40]+struct.pack('<Q', off)+r[48:] for r, off in zip(records, offsets)]
            (p/'packed').write_bytes(b''.join(packed))
            run('check_runs', p/'packed', p/'runs', p/'compact_result', len(edges))
            assert (p/'expanded_result').read_bytes() == (p/'compact_result').read_bytes()
            checks += 1
        # The last valid fixture has both empty and nonempty paths.
        original_runs = (p/'runs').read_bytes()
        first, = struct.unpack_from('<I', original_runs)
        for code in [first & 65535, (65535 << 16) | (first & 65535), (first & 0xffff0000) | 65535]:
            (p/'bad_runs').write_bytes(struct.pack('<I', code)+original_runs[4:])
            run('check_runs', p/'packed', p/'bad_runs', p/'bad_result', len(edges), good=False)
        (p/'bad_runs').write_bytes(original_runs[:-4])
        run('check_runs', p/'packed', p/'bad_runs', p/'bad_result', len(edges), good=False)
        run('check_runs', p/'packed', p/'runs', p/'bad_result', len(edges)+1, good=False)
        bad = bytearray((p/'packed').read_bytes())
        struct.pack_into('<q', bad, 32, -1)
        (p/'bad_nodes').write_bytes(bad)
        run('check_runs', p/'bad_nodes', p/'runs', p/'bad_result', len(edges), good=False)
        # Duplicate a row/column rank, hence attempt to insert a checked leaf twice.
        bad = bytearray((p/'packed').read_bytes())
        struct.pack_into('<i', bad, 72+60, 0)
        (p/'bad_nodes').write_bytes(bad)
        run('check_runs', p/'bad_nodes', p/'runs', p/'bad_result', len(edges), good=False)
    result = dict(status='PASS_REGRESSION_NOT_FORMAL_PROOF', checks=checks,
                  random_dags=20, random_records=9600, seed_range=[0, 19],
                  method='Byte-identical outputs against expanded exact checker, plus malformed-input rejection')
    (HERE/'runs/run_checker_tests.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()

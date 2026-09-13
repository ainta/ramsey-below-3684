"""Count dependency and constant-column run sizes in a SEARCH plan.

These are prospective representation costs, not certificate acceptance. An
unconditional marker whose nominal exponent is too small still needs outward
repair during exact extraction; the count reports these markers explicitly.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from numba import njit


@njit(cache=True)
def analyze(Z, R, Cost, A, FC, req, ids, length, outs, which, grid, ts, zs):
    n, m = Z.shape
    visited = np.zeros((n, m), np.uint8)
    stack = np.empty(n * m, np.int64)
    top = 0
    for k in range(which.shape[0]):
        if outs[k, -1] >= 10:
            continue
        for i in range(n):
            j = which[k, i]
            if j >= 0 and not visited[i, j]:
                visited[i, j] = 1
                stack[top] = i*m+j
                top += 1
    records = edges = runs = input_markers = undersized_markers = 0
    weighted = unconditional = max_path = max_runs = 0
    failures = 0
    while top:
        top -= 1
        ix = stack[top]
        i, j = ix // m, ix % m
        records += 1
        aidx = A[i, j]
        if aidx == -1:
            input_markers += 1
            ei = np.interp(grid[i], ts, zs)
            if Z[i, j] <= ei:
                undersized_markers += 1
            continue
        if aidx == 0:
            failures += 1
            continue
        if aidx > 0:
            weighted += 1
            alpha = aidx
        else:
            unconditional += 1
            alpha = -aidx-2
        u = Z[i, j] - 1e-8
        previous = -1
        count_runs = 0
        max_path = max(max_path, i-alpha)
        for row in range(i, alpha, -1):
            if row == i:
                col = FC[i, j]
            else:
                lo, hi = 0, length[row]
                while lo < hi:
                    mid = (lo+hi)//2
                    if req[row, mid] < u:
                        lo = mid+1
                    else:
                        hi = mid
                if lo == 0:
                    failures += 1
                    break
                col = ids[row, lo-1]
            if col < 0 or (row == i and col >= j):
                failures += 1
                break
            if col != previous:
                count_runs += 1
            previous = col
            edges += 1
            if not visited[row, col]:
                visited[row, col] = 1
                stack[top] = row*m+col
                top += 1
            u -= Cost[row, col] * (grid[row]-grid[row-1])
        runs += count_runs
        max_runs = max(max_runs, count_runs)
        if aidx < -1 and u <= np.interp(grid[alpha], ts, zs):
            for col in range(m):
                if A[alpha, col] < 0 and R[alpha, col] > 14 and Z[alpha, col] < u:
                    if not visited[alpha, col]:
                        visited[alpha, col] = 1
                        stack[top] = alpha*m+col
                        top += 1
                    break
    return (records, edges, runs, input_markers, undersized_markers,
            weighted, unconditional, max_path, max_runs, failures)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('tables', type=Path)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    with np.load(args.tables) as table:
        data = {k: table[k] for k in table.files}
    grid = data.get('grid', np.linspace(0, 1, int(data['N'])+1))
    keys = ['Z', 'R', 'Cost', 'A', 'FC', 'req', 'ids', 'length', 'outs', 'which']
    counts = analyze(*(data[k] for k in keys), grid, data['ts'], data['zs'])
    names = ['reachable_records', 'expanded_path_references', 'column_runs',
             'input_markers', 'input_markers_requiring_repair', 'weighted_records',
             'unconditional_path_records', 'maximum_path_length',
             'maximum_runs_per_path', 'trace_failures']
    report = dict(status='SEARCH_PLAN_COUNTS_NOT_VERIFIED',
                  tables=str(args.tables), **dict(zip(names, map(int, counts))))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

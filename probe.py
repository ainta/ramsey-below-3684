"""Target-directed Bellman discovery; every output is UNVERIFIED SEARCH.

Reuses the author's search. U interpolation is only a discovery approximation;
an exact certificate must separately establish its initial majorant and all
subsequent inference-rule hypotheses. An explicit polygon input is diagnostic
and does not inherit Ramsey validity from a filename or saved report.
"""
import argparse
import json
import math
from pathlib import Path
import time
import numpy as np
from explore_v3 import sweep, forward, hull, initial


def terminal(ts, zs):
    def entropy(x):
        if x <= 0 or x >= 1:
            return 0.0
        return -x * math.log(x) - (1 - x) * math.log1p(-x)
    best = (math.inf, 0.0, 0.0, 0.0)
    for i in range(len(ts) - 1):
        lo, hi = max(float(ts[i]), 0.5), float(ts[i + 1])
        if hi < lo:
            continue
        d = float((zs[i + 1] - zs[i]) / (ts[i + 1] - ts[i]))
        a = float(zs[i] - d * ts[i])
        candidates = [lo, hi]
        if d > math.log(2):
            optimum = 1 / (2 * -math.expm1(-d))
            if lo <= optimum <= hi:
                candidates.append(optimum)
        for t in candidates:
            beta = 1 - t
            rate = entropy(beta) - entropy(2 * beta) / 2 + a + d * t
            if rate < best[0]:
                best = rate, t, a, d
    return dict(rate=best[0], base=math.exp(best[0]), ratio=best[1],
                intercept=best[2], slope=best[3])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--N', type=int, default=200)
    p.add_argument('--M', type=int, default=80)
    p.add_argument('--rounds', type=int, default=8)
    p.add_argument('--input-profile', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--target', type=float, default=3.684)
    p.add_argument('--save-tables', action='store_true')
    p.add_argument('--deficit-power', type=float, default=1.7)
    p.add_argument('--deficit-max', type=float, default=0.8)
    p.add_argument('--grid-power', type=float, default=1.0)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    grid = np.linspace(0, 1, args.N + 1) ** args.grid_power
    search_sweep, search_forward, search_grid = sweep, forward, args.N
    if args.grid_power != 1:
        from adaptive_search import sweep as adaptive_sweep, forward as adaptive_forward
        search_sweep, search_forward, search_grid = adaptive_sweep, adaptive_forward, grid
    if args.input_profile:
        points = json.loads(args.input_profile.read_text())
        if isinstance(points, dict):
            points = points['points'] if 'points' in points else points['input']
        ts = np.array([t[0] / t[1] for t, z in points])
        zs = np.array([z[0] / z[1] for t, z in points])
        source = dict(kind='EXPLICIT_DIAGNOSTIC_PROFILE', path=str(args.input_profile))
    else:
        ts, zs = initial('U')
        source = dict(kind='GNNW_U_DISCOVERY_APPROXIMATION')
    deficits = (np.linspace(0, 1, args.M) ** args.deficit_power * args.deficit_max)[::-1]
    report = dict(status='UNVERIFIED_SEARCH', N=args.N, M=args.M,
                  target=args.target, deficit_power=args.deficit_power,
                  deficit_max=args.deficit_max, grid_power=args.grid_power, source=source,
                  initial=terminal(ts, zs), rounds=[])
    began = time.monotonic()
    starts = [.05, .1, .2, .4, .6, .8]
    for rnd in range(args.rounds):
        print('START', rnd, 'diagonal', math.exp(zs[-1]),
              'terminal', terminal(ts, zs), flush=True)
        tick = time.monotonic()
        arrays = search_sweep(search_grid, deficits, ts, zs)
        Z, R, Cost, A, Mu, FC, su, depth, req, co, ids, length = arrays
        print('SWEEP', rnd, 'seconds', time.monotonic() - tick, flush=True)
        newts, newzs = ts.copy(), zs.copy()
        outs, which, outer_results = [], [], []
        for start in starts:
            F, W = search_forward(search_grid, Z, R, Cost, ts, zs, start)
            outs.append(F)
            which.append(W)
            j0 = max(1, round(start * args.N))
            if args.grid_power != 1:
                j0 = max(1, int(np.searchsorted(grid, start)))
            xs = grid[j0:]
            complete = F[-1] < 10
            row = dict(start=start, complete=bool(complete))
            if complete:
                row.update(terminal(xs, F[j0:]))
                tt = np.unique(np.r_[newts, xs])
                vv = np.interp(tt, newts, newzs)
                mask = tt >= xs[0]
                vv[mask] = np.minimum(vv[mask], np.interp(tt[mask], xs, F[j0:]))
                newts, newzs = tt, vv
            outer_results.append(row)
        if args.save_tables:
            np.savez_compressed(args.output / f'round_{rnd}.npz',
                ts=ts, zs=zs, N=args.N, grid=grid, deficits=deficits, Z=Z, R=R,
                Cost=Cost, A=A, Mu=Mu, FC=FC, startu=su, depth=depth,
                req=req, co=co, ids=ids, length=length,
                outs=np.array(outs), which=np.array(which))
        ts, zs = hull(newts, newzs)
        result = dict(round=rnd, terminal=terminal(ts, zs),
                      diagonal_base=math.exp(zs[-1]), outer=outer_results,
                      knots=len(ts), maximum_depth=int(depth.max()),
                      possible_states=int(np.count_nonzero(R > 0)),
                      elapsed_seconds=time.monotonic() - tick)
        report['rounds'].append(result)
        report['elapsed_seconds'] = time.monotonic() - began
        (args.output / 'search.json').write_text(json.dumps(report, indent=2) + '\n')
        # Preserve exact binary64 values explicitly; still NOT a certified profile.
        points = [[list(float(t).as_integer_ratio()), list(float(z).as_integer_ratio())]
                  for t, z in zip(ts, zs)]
        (args.output / 'search_profile.json').write_text(json.dumps(dict(
            status='UNVERIFIED_SEARCH', points=points), separators=(',', ':')))
        print('END', json.dumps({k: v for k, v in result.items() if k != 'outer'}), flush=True)
        if result['terminal']['base'] < args.target:
            print('SEARCH_TARGET_REACHED; exact certification is still required', flush=True)
            break


if __name__ == '__main__':
    main()

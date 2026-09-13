"""Extract and recheck only the GNNW majorant from a local baseline archive.

No baseline bootstrap round, prior PASS report, or predecessor bound is used.
The checks are the released exact U node and continuum chord-error checks.
They depend on the written analytic chord-error lemma and are not Lean proofs.
"""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import interval_arithmetic as I


def check_points(points):
    """Recheck the actual payload, not its status label or provenance hash."""
    S, V = 10**12, 2 * 10**36
    xs = [F(*t) * S for t, v in points]
    vs = [F(*v) * V for t, v in points]
    assert all(x.denominator == 1 for x in xs + vs)
    xs, vs = list(map(int, xs)), list(map(int, vs))
    assert len(xs) == len(vs) and len(xs) > 1
    assert xs[0] == S // 1000 and xs[-1] == S
    assert all(0 < a < b for a, b in zip(xs, xs[1:]))
    I.increasing_concave(xs, vs)
    for j, (x, value) in enumerate(zip(xs, vs)):
        assert I.ri(value, V)[0] > I.input_U(x, S)[1] + I.ceil_div(I.Q, 10**8)
        if j + 1 < len(xs):
            dx = xs[j + 1] - x
            assert (S + 2*x) * dx*dx * 10**8 < 8*x*S*S
    slope = F((vs[1] - vs[0]) * S, (xs[1] - xs[0]) * V)
    assert I.ri(slope.numerator, slope.denominator)[1] < I.input_Up(xs[0], S)[0]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('certificate', type=Path)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    raw = args.certificate.read_bytes()
    data = json.loads(gzip.decompress(raw))
    assert data['format_version'] == 3
    S, V = data['scale'], data['value_scale']
    assert S == 10**12 and V == 2 * S**3
    xs, vs = data['knots'], data['input_values']
    assert len(xs) == len(vs) and len(xs) > 1
    assert xs[0] == S // 1000 and xs[-1] == S
    assert all(0 < a < b for a, b in zip(xs, xs[1:]))
    I.increasing_concave(xs, vs)
    margin = None
    for j, (x, value) in enumerate(zip(xs, vs)):
        gap = I.ri(value, V)[0] - I.input_U(x, S)[1] - I.ceil_div(I.Q, 10**8)
        assert gap > 0, ('U node margin', j)
        margin = gap if margin is None else min(margin, gap)
        if j + 1 < len(xs):
            dx = xs[j + 1] - x
            assert (S + 2*x) * dx*dx * 10**8 < 8*x*S*S, ('chord error', j)
    first_slope = F((vs[1] - vs[0]) * S, (xs[1] - xs[0]) * V)
    assert I.ri(first_slope.numerator, first_slope.denominator)[1] < I.input_Up(xs[0], S)[0]
    points = [[list(F(x, S).as_integer_ratio()), list(F(v, V).as_integer_ratio())]
              for x, v in zip(xs, vs)]
    result = dict(status='FINITE_U_MAJORANT_CHECKS_PASS_NOT_LEAN',
        source_sha256=hashlib.sha256(raw).hexdigest(),
        source=str(args.certificate), bootstrap_rounds_used=0,
        node_margin_lower=I.fmt(margin), points=points)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'points'}, indent=2))
    print('knots', len(points))


if __name__ == '__main__':
    main()

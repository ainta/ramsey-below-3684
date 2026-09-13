"""Exact terminal check for a concave polygon and its supporting affine line.

Floating point only SELECTS a candidate cell. All accepted comparisons use
Fraction and the released directed integer arithmetic. No acceptance depends
on the exploratory minimization being correct or optimal.
"""
from fractions import Fraction as F
from math import exp, log, expm1, isqrt
import interval_arithmetic as I


def check_terminal(profile, target=F(921, 250), affine=None):
    profile.check_shape()
    best = None
    for j, ((l, v), (r, w)) in enumerate(zip(profile.p, profile.p[1:])):
        if r < F(1, 2):
            continue
        d = (w-v)/(r-l)
        a = v-d*l
        if float(d) <= log(2) or a <= 0 or a >= 1 or d >= 1:
            continue
        rate = float(a)+log(2)+log(expm1(float(d)))/2
        if best is None or rate < best[0]:
            best = rate, j, a, d
    assert best is not None
    _, j, a, d = best
    if affine is not None:
        a, d = map(F, affine)
        j = None
    # The all-subsets transfer needs a GLOBAL affine bound, not just one cell.
    assert all(a+d*t >= v for t, v in profile.p)
    assert a >= profile.p[0][1]-profile.sl[0]*profile.p[0][0]
    ai, di = I.ri(a.numerator, a.denominator), I.ri(d.numerator, d.denominator)
    assert di[0] > I.LOG2[1]
    ea = I.div_positive(I.ONE, I.exp_minus_unit(a.numerator, a.denominator))
    ed = I.div_positive(I.ONE, I.exp_minus_unit(d.numerator, d.denominator))
    sq = I.scale(I.mul(I.mul(ea, ea), I.sub(ed, I.ONE)), 4)
    scale = 10**12
    radicand = sq[1]*scale*scale
    numerator = isqrt(radicand//I.Q)
    if numerator*numerator*I.Q < radicand:
        numerator += 1
    upper = F(numerator, scale)
    assert numerator*numerator*I.Q >= radicand
    margin = target*target*I.Q-sq[1]
    return dict(status='PASS_TARGET' if margin > 0 else 'TARGET_NOT_REACHED',
                target=str(target), base_upper=str(upper),
                base_upper_decimal=I.fmt(upper.numerator, upper.denominator, 12),
                selected_cell=j, intercept=str(a), slope=str(d),
                squared_margin_scaled=str(margin),
                scope='Exact finite arithmetic plus the written global-affine maximum-clique transfer; not Lean verified')

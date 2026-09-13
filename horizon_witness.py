"""Rational-interval witness for the support-condition failure (paper, App. D).

Certifies, with outward rounding only, the two displayed bounds of the
3.6961 witness proposition: at t0 = 0.00229,

    A + t0*B < 0.005342   and   U(t0) > 0.015642,

with a gap exceeding 0.0103, where A = -log X*, B = -log Y*,
X* = chi(F'(t*), m*) and Y* = (1-0.0012) c_rel / X* at t* = m* = 0.001,
for both readings of c_rel (the released decimal and (1/4) e^{0.137/e}).
"""
from fractions import Fraction
import json
import sys

import interval_arithmetic as I

Q = I.Q
ONE = I.ONE

T_STAR = Fraction(1, 1000)
M_STAR = Fraction(1, 1000)
T0 = Fraction(229, 100000)
C_REL_DECIMAL = Fraction(26292278641656774, 10**17)
SHRINK = Fraction(9988, 10000)          # 1 - 0.0012
BOUND_AT0B = Fraction(5342, 10**6)
BOUND_U = Fraction(15642, 10**6)
BOUND_GAP = Fraction(103, 10**4)


def rif(f):
    return I.ri(f.numerator, f.denominator)


def dec_floor(v, digits=12):
    n = v * 10**digits // Q
    return f'{n // 10**digits}.{n % 10**digits:0{digits}d}'


def dec_ceil(v, digits=12):
    n = I.ceil_div(v * 10**digits, Q)
    return f'{n // 10**digits}.{n % 10**digits:0{digits}d}'


def exp_neg(x):
    """e^{-x} for an interval x with 0 <= x <= 8, via eighth roots."""
    lo, hi = x
    assert 0 <= lo and hi <= 8 * Q
    def eighth(n):
        v = I.exp_minus_unit(n, 8 * Q)
        for _ in range(3):
            v = I.mul(v, v)
        return v
    return eighth(hi)[0], eighth(lo)[1]


def log_iv(x):
    """log of a positive interval."""
    assert x[0] > 0
    return I.log_rat(x[0], Q)[0], I.log_rat(x[1], Q)[1]


def fprime(t):
    """F'(t) = log(1+t) - log t + (P'(t) - P(t)) e^{-t}, exact rational t."""
    p = -t / 4 + Fraction(33, 1000) * t**2 + Fraction(2, 25) * t**3 \
        - Fraction(389, 5000) * t**5
    dp = Fraction(-1, 4) + Fraction(66, 1000) * t + Fraction(6, 25) * t**2 \
        - Fraction(389, 1000) * t**4
    logs = I.sub(I.log_rat((1 + t).numerator, (1 + t).denominator),
                 I.log_rat(t.numerator, t.denominator))
    return I.add(logs, I.mul(rif(dp - p),
                             I.exp_minus_unit(t.numerator, t.denominator)))


def witness(c_rel_interval, label):
    fp = fprime(T_STAR)
    g = I.sub(ONE, exp_neg(fp))                      # 1 - e^{-F'(t*)}
    # A = -log X* = log(1/(1-m*)) - (1/(1-m*)) log g
    one_minus_m = 1 - M_STAR
    a = I.sub(I.log_rat(one_minus_m.denominator, one_minus_m.numerator),
              I.mul(rif(1 / one_minus_m), log_iv(g)))
    # B = -log Y* = -log SHRINK - log c_rel + log X* = -log SHRINK - log c_rel - A
    b = I.sub(I.sub(I.log_rat(SHRINK.denominator, SHRINK.numerator),
                    log_iv(c_rel_interval)), a)
    v = I.add(a, I.mul(rif(T0), b))                  # A + t0 B
    u = I.input_U(T0.numerator, T0.denominator)      # U(t0)
    ok = (v[1] < rif(BOUND_AT0B)[0] and
          u[0] > rif(BOUND_U)[1] and
          u[0] - v[1] > rif(BOUND_GAP)[1])
    return ok, dict(reading=label,
                    A_upper=dec_ceil(a[1]), B_upper=dec_ceil(b[1]),
                    A_plus_t0_B_upper=dec_ceil(v[1]),
                    U_t0_lower=dec_floor(u[0]),
                    gap_lower=dec_floor(u[0] - v[1]))


def main():
    # Reading 1: the released decimal.
    dec = rif(C_REL_DECIMAL)
    # Reading 2: (1/4) e^{0.137/e}.
    e_iv = I.div_positive(ONE, I.exp_minus_unit(1, 1))
    x = I.div_positive(rif(Fraction(137, 1000)), e_iv)
    assert 0 < x[0] and x[1] < Q
    e_x = I.div_positive(ONE, (I.exp_minus_unit(x[1], Q)[0],
                               I.exp_minus_unit(x[0], Q)[1]))
    quarter = I.div_pos_int(e_x, 4)
    results, passed = [], True
    for c, label in ((dec, 'released decimal'), (quarter, 'quarter exp(0.137/e)')):
        ok, row = witness(c, label)
        passed = passed and ok
        results.append(row)
    report = dict(status='PASS_HORIZON_WITNESS' if passed else 'FAILED',
                  t_star='0.001', m_star='0.001', t0='0.00229',
                  bounds=dict(A_plus_t0_B='< 0.005342', U_t0='> 0.015642',
                              gap='> 0.0103'),
                  readings=results)
    print(json.dumps(report, indent=2))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())

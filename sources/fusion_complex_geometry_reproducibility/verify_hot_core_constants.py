"""Rational certificates for the Maxwellian hot-core lower bounds.

No floating-point value is used to prove an inequality.  Pi is bounded
using Machin's identity and alternating arctangent series; exp and the
Gaussian integral use alternating Taylor series.  Square-root bounds
are rational, obtained with integer square roots.  Printed decimal
values are only for readability.
"""
from fractions import Fraction as F
from math import factorial, isqrt
import json


def alternating_bounds(terms):
    # The caller supplies terms through N+1, with the final tail in the
    # monotonically decreasing regime of the alternating series.
    partial = sum(terms[:-1], F(0))
    adjacent = partial + terms[-1]
    return min(partial, adjacent), max(partial, adjacent)


def atan_bounds(x, N=100):
    return alternating_bounds([
        (-1)**j * x**(2*j+1) / (2*j+1) for j in range(N+2)
    ])


a5 = atan_bounds(F(1, 5))
a239 = atan_bounds(F(1, 239))
pi_lo = 16*a5[0] - 4*a239[1]
pi_hi = 16*a5[1] - 4*a239[0]
assert F(3141592653589793238, 10**18) < pi_lo < pi_hi
assert pi_hi < F(3141592653589793239, 10**18)


def sqrt_bounds(lo, hi, digits=90):
    scale = 10**digits
    lower_integer = isqrt((lo.numerator*scale**2)//lo.denominator)
    upper_integer = isqrt((hi.numerator*scale**2)//hi.denominator) + 1
    lower, upper = F(lower_integer, scale), F(upper_integer, scale)
    assert lower**2 <= lo <= hi <= upper**2
    return lower, upper


K_lo, K_hi = sqrt_bounds(2/pi_hi, 2/pi_lo)


def hot_bounds(c, N=120):
    t = c*c/2
    # From index N onward both series have strictly decreasing terms.
    assert t < N+1
    exp_lo, exp_hi = alternating_bounds([
        (-t)**j / factorial(j) for j in range(N+2)
    ])
    int_lo, int_hi = alternating_bounds([
        (-1)**j * c**(2*j+1) / (2**j*factorial(j)*(2*j+1))
        for j in range(N+2)
    ])
    a_lo = K_lo*(int_lo-c*exp_hi)
    a_hi = K_hi*(int_hi-c*exp_lo)
    b_lo = K_lo*(int_lo-(c+c**3/3)*exp_hi)
    b_hi = K_hi*(int_hi-(c+c**3/3)*exp_lo)
    d_lo = K_lo*(c*c+2)*exp_lo
    d_hi = K_hi*(c*c+2)*exp_hi
    assert 0 < a_lo < a_hi < 1 and 0 < b_lo < b_hi < 1
    theta_lo = b_lo-d_hi**2/(3*a_lo*a_lo)
    theta_hi = b_hi-d_lo**2/(3*a_hi*a_hi)
    delta = F(1, 100)
    pert_lo = (1-delta)/(1+delta)*b_lo \
        -(d_hi+delta*2*K_hi)**2/(3*(1-delta)**2*a_lo*a_lo)
    tensor_lo = b_lo-d_hi**2/(a_lo*a_lo)
    pert_tensor_lo = (1-delta)/(1+delta)*b_lo \
        -(d_hi+delta*2*K_hi)**2/((1-delta)**2*a_lo*a_lo)
    return a_lo, a_hi, theta_lo, theta_hi, pert_lo, tensor_lo, pert_tensor_lo


result = []
for c, n_target, t_target, pert_target in [
    (F(14,5), F(95056321,10**8), F(82577125,10**8), F(80709315,10**8)),
    (F(3), F(97070911,10**8), F(88757292,10**8), None),
]:
    al, au, tl, tu, pl, tensor, pert_tensor = hot_bounds(c)
    assert al > n_target
    assert tl > t_target
    if pert_target is not None:
        assert pl > pert_target
    if c == F(14,5):
        assert F(25,2)*tensor > F(100983,10000)
    if c == 3:
        assert F(25,2)*pert_tensor > F(107419,10000)
    result.append({
        'c':str(c), 'density_ratio_strict_lower_bound':str(n_target),
        'temperature_ratio_strict_lower_bound':str(t_target),
        'one_percent_perturbation_temperature_lower_bound':
            None if pert_target is None else str(pert_target),
        'display_density_ratio':float(al),
        'display_temperature_ratio':float(tl),
        'display_perturbed_temperature_ratio':float(pl),
        'display_tensor_temperature_keV_at_12_5':float(F(25,2)*tensor),
        'display_perturbed_tensor_temperature_keV_at_12_5':float(F(25,2)*pert_tensor),
        'all_assertions_use_exact_rationals':True,
    })
print(json.dumps(result, indent=2))

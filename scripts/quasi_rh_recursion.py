#!/usr/bin/env python3
"""Stage B: the length-optimisation recursion of Liu, arXiv:2610.12234 (after OpenAI's 7/8).

Formulas transcribed from the paper (Sections 25, 29, 30, 27):
  kappa = 2*sigma - 1                         moment hypothesis beta_* <= (1+kappa)/2
  (216k-18) d^2 - (468k-57) d + 150k - 20 = 0  critical class (counting exponent R = 2/3), xi = smaller root
  B(xi) = (18 xi + 7)/(18 xi + 9)             new bound
Fixed point: 1188 xi^3 - 2160 xi^2 + 171 xi + 190 = 0, B_new = 0.874957019420...
Also checks B_alg = (1507 - 2 sqrt 921)/1653 = B at kappa = 3/4, and the weighted
combination of the three constraints L_0, L_K, H_c that gives B >= (7+18d)/(9+18d).
"""
import json, os
import mpmath as mp
mp.mp.dps = 30

def xi_of_kappa(k):
    a, b, c = 216 * k - 18, -(468 * k - 57), 150 * k - 20
    r = mp.sqrt(b * b - 4 * a * c)
    return min((-b - r) / (2 * a), (-b + r) / (2 * a))

def B(xi): return (18 * xi + 7) / (18 * xi + 9)

out = {}
# fixed point from the cubic
xi_new = mp.findroot(lambda x: 1188 * x**3 - 2160 * x**2 + 171 * x + 190, 0.3886)
out['xi_new'] = mp.nstr(xi_new, 20); out['B_new'] = mp.nstr(B(xi_new), 20)
out['B_alg_closed_form'] = mp.nstr((1507 - 2 * mp.sqrt(921)) / 1653, 15)
out['B_at_kappa_3_4'] = mp.nstr(B(xi_of_kappa(mp.mpf(3) / 4)), 15)
# iterations from several starting hypotheses
runs = {}
for name, s0 in (('sigma0=1 (trivial)', mp.mpf(1)), ('sigma0=7/8', mp.mpf(7) / 8), ('sigma0=0.95', mp.mpf('0.95'))):
    s = s0; seq = [mp.nstr(s, 15)]
    for _ in range(8):
        s = B(xi_of_kappa(2 * s - 1)); seq.append(mp.nstr(s, 15))
    runs[name] = seq
out['iterations'] = runs
# sensitivity of the new bound to the moment input
out['dB_dsigma_at_fixed_point'] = mp.nstr(mp.diff(lambda s: B(xi_of_kappa(2 * s - 1)), B(xi_new)), 6)
out['B_if_moment_were_perfect_kappa_13_18'] = mp.nstr(B(xi_of_kappa(mp.mpf(13) / 18)), 12)
# weighted combination check (symbolic in d, numeric spot check)
def comb(d, M, l):
    L0 = mp.mpf(5) / 6 + M / 12 - l / 6
    LK = mp.mpf(1) / 3 + 7 * M / 12 + l / 3
    Hc = 1 + d - (1 + d) * M / 2 + d * l
    w0, wK, wH = (4 + 18 * d) / (9 + 18 * d), 2 / (9 + 18 * d), 3 / (9 + 18 * d)
    return w0 * L0 + wK * LK + wH * Hc, (7 + 18 * d) / (9 + 18 * d)
chk = [comb(mp.mpf(d), mp.mpf(M), mp.mpf(l)) for d, M, l in ((0.39, 0.3, 0.17), (0.2, 0.9, 0.05), (0.5, 0.1, 0.4))]
out['weighted_combination_independent_of_M_l'] = all(abs(a - b) < mp.mpf(10) ** -25 for a, b in chk)
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'quasi_rh_recursion.json'), 'w'), indent=1)

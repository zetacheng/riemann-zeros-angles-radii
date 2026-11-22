#!/usr/bin/env python3
"""Sensitivity of the backward collision time of the closest pair to the truncation (issue #3).

The zero dynamics dz_k/dt = 2 sum_{j != k} 1/(z_k - z_j) (z = 2 gamma) is integrated backward for
clusters of 2K+2 zeros centred on the closest pair of the first 1200 zeros (gamma = 1329.04), for
K = 0 (isolated pair), 5, 10, 20, 40, 80, 160 and for all 1200 zeros.  Zeros outside the cluster are
ignored (free boundary).  We also estimate the effect of the zeros above the 1200th on the initial
rate d(gap)/dt: with zero density rho(z) = log(z/(4 pi))/(4 pi) per unit z, their contribution is
about 2 d * int_{z_max}^infinity rho(z)/(z - z_k)^2 dz (the far field compresses the gap only to
second order in d).  This is a finite-cluster approximation of the de Bruijn-Newman flow, not the
full infinite-zero deformation.  Writes validation/cluster_sensitivity.json.
"""
import json, math, os
import numpy as np
from scipy.integrate import solve_ivp, quad
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
gam = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json')))); z0 = 2 * gam; n = len(z0)
k = int(np.argmin(np.diff(z0)[:-20])); d0 = z0[k + 1] - z0[k]

def vel(z):
    D = z[:, None] - z[None, :]; np.fill_diagonal(D, np.inf); return 2 * np.sum(1 / D, axis=1)

def collision_time(lo, hi):
    zc = z0[lo:hi].copy(); i = k - lo
    def hit(t, y): return y[i + 1] - y[i] - 1e-5 * d0
    hit.terminal = True
    sol = solve_ivp(lambda t, y: -vel(y), (0, 0.05), zc, events=hit, rtol=1e-11, atol=1e-13, max_step=2e-4)
    return float(-sol.t_events[0][0]) if len(sol.t_events[0]) else None

rows = []
for K in (0, 5, 10, 20, 40, 80, 160):
    lo, hi = max(0, k - K), min(n, k + K + 2)
    rows.append(dict(K=K, cluster_size=hi - lo, t_collision=collision_time(lo, hi)))
    print(rows[-1], flush=True)
rows.append(dict(K='all', cluster_size=n, t_collision=collision_time(0, n))); print(rows[-1], flush=True)

zk = z0[k]; zmax = z0[-1]
rho = lambda z: math.log(z / (4 * math.pi)) / (4 * math.pi)
tail_rate = 2 * d0 * quad(lambda z: rho(z) / (z - zk) ** 2, zmax, np.inf)[0]   # compression of the gap
pair_rate = 4 / d0
out = dict(gamma=float(gam[k]), gap_gamma=float(d0 / 2), isolated_pair_time=float(-d0 ** 2 / 8), rows=rows,
           tail_rate_estimate=tail_rate, pair_rate=pair_rate, relative_tail_effect=tail_rate / pair_rate)
print(json.dumps({k_: v for k_, v in out.items() if k_ != 'rows'}, indent=1))
json.dump(out, open(os.path.join(ROOT, 'validation', 'cluster_sensitivity.json'), 'w'), indent=1)

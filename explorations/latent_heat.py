#!/usr/bin/env python3
"""Is there a 'latent heat' that absorbs the approach to a collision?  (author's idea, log 67)

The zero dynamics dz_k/dt = 2 sum 1/(z_k - z_j) is the gradient flow of the log-gas energy
W = -2 sum_{i<j} log|z_i - z_j|.  For the closest pair of the first 1200 zeros (gamma = 1329.04)
we integrate a cluster of 41 zeros backward and record the squared gap d^2 and the pair energy
-2 log d.  If the approach were absorbed (slowed down near the collision), d^2 would bend away
from a straight line; for an isolated pair d(d^2)/dt = 8 exactly.
Writes latent_heat.json and latent_heat.png.
"""
import json, os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
gam = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json')))); z0 = 2 * gam
k = int(np.argmin(np.diff(z0)[:-20])); lo, hi = k - 20, k + 21; zc = z0[lo:hi]; i = k - lo
def vel(z):
    D = z[:, None] - z[None, :]; np.fill_diagonal(D, np.inf); return 2 * np.sum(1 / D, axis=1)
def hit(t, y): return y[i + 1] - y[i] - 1e-4
hit.terminal = True
sol = solve_ivp(lambda t, y: -vel(y), (0, 0.05), zc, events=hit, rtol=1e-11, atol=1e-13, dense_output=True, max_step=2e-4)
tau = np.linspace(0, sol.t[-1], 400); Y = sol.sol(tau)
d = Y[i + 1] - Y[i]; t = -tau
slope = np.polyfit(t[:300], d[:300] ** 2, 1)[0]
out = dict(gamma=float(gam[k]), collision_t=float(-sol.t[-1]), slope_d2_dt=float(slope),
           d2_start=float(d[0] ** 2), linearity_max_dev=float(np.max(np.abs(d ** 2 - (d[0] ** 2 + slope * t))) / d[0] ** 2))
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'latent_heat.json'), 'w'), indent=1)
plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(9.5, 3.5))
a1.plot(t, d ** 2, color='#1f4e79'); a1.plot(t, d[0] ** 2 + 8 * t, '--', color='#888888', lw=0.9, label='isolated pair: slope 8')
a1.set_xlabel('heat-flow time $t$ (backward)'); a1.set_ylabel('squared gap $d^2$'); a1.legend(frameon=False, fontsize=8)
a1.set_title(f'(a) closest pair ($\\gamma={gam[k]:.2f}$): no slowing')
a2.plot(t, -2 * np.log(d), color='#c0392b'); a2.set_xlabel('$t$'); a2.set_ylabel('pair energy $-2\\log d$')
a2.set_title('(b) the barrier diverges only logarithmically')
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'latent_heat.png'), dpi=130, bbox_inches='tight')

#!/usr/bin/env python3
"""Can spacing work at every height?  The de Bruijn-Newman heat flow (log entry 63).

H_t(z) is the heat-flow deformation of the xi function with H_0(z) = xi(1/2 + iz/2)/8, so the real
zeros of H_0 are z = 2 gamma.  While the zeros stay simple and real they move by
    dz_k/dt = 2 sum_{j != k} 1/(z_k - z_j)        (repulsion forward in t),
so an isolated pair with gap d obeys d(d^2)/dt = 8: running the flow backward, it collides at
t = -d^2/8 and the zeros leave the real line.  Lambda >= 0 (Rodgers-Tao) says such collisions
come arbitrarily close to t = 0.  We use the first 1200 zeros of zeta:
 (1) for each neighbouring pair, the collision time backward, from the pair term plus the
     linearised push of all other zeros, checked against direct integration of the flow for
     a cluster of 41 zeros around the closest pairs;
 (2) the smallest normalised gap, before and after running the flow forward to t = 0.05, 0.2.
Truncation: zeros above the 1200th are ignored (their effect on a gap is a slowly varying shift).
Writes heat_flow_spacing.json and heat_flow_spacing.png.
"""
import json, math, os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
gam = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))
z0 = 2 * gam
n = len(z0)

def velocity(z):
    D = z[:, None] - z[None, :]
    np.fill_diagonal(D, np.inf)
    return 2 * np.sum(1 / D, axis=1)

# (1) linearised collision times
d = np.diff(z0)
v = velocity(z0)
push = v[1:] - v[:-1]                       # d(gap)/dt at t = 0, including the pair term 4/d
# d(d^2)/dt = 2 d * push ; backward collision time estimate t* = -d^2 / (2 d push)
tstar = -d ** 2 / (2 * d * push)
order = np.argsort(np.abs(tstar))
checks = []
for k in order[:5]:
    lo, hi = max(0, k - 20), min(n, k + 22)
    zc = z0[lo:hi].copy(); i = k - lo
    def rhs(t, y): return -velocity(y)        # integrate backward in t (tau = -t)
    def hit(t, y): return y[i + 1] - y[i] - 1e-6 * d[k]
    hit.terminal = True
    sol = solve_ivp(rhs, (0, 5 * abs(tstar[k]) + 1e-3), zc, events=hit, rtol=1e-10, atol=1e-12, max_step=abs(tstar[k]) / 50)
    tc = -sol.t_events[0][0] if len(sol.t_events[0]) else None
    checks.append(dict(pair=int(k), gamma=float(gam[k]), gap_gamma=float(gam[k + 1] - gam[k]),
                       t_linearised=float(tstar[k]), t_cluster_ode=tc, isolated_pair=float(-d[k] ** 2 / 8)))
    print(json.dumps(checks[-1]), flush=True)

# window minima of |t*| against height
win = 100
wins = []
for a in range(0, n - 1, win):
    b = min(a + win, n - 1)
    j = a + int(np.argmin(np.abs(tstar[a:b])))
    wins.append(dict(gamma_mid=float(gam[(a + b) // 2]), min_abs_t=float(abs(tstar[j])), at_gamma=float(gam[j])))

# (2) forward flow: smallest normalised gap (gap * log(gamma/2pi)/2pi in gamma units)
def norm_min_gap(z):
    g = z / 2; dg = np.diff(g); mid = (g[1:] + g[:-1]) / 2
    s = dg * np.log(mid / (2 * np.pi)) / (2 * np.pi)
    inner = slice(100, len(s) - 100)        # avoid edge effects of the truncation
    return float(np.min(s[inner])), float(np.std(s[inner]))
fwd = []
for T in (0.0, 0.05, 0.2):
    if T == 0:
        z = z0.copy()
    else:
        sol = solve_ivp(lambda t, y: velocity(y), (0, T), z0, rtol=1e-8, atol=1e-10)
        z = sol.y[:, -1]
    mg, sd = norm_min_gap(z)
    fwd.append(dict(t=T, min_normalised_gap=mg, std_normalised_gap=sd))
    print('forward t=%.2f  min normalised gap %.4f  std %.4f' % (T, mg, sd), flush=True)

out = dict(n_zeros=n, closest=checks, windows=wins, forward=fwd)
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'heat_flow_spacing.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(10, 3.8))
a1.semilogy([w['gamma_mid'] for w in wins], [w['min_abs_t'] for w in wins], 'o-', color='#1f4e79', ms=3.5)
a1.set_xlabel('height $\\gamma$ (window of 100 zeros)'); a1.set_ylabel('earliest backward collision $|t^*|$')
a1.set_title('(a) collisions approach $t=0$ from below')
a2.bar([str(f['t']) for f in fwd], [f['std_normalised_gap'] for f in fwd], color='#2e7d32')
a2.set_xlabel('forward heat-flow time $t$'); a2.set_ylabel('spread of normalised gaps (std)')
a2.set_title('(b) forward flow evens out the spacing')
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'heat_flow_spacing.png'), dpi=130, bbox_inches='tight')

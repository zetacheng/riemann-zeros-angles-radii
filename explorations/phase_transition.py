#!/usr/bin/env python3
"""The heat flow as a phase transition (author's proposal, log entry 65).

Control parameter: heat-flow time t.  Phases: t >= Lambda, all zeros real ("ordered");
t < Lambda, some zeros complex.  Rodgers-Tao: Lambda >= 0, so RH <=> Lambda = 0.
For the first N zeros (system size N) we define
  apparent critical point  t_c(N) = max_k t*_k  (the backward collision closest to 0),
  order parameter          m(t; N) = max_k Im z_k(t) ~ max_k sqrt(2 (t*_k - t))  for t < t*_k,
with t*_k the linearised collision time of the pair (k, k+1) (see heat_flow_spacing.py; checked
there against direct integration).  Finite-size scaling: t*_k = -(gap in gamma)^2/2 up to
neighbour corrections, and gaps are (2 pi / log(gamma/2 pi)) s with s the normalised gap.  If the
small gaps follow GUE, p(s) ~ (pi^2/3) s^2, the smallest normalised gap among N behaves like
N^{-1/3} (Ben Arous-Bourgade), so |t_c(N)| ~ N^{-2/3} (log)^{-2}.
We compare the zeta zeros with GUE samples (bulk, unfolded by the semicircle law).
Writes phase_transition.json and phase_transition.png.
"""
import json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
gam = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))
z0 = 2 * gam; n = len(z0)
D = z0[:, None] - z0[None, :]; np.fill_diagonal(D, np.inf); v = 2 * np.sum(1 / D, axis=1)
d = np.diff(z0); push = v[1:] - v[:-1]
tstar = np.where(push > 0, -d ** 2 / (2 * d * np.where(push > 0, push, 1)), -np.inf)  # pairs whose gap shrinks backward
tstar[-20:] = -np.inf                                     # truncation edge
mid = (gam[1:] + gam[:-1]) / 2
s = np.diff(gam) * np.log(mid / (2 * np.pi)) / (2 * np.pi)  # normalised gaps

Ns = np.unique(np.round(np.logspace(np.log10(30), np.log10(n - 1), 25)).astype(int))
tc = np.array([np.max(tstar[:N]) for N in Ns])           # closest to zero (all negative)
smin = np.array([np.min(s[5:N]) for N in Ns])            # skip the first few (very low heights)

# GUE comparison: smallest unfolded gap among the first N bulk gaps, averaged in log over samples
rng = np.random.default_rng(0)
size, samples = 2000, 40
logmins = []
gue_mean_check = []
for _ in range(samples):
    A = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    H = (A + A.conj().T) / 2
    ev = np.linalg.eigvalsh(H)
    R = (ev[-1] - ev[0]) / 2; c0 = (ev[-1] + ev[0]) / 2          # semicircle radius from the edges
    bulk = ev[np.abs(ev - c0) < 0.6 * R]
    x = (bulk[1:] + bulk[:-1]) / 2 - c0
    sg = np.diff(bulk) * size * 2 * np.sqrt(R * R - x ** 2) / (np.pi * R * R)   # unfolded gaps, mean ~ 1
    gue_mean_check.append(float(np.mean(sg)))
    logmins.append([math.log(np.min(sg[:N])) for N in Ns if N <= len(sg)])
L = min(len(x) for x in logmins)
gue_smin = np.exp(np.mean([x[:L] for x in logmins], axis=0))
gue_mean_gap = float(np.mean(gue_mean_check))

def slope(x, y):
    return float(np.polyfit(np.log(x), np.log(y), 1)[0])
fit_lo = Ns >= 100
res = dict(n_zeros=n, Ns=Ns.tolist(), t_c=tc.tolist(), s_min_zeta=smin.tolist(), s_min_gue=gue_smin.tolist(),
           slope_s_min_zeta=slope(Ns[fit_lo], smin[fit_lo]), slope_s_min_gue=slope(Ns[:L][fit_lo[:L]], gue_smin[fit_lo[:L]]),
           slope_abs_tc=slope(Ns[fit_lo], -tc[fit_lo]),
           slope_abs_tc_times_log2=slope(Ns[fit_lo], -tc[fit_lo] * np.log(mid[Ns[fit_lo] - 1] / (2 * np.pi)) ** 2),
           gue_prediction_s_min=-1 / 3, gue_prediction_tc=-2 / 3, gue_mean_unfolded_gap=gue_mean_gap)
print(json.dumps({k: (round(v, 3) if isinstance(v, float) else v) for k, v in res.items() if k.startswith('slope') or k.startswith('gue_')and not isinstance(v, list)}, indent=1))
for N, a, b in zip(Ns, tc, smin): print(f'N={N:5d}  t_c(N)={a:+.4f}  s_min={b:.4f}')

# order parameter curves
ts = np.linspace(-0.6, 0.0, 601)
curves = {}
for N in (100, 300, 1199):
    m = np.array([np.max(np.sqrt(2 * np.maximum(tstar[:N] - t, 0))) for t in ts])
    curves[N] = m
res['order_parameter_t'] = ts.tolist(); res['order_parameter'] = {str(k): v.tolist() for k, v in curves.items()}
json.dump(res, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'phase_transition.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(1, 3, figsize=(13, 3.8))
cols = {100: '#2e7d32', 300: '#1f4e79', 1199: '#c0392b'}
for N, m in curves.items():
    ax[0].plot(ts, m, color=cols[N], label=f'first $N={N}$ zeros')
ax[0].axvline(0, color='#888888', lw=0.6)
ax[0].set_xlabel('heat-flow time $t$'); ax[0].set_ylabel('order parameter $\\max\\,\\mathrm{Im}\\,z$')
ax[0].set_title('(a) order parameter: onset moves to $t=0$'); ax[0].legend(frameon=False, fontsize=8)
ax[1].loglog(Ns, -tc, 'o-', color='#1f4e79', ms=3.5, label='$|t_c(N)|$, zeta zeros')
ref = -tc[fit_lo][0] * (Ns[fit_lo] / Ns[fit_lo][0]) ** (-2 / 3)
ax[1].loglog(Ns[fit_lo], ref, '--', color='#888888', lw=0.9, label='slope $-2/3$ (GUE, without the log factor)')
ax[1].set_xlabel('system size $N$ (number of zeros)'); ax[1].set_title('(b) apparent critical point $t_c(N)\\to0^-$')
ax[1].legend(frameon=False, fontsize=8)
ax[2].loglog(Ns, smin, 'o-', color='#1f4e79', ms=3.5, label='zeta zeros')
ax[2].loglog(Ns[:L], gue_smin, 's-', color='#c0392b', ms=3.5, label=f'GUE ({samples} samples)')
ax[2].loglog(Ns[fit_lo], smin[fit_lo][0] * (Ns[fit_lo] / Ns[fit_lo][0]) ** (-1 / 3), '--', color='#888888', lw=0.9, label='slope $-1/3$')
ax[2].set_xlabel('$N$'); ax[2].set_ylabel('smallest normalised gap'); ax[2].set_title('(c) the critical fluctuations: GUE')
ax[2].legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'phase_transition.png'), dpi=130, bbox_inches='tight')

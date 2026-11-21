#!/usr/bin/env python3
"""Reproducible experiments for
"Angles and Radii of the Riemann Zeros: A Numerical Study of the Discrete Spectrum".

Usage:  python3 experiments.py [path/to/zeros_1200.json]

If the zeros file is absent it is regenerated with mpmath.zetazero (about
3 minutes).  All randomness uses numpy default_rng(0).  Writes
../validation/results.json and the PDF figures in ../figures/.
"""
import json, math, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ZFILE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'data', 'zeros_1200.json')
NZ, GAMMA_CUT, SEED = 1200, 600.0, 0

if not os.path.exists(ZFILE):
    import mpmath as mp
    mp.mp.dps = 15
    json.dump([float(mp.zetazero(k).imag) for k in range(1, NZ + 1)], open(ZFILE, 'w'))
g0 = np.array(json.load(open(ZFILE)))[:NZ]
rng = np.random.default_rng(SEED)
res = {'n_zeros': int(g0.size), 'gamma_first': float(g0[0]), 'gamma_last': float(g0[-1]),
       'smoothing_Gamma': GAMMA_CUT, 'seed': SEED}

# ---------------------------------------------------------------- helpers
def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0

def reverse_trace(t, g, delta=None):
    """R(t) = - sum_k w(gamma_k) A_k(t) cos(gamma_k t), w = exp(-(gamma/Gamma)^2).
    A_k = 1 on the critical line; A_k = cosh(delta_k t) for a symmetric
    off-line pair beta = 1/2 +- delta_k (normalised so that delta=0 gives 1)."""
    w = np.exp(-(g / GAMMA_CUT) ** 2)
    C = np.cos(np.outer(t, g))
    if delta is not None:
        C = C * np.cosh(np.outer(t, delta))
    return -(C * w).sum(1)

N = 90
PP = [n for n in range(2, N + 1) if vonmangoldt(n) > 0]
COMP = [n for n in range(2, N + 1) if vonmangoldt(n) == 0]
t = np.linspace(0.5, 4.5, 8001)
ideal = sum(vonmangoldt(n) / math.sqrt(n) * np.exp(-GAMMA_CUT ** 2 * (t - math.log(n)) ** 2 / 4) for n in PP)

def local_peaks(R, thr):
    return [i for i in range(1, len(t) - 1) if R[i] > R[i - 1] and R[i] > R[i + 1] and R[i] > thr]

def score(R):
    corr = float(np.corrcoef(R, ideal)[0, 1])
    ref = float(np.median([R[np.argmin(abs(t - math.log(p)))] for p in (2, 3, 5, 7)]))
    pk = [t[i] for i in local_peaks(R, 0.25 * abs(ref))]
    near = lambda n: any(abs(x - math.log(n)) < 0.004 for x in pk)
    hit = sum(near(n) for n in PP)
    fp = sum(near(n) for n in COMP)
    stray = sum(all(abs(x - math.log(n)) >= 0.004 for n in range(2, N + 2)) for x in pk)
    return dict(corr=round(corr, 3), prime_powers_hit=hit, composite_false=fp, stray=stray)

# ---------------------------------------------------------------- E1 reverse trace
R0 = reverse_trace(t, g0)
mask = t <= 3.3
e1 = []
for i in local_peaks(R0, 6.0):
    if t[i] <= 3.3:
        n = round(math.exp(t[i]))
        e1.append(dict(t=round(float(t[i]), 4), exp_t=round(math.exp(t[i]), 3), height=round(float(R0[i]), 1),
                       n=n, prime_power=vonmangoldt(n) > 0, weight=round(vonmangoldt(n) / math.sqrt(n), 4)))
res['E1_peaks'] = e1
res['E1_composite_values'] = {n: round(float(np.interp(math.log(n), t, R0)), 2)
                              for n in (6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26)}
hp = {d['n']: d['height'] for d in e1}
res['E1_height_ratio_vs_2'] = {n: [round(hp[n] / hp[2], 3), round((vonmangoldt(n) / math.sqrt(n)) / (math.log(2) / math.sqrt(2)), 3)]
                               for n in (3, 4, 5, 7, 8, 11, 13) if n in hp}

# ---------------------------------------------------------------- E2 angle vs radius
rows = []
def run(label, kind, param, R):
    d = score(R); d.update(label=label, kind=kind, param=param); rows.append(d)
run('true zeros', 'true', None, R0)
jit = {}
for e in (0.01, 0.05, 0.2, 1.0):
    gj = g0 + rng.normal(0, e, g0.size); jit[e] = gj
    run(f'on-line, gamma jitter sd={e}', 'jitter', e, reverse_trace(t, gj))
for d in (0.05, 0.1, 0.25, 0.49):
    run(f'off-line, all zeros delta={d}', 'offline', d, reverse_trace(t, g0, np.full(g0.size, d)))
dl = np.zeros(g0.size); dl[rng.choice(g0.size, 120, replace=False)] = 0.45
Rpart = reverse_trace(t, g0, dl)
run('off-line, 10% of zeros delta=0.45', 'offline_partial', 0.45, Rpart)
gr = np.sort(rng.uniform(g0.min(), g0.max(), g0.size))
Rnull = reverse_trace(t, gr)
run('null: uniform random heights on the line', 'null', None, Rnull)
res['E2'] = rows
res['E2_counts'] = dict(prime_powers=len(PP), composites=len(COMP), N=N)

# envelope at large t for one off-line pair (analytic): cosh(delta log x)
res['E2_envelope'] = {f'x=1e{k}': round(math.cosh(0.1 * math.log(10 ** k)), 3) for k in (2, 6, 12, 24)}

# ---------------------------------------------------------------- E3 statistics
th = lambda T: T / 2 * np.log(T / (2 * math.pi)) - T / 2 - math.pi / 8 + 1 / (48 * T)
s = np.diff(th(g0)) / math.pi
from scipy.integrate import quad
gue = lambda x: (32 / math.pi ** 2) * x ** 2 * math.exp(-4 * x ** 2 / math.pi)
res['E3_spacing'] = dict(mean=round(float(s.mean()), 4), min=round(float(s.min()), 4),
                         frac={str(a): [round(float((s < a).mean()), 4), round(1 - math.exp(-a), 4), round(quad(gue, 0, a)[0], 4)]
                               for a in (0.1, 0.25, 0.5)})
ang = np.mod(g0 * math.log(2), 2 * math.pi)
res['E3_angles_b2_hist12'] = np.histogram(ang, bins=12, range=(0, 2 * math.pi))[0].tolist()
res['E3_mean_cos'] = {str(n): round(float(np.mean(np.cos(g0 * math.log(n)))), 4) for n in (2, 3, 4, 5, 6, 10, 12)}
li = 2 * np.arctan(0.5 / g0)                     # angle of z = 1 - 1/rho from z = 1
res['E3_li_angle_deg'] = dict(first=round(float(np.degrees(li[0])), 3), last=round(float(np.degrees(li[-1])), 4))
json.dump(res, open(os.path.join(ROOT, 'validation', 'results.json'), 'w'), indent=1)

# ---------------------------------------------------------------- figures
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
BLUE, ORANGE, AQUA, INK, MUTED, GRID = '#2a78d6', '#eb6834', '#1baf7a', '#222222', '#6b6b6b', '#d9d9d6'
plt.rcParams.update({'font.size': 9, 'axes.edgecolor': MUTED, 'axes.labelcolor': INK, 'xtick.color': MUTED,
                     'ytick.color': MUTED, 'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.grid': True, 'grid.color': GRID, 'grid.linewidth': 0.5, 'lines.linewidth': 1.0})
FIG = os.path.join(ROOT, 'paper', 'figures')

def mark_n(ax, top, upto=27):
    for n in range(2, upto + 1):
        x = math.log(n)
        if vonmangoldt(n) > 0:
            ax.annotate(str(n), (x, top), ha='center', va='bottom', fontsize=7, color=INK)
        else:
            ax.plot([x, x], [-6, -3], color=MUTED, lw=0.6)

fig, ax = plt.subplots(figsize=(6.4, 2.6))
ax.plot(t[mask], R0[mask], color=BLUE)
mark_n(ax, 64)
ax.set_xlim(0.5, 3.3); ax.set_ylim(-8, 72)
ax.set_xlabel('$t$  (labels: prime powers $n$ at $t=\\log n$; ticks below: composites)')
ax.set_ylabel('$R(t)$')
fig.tight_layout(); fig.savefig(os.path.join(FIG, 'fig1_reverse_trace.pdf')); plt.close(fig)

fig, axs = plt.subplots(3, 1, figsize=(6.4, 5.6), sharex=True)
panels = [(reverse_trace(t, jit[1.0]), 'heights $\\gamma_k$ jittered (sd 1.0), all on the line', ORANGE),
          (reverse_trace(t, g0, np.full(g0.size, 0.49)), 'heights kept, every zero moved off the line ($\\delta=0.49$)', AQUA),
          (Rnull, 'null: random heights, all on the line', ORANGE)]
m2 = t <= 3.3
for ax, (R, title, col) in zip(axs, panels):
    ax.plot(t[m2], R0[m2], color=MUTED, lw=0.8, label='true zeros')
    ax.plot(t[m2], R[m2], color=col, lw=0.9, label='modified')
    ax.set_title(title, fontsize=9, loc='left', color=INK)
    ax.legend(loc='upper left', fontsize=7, frameon=False)
axs[-1].set_xlabel('$t$'); [a.set_ylabel('$R(t)$') for a in axs]
fig.tight_layout(); fig.savefig(os.path.join(FIG, 'fig2_angle_vs_radius.pdf')); plt.close(fig)

fig, axs = plt.subplots(1, 2, figsize=(6.4, 2.6))
x = np.linspace(0, 3, 300)
axs[0].hist(s, bins=30, range=(0, 3), density=True, color=BLUE, edgecolor='white', linewidth=0.5, label='zeros')
axs[0].plot(x, np.exp(-x), color=ORANGE, lw=1.5, label='random (Poisson)')
axs[0].plot(x, [gue(v) for v in x], color=INK, lw=1.2, ls='--', label='random unitary (GUE)')
axs[0].set_xlabel('normalised spacing'); axs[0].set_ylabel('density'); axs[0].legend(fontsize=7, frameon=False)
h = np.histogram(ang, bins=24, range=(0, 2 * math.pi))[0]
axs[1].bar(np.arange(24) * 15 + 7.5, h, width=13, color=BLUE)
axs[1].axhline(g0.size / 24, color=INK, lw=1, ls='--', label='uniform')
axs[1].set_xlabel('angle $\\gamma\\log 2$ mod $2\\pi$ (degrees)'); axs[1].set_ylabel('count')
axs[1].set_xticks([0, 90, 180, 270, 360]); axs[1].legend(fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig(os.path.join(FIG, 'fig3_statistics.pdf')); plt.close(fig)
print(json.dumps({k: res[k] for k in ('E2', 'E3_spacing', 'E3_mean_cos', 'E3_angles_b2_hist12', 'E3_li_angle_deg')}, indent=0)[:3000])

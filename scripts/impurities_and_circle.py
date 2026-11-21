#!/usr/bin/env python3
"""Version 3 additions:
  (a) decomposition of the reverse-trace background into the pole term
      -cosh(t/2) e^{1/(4 Gamma^2)} and the archimedean (Gamma-factor) term;
  (b) filling of the circle by the angles gamma*log 2 as the number of zeros grows;
  (c) neighbour spacings along the line versus wrapped onto the circle;
  (d) Figure 4, the circle picture with known impurities.
Writes ../validation/impurities_and_circle.json and ../figures/fig4_circle.pdf."""
import json, math, os
import numpy as np
from mpmath import digamma, mpc

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
g = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))
G = 600.0
w = np.exp(-(g / G) ** 2)
R = lambda x: float(-(w * np.cos(g * x)).sum())
out = {}

# (a) background decomposition
r = np.arange(0, 3000.0001, 0.02)
psi = np.array([float(digamma(mpc(0.25, x / 2)).real) for x in r])
Wr = np.exp(-(r / G) ** 2) * psi
rows = []
for n in (2, 6, 12, 27):
    t = math.log(n)
    base = 0.5 * (R(t - 0.02) + R(t + 0.02))
    pole = -math.cosh(t / 2) * math.exp(1 / (4 * G * G))
    arch = -np.trapezoid(Wr * np.cos(r * t), r) / (2 * math.pi)
    rows.append(dict(n=n, observed=round(base, 3), pole=round(pole, 3), arch=round(float(arch), 3),
                     total=round(pole + float(arch), 3)))
out['background'] = rows

# (b) filling the circle
L2 = math.log(2)
fill = []
for N in (40, 100, 300, 600, 1200):
    gg = g[:N]; T = float(gg[-1])
    a = np.sort(np.mod(gg * L2, 2 * math.pi)); gaps = np.diff(np.r_[a, a[0] + 2 * math.pi])
    fill.append(dict(N=N, T=round(T, 1), max_gap_deg=round(math.degrees(gaps.max()), 2),
                     random_scale_deg=round(math.degrees(2 * math.pi * math.log(N) / N), 2),
                     mean_cos=round(float(np.cos(gg * L2).mean()), 4),
                     landau=round(-(T / (2 * math.pi)) * L2 / (math.sqrt(2) * N), 4)))
out['filling'] = fill
out['landau_asymptotic'] = {f'{T:.0e}': round(-L2 / (math.sqrt(2) * (math.log(T / (2 * math.pi)) - 1)), 4)
                            for T in (1e6, 1e12, 1e24)}

# (c) spacings along the line versus wrapped
th = lambda T: T / 2 * np.log(T / (2 * math.pi)) - T / 2 - math.pi / 8
s_line = np.diff(th(g)) / math.pi
a = np.sort(np.mod(g * L2, 2 * math.pi)); s_circ = np.diff(np.r_[a, a[0] + 2 * math.pi]) * len(a) / (2 * math.pi)
out['spacing'] = {str(x): [round(float(np.mean(s_line < x)), 3), round(float(np.mean(s_circ < x)), 3),
                           round(1 - math.exp(-x), 3)] for x in (0.1, 0.25, 0.5)}
json.dump(out, open(os.path.join(ROOT, 'validation', 'impurities_and_circle.json'), 'w'), indent=1)
print(json.dumps(out, indent=1))

# (d) figure 4
import matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
BLUE, ORANGE, AQUA, MAG, INK, MUTED = '#2a78d6', '#eb6834', '#1baf7a', '#d55181', '#222222', '#8a8a85'
plt.rcParams.update({'font.size': 9})
b = 2.0; rc = math.sqrt(b); g40 = g[:40]
fig, ax = plt.subplots(figsize=(5.6, 5.9))
tt = np.linspace(0, 2 * np.pi, 400); ax.plot(rc * np.cos(tt), rc * np.sin(tt), color=MUTED, lw=1.1)
ax.plot([-2.35, 2.35], [0, 0], color='#e2e2de', lw=0.7, zorder=0); ax.plot([0, 0], [-2.35, 2.35], color='#e2e2de', lw=0.7, zorder=0)
ang = g40 * math.log(b)
ax.scatter(np.r_[rc * np.cos(ang), rc * np.cos(-ang)], np.r_[rc * np.sin(ang), rc * np.sin(-ang)], s=20, color=BLUE,
           edgecolor='white', linewidth=0.5, zorder=3, label='nontrivial zeros (first 40 and conjugates)')
ax.scatter([b, 1], [0, 0], s=70, marker='D', color=ORANGE, edgecolor='white', linewidth=0.7, zorder=4,
           label='known impurities: poles $s=1$, $s=0$ of $\\Lambda(s)$')
tz = [b ** (-2 * n) for n in range(1, 5)]
ax.scatter(tz, [0] * len(tz), s=30, marker='s', color=AQUA, edgecolor='white', linewidth=0.5, zorder=4,
           label='trivial zeros $-2,-4,\\dots$ of $\\zeta$ (absorbed by $\\Gamma$)')
pa, d = 2.35, 0.25
pts = [rc * b ** d, rc * b ** (-d)]
for rr in pts:
    ax.scatter([rr * math.cos(pa)], [rr * math.sin(pa)], s=55, facecolor='white', edgecolor=MAG, linewidth=1.4, zorder=4)
ax.plot([pts[1] * math.cos(pa), pts[0] * math.cos(pa)], [pts[1] * math.sin(pa), pts[0] * math.sin(pa)], color=MAG, ls='--', lw=0.9)
ax.scatter([], [], s=55, facecolor='white', edgecolor=MAG, linewidth=1.4, label='hypothetical off-line pair (excluded by RH)')
ax.annotate('$s=1$', (b, 0), xytext=(1.95, -0.45), ha='center', arrowprops=dict(arrowstyle='-', color=MUTED, lw=0.6))
ax.annotate('$s=0$', (1, 0), xytext=(0.95, 0.4), ha='center', arrowprops=dict(arrowstyle='-', color=MUTED, lw=0.6))
ax.annotate('$|\\alpha|=\\sqrt{b}$', (rc * math.cos(-0.7), rc * math.sin(-0.7)), xytext=(1.6, -1.75), ha='center',
            arrowprops=dict(arrowstyle='-', color=MUTED, lw=0.6))
ax.set_xlim(-2.4, 2.4); ax.set_ylim(-2.4, 2.4); ax.set_aspect('equal'); ax.axis('off')
ax.legend(loc='lower center', bbox_to_anchor=(0.5, -0.23), frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'paper', 'figures', 'fig4_circle.pdf'), bbox_inches='tight')

#!/usr/bin/env python3
"""Figure 10: (a) lowest zero of L(s, (./q)) for primes q = 3 mod 4 near 163;
(b) psi(x, chi)/sqrt(x) for q = 163 against the contribution of the lowest zero pair."""
import cmath, json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
Z = json.load(open(os.path.join(ROOT, 'validation', 'q163_zeros.json')))
A = json.load(open(os.path.join(ROOT, 'validation', 'q163.json')))
g = [r['first_zero'] for r in Z if r['q'] == 163][0]
plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(1, 2, figsize=(10, 3.6))
qs = [r['q'] for r in Z]
ax[0].bar([str(q) for q in qs], [r['first_zero'] for r in Z], color=['#c0392b' if q == 163 else '#1f4e79' for q in qs])
ax[0].set_ylabel('height of lowest zero'); ax[0].set_xlabel('$q$ (character $(\\cdot/q)$, $q\\equiv3$ mod 4)')
ax[0].set_title('(a) lowest zero on the critical line')
x = np.array([r['x'] for r in A['psi_chi']]); y = [r['over_sqrtx'] for r in A['psi_chi']]
xx = np.logspace(1, 13.5, 400); rho = complex(0.5, g)
pred = [-2 * (cmath.exp(1j * g * math.log(v)) / rho).real for v in xx]
ax[1].semilogx(xx, pred, '--', color='#888888', lw=0.9, label='lowest pair: $-2\\,\\mathrm{Re}(x^{i\\gamma}/\\rho)$')
ax[1].semilogx(x, y, 'o', color='#1f4e79', ms=4, label='computed $\\psi(x,\\chi)/\\sqrt{x}$')
ax[1].axhline(0, color='#888888', lw=0.6); ax[1].axvspan(10, 3e6, color='#1f4e79', alpha=0.06)
ax[1].set_xlabel('$x$'); ax[1].set_title('(b) $q=163$: a slow wave, not a trend'); ax[1].legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'paper', 'figures', 'fig10_q163.pdf'), bbox_inches='tight')

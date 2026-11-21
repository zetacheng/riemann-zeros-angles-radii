#!/usr/bin/env python3
"""The radius problem as an upper bound (log entry 60).

Unrolled picture (height gamma against real part beta, i.e. radius b^beta): known zero-free
boundaries for zeta, which push the outer edge of the annulus inward.
  classical (de la Vallee Poussin type, Mossinghoff-Trudgian constant): beta < 1 - 1/(5.5587 log t)
  Vinogradov-Korobov (Ford's constant):  beta < 1 - 1/(57.54 (log t)^{2/3} (log log t)^{1/3})
  announced quasi-RH (unrefereed, Nov 2026): beta < 7/8, refined to 0.874957
  numerically verified: all zeros with t <= 3e12 on the line (Platt-Trudgian)
  RH: beta = 1/2 (with the functional equation, an upper bound 1/2 forces the circle).
Writes upper_bounds.png.
"""
import math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
t = np.logspace(math.log10(3), 40, 600); lt = np.log(t)
classical = 1 - 1 / (5.5587 * lt)
vk = 1 - 1 / (57.54 * lt ** (2 / 3) * np.log(lt) ** (1 / 3))
plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(figsize=(7.6, 4.2))
ax.fill_between(t, np.maximum(classical, vk), 1, color='#1f4e79', alpha=0.15, label='excluded (proved): zero-free region')
ax.semilogx(t, classical, color='#1f4e79', lw=1, label='classical $1-1/(5.56\\log t)$')
ax.semilogx(t, vk, color='#2e7d32', lw=1, label='Vinogradov–Korobov')
ax.fill_between([3, 3e12], 0.5, 1, color='#888888', alpha=0.12, hatch='//', edgecolor='#aaaaaa', lw=0, label='verified on the line numerically ($t\\leq3\\times10^{12}$)')
ax.axhline(0.874957, color='#c0392b', ls='--', lw=1, label='announced quasi-RH $0.874957$ (unrefereed)')
ax.axhline(0.5, color='#555555', lw=1.4, label='RH: $\\beta=1/2$ (the circle $|\\alpha|=\\sqrt{b}$)')
ax.axhline(1, color='#888888', lw=0.6)
ax.set_xlabel('height $t$ (number of turns of the helix)'); ax.set_ylabel('real part $\\beta$ (radius $b^{\\beta}$)')
ax.set_ylim(0.45, 1.02); ax.legend(frameon=False, fontsize=7.5, loc='lower left')
ax.set_title('Outer edge of the annulus: what is proved, announced and conjectured for $\\zeta$')
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'upper_bounds.png'), dpi=130, bbox_inches='tight')

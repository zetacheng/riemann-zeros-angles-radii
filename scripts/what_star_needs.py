#!/usr/bin/env python3
"""Step 2: what the one-sided bound (star_theta) of step 1 must achieve on real families.

E_q(x) = x - phi(q) psi(x; q, 1) for q = 1 and primes q <= 47, x <= X = 5e6.
 (1) size: max over 1e3 <= x <= X of E_q(x)/sqrt(x), and its growth with q;
 (2) constants: C_q(eps) = max E_q(x)/x^{1/2+eps} needed for (star) with theta = 1/2 + eps;
 (3) windows: for q = 5, the maximum of E_q/sqrt(x) in each window [Y, Y^{1.2}] (log scale),
     i.e. what a localised one-sided bound must allow in every window;
 (4) exponent arithmetic: an engine whose error terms are x/m + m^a + sqrt(x) gives, at the best
     chain length m = x^{1/(a+1)}, the exponent theta = max(a/(a+1), 1/2).
Writes validation/what_star_needs.json (the preview figure goes to $TMPDIR).
"""
import json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
X = 5_000_000
sv = np.ones(X + 1, bool); sv[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
pr = np.nonzero(sv)[0]
pp, lw = [], []
for p in pr:
    pk = int(p); l = math.log(p)
    while pk <= X: pp.append(pk); lw.append(l); pk *= int(p)
pp = np.array(pp); lw = np.array(lw); o = np.argsort(pp); pp = pp[o]; lw = lw[o]
grid = np.unique(np.round(np.logspace(3, math.log10(X), 2000)).astype(int))

def E_on_grid(q):
    phi = max(q - 1, 1)
    m = (pp % q == 1 % q) if q > 1 else np.ones(len(pp), bool)
    xs = pp[m]; cum = np.cumsum(lw[m]) * phi
    idx = np.searchsorted(xs, grid, side='right') - 1
    psi = np.where(idx >= 0, cum[np.maximum(idx, 0)], 0.0)
    return grid - psi

qs = [1] + [q for q in range(3, 48) if all(q % d for d in range(2, int(q ** 0.5) + 1))]
rows = []
for q in qs:
    E = E_on_grid(q); n = E / np.sqrt(grid)
    row = dict(q=q, members=max(q - 1, 1), max_over_sqrtx=float(n.max()), min_over_sqrtx=float(n.min()))
    for eps in (0.02, 0.05, 0.1):
        row[f'C_eps_{eps}'] = float(np.max(E / grid ** (0.5 + eps)))
    rows.append(row)
    print(q, {k: round(v, 3) if isinstance(v, float) else v for k, v in row.items() if k != 'q'})
qq = np.array([r['members'] for r in rows[1:]]); mm = np.array([r['max_over_sqrtx'] for r in rows[1:]])
slope = float(np.polyfit(np.log(qq), np.log(mm), 1)[0])
print('growth of max E_q/sqrt(x) with the number of members phi(q): exponent', round(slope, 3))

# windows for q = 5
E5 = E_on_grid(5); n5 = E5 / np.sqrt(grid); lg = np.log(grid)
wins = []; a = math.log(1e3)
while a * 1.2 <= lg[-1]:
    m = (lg >= a) & (lg <= a * 1.2)
    wins.append(dict(logY=round(a, 2), max=float(n5[m].max()), min=float(n5[m].min()))); a *= 1.2
print('q=5 windows:', [(w['logY'], round(w['max'], 2), round(w['min'], 2)) for w in wins])

arith = [dict(a=a_, chain=f'm = x^(1/{a_ + 1})', theta=max(a_ / (a_ + 1), 0.5)) for a_ in (0.5, 1, 1.5, 2, 3)]
out = dict(X=X, rows=rows, growth_exponent_in_members=slope, windows_q5=wins, exponent_arithmetic=arith)
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'what_star_needs.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(1, 3, figsize=(13, 3.6))
for q, c in ((1, '#555555'), (5, '#1f4e79'), (11, '#c0392b')):
    ax[0].semilogx(grid, E_on_grid(q) / np.sqrt(grid), lw=0.6, color=c, label=f'$q={q}$')
ax[0].axhline(0, color='#888888', lw=0.5); ax[0].set_xlabel('$x$'); ax[0].set_ylabel('$E_q(x)/\\sqrt{x}$')
ax[0].set_title('(a) the one-sided statistic on real data'); ax[0].legend(frameon=False, fontsize=8)
ax[1].loglog(qq, mm, 'o', color='#1f4e79', ms=4)
ax[1].loglog(qq, mm[0] * (qq / qq[0]) ** slope, '--', color='#888888', lw=0.8, label=f'slope {slope:.2f}')
ax[1].set_xlabel('family size $\\varphi(q)$'); ax[1].set_ylabel('$\\max E_q/\\sqrt{x}$'); ax[1].legend(frameon=False, fontsize=8)
ax[1].set_title('(b) the constant grows with the family')
aa = np.linspace(0.3, 3, 200); ax[2].plot(aa, np.maximum(aa / (aa + 1), 0.5), color='#1f4e79')
for a_, lab in ((1, '$a=1$: $\\theta=1/2$'), (2, '$a=2$: $\\theta=2/3$')):
    ax[2].plot(a_, max(a_ / (a_ + 1), 0.5), 'o', color='#c0392b'); ax[2].annotate(lab, (a_, max(a_ / (a_ + 1), 0.5)), xytext=(6, 6 if a_ == 1 else -12), textcoords='offset points', fontsize=8)
ax[2].set_xlabel('cost exponent $a$ of a chain of length $m$'); ax[2].set_ylabel('exponent $\\theta$ reached')
ax[2].set_title('(c) error $x/m+m^a$: what the engine must cost')
fig.tight_layout(); fig.savefig(os.path.join(os.environ.get('TMPDIR', '/tmp'), 'what_star_needs.png'), dpi=130, bbox_inches='tight')

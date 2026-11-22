"""Step 4(b): four ways to buy multiplicity, compared by the bound they give.

Written by Claude (Anthropic, Claude Opus 5.5) for Zeta Hoi-Ho Cheng, 22 Nov 2026.

For each engine we measure the bound on the counted quantity, divided by its
true value, as a function of the multiplicity parameter.  A ratio that falls
means multiplicity is being bought cheaply enough to help.

  E1  Z, Frobenius-type iteration: N_j = 2^(3*7^j) - 1, v_7 = 1 + j.
      Ratio = (log N_j / v_7) / (log N_0 / v_7 at j=0)   (cost per unit, normalised)
  E2  Z, one block of Tate twists at a single prime: N = prod_{c<h} p^c.
      v_p(N) log p = log N exactly (product formula): net gain 0 for every h.
  E3  Z, appended binomial blocks: N_M = (Mn)!/(n!)^M = prod_{j<=M} C(jn, n).
      Every prime p in (n, 2n] divides N_M at least mu_M = min_p v_p(N_M) times,
      so theta(2n) - theta(n) <= log N_M / mu_M.  Multiplicity grows linearly
      in M, but the cost of each appended block is about n log j.
  E4  F_p, Stepanov (paper Table 10, p = 401, |S| = 215): bound deg R / M.
  E5  The verified proof as described by R. Zhang (secondary, unverified):
      errors x/m + m; ratio (x/m + m) / (x + 1) at x = 1e6.  A model, not data.
"""
import json, math, os
from math import lgamma, log
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
VAL = os.path.join(HERE, '..', 'validation')
out = {}

# E1
e1 = []
for j in range(0, 7):
    logN = 3 * 7**j * log(2)          # log(2^(3*7^j) - 1) to relative 1e-6
    v = 1 + j
    e1.append({'step': j, 'v7': v, 'logN': logN, 'cost_per_unit': logN / v})
for r in e1:
    r['ratio'] = r['cost_per_unit'] / e1[0]['cost_per_unit']
out['E1_frobenius_iteration'] = e1

# E2
e2 = []
for p in (3, 7, 11):
    for h in (2, 5, 10):
        v = h * (h - 1) // 2
        logN = v * log(p)
        e2.append({'p': p, 'h': h, 'vp_logp': v * log(p), 'logN': logN,
                   'net_gain': v * log(p) - logN})
out['E2_single_prime_block'] = e2

# E3
def vp_fact(N, p):
    s, q = 0, p
    while q <= N:
        s += N // q; q *= p
    return s

n = 1000
S = list(sp.primerange(n + 1, 2 * n + 1))
theta = sum(log(p) for p in S)
e3 = []
for M in (2, 3, 4, 6, 8, 12, 16, 24, 32, 64, 128):
    logN = lgamma(M * n + 1) - M * lgamma(n + 1)
    vs = [vp_fact(M * n, p) - M * vp_fact(n, p) for p in S]
    mu = min(vs)
    weighted = sum(v * log(p) for v, p in zip(vs, S))
    assert weighted <= logN + 1e-6
    e3.append({'M': M, 'logN': logN, 'mu': mu, 'mean_v': sum(vs) / len(vs),
               'bound': logN / mu, 'true': theta, 'ratio': logN / mu / theta,
               'cost_per_block': logN / M})
out['E3_binomial_blocks'] = {'n': n, 'theta_2n_minus_theta_n': theta, 'rows': e3}

# E4
st = json.load(open(os.path.join(VAL, 'stepanov_results.json')))['vs_M_p401']
out['E4_stepanov_p401'] = [{'M': r['M'], 'bound': r['bound'], 'S': r['S'],
                            'ratio': r['bound'] / r['S']} for r in st]

# E5
x = 1e6
e5 = [{'m': m, 'bound': x / m + m, 'ratio': (x / m + m) / (x + 1)}
      for m in (1, 3, 10, 30, 100, 300, 1000, 3000, 10000)]
out['E5_proof_model'] = {'x': x, 'rows': e5, 'note': 'model from a secondary source, not data'}

json.dump(out, open(os.path.join(VAL, 'step4_engines.json'), 'w'), indent=1)

# figure
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
fig, ax = plt.subplots(figsize=(6.4, 4.0))
ink, muted = '#222222', '#777777'
series = [
    ('E1  $\\mathbb{Z}$, Frobenius-type iteration', [1 + r['step'] for r in e1], [r['ratio'] for r in e1], '#c2410c', 'o'),
    ('E3  $\\mathbb{Z}$, appended binomial blocks', [r['M'] for r in e3], [r['ratio'] for r in e3], '#7c3aed', 's'),
    ('E4  $\\mathbb{F}_{401}$, Stepanov', [r['M'] for r in out['E4_stepanov_p401']], [r['ratio'] for r in out['E4_stepanov_p401']], '#0f766e', '^'),
    ('E5  proof as described (model)', [r['m'] for r in e5], [r['ratio'] for r in e5], '#2563eb', 'D'),
]
for lab, xs, ys, col, mk in series:
    ax.plot(xs, ys, color=col, lw=2, marker=mk, ms=7, mec='white', mew=1.5,
            ls='--' if lab.startswith('E5') else '-', label=lab)
ax.axhline(1, color=muted, lw=1, ls=':')
ax.set_xscale('log'); ax.set_yscale('log')
ax.set_xlabel('multiplicity parameter (steps $j+1$, $M$ or $m$)', color=ink)
ax.set_ylabel('bound / true value (E1: cost per unit, normalised)', color=ink)
for s in ('top', 'right'): ax.spines[s].set_visible(False)
ax.grid(True, which='major', color='#e5e5e5', lw=0.8)
ax.legend(frameon=False, fontsize=8, loc='upper left')
fig.tight_layout()
fig.savefig(os.path.join(HERE, '..', 'explorations', 'step4', 'engines.png'), dpi=200)

for k in ('E1_frobenius_iteration',):
    print(k, [(r['step'], round(r['ratio'], 1)) for r in out[k]])
print('E2 net gains', sorted({round(r['net_gain'], 12) for r in e2}))
print('E3 theta =', round(theta, 1))
for r in e3:
    print('  M=%4d mu=%4d mean_v=%7.2f logN/M=%9.1f bound=%10.1f ratio=%.3f' % (r['M'], r['mu'], r['mean_v'], r['cost_per_block'], r['bound'], r['ratio']))
print('E4', [(r['M'], round(r['ratio'], 3)) for r in out['E4_stepanov_p401']])
print('E5', [(r['m'], round(r['ratio'], 5)) for r in e5])

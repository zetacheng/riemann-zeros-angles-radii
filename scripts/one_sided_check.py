#!/usr/bin/env python3
"""The one-sided statistic on real data: E_q(x) = x - phi(q) psi(x; q, 1), normalised by sqrt(x).

By the criterion in skeleton.md, GRH for the characters mod q is equivalent to
E_q(x) <= C x^theta for every theta > 1/2.  Here we only look at the data up to X = 5e6.
Writes validation/one_sided_check.json.
"""
import json, math, os
import numpy as np
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
out = {}
for q in (1, 3, 5, 7, 11):
    phi = max(q - 1, 1)
    m = (pp % q == 1 % q) if q > 1 else np.ones(len(pp), bool)
    xs = pp[m]; cum = np.cumsum(lw[m]) * phi
    grid = np.unique(np.logspace(1, math.log10(X), 300).astype(int))
    idx = np.searchsorted(xs, grid, side='right') - 1
    psi = np.where(idx >= 0, cum[np.maximum(idx, 0)], 0.0)
    E = grid - psi
    norm = E / np.sqrt(grid)
    late = grid > 1e3
    out[str(q)] = dict(max_E_over_sqrtx=float(norm[late].max()), min_E_over_sqrtx=float(norm[late].min()),
                       max_E_over_sqrtx_log2=float((E / (np.sqrt(grid) * np.log(grid) ** 2))[late].max()))
    print(q, {k: round(v, 3) for k, v in out[str(q)].items()})
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'one_sided_check.json'), 'w'), indent=1)

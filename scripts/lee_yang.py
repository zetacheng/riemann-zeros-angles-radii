#!/usr/bin/env python3
"""Lee-Yang: a 'hard wall' that puts partition-function zeros on a circle (log entry 71).

Ising model on the 4x4 periodic square lattice (16 spins, 32 bonds):
    Z(z) = sum_sigma exp( sum_<ij> K_ij s_i s_j ) * z^{#down spins},   z = exp(-2 beta h).
Z is palindromic (a_k = a_{16-k}, the symmetry z <-> 1/z, like a functional equation).
Lee-Yang (1952): if every K_ij >= 0 (ferromagnetic), all zeros lie on |z| = 1.
We compute the coefficients exactly (2^16 configurations) and the roots at 60 digits for
uniform ferromagnetic couplings, random positive couplings, antiferromagnetic couplings and
mixed signs, and record max ||z| - 1|.  Writes validation/lee_yang.json and paper/figures/fig12_leeyang.pdf.
"""
import itertools, json, math, os
import numpy as np
import mpmath as mp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps = 60
L = 4; N = L * L
bonds = []
for x in range(L):
    for y in range(L):
        i = x * L + y
        bonds.append((i, ((x + 1) % L) * L + y)); bonds.append((i, x * L + (y + 1) % L))
configs = np.array(list(itertools.product([1, -1], repeat=N)), dtype=np.int8)
ndown = np.sum(configs == -1, axis=1)
prod = np.array([configs[:, i] * configs[:, j] for i, j in bonds], dtype=np.int8).T   # (2^N, nbonds)

def zeros_for(K):
    E = prod.astype(float) @ np.array(K, float)                  # sum K_ij s_i s_j
    w = [mp.mpf(0)] * (N + 1)
    # group identical (ndown, E) pairs for exact-enough mp accumulation
    keys, counts = np.unique(np.stack([ndown, np.round(E, 12)], axis=1), axis=0, return_counts=True)
    for (k, e), c in zip(keys, counts):
        w[int(k)] += c * mp.exp(mp.mpf(repr(float(e))))
    palin = max(abs(w[k] - w[N - k]) / w[k] for k in range(N + 1))
    roots = mp.polyroots(w[::-1], maxsteps=400, extraprec=200)
    mods = [abs(r) for r in roots]
    return roots, float(max(abs(m - 1) for m in mods)), float(palin)

rng = np.random.default_rng(0)
cases = {'ferromagnetic, K = 0.3': [0.3] * len(bonds),
         'ferromagnetic, random K in (0, 1)': list(rng.uniform(0, 1, len(bonds))),
         'antiferromagnetic, K = -0.3': [-0.3] * len(bonds),
         'mixed signs, K = +-0.5': list(rng.choice([-0.5, 0.5], len(bonds)))}
out = {}
fig, axs = plt.subplots(1, 4, figsize=(14, 3.7))
th = np.linspace(0, 2 * np.pi, 400)
for ax, (name, K) in zip(axs, cases.items()):
    roots, dev, palin = zeros_for(K)
    out[name] = dict(max_dev_from_unit_circle=dev, palindromic_rel_err=palin,
                     roots=[[float(mp.re(r)), float(mp.im(r))] for r in roots])
    print(f'{name:38s} max ||z|-1| = {dev:.3e}   palindromic error = {palin:.1e}')
    ax.plot(np.cos(th), np.sin(th), color='#888888', lw=0.8)
    ax.plot([float(mp.re(r)) for r in roots], [float(mp.im(r)) for r in roots], 'o', ms=4,
            color='#1f4e79' if name.startswith('ferro') else '#c0392b')
    ax.set_aspect('equal'); ax.set_title(name + f'\nmax $||z|-1|$ = {dev:.1e}', fontsize=8.5)
    lim = max(1.6, 1.1 * max(abs(complex(r)) for r in roots))
    ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim); ax.tick_params(labelsize=7)
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'paper', 'figures', 'fig12_leeyang.pdf'), bbox_inches='tight')
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'lee_yang.json'), 'w'), indent=1)

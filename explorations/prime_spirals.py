#!/usr/bin/env python3
"""One spiral arm per prime (the author's drawing, log entry 46).

At s = sigma + i t the prime p contributes the points p^{-k s}, k = 1, 2, ...:
radius p^{-k sigma}, angle -k t log p.  Each prime turns by its own angle t log p
(its own 'Frobenius'), and every arm spirals into the common centre 0.
Summing an arm gives the Euler factor: sum_k p^{-ks}/k = -log(1 - p^{-s}); summing all
arms gives log zeta(s).  Panel (b) adds the arms tip to tail over the primes
up to 10^5, at sigma = 1/2 and sigma = 3/2.
"""
import math, os, sys
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

t = 14.134725141734693                     # first ordinate of zeta
out = sys.argv[1] if len(sys.argv) > 1 else 'prime_spirals.png'
plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(10, 4.8))
cols = ['#1f4e79', '#c0392b', '#2e7d32', '#8e44ad', '#d35400', '#555555']
for p, c in zip([2, 3, 5, 7, 11, 13], cols):
    u = np.linspace(1, 9, 600)
    z = np.exp(-u * (0.5 + 1j * t) * math.log(p))
    a1.plot(z.real, z.imag, color=c, lw=0.9)
    kk = np.arange(1, 10); zk = np.exp(-kk * (0.5 + 1j * t) * math.log(p))
    a1.plot(zk.real, zk.imag, 'o', color=c, ms=3.5, label=f'$p={p}$')
a1.plot(0, 0, 'k+', ms=8)
a1.set_aspect('equal'); a1.set_xlim(-0.75, 0.75); a1.set_ylim(-0.75, 0.75)
a1.set_title(r'(a) arms $p^{-ks}$, $k=1,2,\ldots$, at $s=1/2+14.1347i$')
a1.legend(frameon=False, fontsize=8, loc='lower left'); a1.set_xticks([]); a1.set_yticks([])

N = 100_000
sv = np.ones(N + 1, bool); sv[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
pr = np.nonzero(sv)[0].astype(float)
for sigma, c, lab in ((0.5, '#c0392b', r'$\sigma=1/2$ (critical line)'), (1.5, '#1f4e79', r'$\sigma=3/2$')):
    s = sigma + 1j * t
    w = -np.log(1 - np.exp(-s * np.log(pr)))     # each arm summed
    path = np.concatenate([[0], np.cumsum(w)])
    a2.plot(path.real, path.imag, color=c, lw=0.6, label=lab)
    a2.plot(path[-1].real, path[-1].imag, 'o', color=c, ms=4)
a2.plot(0, 0, 'k+', ms=8)
a2.set_aspect('equal'); a2.legend(frameon=False, fontsize=8, loc='upper left')
a2.set_title(r'(b) arms added tip to tail, primes $\leq10^5$')
a2.set_xticks([]); a2.set_yticks([])
fig.tight_layout(); fig.savefig(out, dpi=130, bbox_inches='tight')

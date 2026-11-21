#!/usr/bin/env python3
"""Rotating the arms independently: the family of Dirichlet characters mod q.

For a character chi mod q (prime), each prime's arm is rotated by chi(p):
    W_chi(P) = sum_{p <= P, p != q} -log(1 - chi(p) p^{-s}),   s = 1/2 + i t,
the logarithm of the partial Euler product of L(s, chi).  For chi = 1 this is the
zeta path of prime_spirals.py.  We compare
    mean_chi |W_chi(P)|^2   with the diagonal  D(P) = sum_{p <= P} sum_k p^{-k}/k^2,
which the average equals exactly when no two prime powers p^k <= P are congruent
mod q (orthogonality), and with the large-sieve worst case (1 + P/q) D(P) for arbitrary coefficients.
Result: the ratio stays near 1 far beyond P = q (the prediction that it would grow like P/q
was wrong), because the twist p^{-it} decorrelates the arms within each residue class.
chi_j(g^a) = exp(2 pi i j a/(q-1)); sums over chi are FFTs over the index a.
Writes character_family.json and character_family.png.
"""
import json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

t = 14.134725141734693
s = 0.5 + 1j * t
NMAX = 1_000_000
K = 4                                         # prime powers p^k, k <= K
sv = np.ones(NMAX + 1, bool); sv[:2] = False
for i in range(2, int(NMAX ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
primes = np.nonzero(sv)[0]

def primroot(q):
    fac = [f for f in range(2, q) if (q - 1) % f == 0 and all(f % d for d in range(2, int(f ** 0.5) + 1))]
    for g in range(2, q):
        if all(pow(g, (q - 1) // f, q) != 1 for f in fac): return g

def run(q, Ps):
    g = primroot(q); n = q - 1
    dlog = np.zeros(q, np.int64); x = 1
    for a in range(n): dlog[x] = a; x = x * g % q
    ps = primes[primes != q]
    a_p = dlog[ps % q]
    rows = []
    for P in Ps:
        m = ps <= P; pp = ps[m].astype(float); ap = a_p[m]
        bins = np.zeros(n, complex); diag = 0.0
        for k in range(1, K + 1):
            w = np.exp(-k * s * np.log(pp)) / k           # chi(p)^k p^{-ks}/k, chi(p)^k = chi(p^k)
            np.add.at(bins, (k * ap) % n, w)
            diag += float(np.sum(np.abs(w) ** 2))
        W = np.fft.fft(bins)                               # W[j] = sum_a bins[a] e^{-2 pi i j a/n}
        ms = float(np.mean(np.abs(W) ** 2))
        rows.append(dict(q=q, P=int(P), mean_sq=ms, diagonal=diag, ratio=ms / diag,
                         trivial_sq=float(abs(W[0]) ** 2), median_sq=float(np.median(np.abs(W) ** 2)),
                         max_sq_nontrivial=float(np.max(np.abs(W[1:]) ** 2)), large_sieve_shape=(1 + P / q) * diag))
        print(json.dumps({k: (round(v, 4) if isinstance(v, float) else v) for k, v in rows[-1].items()}), flush=True)
    return rows

Ps = [10, 30, 100, 300, 1000, 3000, 10_000, 30_000, 100_000, 300_000, 1_000_000]
res = {q: run(q, Ps) for q in (101, 1009, 10007)}
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
json.dump({str(k): v for k, v in res.items()}, open(os.path.join(ROOT, 'validation', 'character_family.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(10, 4.2))
cols = {101: '#2e7d32', 1009: '#1f4e79', 10007: '#8e44ad'}
for q, rows in res.items():
    P = [r['P'] for r in rows]
    a1.loglog(P, [r['ratio'] for r in rows], 'o-', ms=3.5, color=cols[q], label=f'family mod $q={q}$')
    a1.axvline(q, color=cols[q], lw=0.6, ls=':')
a1.axhline(1, color='#888888', lw=0.8)
a1.set_xlabel('arms included: primes $p\\leq P$'); a1.set_ylabel('mean$_\\chi|W_\\chi|^2$ / diagonal')
P0 = np.array([10, 1_000_000.0]); a1.loglog(P0, 1 + P0 / 1009, '--', color='#1f4e79', lw=0.8, label='worst case $1+P/q$, $q=1009$')
a1.set_ylim(0.5, 30); a1.set_title('(a) family mean square stays at the diagonal'); a1.legend(frameon=False, fontsize=8)
rows = res[1009]
P = [r['P'] for r in rows]
a2.loglog(P, [r['trivial_sq'] for r in rows], 's-', color='#c0392b', ms=3.5, label='$\\chi=1$ ($\\zeta$ arms)')
a2.loglog(P, [r['median_sq'] for r in rows], 'o-', color='#1f4e79', ms=3.5, label='median over $\\chi$')
a2.loglog(P, [r['max_sq_nontrivial'] for r in rows], '^-', color='#555555', ms=3.5, label='largest $\\chi\\neq1$')
a2.loglog(P, [r['diagonal'] for r in rows], '--', color='#888888', lw=0.9, label='diagonal $\\sum 1/p$')
a2.axvline(1009, color='#1f4e79', lw=0.6, ls=':')
a2.set_xlabel('primes $p\\leq P$'); a2.set_ylabel('$|W_\\chi(P)|^2$')
a2.set_title('(b) $q=1009$: individual members'); a2.legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'paper', 'figures', 'fig8_family.pdf'), bbox_inches='tight')

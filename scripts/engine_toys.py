#!/usr/bin/env python3
"""Step 3: toy versions of the engine parts that can be computed.

Stepanov over F_p used three things (paper section 10): free linear algebra, a degree that bounds
the number of zeros, and multiplicity obtained cheaply from x -> x^p.  Over Z each needs a
replacement, and each replacement has a cost.
 (A) Linear algebra is not free over Z: Siegel's lemma.  An integer system A y = 0 with M equations,
     N > M unknowns and entries <= B has a nonzero integer solution with |y| <= (N B)^{M/(N-M)}.
     We find small solutions by LLL and compare with the bound.
 (B) Degree is replaced by size (the product formula: a nonzero integer has |n| >= 1).
     Chebyshev: C(2n, n) is divisible by every prime in (n, 2n] and C(2n, n) <= 4^n, hence
     theta(2n) - theta(n) <= n log 4.  The loss is only in the constant (log 4 against 1).
 (C) Multiplicity by iteration costs exponentially over Z.  The chain N_j = a^{n p^j} - 1 gains one
     power of p per step (lifting the exponent), but log N_j grows by a factor p per step.  Over F_p,
     Stepanov's multiplicity M costs only linearly (step A of explorations/README; Table 10 of the paper).
Writes validation/engine_toys.json and paper/figures/fig14_engine.pdf.
"""
import json, math, os
from math import comb, log
import numpy as np
from sympy import Matrix
from sympy.polys.matrices import DomainMatrix
from sympy import ZZ
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

rng = np.random.default_rng(0)
out = {}

# (A) Siegel's lemma vs LLL
def small_kernel_vector(A, K=10**6):
    M, N = A.shape
    basis = np.hstack([np.eye(N, dtype=object), (K * A.T).astype(object)])     # rows: e_i | K * (column i of A)
    dm = DomainMatrix([[ZZ(int(v)) for v in row] for row in basis], (N, N + M), ZZ)
    red = dm.lll().to_Matrix()
    best = None
    for r in range(red.rows):
        row = [int(v) for v in red.row(r)]
        if all(v == 0 for v in row[N:]) and any(row[:N]):
            nrm = max(abs(v) for v in row[:N])
            if best is None or nrm < best: best = nrm
    return best
siegel = []
B = 10
for (M, N) in ((2, 4), (2, 6), (3, 6), (3, 9), (4, 8), (4, 12), (5, 10), (6, 12)):
    sizes = []
    for _ in range(5):
        A = rng.integers(-B, B + 1, (M, N))
        v = small_kernel_vector(A)
        sizes.append(v)
    bound = (N * B) ** (M / (N - M))
    siegel.append(dict(M=M, N=N, B=B, median_lll=float(np.median(sizes)), siegel_bound=float(bound),
                       exponent=M / (N - M)))
    print(f'(A) M={M} N={N}: LLL solution size median {np.median(sizes):.0f}, Siegel bound {bound:.0f}, exponent M/(N-M)={M/(N-M):.2f}')
out['siegel'] = siegel

# (B) Chebyshev counting by size
sv = np.ones(200001, bool); sv[:2] = False
for i in range(2, 448):
    if sv[i]: sv[i * i::i] = False
pr = np.nonzero(sv)[0]
cheb = []
for n in (10, 100, 1000, 10000, 100000):
    th = float(np.sum(np.log(pr[(pr > n) & (pr <= 2 * n)])))
    lb = log(comb(2 * n, n))
    cheb.append(dict(n=n, theta_2n_minus_theta_n=th, log_binomial=lb, n_log4=n * log(4), ratio_to_n=th / n))
    print(f'(B) n={n}: theta(2n)-theta(n)={th:.1f}  <= log C(2n,n)={lb:.1f}  <= n log 4={n*log(4):.1f}   (true ratio {th/n:.3f}, bound ratio {log(4):.3f})')
out['chebyshev'] = cheb

# (C) chain cost: lifting the exponent versus Stepanov
a, p, n0 = 2, 7, 3                     # ord_7(2) = 3
chain = []
for j in range(0, 7):
    e = n0 * p ** j
    # v_p(a^e - 1) by lifting the exponent: v_p(a^{n0}-1) + j
    v = 0; t = pow(a, n0) - 1
    while t % p == 0: t //= p; v += 1
    vj = v + j
    height = e * log(a)                  # log(a^e - 1)
    chain.append(dict(step=j, exponent=e, p_adic_valuation=vj, log_height=height, gain_per_height=vj * log(p) / height))
    print(f'(C) step {j}: v_7(2^{e}-1) = {vj},  log height = {height:.1f},  (gain in log p)/(height) = {vj*log(p)/height:.4f}')
out['lte_chain'] = chain
step = json.load(open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'stepanov_results.json')))
out['stepanov_p401'] = [dict(M=r['M'], degR=r['degR'], degR_over_M=r['bound']) for r in step['vs_M_p401']]
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'engine_toys.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(1, 3, figsize=(13, 3.6))
ex = [s['exponent'] for s in siegel]
ax[0].semilogy(ex, [s['median_lll'] for s in siegel], 'o', color='#1f4e79', label='LLL solution (median)')
ax[0].semilogy(ex, [s['siegel_bound'] for s in siegel], 's', color='#c0392b', mfc='none', label='Siegel bound $(NB)^{M/(N-M)}$')
ax[0].set_xlabel('$M/(N-M)$'); ax[0].set_ylabel('size of smallest integer solution'); ax[0].legend(frameon=False, fontsize=8)
ax[0].set_title('(A) linear algebra over $\\mathbb{Z}$ has a size cost')
nn = [c['n'] for c in cheb]
ax[1].semilogx(nn, [c['ratio_to_n'] for c in cheb], 'o-', color='#1f4e79', label='$(\\theta(2n)-\\theta(n))/n$')
ax[1].axhline(log(4), color='#c0392b', ls='--', lw=1, label='bound from $C(2n,n)\\leq 4^n$: $\\log 4$')
ax[1].axhline(1, color='#888888', lw=0.8); ax[1].set_ylim(0.5, 1.6); ax[1].legend(frameon=False, fontsize=8)
ax[1].set_xlabel('$n$'); ax[1].set_title('(B) size replaces degree: loss only in the constant')
ax[2].semilogy([c['p_adic_valuation'] for c in chain], [c['log_height'] / c['p_adic_valuation'] for c in chain], 'o-', color='#c0392b',
               label='iteration over $\\mathbb{Z}$: $\\log(2^{3\\cdot7^j}-1)/v_7$')
ms = [r['M'] for r in out['stepanov_p401']]
ax[2].semilogy(ms, [r['degR_over_M'] for r in out['stepanov_p401']], 's-', color='#1f4e79', label='Stepanov over $\\mathbb{F}_{401}$: $\\deg R/M$')
ax[2].set_xlabel('multiplicity gained'); ax[2].set_ylabel('cost per unit of multiplicity')
ax[2].set_title('(C) multiplicity: exponential vs bounded cost')
ax[2].legend(frameon=False, fontsize=7)
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'paper', 'figures', 'fig14_engine.pdf'), bbox_inches='tight')

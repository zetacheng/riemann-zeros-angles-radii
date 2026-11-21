#!/usr/bin/env python3
"""Amplification: from the family to one member.

Family: Dirichlet characters chi_j mod q.  W_j = log of the partial Euler product of L(s, chi_j)
over p <= P at s = 1/2 + 14.1347i (as in character_family.py).  To bound one member chi_0:
  trivial:    |W_0|^2 <= sum_j |W_j|^2
  amplified:  A_j = |sum_{l <= L, l prime} conj(chi_0(l)) chi_j(l)|^2  (so A_0 = pi(L)^2), and
              |W_0|^2 <= sum_j A_j |W_j|^2 / A_0.
The gain trivial/amplified measures how much the amplifier isolates chi_0.
Caveat: the amplified moment sum_j A_j |W_j|^2 is computed here exactly from the W_j.  A proof
must estimate it from orthogonality alone, which is exact only while products l * p^k stay
below q (L * P < q); every run below is far outside that range (P = 1e5 > q).
Writes amplifier.json and amplifier.png.
"""
import json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

t = 14.134725141734693; s = 0.5 + 1j * t
q = 10007; P = 100_000; K = 4
N = 200_000
sv = np.ones(N + 1, bool); sv[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
primes = np.nonzero(sv)[0]

def primroot(q):
    fac = [f for f in range(2, q) if (q - 1) % f == 0 and all(f % d for d in range(2, int(f ** 0.5) + 1))]
    for g in range(2, q):
        if all(pow(g, (q - 1) // f, q) != 1 for f in fac): return g
g = primroot(q); n = q - 1
dlog = np.zeros(q, np.int64); x = 1
for a in range(n): dlog[x] = a; x = x * g % q

ps = primes[(primes != q) & (primes <= P)]; ap = dlog[ps % q]
bins = np.zeros(n, complex)
for k in range(1, K + 1):
    np.add.at(bins, (k * ap) % n, np.exp(-k * s * np.log(ps.astype(float))) / k)
W = np.fft.fft(bins); W2 = np.abs(W) ** 2           # W[j] uses chi_j(g^a) = e^{-2 pi i j a/n}; any labelling works

targets = {'largest member': int(np.argmax(W2[1:]) + 1), 'median member': int(np.argsort(W2[1:])[len(W2) // 2] + 1),
           'zeta (trivial)': 0}
Ls = [2, 5, 10, 30, 100, 300, 1000, 3000, 10_000, 30_000, 100_000]
out = dict(q=q, P=P, t=t, family_mean_sq=float(W2.mean()), results={})
trivial = float(W2.sum())
for name, j0 in targets.items():
    rows = []
    for L in Ls:
        lp = primes[(primes <= L) & (primes != q)]
        b = np.zeros(n, complex); np.add.at(b, dlog[lp % q], 1.0)
        S = np.fft.fft(b)                                  # S[j] = sum_l chi_j(l)
        # A_j = |sum_l conj(chi_j0(l)) chi_j(l)|^2 = |S[(j - j0) mod n]|^2 with this labelling
        A = np.abs(np.roll(S, j0)) ** 2
        A0 = A[j0]
        bound = float(np.sum(A * W2) / A0)
        rows.append(dict(L=L, n_amp=int(len(lp)), A0=float(A0), mean_A=float(A.mean()), bound=bound,
                         true=float(W2[j0]), trivial=trivial, gain=trivial / bound, bound_over_true=bound / float(W2[j0])))
        print(name, json.dumps({k: round(v, 3) if isinstance(v, float) else v for k, v in rows[-1].items()}), flush=True)
    out['results'][name] = dict(j0=j0, rows=rows)
ROOT = os.path.dirname(os.path.abspath(__file__))
json.dump(out, open(os.path.join(ROOT, 'amplifier.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(10, 4.2))
cols = {'largest member': '#1f4e79', 'median member': '#2e7d32', 'zeta (trivial)': '#c0392b'}
for name, d in out['results'].items():
    r = d['rows']; L = [x['L'] for x in r]
    a1.loglog(L, [x['bound_over_true'] for x in r], 'o-', ms=3.5, color=cols[name], label=name)
    a2.loglog([x['n_amp'] for x in r], [x['gain'] for x in r], 'o-', ms=3.5, color=cols[name], label=name)
a1.axhline(1, color='#888888', lw=0.8); a1.axvline(math.sqrt(q), color='#888888', lw=0.6, ls=':'); a1.axvline(q, color='#888888', lw=0.6, ls='--')
a1.set_xlabel('amplifier length $L$'); a1.set_ylabel('amplified bound / true $|W_{\\chi_0}|^2$')
a1.set_title(f'(a) how close the bound gets, $q={q}$'); a1.legend(frameon=False, fontsize=8)
nn = np.array([1, 1e4]); a2.loglog(nn, nn, '--', color='#888888', lw=0.8, label='gain $=$ number of amplifier primes')
a2.set_xlabel('number of amplifier primes'); a2.set_ylabel('gain over the trivial bound')
a2.set_title('(b) gain from amplification'); a2.legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'amplifier.png'), dpi=130, bbox_inches='tight')

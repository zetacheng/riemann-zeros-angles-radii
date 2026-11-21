#!/usr/bin/env python3
"""A suspected impurity: is any L(1, chi_q) abnormally small?  (author's question, log entry 52)

A Siegel zero of a real character chi would make L(1, chi) very small, roughly of size
(1 - beta) log q, below 1/log q.  Ordinary extreme values are much milder: under GRH,
Littlewood's bounds give L(1, chi) between about (pi^2 / (12 e^gamma)) / log log q and
2 e^gamma log log q.  For every prime q <= QMAX we compute L(1, (./q)) = sum chi(n)/n up to
N = 40 q (tail <= 2 sqrt(q) log q / N by Polya-Vinogradov) and record the smallest values.
Writes siegel_check.json.
"""
import json, math, os
import numpy as np

QMAX = 20000
EG = math.exp(0.5772156649)
sv = np.ones(QMAX + 1, bool); sv[:2] = False
for i in range(2, int(QMAX ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
rows = []
for q in np.nonzero(sv)[0][1:]:                       # odd primes
    q = int(q)
    chi = -np.ones(q); chi[0] = 0
    chi[(np.arange(1, q) ** 2) % q] = 1                 # Legendre symbol table
    N = 40 * q
    n = np.arange(1, N + 1)
    L = float(np.sum(chi[n % q] / n))
    rows.append(dict(q=q, L1=L, parity='odd' if q % 4 == 3 else 'even', tail_bound=2 * math.sqrt(q) * math.log(q) / N,
                     scaled_low=L * math.log(math.log(q)) if q > 3 else None))
L1 = np.array([r['L1'] for r in rows]); qs = np.array([r['q'] for r in rows])
order = np.argsort(L1)
smallest = [rows[i] for i in order[:8]]
out = dict(QMAX=QMAX, count=len(rows), smallest=smallest,
           min_L1=float(L1.min()), max_L1=float(L1.max()),
           littlewood_low_const=math.pi ** 2 / (12 * EG), littlewood_high_const=2 * EG,
           min_L1_times_loglogq=float(min(r['L1'] * math.log(math.log(r['q'])) for r in rows if r['q'] > 3)),
           min_L1_times_logq=float(min(r['L1'] * math.log(r['q']) for r in rows)),
           max_tail_bound=float(max(r['tail_bound'] for r in rows)))
print(json.dumps({k: v for k, v in out.items() if k != 'smallest'}, indent=1))
for r in smallest: print(r['q'], r['parity'], round(r['L1'], 4), 'L1*log q =', round(r['L1'] * math.log(r['q']), 3))
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'siegel_check.json'), 'w'), indent=1)

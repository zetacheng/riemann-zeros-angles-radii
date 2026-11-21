#!/usr/bin/env python3
"""Is the growth of the worst member an 'impurity'?  (author's question, log entry 50)

For the family of characters mod q, compare the largest |W_chi(P)|^2 (chi != 1, P = 1e5,
s = 1/2 + 14.1347i) with
  (a) extreme-value statistics: if |W|^2 were exponential with the family mean D, the maximum
      of N members would be about D (ln N + 0.577);
  (b) a random model: the same primes, with chi(p) replaced by independent random points of the
      unit circle, N samples.
An impurity (an off-line zero) would instead produce power-law growth.  Also records Re W of
the largest member: Re W = log|partial Euler product|, very negative near a zero on the line.
Writes worst_member.json.
"""
import json, math, os
import numpy as np

t = 14.134725141734693; s = 0.5 + 1j * t; P = 100_000; K = 4
sv = np.ones(P + 1, bool); sv[:2] = False
for i in range(2, int(P ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
primes = np.nonzero(sv)[0]

def primroot(q):
    fac = [f for f in range(2, q) if (q - 1) % f == 0 and all(f % d for d in range(2, int(f ** 0.5) + 1))]
    for g in range(2, q):
        if all(pow(g, (q - 1) // f, q) != 1 for f in fac): return g

rng = np.random.default_rng(0)
rows = []
for q in (31, 101, 307, 1009, 3001, 10007, 30011, 100003):
    g = primroot(q); n = q - 1
    dlog = np.zeros(q, np.int64); x = 1
    for a in range(n): dlog[x] = a; x = x * g % q
    ps = primes[primes != q]; ap = dlog[ps % q]; lp = np.log(ps.astype(float))
    bins = np.zeros(n, complex)
    for k in range(1, K + 1):
        np.add.at(bins, (k * ap) % n, np.exp(-k * s * lp) / k)
    W = np.fft.fft(bins); W2 = np.abs(W) ** 2
    D = float(np.mean(W2[1:])); N = n - 1
    jmax = int(np.argmax(W2[1:]) + 1)
    # random model: chi(p) -> e^{i theta_p}, chi(p^k) -> e^{i k theta_p}
    w1 = np.exp(-s * lp)
    nsamp = min(N, 20000); mx = 0.0
    done = 0
    while done < nsamp:
        b = min(500, nsamp - done); done += b
        th = rng.uniform(0, 2 * np.pi, (b, len(ps)))
        Z = np.zeros(b, complex)
        for k in range(1, K + 1):
            Z += (np.exp(1j * k * th) * (w1 ** k / k)).sum(axis=1)
        mx = max(mx, float(np.max(np.abs(Z) ** 2)))
    # tail check: fraction of members above 3 D and 5 D (exponential law: e^-3 = 0.050, e^-5 = 0.0067)
    rows.append(dict(q=q, members=N, mean=D, max=float(W2[jmax]), ev_prediction=D * (math.log(N) + 0.5772),
                     random_model_max=mx, random_model_samples=nsamp,
                     frac_above_3D=float(np.mean(W2[1:] > 3 * D)), frac_above_5D=float(np.mean(W2[1:] > 5 * D)),
                     ReW_of_max=float(W[jmax].real), ImW_of_max=float(W[jmax].imag)))
    print(json.dumps({k: round(v, 4) if isinstance(v, float) else v for k, v in rows[-1].items()}), flush=True)
json.dump(rows, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'worst_member.json'), 'w'), indent=1)

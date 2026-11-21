#!/usr/bin/env python3
"""How close does the helix come to closing?  The line t -> (t log p / 2pi mod 1)_{p <= P}
on the torus, one circle per prime (Bohr's lift).  For the first k primes and tolerance eps,
find the first t > 0 at which every coordinate is within eps of an integer.

Search: the coordinate of p = 2 vanishes exactly at t = 2 pi m / log 2; we scan m and record the
first m with max_p ||m log p / log 2|| < eps (an upper bound for the true first time, which can
lie slightly off these points).  Heuristic: a box of side 2 eps in k-1 dimensions is hit after
about (2 eps)^-(k-1) values of m; Dirichlet's theorem guarantees a hit with m <= eps^-(k-1).
Writes torus_closure.json.
"""
import json, math, os
import numpy as np

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
L = np.log(np.array(primes, dtype=np.float64))
r = (L[1:] / L[0])                      # coordinate of p at t = 2 pi m / log 2 is m * r_p mod 1
CHUNK = 5_000_000
MAXM = 2_000_000_000

def first_hit(k, eps):
    rr = r[:k - 1]
    m0 = 1
    while m0 <= MAXM:
        m = np.arange(m0, m0 + CHUNK, dtype=np.float64)
        ok = np.ones(CHUNK, bool)
        for x in rr:                    # longdouble-free: m*x with m < 2e9 keeps ~7 digits of the fraction
            f = m * x; d = np.abs(f - np.rint(f)); ok &= d < eps
            if not ok.any(): break
        idx = np.nonzero(ok)[0]
        if len(idx):
            mm = int(m0 + idx[0]); t = 2 * math.pi * mm / math.log(2)
            worst = max(abs(mm * x - round(mm * x)) for x in rr) if k > 1 else 0.0
            return dict(k=k, P=primes[k - 1], eps=eps, m=mm, t=t, worst=worst,
                        heuristic_m=(2 * eps) ** -(k - 1), dirichlet_m=eps ** -(k - 1))
        m0 += CHUNK
    return dict(k=k, P=primes[k - 1], eps=eps, m=None, note=f'no hit with m <= {MAXM}')

out = []
for eps in (0.1, 0.05):
    for k in range(2, 13):
        res = first_hit(k, eps); out.append(res)
        print(json.dumps(res), flush=True)
        if res.get('m') is None: break
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'torus_closure.json'), 'w'), indent=1)

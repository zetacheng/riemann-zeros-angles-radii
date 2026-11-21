#!/usr/bin/env python3
"""Peak heights of the reverse trace at t = log n versus the explicit-formula
prediction A * Lambda(n) / sqrt(n), A = Gamma / (4 sqrt(pi)).
Baseline = mean of R at t = log n +- 0.02.  Writes ../validation/peak_heights.json."""
import json, math, os
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
g = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))
G = 600.0
A = G / (4 * math.sqrt(math.pi))
w = np.exp(-(g / G) ** 2)
R = lambda x: float(-(w * np.cos(g * x)).sum())

def lam(n):
    p = min(d for d in range(2, n + 1) if n % d == 0)
    m = n
    while m % p == 0:
        m //= p
    return math.log(p) if m == 1 else 0.0

out = []
for n in range(2, 28):
    x = math.log(n)
    base = 0.5 * (R(x - 0.02) + R(x + 0.02))
    out.append(dict(n=n, observed=round(R(x) - base, 2), predicted=round(A * lam(n) / math.sqrt(n), 2),
                    baseline=round(base, 2)))
    print(out[-1])
json.dump(dict(A=round(A, 3), rows=out), open(os.path.join(ROOT, 'validation', 'peak_heights.json'), 'w'), indent=1)
print('max |observed - predicted| =', max(abs(r['observed'] - r['predicted']) for r in out))

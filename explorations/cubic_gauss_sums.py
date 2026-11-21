#!/usr/bin/env python3
"""Cubic Gauss sums at primes of Z[omega] -- the coefficients behind Kubota's cubic theta.

For each rational prime p = 1 mod 3, write p = pi * conj(pi) with pi = a + b*omega
primary (a = 2, b = 0 mod 3).  Both pi and conj(pi) are primary primes of norm p.
  chi_pi(d) = omega^k  where d^((p-1)/3) = omega_p^k (mod p), omega_p = -a/b (mod p),
  g(pi)     = sum_{d mod p} chi_pi(d) e(Tr(d/pi)),  Tr(d/pi) = d (2a-b)/p.
Checks |g|^2 = p and the cube identity, then studies the angles of g/sqrt(p):
equidistribution (Heath-Brown--Patterson) and the growth of their partial sums
(Patterson's conjecture predicts a bias of order X^{5/6} in sum g/sqrt(N)).
Usage: python3 cubic_gauss_sums.py X
"""
import cmath, json, math, os, sys
import numpy as np

X = int(sys.argv[1]) if len(sys.argv) > 1 else 50000
OMEGA = cmath.exp(2j * math.pi / 3)
ROOT = os.path.dirname(os.path.abspath(__file__))

def primes_upto(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]

def powmod_vec(base, e, p):
    r = np.ones_like(base); b = base % p
    while e:
        if e & 1: r = (r * b) % p
        b = (b * b) % p; e >>= 1
    return r

def primary(p):
    for b in range(0, int(2 * math.sqrt(p / 3)) + 2):
        disc = 4 * p - 3 * b * b
        if disc < 0: break
        s = math.isqrt(disc)
        if s * s == disc:
            for a in ((b + s) // 2, (b - s) // 2):
                if a * a - a * b + b * b == p:
                    x, y = a, b
                    for _ in range(6):           # associates: multiply by -omega repeatedly
                        if x % 3 == 2 and y % 3 == 0:
                            return x, y
                        x, y = y, y - x          # (-omega)(x + y omega) = y + (y - x) omega
    raise ValueError(p)

def gauss(a, b, p):
    d = np.arange(1, p, dtype=np.int64)
    wp = (-a * pow(b, -1, p)) % p
    r = powmod_vec(d, (p - 1) // 3, p)
    k = np.where(r == 1, 0, np.where(r == wp, 1, 2))
    chi = np.array([1, OMEGA, OMEGA ** 2])[k]
    t = (2 * a - b) % p
    return complex(np.sum(chi * np.exp(2j * np.pi * ((d * t) % p) / p)))

rows = []
for p in primes_upto(X):
    p = int(p)
    if p % 3 != 1: continue
    a, b = primary(p)
    for (x, y) in ((a, b), (a - b, -b)):        # pi and conj(pi), both primary
        g = gauss(x, y, p)
        pi = complex(x, 0) + y * OMEGA
        rows.append((p, x, y, g, pi))

err_abs = max(abs(abs(g) ** 2 - p) / p for p, x, y, g, pi in rows)
# cube identity: compare g^3 / p with pi, conj(pi) and their unit multiples
cands = {}
for p, x, y, g, pi in rows:
    c = g ** 3 / p
    for name, z in (('pi', pi), ('conj(pi)', pi.conjugate()), ('-pi', -pi), ('-conj(pi)', -pi.conjugate())):
        cands.setdefault(name, 0.0)
        cands[name] = max(cands[name], abs(c - z) / math.sqrt(p))
ang = np.array([cmath.phase(g) for p, x, y, g, pi in rows])
hist = np.histogram(np.mod(ang, 2 * math.pi), bins=12, range=(0, 2 * math.pi))[0].tolist()
gn = np.array([g / math.sqrt(p) for p, x, y, g, pi in rows])
Ns = np.array([p for p, x, y, g, pi in rows])
partial = []
for Y in (X // 16, X // 8, X // 4, X // 2, X):
    m = Ns <= Y
    s = gn[m].sum()
    partial.append(dict(X=Y, count=int(m.sum()), sum_real=round(s.real, 2), sum_imag=round(s.imag, 2),
                        sqrt_count=round(math.sqrt(m.sum()), 2), X56_over_logX=round(Y ** (5 / 6) / math.log(Y), 2)))
out = dict(X=X, primes_pi=len(rows), max_rel_err_abs2=err_abs, cube_identity_max_err=cands,
           angle_hist12=hist, partial_sums=partial)
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(ROOT, f'cubic_gauss_X{X}.json'), 'w'), indent=1)

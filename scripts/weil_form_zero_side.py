#!/usr/bin/env python3
"""Truncated Weil quadratic form on even test functions supported in [-L/2, L/2]
(log variable u = log x), computed from the explicit formula of the paper:

  sum_gamma h(gamma) = h(i/2)+h(-i/2) - g(0) log pi
                       + (1/2pi) int h(r) Re psi(1/4 + i r/2) dr
                       - 2 sum_n Lambda(n) n^{-1/2} g(log n),

with h(r) = phi_hat_j(r) phi_hat_k(r), g = phi_j * phi_k (supported in [-L, L]).
Basis: phi_k(u) = cos(w_k u), w_k = (2k+1) pi / L, k = 0..N-1 (vanishes at +-L/2).
  phi_hat_k(r) = (-1)^k cos(rL/2) 2 w_k / (w_k^2 - r^2).
Under RH the left side is the Gram matrix sum_gamma v_gamma v_gamma^T (PSD);
Weil: RH <=> the right side is PSD for every L and N.
The script also builds the left side from the first 1200 zeros as an
independent check of the matrix.

Usage: python3 weil_form.py L N
"""
import json, math, os, sys
import numpy as np
from mpmath import digamma, mpc

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
L = float(eval(sys.argv[1])) if len(sys.argv) > 1 else math.log(13)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 8
w = (2 * np.arange(N) + 1) * math.pi / L
sgn = (-1.0) ** np.arange(N)

def phihat(r):                      # shape (len(r), N)
    r = np.asarray(r, float)[:, None]
    return sgn * np.cos(r * L / 2) * 2 * w / (w ** 2 - r ** 2)

def conv(j, k, x, m=4001):          # (phi_j * phi_k)(x), x >= 0
    a, b = x - L / 2, L / 2
    if a >= b:
        return 0.0
    v = np.linspace(a, b, m)
    f = np.cos(w[j] * v) * np.cos(w[k] * (x - v))
    return np.trapezoid(f, v)

def vonmangoldt(n):
    p = min(d for d in range(2, n + 1) if n % d == 0)
    m = n
    while m % p == 0:
        m //= p
    return math.log(p) if m == 1 else 0.0

# ---- pole term (rank one for even test functions)
A = sgn * math.cosh(L / 4) * 2 * w / (w ** 2 + 0.25)
Q_pole = 2 * np.outer(A, A)
# ---- log pi term
Q_logpi = -math.log(math.pi) * (L / 2) * np.eye(N)
# ---- archimedean term: (1/2pi) int_R h(r) Re psi(1/4+ir/2) dr = (1/pi) int_0^inf ...
#      integrand has removable singularities at r = w_k; avoid them by an offset grid
R_MAX, DR = 4000.0, 0.0025
r = np.arange(DR / 2, R_MAX, DR)
psi = np.array([float(digamma(mpc(0.25, x / 2)).real) for x in r[::40]])
psi = np.interp(r, r[::40], psi)
P = phihat(r)
Q_arch = (P * psi[:, None]).T @ P * DR / math.pi
# tail r > R_MAX: |phihat| <~ 2w/r^2, psi ~ log(r/2)
Q_arch_tail_bound = (4 * np.outer(w, w)) * (math.log(R_MAX / 2) + 1) / (3 * R_MAX ** 3) / math.pi
# ---- prime term
ns = [n for n in range(2, int(math.exp(L)) + 1) if vonmangoldt(n) > 0]
Q_prime = np.zeros((N, N))
for n in ns:
    x = math.log(n)
    c = 2 * vonmangoldt(n) / math.sqrt(n)
    for j in range(N):
        for k in range(j, N):
            Q_prime[j, k] += c * conv(j, k, x)
            if k != j:
                Q_prime[k, j] = Q_prime[j, k]
Q = Q_pole + Q_logpi + Q_arch - Q_prime

# ---- zero-side check: sum over gamma of h(gamma), both signs => 2 * sum over gamma > 0
g = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))
V = phihat(g)
Q_zero = 2 * V.T @ V

ev, evec = np.linalg.eigh(Q)
evz = np.linalg.eigvalsh(Q_zero)
out = dict(L=L, e_L=math.exp(L), N=N, prime_powers=ns,
           eig_formula=[float(x) for x in ev], eig_zero_side=[float(x) for x in evz],
           max_abs_diff=float(np.abs(Q - Q_zero).max()), max_entry=float(np.abs(Q).max()),
           arch_tail_bound=float(np.abs(Q_arch_tail_bound).max()))
c0 = evec[:, 0]
rr = np.linspace(0.5, 60, 200000)
F = phihat(rr) @ c0
zc = rr[1:][np.sign(F[1:]) != np.sign(F[:-1])]
out['ground_state_zeros'] = [float(z) for z in zc[:8]]
out['zeta_zeros'] = [float(z) for z in g[:8]]
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(ROOT, 'validation', f'weil_form_L{L:.4f}_N{N}.json'), 'w'), indent=1)

#!/usr/bin/env python3
"""High-precision truncated Weil form (no zeros used).

Even test functions on [-L/2, L/2], basis phi_k(u) = cos(w_k u), w_k = (2k+1)pi/L.
g_jk = phi_j * phi_k is computed in closed form.  Terms:
  pole     2 A_j A_k,            A_k = phihat_k(i/2) = (-1)^k cosh(L/4) 2w_k/(w_k^2+1/4)
  log pi   -log(pi) g(0)
  arch     psi(1/4) g(0) + 2 int_0^inf e^{-u/2}/(1-e^{-2u}) [g(0)-g(u)] du
           (from Re psi(1/4+ir/2) = psi(1/4) + int_0^inf e^{-t/4}(1-cos(rt/2))/(1-e^{-t}) dt)
  primes   -2 sum_{n <= e^L} Lambda(n) n^{-1/2} g(log n)
Usage: python3 weil_form_mp.py L N [dps]
"""
import json, math, os, sys
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
Ls = sys.argv[1] if len(sys.argv) > 1 else 'log(13)'
N = int(sys.argv[2]) if len(sys.argv) > 2 else 8
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 60
L = mp.mpf(eval(Ls, {'log': mp.log, 'mpf': mp.mpf}))
w = [(2 * k + 1) * mp.pi / L for k in range(N)]

def icos(al, be, a, b):            # int_a^b cos(al v + be) dv
    if al == 0:
        return mp.cos(be) * (b - a)
    return (mp.sin(al * b + be) - mp.sin(al * a + be)) / al

def g(j, k, x):                    # (phi_j * phi_k)(x), even in x
    x = abs(x)
    if x >= L:
        return mp.mpf(0)
    a, b = x - L / 2, L / 2
    return (icos(w[j] - w[k], w[k] * x, a, b) + icos(w[j] + w[k], -w[k] * x, a, b)) / 2

def lam(n):
    p = min(d for d in range(2, n + 1) if n % d == 0)
    m = n
    while m % p == 0:
        m //= p
    return mp.log(p) if m == 1 else mp.mpf(0)

A = [(-1) ** k * mp.cosh(L / 4) * 2 * w[k] / (w[k] ** 2 + mp.mpf(1) / 4) for k in range(N)]
tailK = mp.nsum(lambda m: 2 * mp.exp(-L * (mp.mpf(1) / 2 + 2 * m)) / (mp.mpf(1) / 2 + 2 * m), [0, mp.inf])
ns = [n for n in range(2, int(mp.floor(mp.exp(L))) + 1) if lam(n) != 0]
Q = mp.matrix(N, N)
for j in range(N):
    for k in range(j, N):
        g0 = g(j, k, 0)
        arch = mp.digamma(mp.mpf(1) / 4) * g0 \
            + mp.quad(lambda u: 2 * mp.exp(-u / 2) / (1 - mp.exp(-2 * u)) * (g0 - g(j, k, u)), [0, L / 2, L]) \
            + g0 * tailK
        prime = sum(2 * lam(n) / mp.sqrt(n) * g(j, k, mp.log(n)) for n in ns)
        Q[j, k] = 2 * A[j] * A[k] - mp.log(mp.pi) * g0 + arch - prime
        Q[k, j] = Q[j, k]
E, V = mp.eigsy(Q)
order = sorted(range(N), key=lambda i: E[i])
ev = [E[i] for i in order]
c0 = [V[r, order[0]] for r in range(N)]
def F(r):                          # Fourier transform of the ground state
    return sum(c0[k] * (-1) ** k * mp.cos(r * L / 2) * 2 * w[k] / (w[k] ** 2 - r ** 2) for k in range(N))
# zeros of F excluding the common factor cos(rL/2)
def Fred(r):
    return sum(c0[k] * (-1) ** k * 2 * w[k] / (w[k] ** 2 - r ** 2) for k in range(N))
zs = []
grid = [mp.mpf(i) / 20 for i in range(1, 1200)]
vals = [Fred(x) for x in grid]
for i in range(len(grid) - 1):
    if vals[i] * vals[i + 1] < 0 and all(abs(grid[i] - wk) > 0.06 for wk in w):
        zs.append(mp.findroot(Fred, (grid[i], grid[i + 1]), solver='anderson'))
out = dict(L=mp.nstr(L, 12), e_L=mp.nstr(mp.exp(L), 10), N=N, dps=mp.mp.dps, prime_powers=ns,
           eigenvalues=[mp.nstr(x, 12) for x in ev], ground_state_zeros=[mp.nstr(z, 12) for z in zs[:6]],
           basis_frequencies=[mp.nstr(x, 8) for x in w])
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(ROOT, 'validation', f'weil_mp_{Ls.replace("(", "").replace(")", "")}_N{N}.json'), 'w'), indent=1)

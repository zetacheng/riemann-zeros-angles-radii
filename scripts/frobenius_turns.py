#!/usr/bin/env python3
"""'Turning the circle n times' where Frobenius exists: an elliptic curve over F_p.

E: y^2 = x^3 + x + 1 over F_7.  Count points over F_{7^n} directly, compare with
N_n = q^n + 1 - alpha^n - conj(alpha)^n, and contrast with a fake 'curve' whose
Frobenius roots are off the circle but whose counts are still positive integers.
Number-field side: psi(2^n) - 2^n, the analogue of the sum of alpha^n over zeros.
Writes validation/frobenius_turns.json and paper/figures/fig5_turning.pdf.
"""
import cmath, itertools, json, math, os
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

p = 7
def polymulmod(a, b, mod):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    n = len(mod) - 1
    for i in range(len(r) - 1, n - 1, -1):
        c = r[i]
        if c:
            for j in range(n + 1):
                r[i - n + j] = (r[i - n + j] - c * mod[j]) % p
    return (r[:n] + [0] * n)[:n]

def irreducible(n):
    for coeffs in itertools.product(range(p), repeat=n):
        mod = list(coeffs) + [1]
        if n == 1: return mod
        # x^(p^n) = x and no smaller-degree factor: check gcd-free via brute root/structure test
        x = [0, 1] + [0] * (n - 2)
        y = x[:]
        ok = True
        for k in range(1, n + 1):
            z = [1] + [0] * (n - 1)
            for _ in range(p): z = polymulmod(z, y, mod)
            y = z
            if y == x and k < n and n % k == 0: ok = False; break
        if ok and y == x: return mod

def powe(a, e, mod):
    r = [1] + [0] * (len(mod) - 2); b = a[:]
    while e:
        if e & 1: r = polymulmod(r, b, mod)
        b = polymulmod(b, b, mod); e >>= 1
    return r

def count(n):
    mod = irreducible(n); q = p ** n; one = [1] + [0] * (n - 1); zero = [0] * n
    N = 1                                   # point at infinity
    for el in itertools.product(range(p), repeat=n):
        x = list(el)
        f = polymulmod(polymulmod(x, x, mod), x, mod)
        f = [(f[i] + x[i] + (1 if i == 0 else 0)) % p for i in range(n)]
        if f == zero: N += 1
        elif powe(f, (q - 1) // 2, mod) == one: N += 2
    return N

N1 = count(1); a = p + 1 - N1
alpha = complex(a / 2, math.sqrt(4 * p - a * a) / 2)
print(f'E: y^2=x^3+x+1 over F_{p}:  N_1={N1}, a_p={a}, |alpha|={abs(alpha):.6f}, sqrt(p)={math.sqrt(p):.6f}')
print(' n   direct count   p^n+1-2Re(alpha^n)   |alpha^n|/p^(n/2)   angle of alpha^n (deg)')
real_rows = []
for n in range(1, 5):
    pred = p ** n + 1 - 2 * (alpha ** n).real
    real_rows.append(dict(n=n, direct=count(n), predicted=round(pred, 9), radius_ratio=round(abs(alpha**n)/p**(n/2), 12), angle_deg=round(math.degrees(cmath.phase(alpha**n)), 1)))
    print(f'{n:2d} {count(n):14d} {pred:20.6f} {abs(alpha**n)/p**(n/2):19.6f} {math.degrees(cmath.phase(alpha**n)):12.1f}')

# fake 'curve': T^2 - p T + p, roots real, off the circle
r = math.sqrt(p * p - 4 * p)
A, B = (p + r) / 2, (p - r) / 2
print(f'\nFake roots of T^2-{p}T+{p}: {A:.4f}, {B:.4f}  (|alpha| vs sqrt(p)={math.sqrt(p):.4f})')
print(' n   N_n = p^n+1-A^n-B^n (integer, positive?)   deviation/p^(n/2)')
fake_rows = []
for n in range(1, 11):
    s = round(A ** n + B ** n)
    Nn = p ** n + 1 - s
    fake_rows.append(dict(n=n, N=Nn, ratio=round(abs(s)/p**(n/2), 2)))
    print(f'{n:2d} {Nn:20d} {Nn>0!s:>8}  {abs(s)/p**(n/2):18.2f}')

# divisibility checks for the fake counts
fk = {r['n']: r['N'] for r in fake_rows}
div = all(fk[n] % fk[m] == 0 for n in fk for m in fk if n % m == 0)
print('fake counts satisfy N_m | N_n for m | n:', div)
real_dev = [abs(2 * (alpha ** n).real) / p ** (n / 2) for n in range(1, 11)]

# number field: psi(2^n) - 2^n
M = 26
lim = 2 ** M
s = np.ones(lim + 1, bool); s[:2] = False
for i in range(2, int(lim ** 0.5) + 1):
    if s[i]: s[i * i::i] = False
pr = np.nonzero(s)[0]
nf_rows = []
for n in range(1, M + 1):
    x = 2 ** n
    q = pr[pr <= x]
    psi = float(np.sum(np.log(q) * np.floor(np.log(x) / np.log(q) + 1e-12)))
    nf_rows.append(dict(n=n, x=x, psi_minus_x=round(psi - x, 4), ratio=round(abs(psi - x) / math.sqrt(x), 4)))
print('\nzeta, b = 2:  n  psi(2^n)-2^n   |.|/2^(n/2)')
for r in nf_rows: print(f"{r['n']:3d} {r['psi_minus_x']:14.3f} {r['ratio']:10.4f}")

out = dict(curve='y^2=x^3+x+1 over F_7', a_p=a, real=real_rows, fake_poly='T^2-7T+7', fake=fake_rows,
           fake_divisibility=div, zeta_base2=nf_rows)
json.dump(out, open(os.path.join(ROOT, 'validation', 'frobenius_turns.json'), 'w'), indent=1)

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(9.2, 4.0))
ns = np.arange(1, 11)
a1.semilogy(ns, [r['ratio'] for r in fake_rows], 'o-', color='#c0392b', ms=4, label='fake roots of $T^2-7T+7$ (off the circle)')
a1.semilogy(ns, real_dev, 's-', color='#1f4e79', ms=4, label=r'$E/\mathbb{F}_7$: $|\alpha^n+\bar\alpha^n|/7^{n/2}$')
a1.semilogy([r['n'] for r in nf_rows], [max(r['ratio'], 1e-3) for r in nf_rows], '^-', color='#555555', ms=3.5,
            label=r'$\zeta$, $b=2$: $|\psi(2^n)-2^n|/2^{n/2}$')
a1.axhline(2, color='#1f4e79', lw=0.6, ls=':'); a1.set_ylim(1e-2, 3e5)
a1.set_xlabel('number of turns $n$'); a1.set_ylabel('deviation / $b^{n/2}$')
a1.set_title('(a) turning the circle $n$ times'); a1.legend(fontsize=7.5, loc='upper left', frameon=False)
# (b) annulus picture in the alpha-plane, b fixed, radii b^theta normalised to sqrt(b)=1
b = 4.0
t = np.linspace(0, 2 * np.pi, 400)
for th, ls, lab in ((1.0, '-', r'$\theta=1$'), (0.75, '--', r'$\theta=3/4$')):
    R = b ** (th - 0.5)
    a2.plot(R * np.cos(t), R * np.sin(t), ls, color='#888888', lw=0.8)
    a2.plot(np.cos(t) / R, np.sin(t) / R, ls, color='#888888', lw=0.8)
    a2.text(R * 0.74, -R * 0.74, lab, fontsize=8, color='#555555')
a2.plot(np.cos(t), np.sin(t), color='#1f4e79', lw=1.6)
a2.text(-0.25, -1.17, r'$|\alpha|=\sqrt{b}$', color='#1f4e79', fontsize=8)
z = 1.35 * np.exp(0.9j)                         # hypothetical off-circle point, normalised
pts = [z ** k for k in range(1, 4)]
for k, w in enumerate(pts, 1):
    a2.plot(w.real, w.imag, 'o', color='#c0392b', ms=4)
    a2.annotate(f'$n={k}$', (w.real, w.imag), textcoords='offset points', xytext=(4, 3), fontsize=7.5, color='#c0392b')
th = np.linspace(0.9, 2.7, 200); rr = 1.35 ** (th / 0.9)
a2.plot(rr * np.cos(th), rr * np.sin(th), color='#c0392b', lw=0.7, ls=':')
a2.set_aspect('equal'); a2.set_xlim(-2.6, 2.6); a2.set_ylim(-2.6, 2.6); a2.axis('off')
a2.set_title(r'(b) annulus $b^{1-\theta}\leq|\alpha|\leq b^{\theta}$; off-circle point under $\alpha\mapsto\alpha^n$', fontsize=8.5)
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'paper', 'figures', 'fig5_turning.pdf'), bbox_inches='tight')
fig.savefig(os.path.join(os.environ.get('TMPDIR', '/tmp'), 'fig5_preview.png'), dpi=110, bbox_inches='tight')

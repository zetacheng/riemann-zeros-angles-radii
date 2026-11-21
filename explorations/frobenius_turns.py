#!/usr/bin/env python3
"""'Turning the circle n times' where Frobenius exists: an elliptic curve over F_p.

E: y^2 = x^3 + x + 1 over F_7.  Count points over F_{7^n} directly, compare with
N_n = q^n + 1 - alpha^n - conj(alpha)^n, and contrast with a fake 'curve' whose
Frobenius roots are off the circle but whose counts are still positive integers.
"""
import cmath, itertools, math

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
for n in range(1, 5):
    pred = p ** n + 1 - 2 * (alpha ** n).real
    print(f'{n:2d} {count(n):14d} {pred:20.6f} {abs(alpha**n)/p**(n/2):19.6f} {math.degrees(cmath.phase(alpha**n)):12.1f}')

# fake 'curve': T^2 - p T + p, roots real, off the circle
r = math.sqrt(p * p - 4 * p)
A, B = (p + r) / 2, (p - r) / 2
print(f'\nFake roots of T^2-{p}T+{p}: {A:.4f}, {B:.4f}  (|alpha| vs sqrt(p)={math.sqrt(p):.4f})')
print(' n   N_n = p^n+1-A^n-B^n (integer, positive?)   deviation/p^(n/2)')
for n in range(1, 11):
    s = round(A ** n + B ** n)
    Nn = p ** n + 1 - s
    print(f'{n:2d} {Nn:20d} {Nn>0!s:>8}  {abs(s)/p**(n/2):18.2f}')

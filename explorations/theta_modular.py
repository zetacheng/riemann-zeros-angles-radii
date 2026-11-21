#!/usr/bin/env python3
"""How the modular transformation of theta produces pointwise cancellation.

theta3(tau) = sum_{n in Z} exp(pi i n^2 tau), tau = x + i y.  For small y this is a
long oscillating sum of about N = 1/sqrt(y) effective terms.  We evaluate it
(a) directly, and
(b) by reducing tau to the fundamental domain with tau -> tau+1, tau -> -1/tau,
    tracking theta2, theta3, theta4 and the multipliers sqrt(-i tau).
The product of multipliers gives the size of the sum explicitly.
"""
import cmath, math, sys
import mpmath as mp

mp.mp.dps = 30
E8 = cmath.exp(1j * math.pi / 4)

def series(kind, tau):
    q = mp.exp(1j * mp.pi * tau)
    s = mp.mpc(0)
    if kind == 3:
        n = 1
        s = mp.mpc(1)
        while True:
            t = 2 * q ** (n * n)
            s += t
            if abs(t) < mp.mpf(10) ** (-25): break
            n += 1
    elif kind == 4:
        n = 1
        s = mp.mpc(1)
        while True:
            t = 2 * (-1) ** n * q ** (n * n)
            s += t
            if abs(t) < mp.mpf(10) ** (-25): break
            n += 1
    else:  # theta2 = sum exp(pi i (n+1/2)^2 tau)
        n = 0
        while True:
            t = 2 * mp.exp(1j * mp.pi * (n + mp.mpf(1) / 2) ** 2 * tau)
            s += t
            if abs(t) < mp.mpf(10) ** (-25): break
            n += 1
    return s

def reduce_eval(tau, kind=3):
    """theta_kind(tau) = factor * theta_kind'(tau_final), tau_final in fundamental domain."""
    factor, steps, log = mp.mpc(1), 0, []
    while True:
        k = int(mp.nint(tau.real))
        if k != 0:                     # tau = tau' + k
            for _ in range(abs(k)):
                if k > 0:              # theta(tau'+1)
                    if kind == 3: kind = 4
                    elif kind == 4: kind = 3
                    else: factor *= E8
                else:                  # theta(tau'-1)
                    if kind == 3: kind = 4
                    elif kind == 4: kind = 3
                    else: factor *= E8.conjugate()
            tau = tau - k
        if abs(tau) >= 1:
            break
        tp = -1 / tau                  # tau = -1/tp
        m = mp.sqrt(-1j * tp)
        factor *= m
        kind = {3: 3, 4: 2, 2: 4}[kind]
        tau = tp
        steps += 1
        log.append(float(abs(m)))
    return factor * series(kind, tau), steps, log, kind, tau

if __name__ == '__main__':
    y = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf('1e-6')
    N = 1 / mp.sqrt(y)
    golden = (mp.sqrt(5) - 1) / 2
    cases = [('0', mp.mpf(0)), ('1/2', mp.mpf(1) / 2), ('1/3', mp.mpf(1) / 3), ('1/7', mp.mpf(1) / 7),
             ('1/101', mp.mpf(1) / 101), ('(sqrt5-1)/2', golden), ('sqrt2-1', mp.sqrt(2) - 1), ('pi-3', mp.pi - 3)]
    print(f'y = {mp.nstr(y,3)}, effective length N = 1/sqrt(y) = {mp.nstr(N,6)}, sqrt(N) = {mp.nstr(mp.sqrt(N),6)}')
    print(f'{"x":>12} {"|theta| direct":>16} {"|theta| reduced":>16} {"S-steps":>8} {"|theta|/sqrt(N)":>16}')
    for name, x in cases:
        tau = mp.mpc(x, y)
        d = series(3, tau)
        r, steps, log, kind, tf = reduce_eval(tau)
        print(f'{name:>12} {mp.nstr(abs(d),10):>16} {mp.nstr(abs(r),10):>16} {steps:>8} {mp.nstr(abs(d)/mp.sqrt(N),6):>16}')

#!/usr/bin/env python3
"""The lowest zero of L(s, (./q)) for q = 163 and its neighbours (log entry 54).

For a real primitive odd character, Lambda(s) = (q/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi)
satisfies Lambda(s) = Lambda(1 - s), so Lambda(1/2 + it) is real and its sign changes are zeros
on the critical line.  We locate the first zero for primes q = 3 mod 4 near 163.
Writes q163_zeros.json.
"""
import json, os
import mpmath as mp
mp.mp.dps = 20

def first_zero(q, tmax=4.0, step=0.04):
    chi = [0] + [1 if pow(a, (q - 1) // 2, q) == 1 else -1 for a in range(1, q)]
    def Lam(t):
        s = mp.mpc(0.5, t)
        return mp.re((q / mp.pi) ** ((s + 1) / 2) * mp.gamma((s + 1) / 2) * mp.dirichlet(s, chi))
    prev_t, prev = 0.0, Lam(0.0)
    t = step
    while t <= tmax:
        v = Lam(t)
        if v * prev < 0:
            z = mp.findroot(Lam, (prev_t, t), solver='bisect' if False else 'anderson')
            return float(z), float(Lam(0.0))
        prev_t, prev = t, v; t += step
    return None, float(Lam(0.0))

rows = []
for q in (131, 139, 151, 163, 167, 179, 191, 199, 211, 223):
    z, lam0 = first_zero(q)
    rows.append(dict(q=q, first_zero=z, Lambda_half=lam0))
    print(q, 'first zero on the line at t =', None if z is None else round(z, 5), '  Lambda(1/2) =', round(lam0, 4), flush=True)
json.dump(rows, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'q163_zeros.json'), 'w'), indent=1)

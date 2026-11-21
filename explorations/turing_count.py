#!/usr/bin/env python3
"""Angles constrain the radius by counting (Turing-type check), log entry 62.

For a height T:
 (1) total count N(T) of zeros with 0 < gamma <= T in the whole strip, by the argument principle:
     N(T) = theta(T)/pi + 1 + S(T),  S(T) = arg zeta(1/2 + iT)/pi, with arg followed continuously
     from 2 + iT (where Re zeta > 0) to 1/2 + iT;
 (2) the zeros on the critical line, counted as sign changes of the real function Z(t);
 (3) if the two agree, no zero with gamma <= T lies off the line (off-line zeros come in pairs
     and produce no sign changes of Z).
Writes turing_count.json.
"""
import json, math, os, sys, time
import mpmath as mp
mp.mp.dps = 20

def N_argument(T):
    T = mp.mpf(T)
    z = mp.zeta(mp.mpc(2, T)); arg = mp.arg(z)          # principal value, Re zeta(2+iT) > 0
    steps = 3000; prev = z
    for k in range(1, steps + 1):
        sig = 2 - mp.mpf(1.5) * k / steps
        z = mp.zeta(mp.mpc(sig, T))
        d = mp.arg(z / prev)                              # small increment, |d| < pi
        arg += d; prev = z
    return mp.siegeltheta(T) / mp.pi + 1 + arg / mp.pi, arg / mp.pi

def sign_changes(T, h=0.02):
    count, t, prev = 0, mp.mpf('0.5'), mp.siegelz(0.5)
    suspicious = []
    vals = []
    while t < T:
        t2 = min(t + h, mp.mpf(T)); v = mp.siegelz(t2)
        if v * prev < 0: count += 1
        vals.append((float(t2), float(v)))
        t, prev = t2, v
    # look for close pairs missed by the grid: a local extremum of |Z| that does not reach zero
    for i in range(1, len(vals) - 1):
        a, b, c = vals[i - 1][1], vals[i][1], vals[i + 1][1]
        if abs(b) < abs(a) and abs(b) < abs(c) and a * b > 0 and b * c > 0 and abs(b) < 0.05:
            suspicious.append(vals[i][0])
    return count, suspicious

rows = []
for T in [float(x) for x in (sys.argv[1:] or ['100', '250', '500', '1000'])]:
    t0 = time.time()
    N, S = N_argument(T)
    sc, sus = sign_changes(T)
    rows.append(dict(T=T, N_argument=float(N), S_T=float(S), N_rounded=int(mp.nint(N)), sign_changes_on_line=sc,
                     agree=(int(mp.nint(N)) == sc), suspicious_minima=sus, seconds=round(time.time() - t0, 1)))
    print(json.dumps(rows[-1]), flush=True)
json.dump(rows, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'turing_count.json'), 'w'), indent=1)

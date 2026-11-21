#!/usr/bin/env python3
"""Does q = 163 show a faint impurity-like effect?  (author's question, log entry 54)

chi = (./163), the character of Q(sqrt(-163)), class number one, L(1, chi) = pi/sqrt(163).
(1) Which small primes are inert (chi(p) = -1)?
(2) The prime sum psi(x, chi) = sum_{n <= x} Lambda(n) chi(n).  A real zero beta near 1
    (a Siegel zero) would add a term -x^beta / beta, so psi(x, chi)/x would stay near -1/beta.
    Without one, psi(x, chi) is of size sqrt(x) times logarithms.
(3) L(sigma, chi) on the real segment 1/2 <= sigma <= 1: a real zero would be a sign change.
(4) Low zeros on the critical line: minima of |L(1/2 + it, chi)|.
Writes q163.json and q163.png.
"""
import json, math, os
import numpy as np
import mpmath as mp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

q = 163
chi = [0] + [1 if pow(a, (q - 1) // 2, q) == 1 else -1 for a in range(1, q)]
out = {}
small = [p for p in range(2, 200) if all(p % d for d in range(2, int(p ** 0.5) + 1)) and p != q]
out['inert_primes_below_200'] = [p for p in small if chi[p % q] == -1]
out['split_primes_below_200'] = [p for p in small if chi[p % q] == 1]
print('first split prime:', out['split_primes_below_200'][0], ' inert primes below 41:', [p for p in small if p < 41])

X = 3 * 10 ** 6
sv = np.ones(X + 1, bool); sv[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
lam = np.zeros(X + 1)
for p in np.nonzero(sv)[0]:
    pk = p; lp = math.log(p)
    while pk <= X: lam[pk] = lp; pk *= p
ch = np.resize(np.array(chi, dtype=np.int8), X + 1)
psi_chi = np.cumsum(lam * ch)
xs = np.unique(np.round(np.logspace(0.3, math.log10(X), 400)).astype(int))
ratio = psi_chi[xs] / xs
norm = psi_chi[xs] / np.sqrt(xs)
out['psi_chi'] = [dict(x=int(x), psi=float(psi_chi[x]), over_x=float(psi_chi[x] / x), over_sqrtx=float(psi_chi[x] / math.sqrt(x)))
                  for x in (10, 40, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 3 * 10 ** 6)]
for r in out['psi_chi']: print('x=%-9d psi=%12.1f  psi/x=%8.4f  psi/sqrt(x)=%8.3f' % (r['x'], r['psi'], r['over_x'], r['over_sqrtx']))

mp.mp.dps = 20
def L(s): return mp.dirichlet(s, chi)
out['L1'] = float(-sum(chi[a] * mp.digamma(mp.mpf(a) / q) for a in range(1, q)) / q);  # mp.dirichlet at s = 1 hits the Hurwitz pole
out["pi_over_sqrt163"] = float(mp.pi / mp.sqrt(q))
sig = [0.5 + 0.05 * i for i in range(10)] + [0.99]
out['L_real_segment'] = [dict(sigma=s_, L=float(L(s_))) for s_ in sig]
print('L(sigma) on [1/2,1]:', [round(r['L'], 4) for r in out['L_real_segment']])
ts = [0.05 * i for i in range(1, 501)]
absL = [float(abs(L(mp.mpc(0.5, t)))) for t in ts]
mins = []
for i in range(1, len(ts) - 1):
    if absL[i] < absL[i - 1] and absL[i] < absL[i + 1] and absL[i] < 0.2:
        mins.append(dict(t=ts[i], absL=absL[i]))
out['critical_line_minima'] = mins
print('minima of |L(1/2+it)| (t<=25):', [(round(m['t'], 2), round(m['absL'], 4)) for m in mins])
ROOT = os.path.dirname(os.path.abspath(__file__))
json.dump(out, open(os.path.join(ROOT, 'q163.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(10, 3.8))
a1.semilogx(xs, ratio, color='#1f4e79', lw=0.9, label=r'$\psi(x,\chi)/x$, $q=163$')
for beta in (0.95, 0.99):
    a1.semilogx(xs, -xs ** (beta - 1) / beta, '--', lw=0.8, label=fr'Siegel model $-x^{{\beta-1}}/\beta$, $\beta={beta}$')
a1.axhline(0, color='#888888', lw=0.6); a1.axvline(41, color='#c0392b', lw=0.6, ls=':')
a1.set_xlabel('$x$'); a1.set_title('(a) the prime sum against a Siegel-zero model'); a1.legend(frameon=False, fontsize=7.5)
a2.semilogx(xs, norm, color='#1f4e79', lw=0.9)
a2.axhline(0, color='#888888', lw=0.6); a2.axvline(41, color='#c0392b', lw=0.6, ls=':')
a2.set_xlabel('$x$'); a2.set_ylabel(r'$\psi(x,\chi)/\sqrt{x}$'); a2.set_title(r'(b) normalised by $\sqrt{x}$')
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'q163.png'), dpi=130, bbox_inches='tight')

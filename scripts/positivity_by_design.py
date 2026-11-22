#!/usr/bin/env python3
"""Step 1 of the human path: why a positive-weight family makes a one-sided bound decisive.

Model (explicit formula, main terms only): for a family of L-functions with zero sets Z_chi,
    x - sum_chi c_chi psi(x, chi)  ~  sum_chi c_chi sum_{rho in Z_chi} x^rho / rho      (c_chi0 = 1)
With all c_chi = 1 (the family of all characters mod q, i.e. primes = 1 mod q) every zero enters
with the same coefficient.  We use synthetic zero sets (ordinates of zeta's first 200 zeros, shifted
per member, all on the line) and plant impurities:
 (a) positive family, one off-line pair 1/2 + delta +- i gamma* in one member;
 (b) signed family c = (+1, -1, ...): the same impurity in two members with opposite signs;
 (c) a real zero beta (Siegel-type) in one member, seen through the statistic
     E_hat = x - sum psi  (each real zero adds + x^beta/beta)  and through -E_hat.
Statistics are normalised by sqrt(x) and compared with a one-sided bound C x^{eps}.
Writes validation/positivity_by_design.json and paper/figures/fig13_positivity.pdf.
"""
import json, math, os
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
g0 = np.array(json.load(open(os.path.join(ROOT, 'data', 'zeros_1200.json'))))[:200]
rng = np.random.default_rng(0)
members = [g0 + rng.uniform(-3, 3)] + [g0 * rng.uniform(0.9, 1.1) + rng.uniform(-3, 3) for _ in range(3)]
u = np.linspace(1, 60, 6000); x = np.exp(u)

def S(gammas, beta=0.5, weight=1.0):
    """sum over the pairs beta +- i gamma of x^rho/rho, normalised by sqrt(x)."""
    tot = np.zeros_like(u)
    for g in gammas:
        rho = complex(beta, g)
        tot += weight * 2 * (np.exp((rho - 0.5) * u) / rho).real
    return tot

base = [S(m) for m in members]
delta, gstar = 0.15, 30.0
imp = S([gstar], beta=0.5 + delta)
pos_clean = sum(base)
pos_imp = pos_clean + imp                                   # (a)
signed = base[0] - base[1] + base[2] - base[3] + imp - imp  # (b) impurity in members 0 and 1, opposite signs
beta_real = 0.8
real_term = np.exp((beta_real - 0.5) * u) / beta_real       # (c) + x^beta / beta, normalised
Ehat = pos_clean + real_term

eps, C = 0.02, 3 * np.max(np.abs(pos_clean))
bound = C * np.exp(eps * u)
def first_violation(stat):
    v = np.nonzero(stat > bound)[0]
    return float(u[v[0]]) if len(v) else None
# localised windows [Y, Y^{1.2}] in log scale: does every late window contain a violation?
def windows_with_violation(stat, lo=20):
    res = []
    a = lo
    while a * 1.2 <= u[-1]:
        m = (u >= a) & (u <= a * 1.2)
        res.append(bool(np.any(stat[m] > bound[m]))); a *= 1.2
    return res
out = dict(delta=delta, gamma_star=gstar, beta_real=beta_real, eps=eps, C=float(C),
           first_violation_log_x={'positive_clean': first_violation(pos_clean), 'positive_impurity': first_violation(pos_imp),
                                  'signed_two_impurities': first_violation(signed),
                                  'real_zero_Ehat': first_violation(Ehat), 'real_zero_minus_Ehat': first_violation(-Ehat)},
           late_windows_violated_positive_impurity=windows_with_violation(pos_imp),
           max_abs_signed=float(np.max(np.abs(signed))), max_abs_clean=float(np.max(np.abs(pos_clean))))
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'validation', 'positivity_by_design.json'), 'w'), indent=1)

plt.rcParams.update({'font.size': 9})
fig, ax = plt.subplots(1, 3, figsize=(13, 3.6))
ax[0].plot(u, pos_clean, color='#888888', lw=0.6, label='no impurity')
ax[0].plot(u, pos_imp, color='#c0392b', lw=0.7, label=f'one off-line pair ($\\delta={delta}$)')
ax[0].plot(u, bound, '--', color='#1f4e79', lw=1, label='one-sided bound $Cx^{\\varepsilon}$')
ax[0].set_title('(a) positive family: the impurity cannot hide'); ax[0].set_xlabel('$\\log x$'); ax[0].set_ylabel('statistic $/\\sqrt{x}$')
ax[0].legend(frameon=False, fontsize=7.5); ax[0].set_ylim(-40, 60)
ax[1].plot(u, signed, color='#2e7d32', lw=0.7, label='two impurities, weights $+1,-1$')
ax[1].plot(u, bound, '--', color='#1f4e79', lw=1)
ax[1].set_title('(b) signed family: impurities cancel'); ax[1].set_xlabel('$\\log x$'); ax[1].legend(frameon=False, fontsize=7.5)
ax[1].set_ylim(-40, 60)
ax[2].plot(u, Ehat, color='#c0392b', lw=0.7, label='$\\hat E=x-\\sum\\psi$ (real zero adds $+x^\\beta/\\beta$)')
ax[2].plot(u, -Ehat, color='#888888', lw=0.7, label='$-\\hat E$')
ax[2].plot(u, bound, '--', color='#1f4e79', lw=1)
ax[2].set_title(f'(c) a real zero $\\beta={beta_real}$: orientation matters'); ax[2].set_xlabel('$\\log x$')
ax[2].legend(frameon=False, fontsize=7.5); ax[2].set_ylim(-60, 80)
fig.tight_layout(); fig.savefig(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'paper', 'figures', 'fig13_positivity.pdf'), bbox_inches='tight')

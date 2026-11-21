#!/usr/bin/env python3
"""Figure 6: (a) Stepanov's bound against the multiplicity M (p = 401);
(b) the quasi-RH length-optimisation recursion from three starting bounds."""
import json, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
A = json.load(open(os.path.join(ROOT, 'validation', 'stepanov_results.json')))
B = json.load(open(os.path.join(ROOT, 'validation', 'quasi_rh_recursion.json')))
plt.rcParams.update({'font.size': 9})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(9.2, 3.6))
rows = A['vs_M_p401']; S = rows[0]['S']; p = rows[0]['p']
a1.plot([r['M'] for r in rows], [r['bound'] for r in rows], 'o-', color='#1f4e79', ms=4, label=r'bound $\deg R/M$')
a1.axhline(p, color='#888888', lw=0.8, ls='--'); a1.text(10.2, p + 8, f'trivial bound $|S|\\leq p={p}$', fontsize=8, color='#555555')
a1.axhline(S, color='#c0392b', lw=0.9); a1.text(10.2, S - 26, f'true $|S|={S}$', fontsize=8, color='#c0392b')
a1.set_xlabel('multiplicity $M$'); a1.set_ylabel('upper bound for $|S|$'); a1.set_ylim(150, 640)
a1.set_title(f'(a) Stepanov, $y^2=x^3+x+1$ over $\\mathbb{{F}}_{{{p}}}$'); a1.legend(frameon=False, fontsize=8, loc='upper right')
styles = {'sigma0=1 (trivial)': ('#1f4e79', 'o', r'start $\sigma_0=1$'), 'sigma0=0.95': ('#555555', 's', r'start $\sigma_0=0.95$'),
          'sigma0=7/8': ('#c0392b', '^', r'start $\sigma_0=7/8$')}
for k, (col, mk, lab) in styles.items():
    seq = [float(x) for x in B['iterations'][k]][:5]
    a2.plot(range(len(seq)), seq, marker=mk, color=col, ms=4, label=lab)
a2.axhline(float(B['B_new']), color='#888888', lw=0.8, ls='--')
a2.text(1.6, float(B['B_new']) + 0.018, r'fixed point $0.874957\ldots$', fontsize=8, color='#555555')
a2.axhline(0.5, color='#1f4e79', lw=0.6, ls=':'); a2.text(0.1, 0.51, r'$\sigma=1/2$ (RH)', fontsize=8, color='#1f4e79')
a2.set_xlabel('iteration'); a2.set_ylabel(r'zero-free abscissa $\sigma$'); a2.set_xticks(range(5)); a2.set_ylim(0.45, 1.02)
a2.set_title('(b) quasi-RH recursion (Liu 2026)'); a2.legend(frameon=False, fontsize=8, loc='center right')
fig.tight_layout(); fig.savefig(os.path.join(ROOT, 'paper', 'figures', 'fig6_routes.pdf'), bbox_inches='tight')
fig.savefig('/tmp/claude-0/-home-claude/cf93799a-fb7f-57c7-892c-558ec1b644f9/scratchpad/fig6.png', dpi=110, bbox_inches='tight')

#!/usr/bin/env python3
"""Sweep Stepanov's method: best bound for each multiplicity M, and scaling in p."""
import json, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stepanov import run

m = 3
def best_params(p, M):
    """Smallest predicted deg R / M with more unknowns (2JK) than equations."""
    c = (p - 1) // 2; best = None
    for J in range(M // 2 + 1, 4 * M + 8):
        rhs = M * J + (m - 1) * M * (M - 1) // 2      # need K (2J - M) > rhs
        K = rhs // (2 * J - M) + 1
        if K > c - m: continue
        deg = m * M + (K - 1) + m * c + p * (J - 1)
        if best is None or deg / M < best[0]: best = (deg / M, J, K)
    return best

out = {}
p = 401
rows = []
for M in (1, 2, 4, 6, 8, 10, 12, 14, 16):
    b = best_params(p, M)
    if b is None: continue
    r = run(p, M, b[1], b[2]); rows.append(r)
    print(f"p={p} M={M:2d} J={b[1]:2d} K={b[2]:3d} eq={r.get('equations')} unk={r.get('unknowns')} "
          f"degR={r.get('degR')} bound={r.get('bound', float('nan')):.1f} |S|={r.get('S')} ok={r.get('vanishes_to_order_M_on_S')}", flush=True)
out['vs_M_p401'] = rows
scal = []
for p in (101, 211, 307, 401):
    cand = []
    for M in range(2, 17):
        b = best_params(p, M)
        if b: cand.append((b[0], M, b[1], b[2]))
    _, M, J, K = min(cand)
    r = run(p, M, J, K); scal.append(r)
    ex = r['bound'] - p / 2
    print(f"p={p} best M={M} J={J} K={K}: bound={r['bound']:.1f}  |S|={r['S']}  bound-p/2={ex:.1f}  /sqrt(p)={ex/math.sqrt(p):.2f}  ok={r['vanishes_to_order_M_on_S']}", flush=True)
out['scaling'] = scal
# larger p: parameter count only (kernel guaranteed since unknowns > equations; R != 0 verified above)
pred = []
for p in (1009, 4001, 10007, 40009, 100003):
    b = min((best_params(p, M) + (M,)) for M in range(2, int(3 * math.sqrt(p))) if best_params(p, M))
    ex = b[0] - p / 2
    pred.append(dict(p=p, M=b[3], J=b[1], K=b[2], predicted_bound=round(b[0], 1), excess=round(ex, 1), excess_over_sqrtp=round(ex / math.sqrt(p), 2)))
    print('predicted', pred[-1], flush=True)
out['predicted_larger_p'] = pred
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'stepanov_results.json'), 'w'), indent=1)

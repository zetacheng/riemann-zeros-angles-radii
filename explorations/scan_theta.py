import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from theta_modular import series, reduce_eval
mp.mp.dps = 30
golden = (mp.sqrt(5) - 1) / 2
cases = [('1/2', mp.mpf(1)/2), ('1/4', mp.mpf(1)/4), ('1/10', mp.mpf(1)/10), ('1/100', mp.mpf(1)/100),
         ('(sqrt5-1)/2', golden), ('sqrt2-1', mp.sqrt(2) - 1)]
ys = [mp.mpf('1e-4'), mp.mpf('1e-6'), mp.mpf('1e-8')]
print('%12s' % 'x' + ''.join('%26s' % ('y=%s (N=%d)' % (mp.nstr(y, 1), int(1/mp.sqrt(y)))) for y in ys))
for name, x in cases:
    row = '%12s' % name
    for y in ys:
        r = reduce_eval(mp.mpc(x, y))[0]
        N = 1 / mp.sqrt(y)
        row += '%26s' % ('%s  (/sqrtN=%s)' % (mp.nstr(abs(r), 5), mp.nstr(abs(r)/mp.sqrt(N), 3)))
    print(row)
y = mp.mpf('1e-8'); tau = mp.mpc(golden, y)
d = series(3, tau); r = reduce_eval(tau)
print('direct vs reduced, golden, y=1e-8:', mp.nstr(abs(d), 12), mp.nstr(abs(r[0]), 12), '| S-steps', r[1], '| multipliers', [round(v, 3) for v in r[2]])

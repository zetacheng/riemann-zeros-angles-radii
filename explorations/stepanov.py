#!/usr/bin/env python3
"""Stepanov's method, carried out explicitly for y^2 = f(x) over F_p.

S = {x in F_p : f(x)^c = 1}, c = (p-1)/2  (the x with f(x) a nonzero square).
Auxiliary polynomial
    R(X) = f(X)^M * sum_{j<J} ( r_j(X) + s_j(X) g(X) ) X^{p j},   g = f^c,  deg r_j, s_j < K.
Two uses of Frobenius x -> x^p:
  (i)  on S, X^{pj} = X^j and g = 1          (points of S are Frobenius fixed points),
  (ii) d/dX X^{pj} = 0 in characteristic p   (derivatives pass through the X^{pj}).
Hence D^k R(x) = f(x)^{M-k} W_k(x) for x in S, where W_k is a polynomial whose
coefficients are linear in the unknowns and whose degree does NOT depend on |S|.
Imposing W_k == 0 (k < M) is a linear system with fewer equations than unknowns;
any nonzero solution gives R != 0 vanishing to order M at every point of S, so
    |S| <= deg R / M.
Usage: python3 stepanov.py p M J K
"""
import json, os, sys, time
import numpy as np

def pmul(a, b, p):
    return np.convolve(a, b) % p if len(a) and len(b) else np.zeros(0, np.int64)

def padd(a, b, p):
    n = max(len(a), len(b)); r = np.zeros(n, np.int64)
    r[:len(a)] += a; r[:len(b)] += b
    return r % p

def pder(a, p):
    return (a[1:] * np.arange(1, len(a))) % p if len(a) > 1 else np.zeros(0, np.int64)

def ppow(a, e, p):
    r = np.array([1], np.int64); b = a.copy()
    while e:
        if e & 1: r = pmul(r, b, p)
        b = pmul(b, b, p); e >>= 1
    return r

def peval(a, x, p):
    v = 0
    for c in a[::-1]: v = (v * x + int(c)) % p
    return v

def nullvec(A, p):
    """One nonzero vector in the kernel of A over F_p (A: rows x cols, cols > rank)."""
    A = A.copy() % p; rows, cols = A.shape; piv = []; r = 0
    for c in range(cols):
        if r == rows: break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = (A[r] * pow(int(A[r, c]), -1, p)) % p
        col = A[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr): A[nzr] = (A[nzr] - np.outer(col[nzr], A[r])) % p
        piv.append(c); r += 1
    free = [c for c in range(cols) if c not in set(piv)]
    if not free: return None, len(piv)
    v = np.zeros(cols, np.int64); f = free[0]; v[f] = 1
    for i, c in enumerate(piv): v[c] = (-A[i, f]) % p
    return v, len(piv)

def run(p, M, J, K, fcoef=(1, 1, 0, 1)):
    f = np.array(fcoef, np.int64) % p                  # low -> high: 1 + x + x^3
    m = len(f) - 1; c = (p - 1) // 2; fp = pder(f, p)
    # derivative chains: D^k[f^M h] = f^{M-k} U_k,  D^k[f^M h g] = g f^{M-k} T_k   (h = X^i)
    def chain(i, with_g):
        h = np.zeros(i + 1, np.int64); h[i] = 1; a = M; out = [h]
        for _ in range(M - 1):
            coef = (a + (c if with_g else 0)) % p
            h = padd(pmul(np.array([coef]), pmul(fp, h, p), p), pmul(f, pder(h, p), p), p)
            a -= 1; out.append(h)
        return out
    chains = {(t, i): chain(i, t == 1) for t in (0, 1) for i in range(K)}
    deg_k = [J - 1 + K - 1 + k * (m - 1) for k in range(M)]
    offs = np.cumsum([0] + [d + 1 for d in deg_k]); nrows = int(offs[-1]); ncols = 2 * J * K
    A = np.zeros((nrows, ncols), np.int64)
    col = 0; index = []
    for j in range(J):
        for t in (0, 1):
            for i in range(K):
                for k in range(M):
                    poly = chains[(t, i)][k]                 # W_k gets X^j * poly (g -> 1 on S)
                    A[offs[k] + j: offs[k] + j + len(poly), col] = poly
                index.append((j, t, i)); col += 1
    t0 = time.time(); v, rank = nullvec(A, p); t_solve = time.time() - t0
    if v is None: return dict(p=p, M=M, J=J, K=K, status='no kernel', equations=nrows, unknowns=ncols)
    # build R explicitly
    g = ppow(f, c, p); inner = np.zeros(1, np.int64)
    for j in range(J):
        rj = np.zeros(K, np.int64); sj = np.zeros(K, np.int64)
        for (jj, t, i), val in zip(index, v):
            if jj == j: (rj if t == 0 else sj)[i] = val
        term = padd(rj, pmul(sj, g, p), p)
        shift = np.zeros(p * j + len(term), np.int64); shift[p * j:] = term
        inner = padd(inner, shift, p)
    R = pmul(ppow(f, M, p), inner, p)
    nzi = np.nonzero(R)[0]
    if len(nzi) == 0: return dict(p=p, M=M, J=J, K=K, status='R == 0')
    R = R[: nzi[-1] + 1]; degR = len(R) - 1
    S = [x for x in range(p) if peval(f, x, p) != 0 and pow(peval(f, x, p), c, p) == 1]
    # check vanishing order >= M at every point of S
    ders = [R]
    for _ in range(M - 1): ders.append(pder(ders[-1], p))
    ok = all(peval(d, x, p) == 0 for x in S for d in ders)
    roots_f = sum(1 for x in range(p) if peval(f, x, p) == 0)
    return dict(p=p, M=M, J=J, K=K, equations=nrows, unknowns=ncols, rank=rank, solve_s=round(t_solve, 2),
                degR=degR, vanishes_to_order_M_on_S=ok, S=len(S), bound=degR / M,
                trivial_bound_deg_g_minus_1=m * c, half_p=p / 2,
                affine_points=2 * len(S) + roots_f, hasse_interval=[p + 1 - 2 * p ** 0.5, p + 1 + 2 * p ** 0.5])

if __name__ == '__main__':
    p, M, J, K = (int(a) for a in sys.argv[1:5])
    print(json.dumps(run(p, M, J, K), indent=1))

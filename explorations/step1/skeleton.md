# Step 1 of a human path: the skeleton

*Written by Claude (Anthropic, Claude Opus 5.5) at the request of Zeta Hoi-Ho Cheng, 21 November 2026. The plan of walking the route out in a human way is the author's (CONTRIBUTIONS_LOG entry 78).*

According to the architecture guide (paper §19), the verified proof avoids the obstacle at which Part IV of the paper stopped. Part IV needed off-diagonal estimates to pass from a family to one member; the proof instead uses a family whose zeros all enter **with one sign**, together with a **one-sided** bound. This note states and proves the simplest version of that mechanism. The statement is classical in spirit (Landau's theorem on Dirichlet series with non-negative coefficients). It is **not** the localised statistic of the verified proof, which uses windows [Y, Y^{1+δ}] and unequal weights over a Galois group; we do not prove that refinement here.

## Setting

Let q be a prime, or q = 1 (then the family is ζ alone). For s with Re s > 1 put

$$D_q(s)=\sum_{\chi \bmod q}\Bigl(-\frac{L'}{L}(s,\chi)\Bigr)=\sum_{n\ge1}\frac{a_n}{n^s},\qquad a_n=\varphi(q)\,\Lambda(n)\,\mathbf 1[n\equiv1 \bmod q].$$

The coefficients are **non-negative**, because $\sum_{\chi}\chi(n)=\varphi(q)$ if $n\equiv1 \pmod q$ and $0$ otherwise. Averaging over the whole family with equal weights keeps exactly the prime powers on which every character takes the value 1, the identity. This is the precise form of the author's remark that "1, the identity" synchronises the primes (log entry 70).

Put $E_q(x)=x-\sum_{n\le x}a_n=x-\varphi(q)\,\psi(x;q,1)$.

## Theorem (one-sided criterion)

Let $\tfrac12\le\theta<1$. Suppose there are constants $C$ and $x_0$ such that

$$E_q(x)\le C\,x^{\theta}\qquad(x\ge x_0).\tag{$\star_\theta$}$$

Then no $L(s,\chi)$ with $\chi$ a character mod $q$ (for $q=1$: no $\zeta(s)$) has a zero with $\mathrm{Re}\,s>\theta$.

Conversely, if every $L(s,\chi)$ mod $q$ satisfies the Riemann Hypothesis, then $|E_q(x)|\le C_q\sqrt{x}\log^2x$ by the explicit formula, so ($\star_\theta$) holds for every $\theta>\tfrac12$. Hence

> **GRH for the characters mod q ⇔ ($\star_\theta$) for every θ > 1/2,**

where ($\star_\theta$) is a **one-sided lower bound** for the primes ≡ 1 (mod q).

## Proof

*Mellin transforms.* For Re s > 1, partial summation gives $\int_1^\infty\bigl(\sum_{n\le x}a_n\bigr)x^{-s-1}dx=D_q(s)/s$, and $\int_1^\infty x\cdot x^{-s-1}dx=1/(s-1)$, $\int_1^\infty Cx^\theta x^{-s-1}dx=C/(s-\theta)$. With $g(x)=Cx^\theta-E_q(x)$,

$$F(s):=\int_1^\infty g(x)\,x^{-s-1}\,dx=\frac{C}{s-\theta}-\frac1{s-1}+\frac{D_q(s)}{s}\qquad(\mathrm{Re}\,s>1).$$

*The right-hand side.* $D_q(s)/s-1/(s-1)$ extends meromorphically to $\mathbb C$. Its only possible poles are at the zeros of the $L(s,\chi)$. At $s=1$ the pole cancels: $-L'/L(s,\chi_0)=-\zeta'/\zeta(s)-\frac{q^{-s}\log q}{1-q^{-s}}$ has residue 1 there, and the other $L(s,\chi)$ are holomorphic and non-zero at $s=1$. At a zero $\rho$, $D_q$ has a simple pole with residue $-m(\rho)$, where $m(\rho)\ge1$ is the **total** multiplicity of $\rho$ over all characters mod q. These residues all have the same sign, so poles from different characters can never cancel. (This is "positivity by design".)

*Landau's theorem.* Split $F=F_0+F_1$ with $F_0=\int_1^{x_0}$, which is entire, and $F_1=\int_{x_0}^\infty$, whose integrand is $\ge0$ by ($\star_\theta$). For a Laplace–Mellin transform of a non-negative function, if $\sigma_c$ is the abscissa of convergence, the real point $s=\sigma_c$ is a singularity (Landau; see Widder, *The Laplace Transform*, Ch. II).

*Contradiction.* Suppose $\sigma_c>\theta$. Then $\sigma_c\le1$, and $\sigma_c=1$ is impossible because the right-hand side is holomorphic at 1. So $\sigma_c=\beta_0\in(\theta,1)$ is a real singularity of $F_1=F-F_0$, hence a pole of $D_q(s)/s$: a **real zero** $\beta_0$ of some $L(s,\chi)$. Near it, $D_q(s)/s\sim-m(\beta_0)/(\beta_0(s-\beta_0))$, so $F_1(\sigma)\to-\infty$ as $\sigma\downarrow\beta_0$. But $F_1(\sigma)\ge0$ for real $\sigma>\sigma_c$. This is a contradiction, so $\sigma_c\le\theta$.

*Conclusion.* $F_1$, and therefore $D_q(s)/s$, is holomorphic in $\mathrm{Re}\,s>\theta$. So no $L(s,\chi)$ mod q vanishes there. ∎

## Two remarks the proof makes visible

1. **Orientation matters (Siegel zeros).** If the hypothesis were the opposite one-sided bound $\varphi(q)\psi(x;q,1)-x\le Cx^\theta$, an upper bound for the primes, then the sign at a real zero would be $+\infty$ and there would be no contradiction. Landau's argument would still exclude complex zeros to the right of the largest real zero, but it could not exclude a real (Siegel-type) zero. The lower bound is the version that sees real zeros, because a real zero pushes $E_q$ up by $+x^\beta/\beta$. The architecture guide notes that in the verified proof real zeros near 1 likewise "have positive residue".
2. **No off-diagonal estimate is needed.** The family is used as a whole: a zero of *any* member makes $D_q$ singular, and the one-sided bound excludes all of them at once. This replaces the step at which Part IV stopped (family to one member via two-sided moments and an amplifier).

## Demonstration (`scripts/positivity_by_design.py`, Figure 13 of the paper)

Synthetic zero sets for four members, all on the line, with impurities planted. Main terms of the explicit formula only, normalised by √x, compared with a one-sided bound Cx^ε (ε = 0.02):

| scenario | first violation of the one-sided bound |
|---|---|
| positive family, no impurity | none (log x ≤ 60) |
| positive family, one off-line pair (δ = 0.15, γ = 30) | log x ≈ 31.7, and in every later window [Y, Y^1.2] |
| signed family (+1, −1), the same impurity in two members | none: the impurities cancel exactly |
| real zero β = 0.8, statistic E = x − Σψ | log x ≈ 4.0 |
| real zero β = 0.8, opposite orientation −E | none |

## Real data (`scripts/one_sided_check.py`)

For x ≤ 5·10⁶ the statistic $E_q(x)/\sqrt x$ stays between about −4.4 and +5.2 for q = 1, 3, 5, 7, 11, and $E_q(x)/(\sqrt x\log^2x)\le0.093$. This is consistent with ($\star_\theta$) for every θ > 1/2, but it is finite data and proves nothing.

## Where this leaves the human path

The skeleton reduces GRH mod q to the one-sided bound ($\star_\theta$). Everything difficult is now concentrated in **proving** ($\star_\theta$) (in the proof, its localised form) for θ arbitrarily close to 1/2. According to the guide, that is where the Stepanov engine enters: m ≍ √x iterated theta lifts, divisibility at inert primes, and Bost's slope inequality give an upper bound for a prime sum with exponent 1/2 + 9ε. Step 2 will measure what the bound has to achieve on real families; step 3 will build toy versions of the engine.

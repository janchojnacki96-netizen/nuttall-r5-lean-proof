# Analytic transformation: from the Riemann theta integral to the certified coefficient matrix

**Status:** Detailed human mathematical derivation and formalization
specification. This note is **not** a compiled Lean proof. It isolates
the analytic work still needed before claiming the unconditional W5
theorem. The code in `W5/AnalyticTargets.lean` currently defines both
sides of the proposed identity; it does not prove them equal.

## Definitions

For `n >= 1`, write `p=n²` and
```text
phi_n(t) = [2p² pi² exp(9t) - 3p pi exp(5t)] exp(-p pi exp(4t))
Phi(t)   = sum_{n>=1} phi_n(t)
Psi1(t)  = integral_{t}^{infty} Phi(v) dv
y        = pi exp(4t)  > 0
x        = y^(-1/2)   > 0.
```
The objective is the signs of the leading Hankel/Wronskian minors
`W_r(t)=det[Psi1^(i+j)(t)]_(0<=i,j<r)` for `1<=r<=5`.

## 1. The exact one-summand integral

Because `dt = dy/(4y)`, the `n`th summand satisfies
```text
phi_n(t) dt =
    pi^(-1/4)/4 * p * y^(1/4) * (2p*y - 3) exp(-p*y) dy.
```
Use the derivative identity
```text
d/dy (y^(5/4) exp(-p*y))
   = (5/4)*y^(1/4)*exp(-p*y) - p*y^(5/4)*exp(-p*y).
```
Thus
```text
y^(1/4)*(2p*y-3)exp(-p*y)
 = -2*d/dy[y^(5/4)exp(-p*y)] - (1/2)*y^(1/4)exp(-p*y).
```
Integration from `y` to infinity (the boundary at infinity
vanishes) gives, term by term,
```text
Psi1(t) = (pi^(-1/4)/2)*y^(5/4)
  * sum_{n>=1} p *
     [ exp(-p*y)
       - (1/4)*integral_{s=1}^infty s^(1/4) exp(-p*y*s) ds ].
                                                 [A]
```

**Interchange justification that Lean must verify:** for every fixed
`t0>=0`, the summands are absolutely integrable on `[t0,infty)`
and the sum of their integrals is finite. Set `y0=pi*exp(4*t0)>0`.
In the variable `z=pi*exp(4v)` one has the elementary dominating
bound, for `z>=y0`,
```text
z^(1/4)*(2p*z+3)*exp(-p*z)
 <= exp(-p*y0/2)*z^(1/4)*(2p*z+3)*exp(-p*z/2).
```
The integral of the RHS is
`exp(-p*y0/2)` times a sum of fixed gamma moments with polynomial
powers of `p`. Summation over squares `p=n²` converges absolutely.
Higher derivatives on every compact interval admit similar bounds
`C_k(1+n)^{N_k} exp(-c n²)` for `k<=8`. This also justifies
`Psi1'(t)=-Phi(t)` and repeated differentiation where needed.

## 2. Positive analytic coordinate change

Fix `x>0`, `y=1/x²`, `t=log(y/pi)/4`. Put
```text
s(u) = log(1+x*u)/4
h(u) = exp(u/x)/(1+x*u)^(5/4)
c    = 2*pi^(1/4)*exp(y)/y^(5/4)  > 0
H_x(u,v) = c*h(u)*h(v)*Psi1(t+s(u)+s(v)).
                                                 [B]
```
All factors are real analytic near `u=v=0`; the neighborhood may
be restricted so `1+x*u`, `1+x*v` stay positive. The choice
of `s` means
`pi*exp(4*(t+s(u)+s(v)))=y*(1+x*u)*(1+x*v)`.

For `0<=k,i<=4` define the exact Taylor-jet transform
`T_ik=[u^i]h(u)s(u)^k`. Then `T_ik=0` for `k>i`,
`T_ii=(x/4)^i>0`, since `h(0)=1` and
`s(u)=(x/4)u+O(u²)`. Let
`C_kl=Psi1^(k+l)(t)/(k! l!)`.
For every `r=1,...,5`, the leading coefficient matrix of `H_x`
is `A_r=c*T_r*C_r*T_r^T`.
Therefore
```text
det(A_r)
 = c^r*(x/4)^(r*(r-1))
   *(product_{i=0}^{r-1} (i!)^-2) * W_r(t).
                                                 [C]
```
All factors other than `W_r` are strictly positive for `x>0`,
so leading determinant signs coincide. This is the **specific
analytic identification** still to be implemented in Lean;
the existing generic matrix congruence lemmas alone do not
establish it.

## 3. Exact theta coefficient series

In [A] replace `y` by `y*(1+x*u)*(1+x*v)` and multiply by
the factors in [B]. In the integral use
`w=p*y*(s_old-1)`, so `s_old=1+w*x²/p`.
Direct exponent expansion gives
```text
d_w = (p-1)/x+w*x,
q_w = p+w*x²,
K_{p,w}(u,v) = exp(-d_w*(u+v)-q_w*u*v).
```
Then, near `u=v=0`,
```text
H_x(u,v) =
 sum_{n>=1} p*exp(-(p-1)/x²)
 [ K_{p,0}(u,v)
   -x²/(4p) * integral_{w=0}^infty
     exp(-w)*(1+w*x²/p)^(1/4)*K_{p,w}(u,v) dw ].
                                                 [D]
```
For `0<=i,j<=4`, expand three exponential factors
`exp(-d*u) exp(-d*v) exp(-q*u*v)`.
The coefficient of `u^i*v^j` is the **finite** polynomial
```text
B_ij(d,q) =
 sum_{k=0}^{min(i,j)}
   (-1)^(i+j-k)*d^(i+j-2k)*q^k
     /[k! (i-k)! (j-k)!].
                                                 [E]
```
This is the expression used by the C++ certificate and defined
by `W5.coefficientPolynomial` in Lean.

For each fixed `x>0`, the series in [D] and derivatives up to
orders 4 in `u,v` converge locally uniformly:
choose `u,v` in a sufficiently small rectangle about zero,
so `(1+x*u)(1+x*v)` stays uniformly positive. For the integral,
the exponential has a uniform decaying factor in `w`;
derivatives add only polynomial factors. Across `n`,
`exp(-c*n²*y)` dominates every fixed polynomial factor.
Thus derivative extraction may be moved through the integral and
sum, obtaining the equality of the matrices from [B] and [D].

**Precise remaining Lean goal:** implement the convergence and
derivative-interchange arguments, prove `thetaTransformCorrect`,
then connect the coefficient matrix to `W_r` through [C].

## 4. Uniform theta tail and finite moment checker

The majorants and rigorous finite moment enclosure are described
in `certificate/certyfikat_theta_W5.cpp` and the previous audit.
The ratio contraction
`M_(n+1)(y) < M_n(y)/2` for `n>=2,y>=3`
already has an independent Lean lemma in `W5/TailRatioGeneral.lean`.

This does **not** prove the majorization of every coefficient by
`M_n(y)`, the exact integrals on all 256 bins, or the 255 interval
pivot signs in Lean. These are separate obligations.

## Completion criterion

The theorem must ultimately have the **unconditional** type
`W5.nuttall_r5 : W5.MainClaim` without assuming
`thetaTransformCorrect`, an interval certificate oracle,
or any unproved `hdet`/`hlocal` hypothesis. A green `lake build`
of the current conditional modules does not meet this criterion.

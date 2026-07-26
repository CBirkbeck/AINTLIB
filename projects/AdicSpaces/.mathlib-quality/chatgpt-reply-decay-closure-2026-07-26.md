Yes: \(D_\rho\) is a subring. The missing ingredient is a moving-prefix tail estimate, not a coordinatewise Lipschitz estimate.

For \(a=\sum_{n\ge0}p^n[a_n]\), define

\[
P_N(a):=\sum_{i<N}p^i[a_i],\qquad
\sigma_N(a):=\sum_{k\ge0}p^k[a_{N+k}],
\]

so that

\[
a=P_N(a)+p^N\sigma_N(a).
\]

For a \(w\)-bounded vector, put

\[
T_N(a):=\rho^Nw(\sigma_N(a))
       =\sup_{n\ge N}\rho^n|a_n|,
\]

and

\[
H_N(a):=\rho^N\max_{i<N}|a_i|,
\]

with the empty maximum equal to \(0\).

## The exact addition inequality

For all \(w\)-bounded \(x,y\),

\[
\boxed{
T_N(x+y)\le
\max\{T_N(x),T_N(y),H_N(x),H_N(y)\}.
}
\tag{1}
\]

Equivalently, for every \(k\ge0\),

\[
\boxed{
\rho^{N+k}|(x+y)_{N+k}|
\le
\max\left\{
T_N(x),T_N(y),
\rho^N\max_{i<N}\max(|x_i|,|y_i|)
\right\}.
}
\tag{2}
\]

This is the tail-refined digit inequality that does the work.

### Proof of (1)

Set

\[
A_N:=P_N(x)+P_N(y),\qquad C_N:=\sigma_N(A_N).
\]

Thus

\[
A_N=P_N(A_N)+p^NC_N.
\tag{3}
\]

Let

\[
M_N:=\max_{i<N}\max(|x_i|,|y_i|).
\]

Since \(A_N\) is a finite sum of shifted Teichmüller lifts, your finite-sum digit bound gives

\[
|(A_N)_j|\le M_N\qquad(j\ge0).
\tag{4}
\]

Consequently,

\[
w(C_N)
=\sup_{k\ge0}\rho^k|(A_N)_{N+k}|
\le M_N.
\tag{5}
\]

For completeness, (4) also has a short scaling proof. If \(M_N>0\), choose one input coefficient \(c\) with \(|c|=M_N\). Then

\[
A_N=[c]\left(
 \sum_{i<N}p^i[x_i/c]+\sum_{i<N}p^i[y_i/c]
\right).
\]

The term in parentheses lies in \(W(\mathcal O_F)\), so all its Teichmüller coordinates have norm at most \(1\); multiplication by \([c]\) multiplies every Teichmüller coordinate by \(c\).

Now substitute the three tail decompositions:

\[
\begin{aligned}
x+y
 &=A_N+p^N(\sigma_N(x)+\sigma_N(y))\\
 &=P_N(A_N)+p^N\bigl(C_N+\sigma_N(x)+\sigma_N(y)\bigr).
\end{aligned}
\tag{6}
\]

Uniqueness of the Teichmüller expansion gives the exact identity

\[
\sigma_N(x+y)=C_N+\sigma_N(x)+\sigma_N(y).
\tag{7}
\]

All three families on the right are bounded, so the already-proved ultrametric inequality applies:

\[
\begin{aligned}
T_N(x+y)
 &=\rho^Nw(\sigma_N(x+y))\\
 &\le
 \max\{\rho^Nw(C_N),T_N(x),T_N(y)\}\\
 &\le
 \max\{\rho^NM_N,T_N(x),T_N(y)\}.
\end{aligned}
\]

Finally,

\[
\rho^NM_N=\max\{H_N(x),H_N(y)\},
\]

which proves (1).

This is precisely the repair of your attempt (6): the junk cofactor is \(C_N\), but it satisfies the stronger unweighted estimate

\[
|(C_N)_k|\le M_N,
\]

not merely a bound of size \(M/\rho^N\).

## Why the four terms tend to zero

If \(a\in D_\rho\), then \(T_N(a)\to0\), because \(T_N(a)\) is the supremum of the \(N\)-th tail of the sequence \(\rho^n|a_n|\to0\).

Also,

\[
H_N(a)=\max_{i<N}\rho^{N-i}\bigl(\rho^i|a_i|\bigr)\longrightarrow0.
\tag{8}
\]

Here is an explicit proof. Given \(\varepsilon>0\), choose \(K\) such that

\[
\rho^i|a_i|<\varepsilon\qquad(i\ge K).
\]

Put \(C=\max_{i<K}|a_i|\). For sufficiently large \(N\),

\[
\rho^NC<\varepsilon.
\]

Then, for \(i<N\):

- if \(i<K\), then \(\rho^N|a_i|\le\rho^NC<\varepsilon\);
- if \(K\le i<N\), then
  \[
  \rho^N|a_i|
   =\rho^{N-i}\bigl(\rho^i|a_i|\bigr)
   \le \rho^i|a_i|
   <\varepsilon.
  \]

Thus \(H_N(a)<\varepsilon\).

Applying this to \(x,y\) in (1) proves

\[
T_N(x+y)\longrightarrow0,
\]

and hence

\[
\rho^n|(x+y)_n|\le T_n(x+y)\longrightarrow0.
\]

Therefore \(x+y\in D_\rho\).

## A useful perturbation and closedness corollary

If \(u\in D_\rho\) and \(e\) is merely \(w\)-bounded, then (1) gives

\[
\boxed{
T_N(u+e)\le
\max\{T_N(u),H_N(u),w(e)\}.
}
\tag{9}
\]

Indeed, \(T_N(e)\le w(e)\), and for \(i<N\),

\[
\rho^N|e_i|
=\rho^{N-i}\bigl(\rho^i|e_i|\bigr)
\le w(e),
\]

so \(H_N(e)\le w(e)\).

Consequently \(D_\rho\) is \(w\)-closed among bounded Witt vectors. Explicitly, if \(u_m\in D_\rho\) and \(w(z-u_m)\to0\), then for any \(\varepsilon>0\), choose \(m\) with \(w(z-u_m)<\varepsilon\). Applying (9) to

\[
z=u_m+(z-u_m)
\]

and then taking \(N\) large gives \(T_N(z)\le\varepsilon\). Hence \(z\in D_\rho\).

This is the correct asymptotic substitute for the false digitwise perturbation inequality.

## Multiplication

Let

\[
x^{(N)}:=P_N(x),\qquad y^{(N)}:=P_N(y),\qquad
q_N:=x^{(N)}y^{(N)}.
\]

By distributivity and Teichmüller multiplicativity,

\[
q_N
=\sum_{i,j<N}p^{i+j}[x_i y_j].
\tag{10}
\]

This is a finite shifted-Teichmüller sum. Its canonical coordinates are uniformly bounded by the finite number

\[
\max_{i,j<N}|x_i y_j|,
\]

so \(q_N\in D_\rho\).

Moreover,

\[
w(x-x^{(N)})=T_N(x),\qquad
w(y-y^{(N)})=T_N(y),
\]

and

\[
xy-q_N=(x-x^{(N)})y+x^{(N)}(y-y^{(N)}).
\]

Thus multiplicativity/submultiplicativity and the ultrametric inequality give

\[
\begin{aligned}
w(xy-q_N)
&\le
\max\left\{
T_N(x)w(y),
w(x^{(N)})T_N(y)
\right\}\\
&\le
\max\left\{
T_N(x)w(y),
w(x)T_N(y)
\right\}
\longrightarrow0.
\end{aligned}
\tag{11}
\]

Since every \(q_N\in D_\rho\) and \(D_\rho\) is \(w\)-closed, \(xy\in D_\rho\). Only submultiplicativity is needed here. Since \(-1\in D_\rho\), multiplication also gives closure under negation.

## Application to `ArSub`

Let \(z\in\mathrm{ArSub}\), and let

\[
b_n:=\operatorname{teichCoeffAr}(z,n)
\]

be its limit coordinates. Fix \(u\in\mathrm{Aloc}\), writing the coordinates of its image in \(W(F)\) also as \(u_n\).

First, every \(\mathrm{Aloc}\)-element has decaying coordinates: write \(u=A/[\pi]^k\) with \(A\in W(\mathcal O_F)\). Then

\[
u_n=\pi^{-k}A_n,\qquad |u_n|\le|\pi|^{-k},
\]

so \(\rho^n|u_n|\to0\).

Now fix \(\eta>v(z-u)\). Along the filter of \(\mathrm{Aloc}\)-approximants \(a\to z\), one eventually has

\[
w(a-u)\le\eta.
\]

Apply (9) in \(W(F)\):

\[
T_N(a)\le
\max\{T_N(u),H_N(u),\eta\}.
\tag{12}
\]

The bound is uniform over all coordinates \(n\ge N\). For each fixed \(n\ge N\), the coordinates \(a_n\) converge to \(b_n\). Passing to the limit through the closed valuation ball gives

\[
\rho^n|b_n|
\le
\max\{T_N(u),H_N(u),\eta\}.
\]

Taking the supremum over \(n\ge N\),

\[
\boxed{
T_N(b)\le
\max\{T_N(u),H_N(u),\eta\}.
}
\tag{13}
\]

This is the required tail-sup semicontinuity inequality.

Since \(u\) has decaying coordinates, its first two terms tend to zero. Therefore

\[
\limsup_{N\to\infty}T_N(b)\le v(z-u).
\tag{14}
\]

Finally, \(z\) lies in the closure of \(\mathrm{Aloc}\), so \(u\) can be chosen with \(v(z-u)\) arbitrarily small. Hence \(T_N(b)\to0\), and in particular

\[
\rho^n|b_n|\longrightarrow0.
\]

Thus every element of `ArSub` has decaying limit coordinates. Your `valued_PhiHatK` isometry can then be used after this decay statement; it is not itself needed to establish decay.

The norm background is Kedlaya’s Lemma 4.1 in [Nonarchimedean geometry of Witt vectors](https://arxiv.org/abs/1004.0466) and Definition 2.2/Lemma 2.3 in [Noetherian properties of Fargues–Fontaine curves](https://arxiv.org/abs/1410.5160). The additional tail refinement needed for formalization is exactly (1)/(2).
Yes: (DC) is true. In fact one gets a stronger symmetric estimate, and it proves that all radius-\(\rho\) maximizing indices—not merely the largest one—are unchanged by a sufficiently small perturbation. Your proposed proof of multiplicativity of degree is then correct once the infinite regrouping is written carefully.

This supplies the single-radius details omitted in Kedlaya’s Lemma 2.6 and Remark 2.7; the paper indeed attributes them to multiplicativity plus convex duality. [Kedlaya, §2](https://arxiv.org/abs/1410.5160)

Throughout, use

\[
w(p)=\rho,\qquad w([z])=|z|.
\]

We also use the standard complete nonarchimedean series fact:

> If \(w(t_n)\to0\), then \(\sum_n t_n\) converges, and
> \[
> w\left(\sum_n t_n\right)\le \sup_n w(t_n).
> \]

Indeed, finite tails are bounded by their largest term, so the partial sums are Cauchy; the bound passes to the limit.

## Q1: digit comparison and stability of degree

Let

\[
x=\sum_{n\ge0}p^n[x_n],\qquad
y=\sum_{n\ge0}p^n[y_n].
\]

The following holds without assuming \(w(x-y)<w(x)\):

\[
\boxed{
\sup_n \rho^n|x_n-y_n|
\le
\max\bigl(w(x-y),\,\rho\max(w(x),w(y))\bigr).
}
\tag{DC\(^+\)}
\]

Consequently, under \(w(x-y)<w(x)\), this becomes exactly your proposed estimate

\[
\boxed{
\rho^n|x_n-y_n|
\le
\max\bigl(w(x-y),\rho w(x)\bigr)
\quad\text{for every }n.
}
\tag{DC}
\]

### Proof of \((\mathrm{DC}^+)\)

Put

\[
e_n=x_n-y_n.
\]

Since

\[
\rho^n|e_n|
\le \max(\rho^n|x_n|,\rho^n|y_n|)\longrightarrow0,
\]

the sequence \(e=(e_n)\) is decaying, so \(\Phi(e)\) exists and

\[
w(\Phi(e))=\sup_n\rho^n|e_n|.
\tag{1}
\]

Define the one-digit Witt-addition error

\[
h_n=[x_n]-[y_n]-[x_n-y_n].
\]

By the signed two-term instance of (H),

\[
w(h_n)\le \rho\max(|x_n|,|y_n|).
\tag{2}
\]

Hence

\[
w(p^nh_n)
\le
\rho^{n+1}\max(|x_n|,|y_n|)
=
\rho\max(\rho^n|x_n|,\rho^n|y_n|)
\longrightarrow0.
\]

Therefore

\[
H_\infty:=\sum_{n\ge0}p^nh_n
\]

converges. Moreover, writing

\[
M=\max(w(x),w(y)),
\]

we obtain

\[
w(H_\infty)
\le \sup_n w(p^nh_n)
\le \rho M.
\tag{3}
\]

For every finite \(N\),

\[
\begin{aligned}
&\sum_{n=0}^N p^n[x_n]
-\sum_{n=0}^N p^n[y_n]
-\sum_{n=0}^N p^n[x_n-y_n]  \\
&\qquad=\sum_{n=0}^Np^nh_n.
\end{aligned}
\]

Taking limits gives the exact identity

\[
x-y-\Phi(e)=H_\infty.
\tag{4}
\]

Thus, by ultrametricity and (3),

\[
w(\Phi(e))
\le
\max\bigl(w(x-y),\rho M\bigr).
\]

Combining this with (1) proves \((\mathrm{DC}^+)\).

A formalization detail: if your version of (H) only handles unsigned sums, do not use the generally false identity \([-v]=-[v]\), especially at \(p=2\). Instead write

\[
\begin{aligned}
[u]-[v]-[u-v]
={}&\bigl([u]+[-v]-[u-v]\bigr)\\
&-\bigl([v]+[-v]\bigr),
\end{aligned}
\]

and apply unsigned (H) separately to \((u,-v)\) and \((v,-v)\). This yields the same bound (2).

### Deduction of Remark 2.7

Now assume

\[
D:=w(x-y)<w(x)=:A.
\]

First, ultrametricity gives \(w(y)=A\). Therefore \((\mathrm{DC}^+)\) says

\[
\rho^n|x_n-y_n|
\le B:=\max(D,\rho A)<A
\tag{5}
\]

for every \(n\).

Define

\[
\alpha_n=\rho^n|x_n|,\qquad
\beta_n=\rho^n|y_n|,\qquad
\delta_n=\rho^n|x_n-y_n|.
\]

Suppose \(\alpha_n=A\). Since \(x_n=y_n+(x_n-y_n)\),

\[
A=\alpha_n\le\max(\beta_n,\delta_n).
\]

But \(\delta_n<A\) by (5), while \(\beta_n\le w(y)=A\). Hence \(\beta_n=A\).

The same argument with \(x\) and \(y\) interchanged proves the converse. Thus

\[
\boxed{
\{n:\rho^n|x_n|=A\}
=
\{n:\rho^n|y_n|=A\}.
}
\tag{6}
\]

Their largest elements agree, so

\[
\boxed{\deg(x)=\deg(y).}
\]

This is stronger than Remark 2.7: the complete radius-\(\rho\) leading support is locally constant.

## Q2: multiplicativity of degree

Assume \(x,y\ne0\), and write

\[
x=\Phi(a),\qquad y=\Phi(b).
\]

Set

\[
\alpha_i=\rho^i|a_i|,\qquad
\beta_j=\rho^j|b_j|,
\]

and

\[
A=w(x)=\max_i\alpha_i,\qquad
B=w(y)=\max_j\beta_j.
\]

Let

\[
m=\deg(x),\qquad \ell=\deg(y).
\]

Thus \(m\) and \(\ell\) are the largest indices satisfying

\[
\alpha_m=A,\qquad \beta_\ell=B.
\]

Define the ordinary convolution in \(F\):

\[
c_n=\sum_{i+j=n}a_ib_j.
\tag{7}
\]

### 1. The convolution sequence is decaying

Put

\[
\Delta_n=\max_{i+j=n}\alpha_i\beta_j.
\]

Then \(\Delta_n\to0\). To see this, fix \(\varepsilon>0\). Since \(A,B>0\), choose \(N\) such that

\[
i>N\Longrightarrow \alpha_i<\frac{\varepsilon}{B},
\qquad
j>N\Longrightarrow \beta_j<\frac{\varepsilon}{A}.
\]

If \(n>2N\) and \(i+j=n\), then \(i>N\) or \(j>N\). Hence

\[
\alpha_i\beta_j<\varepsilon.
\]

Therefore \(\Delta_n<\varepsilon\) for \(n>2N\).

By the ultrametric inequality in \(F\),

\[
\rho^n|c_n|
\le
\max_{i+j=n}\rho^n|a_ib_j|
=
\max_{i+j=n}\alpha_i\beta_j
=
\Delta_n\longrightarrow0.
\tag{8}
\]

Thus \(c\) is a valid decaying sequence. By your realization theorem, \(\Phi(c)\) has canonical coordinates exactly \(c_n\).

### 2. Rigorous regrouping of the product

Define in the Witt ring

\[
U_n=\sum_{i+j=n}[a_ib_j].
\]

We first verify

\[
xy=\sum_{n\ge0}p^nU_n.
\tag{9}
\]

Let

\[
X_N=\sum_{i=0}^Np^i[a_i],\qquad
Y_N=\sum_{j=0}^Np^j[b_j],
\]

and

\[
T_N=\sum_{n=0}^Np^nU_n
=\sum_{i+j\le N}p^{i+j}[a_ib_j].
\]

The finite distributive law and multiplicativity of Teichmüller lifts give

\[
X_NY_N
=
\sum_{0\le i,j\le N}p^{i+j}[a_ib_j].
\]

Consequently,

\[
X_NY_N-T_N
=
\sum_{\substack{0\le i,j\le N\\i+j>N}}
p^{i+j}[a_ib_j].
\]

Therefore

\[
w(X_NY_N-T_N)
\le
\sup_{i+j>N}\alpha_i\beta_j.
\tag{10}
\]

The right side tends to zero by exactly the same tail-splitting argument used above: for \(N\ge2K\), any \(i+j>N\) has \(i>K\) or \(j>K\).

Since \(X_N\to x\), \(Y_N\to y\), and multiplication is continuous, \(X_NY_N\to xy\). Equation (10) therefore implies \(T_N\to xy\), proving (9). This removes the infinite double-sum regrouping gap.

### 3. The Witt-addition error

Define

\[
q_n=U_n-[c_n].
\]

Applying (H) to the finite antidiagonal family

\[
(a_0b_n,a_1b_{n-1},\ldots,a_nb_0)
\]

gives

\[
w(q_n)
\le
\rho\max_{i+j=n}|a_ib_j|.
\]

Hence

\[
\begin{aligned}
w(p^nq_n)
&\le
\rho^{n+1}\max_{i+j=n}|a_ib_j|\\
&=
\rho\Delta_n
\longrightarrow0.
\end{aligned}
\tag{11}
\]

Thus

\[
E:=\sum_{n\ge0}p^nq_n
\]

converges, and

\[
w(E)
\le
\sup_n\rho\Delta_n
\le
\rho AB.
\tag{12}
\]

Since \(U_n=[c_n]+q_n\), equations (9)–(12) give

\[
\boxed{xy=\Phi(c)+E,\qquad w(E)\le\rho AB.}
\tag{13}
\]

So your desired error estimate does follow from (H); the only extra ingredient is the elementary tail argument justifying diagonal regrouping.

### 4. Degree of the ordinary convolution realization

For every \(n\),

\[
\rho^n|c_n|
\le
\max_{i+j=n}\alpha_i\beta_j
\le AB.
\tag{14}
\]

Set

\[
n_0=m+\ell.
\]

On the antidiagonal \(i+j=n_0\), the term \(a_mb_\ell\) has scaled size

\[
\rho^{n_0}|a_mb_\ell|=\alpha_m\beta_\ell=AB.
\]

It is the unique term of this size.

Indeed, take \((i,j)\ne(m,\ell)\) with \(i+j=m+\ell\).

- If \(i>m\), then \(\alpha_i<A\), since \(m\) is the largest maximizing index. Hence
  \[
  \alpha_i\beta_j<AB.
  \]

- If \(i<m\), then
  \[
  j=m+\ell-i>\ell,
  \]
  so \(\beta_j<B\), and again
  \[
  \alpha_i\beta_j<AB.
  \]

Thus the finite sum defining \(c_{n_0}\) has one uniquely dominant summand. The nonarchimedean unique-maximum principle gives

\[
\rho^{n_0}|c_{n_0}|=AB.
\tag{15}
\]

Now let \(n>m+\ell\). For every pair \(i+j=n\), it is impossible to have simultaneously \(i\le m\) and \(j\le\ell\). Therefore \(i>m\) or \(j>\ell\), and hence

\[
\alpha_i\beta_j<AB.
\]

There are only finitely many pairs on this antidiagonal, so their maximum is also strictly less than \(AB\). Therefore

\[
\rho^n|c_n|<AB\qquad(n>m+\ell).
\tag{16}
\]

Equations (14)–(16) show that \(m+\ell\) is a maximizing index and that no larger index is maximizing. Since \(c_n\) are the canonical coordinates of \(\Phi(c)\),

\[
\boxed{
w(\Phi(c))=AB,\qquad
\deg(\Phi(c))=m+\ell.
}
\tag{17}
\]

No assertion about cancellation on earlier antidiagonals is needed. Earlier indices may also maximize; the degree uses the largest one.

### 5. Transfer from \(\Phi(c)\) to \(xy\)

Multiplicativity of \(w\) gives

\[
w(xy)=w(x)w(y)=AB.
\]

From (13),

\[
w(xy-\Phi(c))
=
w(E)
\le
\rho AB
<
AB
=
w(xy).
\]

Applying Q1 to \(xy\) and \(\Phi(c)\), and then using (17), gives

\[
\boxed{
\deg(xy)
=
\deg(\Phi(c))
=
m+\ell
=
\deg(x)+\deg(y).
}
\]

Thus your proposed argument is fully correct after inserting the convergence/regrouping lemma.

## Q3: leading-part interpretation

No alternative route is necessary because (DC) holds. Nevertheless, equation (6) gives exactly the useful leading-part formulation:

\[
\operatorname{LeadSupp}_\rho(x)
:=
\{n:\rho^n|x_n|=w(x)\}
\]

is unchanged whenever \(w(x-y)<w(x)\). Moreover, at each leading index,

\[
\rho^n|x_n-y_n|<w(x),
\]

so the leading digit is unchanged modulo strictly lower radius-\(\rho\) size. This is the single-radius analogue of stability of an initial form, with no Newton polygon or varying family \(\lambda_t\).

Under the hypotheses you listed, I see no remaining mathematical gap. The main formalization-sensitive points are the signed version of (H), the complete nonarchimedean series lemma, and the elementary fact that \(\max_{i+j=n}\alpha_i\beta_j\to0\).
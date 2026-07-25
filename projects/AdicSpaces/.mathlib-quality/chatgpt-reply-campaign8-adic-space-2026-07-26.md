The norm construction is sound, but the plan is not complete as written. Lane C contains one incorrect plus-ring claim and two major missing bridges: the rational-localization/\(B^I\) comparison, and descent of the locally valued ringed structure through \(Y/\varphi^{\mathbf Z}\).

1. **The formula is correct.**

For \(t>0\) and \(\rho=p^{-1/t}\),

\[
\lambda_t\!\left(\sum_n p^n[a_n]\right)^{1/t}
 =\left(\max_n p^{-n}|a_n|^t\right)^{1/t}
 =\max_n p^{-n/t}|a_n|
 =\max_n \rho^n|a_n|.
\]

Thus there is no Frobenius or exponent twist on \(|a_n|\). Raising a nonarchimedean multiplicative norm to a positive real power preserves all norm axioms, and \(\lambda_t\) and \(w_\rho\) define the same Spa point because positive powering preserves all value comparisons.

The maximum is attained: \(|a_n|\le1\), so \(\rho^n|a_n|\le\rho^n\to0\). For a nonzero vector, choose one positive term; all sufficiently late terms are smaller, leaving a finite maximum. This is exactly the specialization of Kedlaya’s formula and multiplicativity lemma in [Definition 2.2 and Lemma 2.3](https://arxiv.org/pdf/1410.5160).

In particular,

\[
w_\rho(p)=\rho,\qquad w_\rho([w])=|w|,\qquad
w_\rho(p[w])=\rho|w|>0.
\]

2. **There is a formalizable proof, but density alone does not remove the Witt-arithmetic input.**

The cleanest formalization target is Kedlaya’s earlier Lemma 4.1. Put

\[
\alpha(a)=|a|^t\qquad(a\in O_F).
\]

Then \(\alpha\) is multiplicative, nonarchimedean, and bounded by the trivial norm. The lemma states that

\[
N_t\!\left(\sum_i p^i[a_i]\right)
  :=\max_i p^{-i}\alpha(a_i)
\]

is multiplicative. Then \(w_\rho=N_t^{1/t}\). See [Kedlaya, Lemma 4.1](https://arxiv.org/pdf/1004.0466).

A small amount of universal Witt-polynomial homogeneity suffices. For \(a,b\) in a perfect \(\mathbf F_p\)-algebra, one can write

\[
[a]\pm[b]
 =\sum_{j\ge0}p^j\bigl[P_j^\pm(a,b)^{p^{-j}}\bigr],
\]

where \(P_j^\pm\in\mathbf F_p[X,Y]\) is homogeneous of ordinary degree \(p^j\). Consequently, if \(c_j=P_j^\pm(a,b)^{p^{-j}}\), then

\[
|c_j|\le\max(|a|,|b|).
\]

This gives

\[
w_\rho\bigl(p^i([a]\pm[b])\bigr)
 \le \rho^i\max(|a|,|b|).
\]

From here one may follow Kedlaya’s digit-carry argument:

- Successively combine Teichmüller terms at each \(p\)-adic level.
- The carry to the next level never increases the bound.
- Passing through all levels proves
  \[
  w_\rho(x+y)\le\max(w_\rho(x),w_\rho(y)).
  \]
- Since
  \[
  p^i[a]\cdot p^j[b]=p^{i+j}[ab],
  \]
  the triangle inequality gives submultiplicativity.
- For the reverse product inequality, choose the least indices \(i,j\) where the maxima for \(x,y\) occur. In the products of the corresponding tails, the \(p^{i+j}\)-coefficient is \(a_i b_j\); all discarded parts have strictly smaller norm. The strict-triangle consequence then gives equality.

This route needs no general multiplication-polynomial theorem beyond Teichmüller multiplicativity. If one instead works with arbitrary Witt coordinates, the standard sufficient statement is that addition polynomials are weighted homogeneous of weight \(p^n\), with \(X_i,Y_i\) of weight \(p^i\), and multiplication polynomials are bi-weight-homogeneous.

Finite Teichmüller approximations are useful only after this finite-level estimate: the tails satisfy

\[
w_\rho\!\left(\sum_{i\ge N}p^i[a_i]\right)\le\rho^N.
\]

Density then extends the norm laws to infinite vectors. It cannot by itself prove the initial triangle inequality, and using “strict triangle” before proving ultrametricity would be circular. There is also no need to approximate arbitrary \(\rho\) by rational radii.

3. **The continuity argument is correct if “values tend to zero” is made uniform.**

Let \(I=(p,[w])\) and

\[
q=\max(\rho,|w|)<1.
\]

Every element of \(I^n\) is a finite sum of terms

\[
r_{a,b}p^a[w]^b,\qquad a+b=n,\quad r_{a,b}\in A_{\inf}.
\]

Since \(w_\rho(r_{a,b})\le1\),

\[
w_\rho(I^n)\le q^n,
\]

meaning \(w_\rho(z)\le q^n\) for every \(z\in I^n\). Hence, for every \(\varepsilon>0\), some \(I^n\) lies in

\[
\{z:w_\rho(z)<\varepsilon\}.
\]

That is exactly what proves Huber-continuity for this real rank-one valuation. Merely asserting pointwise convergence for selected elements of \(I^n\) would not be enough; the uniform inclusion is the correct formulation. In general Huber language, continuity requires the value of each generator of an ideal of definition to be cofinal in the value group; for a real value \(q<1\), this follows from \(q^n\to0\). See [Wedhorn, Definition 7.7 and Theorem 7.10](https://arxiv.org/pdf/1910.05934).

For membership in \(\operatorname{Spa}(A_{\inf},A_{\inf})\), after multiplicativity and continuity are established, the remaining condition is precisely

\[
w_\rho(a)\le1\qquad(a\in A^+=A_{\inf}).
\]

So yes, that bound is enough for the plus condition. It is not by itself enough for continuity.

4. **The two-sided windows are governed by Theorem 4.10, not merely Theorem 3.2.**

Normalize the absolute value on \(F\) so that

\[
|w|=p^{-1}.
\]

For a rank-one point define

\[
\kappa(v)=\frac{\log v([w])}{\log v(p)}.
\]

At the Gauss point \(\lambda_t\), one has \(\kappa(\lambda_t)=t\). Therefore

\[
U_0=Y_{[1,c]},\qquad V_0=Y_{[c,p]},
\]

and their rings are

\[
B^{[1,c]}_{F,\mathbf Q_p},
\qquad
B^{[c,p]}_{F,\mathbf Q_p}.
\]

Without normalizing \(|w|\), put

\[
\tau=\frac{\log(p^{-1})}{\log|w|}>0.
\]

Then \(\kappa(\lambda_t)=t/\tau\), so the intervals are

\[
I_U=[\tau,c\tau],\qquad I_V=[c\tau,p\tau].
\]

The precise division of responsibilities in Kedlaya’s paper is:

- Definition 4.2 defines \(B^I\).
- Lemma 4.9 computes changes of interval as Banach/rational localizations and contains relevant integral-closure information.
- Theorem 4.10 proves
  \[
  B^I\{T_1/\rho_1,\dots,T_n/\rho_n\}
  \]
  noetherian for every closed \(I\subset(0,\infty)\); in particular \(B^I\) is strongly noetherian.
- Theorem 3.2 only treats the one-radius/one-sided rings \(A^r\).

Thus Lane B should explicitly include Lemma 4.9. Theorem 4.10 proves strong noetherianity once the chart ring has been identified; it does not itself prove the identification with \(\mathcal O(U_0)\) or \(\mathcal O(V_0)\). See [Kedlaya, Definition 4.2, Lemma 4.9, and Theorem 4.10](https://arxiv.org/pdf/1410.5160).

5. **This is the main missing comparison theorem, and the proposed plus ring is wrong as stated.**

Write \(c=a/b\) in lowest terms. The windows really are rational subsets of the non-Tate pair \((A_{\inf},A_{\inf})\). They admit single-denominator presentations:

\[
s_U=p[w]^b,\qquad
T_U=\{p^{a+1},[w]^{b+1}\},
\]

and

\[
s_V=p^a[w],\qquad
T_V=\{[w]^{b+1},p^{p+a}\}.
\]

Indeed,

\[
U_0=R(T_U/s_U),
\]

because its two fractions are

\[
\frac{[w]^{b+1}}{p[w]^b}=\frac{[w]}p,
\qquad
\frac{p^{a+1}}{p[w]^b}=\frac{p^a}{[w]^b},
\]

encoding \(\kappa\ge1\) and \(\kappa\le a/b\). Similarly,

\[
V_0=R(T_V/s_V),
\]

with fractions

\[
\frac{[w]^b}{p^a},\qquad \frac{p^p}{[w]},
\]

encoding \(\kappa\ge a/b\) and \(\kappa\le p\). The numerator ideals have radical \((p,[w])\), so they are open.

Therefore the precise target statements are

\[
\widehat{A_{\inf}(T_U/s_U)}
 \;\cong\; B^{[\tau,c\tau]}_{F,\mathbf Q_p},
\]

\[
\widehat{A_{\inf}(T_V/s_V)}
 \;\cong\; B^{[c\tau,p\tau]}_{F,\mathbf Q_p},
\]

as complete topological rings, extending the identity on the common dense algebra

\[
B_{F,\mathbf Q_p}
 =W(O_F)[1/p,1/[w]].
\]

No preliminary passage to a global Tate localization is necessary. Rational localization and its structure-presheaf value are defined for a general Huber pair, even if it is non-Tate or non-sheafy. For these particular rational subsets, the localized ring is Tate: \(s_U\) or \(s_V\) becomes invertible, hence both \(p\) and \([w]\) become invertible; the image of \(p\) remains topologically nilpotent. Thus \(p\) is a topologically nilpotent unit.

However, the universal property alone does not prove the displayed isomorphisms. It produces a map to \(B^I\) after checking the displayed fractions are power-bounded. To prove it is an isomorphism, you must show that:

- both sides contain the same dense algebra \(B_{F,\mathbf Q_p}\);
- the rational-localization topology and the \(\lambda_I\)-Banach topology are equivalent.

This can be done explicitly from the fractions above, or via Kedlaya’s Lemma 4.9. It is a genuine theorem, not bookkeeping.

The plus-ring statement must be corrected. Huber’s rational plus ring is formed from the integral closure of

\[
A^+\left[\frac{t}{s}:t\in T\right]
\]

in the localization, not from the integral closure of the image of \(A^+\) alone. Thus for \(U_0\) it must at least contain

\[
\frac{[w]}p,\qquad \frac{p^a}{[w]^b},
\]

and analogously for \(V_0\). This is part of the standard rational-localization construction in [Wedhorn §8.1](https://arxiv.org/pdf/1910.05934). If you want this plus ring to equal Kedlaya’s unit ball \(B^{I,+}=\{\lambda_I\le1\}\), that equality is another lemma. It is unnecessary for sheafiness: transport the actual rational plus ring across the topological-ring isomorphism and apply 8.28(b).

Also record explicitly that Kedlaya’s Banach Tate algebra \(B^I\{T_1,\dots,T_n\}\) agrees topologically with the Huber Tate algebra used in your definition of strong noetherianity.

6. **For \(Y\), the local criterion works; for \(X\), substantial descent/gluing is missing.**

For \(Y\), the following is enough:

1. Equip \(Y\) with the restriction of the standard pre-adic structure on \(\operatorname{Spa}(A_{\inf},A_{\inf})\).
2. Identify every \(U_n,V_n\), as a pre-adic open subspace, with the appropriate \(\operatorname{Spa}(B^I,C^+)\).
3. Prove these identifications respect restriction maps, not just underlying points.
4. Apply strong noetherianity and Wedhorn 8.28(b).

Sheafiness is local once these are genuinely open affinoid subspaces; Wedhorn’s local criterion is [Remark 8.27](https://arxiv.org/pdf/1910.05934).

For \(X\), a topological quotient and homeomorphisms

\[
U_0\xrightarrow{\sim}q(U_0),\qquad
V_0\xrightarrow{\sim}q(V_0)
\]

do not define a locally valued ringed space. You must either:

- define
  \[
  \mathcal O_X(W)
    =\mathcal O_Y(q^{-1}W)^{\varphi^{\mathbf Z}}
  \]
  and similarly descend the plus sheaf and stalk valuations; or
- glue the two affinoid charts using the Frobenius transition maps.

The overlap has real content. Under the convention \(\kappa(\varphi x)=p\kappa(x)\), it has two pieces:

- the common boundary \(\kappa=c\), with identity transition;
- the boundary \(\kappa=1\) in \(U_0\), identified by \(\varphi\) with \(\kappa=p\) in \(V_0\).

These transition maps must be morphisms of affinoid adic spaces and satisfy the cocycle condition. Only after constructing this pre-adic quotient and proving that \(q\) is locally an isomorphism does the sheafy-affinoid cover imply that \(X\) is an adic space. Kedlaya correspondingly defines the quotient in the category of locally \(v\)-ringed spaces, not merely topological spaces; see [AWS §3.1](https://swc-math.github.io/aws/2017/2017KedlayaNotes.pdf).

So the corrected dependency chain is:

\[
\text{Gauss norms}
\to B^I
\to
\bigl(\mathcal O(U_n)\cong B^{I_n}\bigr)
\to
Y\text{ pre-adic and sheafy}
\to
\varphi\text{-equivariant locally ringed descent}
\to
X\text{ adic}.
\]

The current plan stops before the two arrows in the middle.
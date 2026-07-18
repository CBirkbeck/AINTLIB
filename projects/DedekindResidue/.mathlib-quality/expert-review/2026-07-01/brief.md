# Review brief — Effective residue of the Dedekind zeta function

*Prepared 2026-07-01 for an external number theorist. Self-contained: no repository access
required. We are at the **planning** stage — no substantial proof has been written yet — and
we want a soundness check on the overall strategy before committing to a long build.*

---

## 1. Goal

We aim to formalise, in the Lean 4 / mathlib proof assistant and completely (no unproved
placeholders, no extra axioms), the main effective theorem of

> K. Belabas and E. Friedman, *Computing the residue of the Dedekind zeta function*,
> Mathematics of Computation **84** (2015), 357–369 (arXiv:1305.0035).

Let $K$ be a number field of degree $n = [K:\mathbb{Q}] > 1$, with absolute discriminant
$\Delta_K = |d_K|$, and let
$$\kappa_K \;=\; \operatorname*{Res}_{s=1} \zeta_K(s)$$
be the residue at $s=1$ of the Dedekind zeta function. The target is:

> **Theorem 1 (Belabas–Friedman).** Assume the Generalized Riemann Hypothesis for $\zeta_K$
> and the Riemann Hypothesis for $\zeta_\mathbb{Q}$. Then for every real $X \geq 69$,
> $$\bigl|\log\kappa_K - f_K(X)\bigr| \;\leq\; \frac{2.324\,\log\Delta_K}{\sqrt{X}\,\log(3X)}
> \left(\Bigl(1+\tfrac{3.88}{\log(X/9)}\Bigr)\Bigl(1+\tfrac{2}{\sqrt{\log\Delta_K}}\Bigr)^2
> + \frac{4.26\,(n-1)}{\sqrt{X}\,\log\Delta_K}\right),$$
> where $f_K(X)$ is an explicit finite sum over prime-ideal powers of norm below $X$
> (defined in §4).

We also intend the sharper variants **Theorem 7** and **Corollary 8** of the same paper.

**The single hard constraint that shapes everything below.** The only assumption permitted in
the final statements is GRH, threaded as an ordinary hypothesis (not an added axiom); every
other ingredient — in particular the analytic substrate of $\zeta_K$ — must be genuinely
proved. And we want the theorem for a **general** number field $K$, not merely for abelian
extensions of $\mathbb{Q}$. As will become clear, this constraint forces us to build the full
Hecke functional equation of $\zeta_K$ from the ground up, which is the main subject we would
like reviewed.

**Motivation.** By the analytic class number formula,
$$\kappa_K = \frac{2^{r_1}(2\pi)^{r_2}\,R_K\,h_K}{w_K\sqrt{\Delta_K}},$$
so a rigorously certified approximation to $\kappa_K$ yields a certified value of the product
$h_K R_K$ of class number and regulator — the halting datum of Buchmann's class-group and
regulator algorithm. The formula itself is already available in mathlib, so our theorem plugs
directly into that downstream application.

---

## 2. Background and references

### 2.1 Setting and conventions

Throughout, $K$ is a number field with ring of integers $\mathcal{O}_K$, $r_1$ real and $r_2$
complex places ($n = r_1 + 2r_2$), $w_K$ roots of unity, regulator $R_K$, class number $h_K$.
Prime ideals are $\mathfrak{p}$; $N\mathfrak{p}$ is the absolute norm. We write
$\zeta_K(s) = \sum_{\mathfrak{a}} N\mathfrak{a}^{-s} = \prod_{\mathfrak p}(1-N\mathfrak p^{-s})^{-1}$
for $\operatorname{Re}s > 1$. The completed zeta function is
$$\Lambda_K(s) = \Delta_K^{s/2}\,\Gamma_\mathbb{R}(s)^{r_1}\,\Gamma_\mathbb{C}(s)^{r_2}\,\zeta_K(s),
\qquad \Gamma_\mathbb{R}(s)=\pi^{-s/2}\Gamma(\tfrac s2),\ \ \Gamma_\mathbb{C}(s)=2(2\pi)^{-s}\Gamma(s),$$
which continues meromorphically to $\mathbb{C}$ with simple poles only at $s=0,1$ and satisfies
$\Lambda_K(s)=\Lambda_K(1-s)$. Nontrivial zeros are written $\rho = \tfrac12 + i\gamma_\rho$.
Euler's constant is $C = 0.5772\ldots$.

### 2.2 References

- **[BF15]** K. Belabas, E. Friedman. *Computing the residue of the Dedekind zeta function.*
  Math. Comp. 84 (2015), 357–369; arXiv:1305.0035. — the paper we formalise.
- **[Bach95]** E. Bach. *Improved approximations for Euler products.* In *Number Theory
  (Halifax, 1994)*, CMS Conf. Proc. 15, AMS 1995, 13–28. — the result [BF15] improves.
- **[Weil52]** A. Weil. *Sur les "formules explicites" de la théorie des nombres premiers.*
  Comm. Sém. Math. Univ. Lund (1952), 252–265. — the explicit formula.
- **[Poitou77]** G. Poitou. *Sur les petits discriminants.* Séminaire Delange–Pisot–Poitou
  1976/77, exp. 6. — the simplified form of the explicit formula used by [BF15].
- **[Stark74]** H. M. Stark. *Some effective cases of the Brauer–Siegel theorem.* Invent.
  Math. 23 (1974), 135–152. — the sum-over-zeros formula (eq. 19 of [BF15]).
- **[Davenport]** H. Davenport. *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer 2000.
  — classical facts about the zeros of $\zeta_\mathbb{Q}$.
- **[Buchmann90]** J. Buchmann. *A subexponential algorithm for the determination of class
  groups and regulators of algebraic number fields.* Sém. Théorie des Nombres Paris 1988–89,
  Progr. Math. 91, Birkhäuser 1990, 27–41. — the downstream application.
- **[Lang]** S. Lang. *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994. — Ch. XIII–XIV
  (Hecke's functional equation via theta), Ch. XVII (explicit formulas).
- **[Neukirch]** J. Neukirch. *Algebraic Number Theory*, Springer 1999. — Ch. VII §5–8
  (Hecke $L$-functions, theta, functional equation).
- **[Tate]** J. Tate. *Fourier analysis in number fields and Hecke's zeta-functions* (thesis),
  in Cassels–Fröhlich, *Algebraic Number Theory*, 1967. — the adelic route to the same FE.

### 2.3 State of the art in the formalisation

mathlib currently contains: the Dedekind zeta function as a Dirichlet series and its Euler
product (convergent region only); the analytic class number formula for $\kappa_K$; all the
arithmetic invariants ($h_K$, $R_K$, $\Delta_K$, $w_K$, $r_1$, $r_2$, ideal norm); the Riemann
zeta function complete with functional equation, meromorphic continuation, and the statement of
RH; Dirichlet $L$-functions complete with their functional equation and root numbers; the
Deligne $\Gamma$-factors, the digamma function, and Euler's constant with explicit bounds; the
Mellin and Fourier transforms, one-dimensional Poisson summation, an abstract Mellin-based
functional-equation package, bounded-variation theory; the Minkowski embedding of $\mathcal O_K$
as a lattice with its covolume and a fundamental domain for the unit action; and the
one-variable and multivariable Fourier series on tori.

What mathlib does **not** contain, and what we must therefore build:
1. the meromorphic continuation and functional equation of $\zeta_K$ (equivalently $\Lambda_K$)
   for a **general** number field $K$ — mathlib has this only for $\mathbb{Q}$ and for
   Dirichlet $L$-functions, and a companion project has it only for cyclotomic fields (both
   are abelian and rest on the factorisation $\zeta_K = \prod_\chi L(\chi,s)$, which is false
   for non-abelian $K$);
2. any explicit formula (Riemann–von Mangoldt / Weil / Poitou) for any zeta function;
3. the sum-over-zeros identity of Stark (eq. 19 below);
4. $n$-dimensional Poisson summation over a lattice, the dual lattice, the multivariate
   Gaussian theta transformation, and an Epstein-type lattice theta function.

To our knowledge no formalisation of the general Dedekind functional equation exists in any
proof assistant.

---

## 3. Strategy

We work strictly bottom-up, in four tiers. Everything above the substrate is field-agnostic
and reused verbatim for all $K$; the substrate is where the general-vs-abelian question lives.

- **Tier 1 — analytic substrate (the largest part).** Construct $\Lambda_K$, prove its
  meromorphic continuation, the functional equation $\Lambda_K(s)=\Lambda_K(1-s)$, the residue
  at $s=1$ (matching $\kappa_K$), the Hadamard product, and the zero set. Because
  $\zeta_K = \prod L(\chi)$ fails for non-abelian $K$, we take **Hecke's route**: build the
  theta function of the ideal lattice under the Minkowski embedding, prove its transformation
  law by $n$-dimensional Poisson summation, take a Mellin transform to obtain $\Lambda_K$, and
  read off the FE from the theta transformation, summing over the ideal class group.
- **Tier 2 — the Weil–Poitou explicit formula** (§5, identity (E)), obtained by contour
  integration of $-\Lambda_K'/\Lambda_K$ against a test function, using Tier 1 and the Euler
  product.
- **Tier 3 — the paper's own analytic estimates.** Stark's sum-over-zeros formula and the
  $O(\log\Delta_K)$ bound; the auxiliary test function $F_{s,X}$ and its Fourier transform
  (Lemma 2); the application of the explicit formula to $F_{s,X}$ with analytic continuation to
  $\operatorname{Re}s>\tfrac12$ (Lemma 3); the "$T$ and $T-a$" difference trick (Lemma 4); and
  finally Theorem 1, Theorem 7, Corollary 8.
- **Bridge.** Combine the bound with the analytic class number formula to expose the certified
  error on $\log(h_K R_K)$.

GRH enters only in Tier 3 (Lemma 3 onward), exactly where [BF15] uses it.

---

## 4. Definitions

**Definition 4.1 (the computable approximant).** For $\operatorname{Re}s>1$ set, following the
naïve partial sum of $\log\zeta_K$,
$$B_K(X) = \sum_{\substack{\mathfrak p,\,m\ \geq 1 \\ N\mathfrak p^{m}<X}}
\frac{\log N\mathfrak p}{N\mathfrak p^{m/2}}
\left(\frac{\sqrt{X}\,\log X}{N\mathfrak p^{m/2}\,\log N\mathfrak p^{m}}-1\right),
\qquad
f_K(X) = \frac{3\bigl(B_K(X)-B_K(X/9)\bigr)}{2\sqrt X\,\log(3X)}.$$
These are the finite sums that Theorem 1 bounds against $\log\kappa_K$.

**Definition 4.2 (auxiliary function).** With $h=s-\tfrac12$ and $T=\log X$, put
$g_s(t)=e^{-h|t|}/|t|$ and
$$F_{s,X}(t) = \begin{cases} 1, & |t|\leq T,\\[2pt] \dfrac{T}{|t|}\,e^{-h(|t|-T)}, & |t|>T.\end{cases}$$
This is the test function fed to the explicit formula; its Fourier transform is Lemma 2.

**Definition 4.3 (GRH hypothesis).** We formulate GRH for $\zeta_K$ as: *every zero of
$\Lambda_K$ lies on the line $\operatorname{Re}s=\tfrac12$.* Since $\Lambda_K$ has no trivial
zeros (the $\Gamma$-factors cancel them) and its only poles are at $s=0,1$, this is exactly the
statement that all nontrivial zeros of $\zeta_K$ have real part $\tfrac12$, i.e. $\gamma_\rho
\in \mathbb{R}$ in the notation of [BF15, p. 3]. Under the functional equation this is
equivalent to "$\zeta_K(s)\neq 0$ for $\operatorname{Re}s>\tfrac12$", the form stated in
[BF15]. The companion hypothesis for $\zeta_\mathbb{Q}$ is the ordinary Riemann Hypothesis.

We take $\kappa_K$ itself directly from the already-formalised analytic class number formula,
so it needs no new definition.

---

## 5. The results to be proved (with sketches)

We state the tier structure as the mathematician would read it. Nothing here is proved yet;
the sketches are the intended arguments, drawn from the cited sources.

**(FE) Functional equation of $\Lambda_K$.** *$\Lambda_K$ continues to a meromorphic function
on $\mathbb{C}$, holomorphic except for simple poles at $s=0,1$, with
$\operatorname*{Res}_{s=1}\Lambda_K = $ (an explicit archimedean constant)$\cdot\kappa_K$, and
$\Lambda_K(s)=\Lambda_K(1-s)$.*

> *Sketch (Hecke, [Lang XIII–XIV], [Neukirch VII]).* For each ideal class $\mathfrak c$ form
> the partial zeta function $\zeta_K(s,\mathfrak c)$; via the Minkowski embedding it becomes a
> Mellin transform of a theta function $\Theta_{\mathfrak c}(t)=\sum_{x\in\mathfrak a} e^{-\pi
> t Q(x)}$ over a fractional ideal $\mathfrak a$ representing $\mathfrak c^{-1}$, integrated
> over a fundamental domain of the totally-positive-unit action. The transformation law
> $\Theta(1/t)=(\text{covolume factor})\,t^{n/2}\,\Theta^{*}(t)$ follows from Poisson summation
> on the ideal lattice together with the fact that the Gaussian is its own Fourier transform;
> the covolume factor is $\Delta_K^{-1/2}$. Splitting the Mellin integral at $t=1$ and applying
> the theta law gives the meromorphic continuation and the symmetry $s\leftrightarrow 1-s$,
> summed over the finite class group. ∎

This decomposes into three genuinely new pieces, each a self-contained sub-project:

- **(P) $n$-dimensional Poisson summation.** *For a full lattice $L$ in a finite-dimensional
  real inner-product space $V$, with dual lattice $L^{*}$ and covolume $\operatorname{covol}(L)$,
  and a Schwartz function $f$, one has $\sum_{x\in L} f(x) = \operatorname{covol}(L)^{-1}
  \sum_{y\in L^{*}} \widehat f(y)$.* Route: define the dual lattice (not currently in mathlib);
  prove Poisson for $\mathbb{Z}^n$ by generalising the existing one-dimensional proof to the
  $n$-torus (the multivariate Fourier basis is available); transport to a general lattice by a
  linear change of variables, picking up the covolume Jacobian.
- **(Θ) Lattice Gaussian theta.** *The transformation law for $\Theta_L(t)=\sum_{x\in L}
  e^{-\pi t\|x\|^2}$*, from (P) applied to the Gaussian plus the $n$-dimensional Gaussian
  Fourier self-duality (assembled from the one-dimensional case).
- **(H) Hecke construction.** *The ideal-lattice theta, the integral over the unit fundamental
  domain, the sum over the class group, and the identification of the Mellin transform with
  $\Lambda_K$.* This is the deepest node and the one place we expect to lean hardest on the
  book references ([Lang]/[Neukirch]/[Tate]).

**(EF) Weil–Poitou explicit formula.** *For an admissible even test function $F$ (with the
integrability / bounded-variation side conditions of [Weil52]/[Poitou77]) and its Fourier
transform $\widehat F$,*
$$\sum_{\rho}\widehat F(\gamma_\rho) = -2\sum_{\mathfrak p,m}\frac{\log N\mathfrak p}{N\mathfrak p^{m/2}}F(m\log N\mathfrak p) + F(0)\bigl(\log\Delta_K - nC - n\log(8\pi) - r_1\tfrac{\pi}{2}\bigr) + (\text{archimedean integrals}),$$
*the sum on the left over nontrivial zeros.*

> *Sketch.* Integrate $-\tfrac{1}{2\pi i}\,\Lambda_K'/\Lambda_K$ (equivalently, use the Hadamard
> product) against the Mellin transform of $F$ over a vertical strip and shift the contour past
> the critical line, using (FE) to fold the two sides together; the prime sum is the logarithmic
> derivative of the Euler product, and the archimedean terms are the logarithmic derivatives of
> the $\Gamma$-factors. ∎

**(St) Stark's formula** ([Stark74], [BF15] eq. 19). *For $\sigma>1$,
$\sum_{\rho}\frac{1}{\sigma-\rho} = \tfrac12\log\Delta_K + \frac{1}{\sigma-1} + \frac1\sigma -
\tfrac12 d_{K,\sigma}$, where $d_{K,\sigma}$ is an explicit combination of $-\zeta_K'/\zeta_K$
and digamma values; consequently $\sum_{\rho}(\tfrac14+\gamma_\rho^2)^{-1} = O(\log\Delta_K)$.*

> *Sketch.* Logarithmic derivative of the Hadamard product of $\Lambda_K$, combined with the
> functional equation and the duplication formula for $\Gamma$. Depends on (FE). ∎

**(L2) Fourier transform of $F_{s,X}$** ([BF15] Lemma 2). *An explicit closed form for
$\widehat{F_{s,X}}(\gamma)$.* — elementary calculus (two integrations by parts) once
$F_{s,X}$ and the Fourier integral are in place; **independent of the substrate**, hence our
first concrete target above the definitions.

**(L3) Explicit formula at $F_{s,X}$** ([BF15] Lemma 3, eq. 13). *An identity valid first for
$\operatorname{Re}s>1$, then continued to $\operatorname{Re}s>\tfrac12$ using GRH (which makes
$\gamma_\rho^2+h^2\neq 0$).* From (EF) and (L2).

**(L4) The "$T$ and $T-a$" trick** ([BF15] Lemma 4, eq. 14). *A difference of two instances of
(L3) that avoids the loss of a factor $\log X$.* From (L3), by the mean value theorem and
monotonicity of certain explicit integrals.

**(Main) Theorem 1**, then **Theorem 7 / Corollary 8.** From (L4) with $k=\mathbb{Q}$,
$a=\log 9$, $T=\log X$, together with (St) for the $\zeta_K$ zero-sum, the classical value
$\sum_\rho(\tfrac14+\gamma_\rho^2)^{-1}=0.0230\ldots$ for $\zeta_\mathbb{Q}$ ([Davenport §12]),
and elementary constant-chasing.

---

## 6. What is already in place

- The paper's **own explicit functions** — $g_s$, $F_{s,X}$, and $f_K$ (via $B_K$) — are
  formalised as real definitions matching Definitions 4.1–4.2. (The prime-ideal-power indexing
  of $B_K$ is drafted but not yet finalised.)
- The **GRH hypothesis** (Definition 4.3) is formalised.
- The **statement** of Theorem 1 is written down in full and type-checks against the
  already-available $\kappa_K$, $\Delta_K$, $n$.
- Everything listed as "available" in §2.3 is reused directly; in particular $\kappa_K$ and the
  analytic class number formula are taken as given.

Nothing above the definitions is proved yet — this brief is precisely to sanity-check the plan
before we start.

---

## 7. The critical strategic decision

The whole difficulty is concentrated in **(FE)** and its sub-pieces **(P)/(Θ)/(H)**. We have
verified that neither of the two "cheap" routes yields the general theorem:

- The **abelian route** $\zeta_K=\prod_\chi L(\chi,s)$ (which underlies the existing cyclotomic
  formalisation) produces $\Lambda_K$ and its FE **only for abelian $K$**, and even then leaves
  two genuine gaps: that the product of root numbers $\prod_\chi W_\chi = 1$ (the Artin root
  number of the regular representation), and the conductor–discriminant identity $\Delta_K =
  \prod_\chi \mathfrak f_\chi$. Neither is currently formalised.
- The **Artin route** $\zeta_K=\prod_\rho L(\rho,s)^{\dim\rho}$ needs Artin $L$-functions,
  which are entirely absent from the library.

We have therefore committed to building the general **Hecke theta stack** (P)→(Θ)→(H)→(FE), so
that $\Lambda_K$, the FE, and hence GRH and Theorem 1 are genuinely general. This is a large
undertaking — (P) alone is a worthwhile self-contained analysis result — and it is the main
thing we would like a second opinion on before starting.

---

## 8. Where the risk is

**8.1 The Hecke construction (H).** The passage from "theta transformation law" to "functional
equation of $\Lambda_K$" for a general field involves the unit action (integration over a
fundamental domain of the totally positive units modulo torsion, dimension $r_1+r_2-1$) and the
sum over the class group. The Minkowski-embedding lattice, its covolume, and a fundamental
domain for the unit action are available; the theta function itself, the class-group sum, and
the precise archimedean $\Gamma$-factor bookkeeping are not. We are unsure how heavy the
"fundamental domain / unit action" part will be in practice, and whether the cleanest
formalisation follows Hecke's classical theta argument ([Lang]/[Neukirch]) or Tate's adelic
reformulation.

**8.2 The dual lattice (P.1).** $n$-dimensional Poisson needs the dual lattice $L^{*}$ and the
identity $\operatorname{covol}(L^{*})=\operatorname{covol}(L)^{-1}$; there is no dual lattice in
the library yet. This is elementary but load-bearing.

**8.3 The explicit formula (EF).** We plan to derive it by contour integration of
$-\Lambda_K'/\Lambda_K$; the analytic side conditions on the test function in [Weil52]/
[Poitou77] (bounded variation of $F(x)e^{(1/2+\varepsilon)x}$ and of $(F(0)-F(x))/x$,
average-of-jump conventions) are fiddly and we want to be sure we state the admissibility class
correctly.

**8.4 The estimates (Tier 3).** These are the paper's own content and look routine given the
substrate, but they involve delicate real-analysis bounds (monotonicity of the integrals
$q(T),\tilde q(T)$; the decreasing function $\beta(U)$; the numerical constants $2.324$, $3.88$,
$4.26$). We would like to know whether any of these steps are subtler than the paper's terse
presentation suggests.

---

## 9. Questions for the reviewer

**Q1 (overall decomposition).** Does the four-tier decomposition in §3 — substrate → explicit
formula → Stark + auxiliary estimates → Theorem 1 — faithfully mirror the logical structure of
[BF15], or have we mis-placed a dependency (for instance, does any Tier-3 step secretly need
more of the substrate than we have allowed for)?

**Q2 (the substrate route).** Is the Hecke theta route (P)→(Θ)→(H)→(FE) the right and most
efficient path to the general Dedekind functional equation for a formalisation, or is there a
cleaner route we are missing? In particular: would you build (H) along Hecke's classical
theta-and-fundamental-domain lines ([Lang XIII–XIV], [Neukirch VII]) or along Tate's adelic
lines, and which is likely to be less painful to formalise?

**Q3 (abelian stepping stone).** Is it worth first doing the abelian case as a stepping stone
(reusing Dirichlet $L$-function machinery and closing the two gaps $\prod W_\chi=1$ and the
conductor–discriminant identity), both as a sanity check and to have *some* general-looking
result early — or is that a detour that shares little with the general theta construction and
should be skipped?

**Q4 (GRH and the gap inventory).** Is our GRH formulation (Definition 4.3 — all zeros of
$\Lambda_K$ on the critical line) the correct and cleanest one for this application, given the
paper uses "$\gamma_\rho\in\mathbb{R}$" and also "$\zeta_K(s)\neq0$ for $\operatorname{Re}s
>\tfrac12$"? And is our inventory of substrate gaps — dual lattice, multivariate Gaussian theta,
Hecke construction; plus (for the abelian shortcut only) $\prod W_\chi=1$ and the
conductor–discriminant identity; plus the explicit formula and Stark's formula — correct and
complete, or are we forgetting a prerequisite (e.g. a growth/order estimate needed for the
Hadamard product, or a convergence subtlety in the sum over zeros)?

**Q5 (hidden pitfalls).** Are there hidden pitfalls in either (a) the paper's estimates — any
step in Lemmas 2–5 or the proof of Theorem 1 that is subtler than its terse write-up suggests,
or relies on an unstated convention — or (b) the substrate, e.g. the precise archimedean
constant in $\operatorname{Res}_{s=1}\Lambda_K$, the conditional convergence of $\sum_\rho
\widehat F(\gamma_\rho)$, or the admissibility conditions on the explicit-formula test function?

We would be grateful for a paragraph on each, and especially for a clear verdict on Q2, which
governs how we spend the next several months.

---

## 10. Document metadata

- Project: effective residue of the Dedekind zeta function (formalisation of [BF15]).
- Stage: planning complete; substrate build not yet started.
- What is formalised: the paper's auxiliary functions and $f_K$; the GRH hypothesis; the
  statement of Theorem 1. Nothing above the definitions is proved.
- Prepared: 2026-07-01.

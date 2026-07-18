import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import DedekindResidue

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Computing the residue of the Dedekind zeta function — Lean blueprint" =>

This is the blueprint for the `DedekindResidue` formalisation of
**Belabas–Friedman, _Computing the residue of the Dedekind zeta function_**
(arXiv:1305.0035), **Theorem 1**: under the Generalized Riemann Hypothesis, the residue
$`\kappa_K = \operatorname{Res}_{s=1}\zeta_K` of the Dedekind zeta function of a number
field $`K` of degree $`n > 1` is computable from prime-power data below a cutoff $`X`,
with a fully explicit error bound. GRH enters as a `Prop` hypothesis — never an axiom —
and every other ingredient is genuinely proven: the axiom footprint of every public
declaration is $`\{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}`.

The development has four layers. **SP1** constructs the completed zeta function by the
classical Hecke theta route (Poisson summation over lattices, theta inversion, Hecke
theta series over ideal classes, Mellin transform) so that the GRH statement quantifies
over a genuinely inhabited characterisation. **SP1-AC** provides Hadamard-free analytic
control: Stirling-free $`\Gamma`-strip bounds, strip decay of the entire completion,
Jensen zero-counting, and Landau-style local partial fractions for the logarithmic
derivative. **SP2** proves the Weil–Poitou explicit formula by expanding-rectangle
contour integration, following Poitou's exposé (_Sur les petits discriminants_,
Séminaire DPP 1976/77). **SP3** discharges every hypothesis of the explicit formula at
the Belabas–Friedman test function $`F_{s,X}`, and the Tier-3 spine (this frontier)
walks their Lemma 3 → Lemma 4 → Theorem 1.

Each node carries a `(lean := …)` reference to the actual declaration, so the graph
reads completion status directly from Lean.

# The target: Theorem 1 and the auxiliary function

:::definition "aux-g" (lean := "DedekindResidue.gAux")
For $`s \in \mathbb{C}` the kernel of Belabas–Friedman eq. (6) is
$$`g_s(t) = \frac{e^{-(s-1/2)\,|t|}}{|t|},`
an even function of $`t \neq 0`, exponentially decaying when
$`\operatorname{Re} s > 1/2`.
:::

:::definition "aux-f" (lean := "DedekindResidue.auxF")
The **auxiliary test function** of Belabas–Friedman (eqs. (11)–(12)): with
$`T = \log X` and $`h = s - 1/2`,
$$`F_{s,X}(t) = \begin{cases} 1 & |t| \le T, \\[2pt]
\dfrac{T}{|t|}\, e^{-h(|t|-T)} & |t| > T, \end{cases}`
i.e. the plateau $`1` up to the cutoff and the normalised kernel
$`g_s(t)/g_s(T)` beyond it. It is even and continuous. Depends on:
{uses "aux-g"}[]
:::

:::definition "b-sum" (lean := "DedekindResidue.bSum")
The prime-power sum $`B_K(X)` of Belabas–Friedman (p. 2):
$$`B_K(X) = \sum_{\substack{\mathfrak{p},\,m \\ N\mathfrak{p}^m < X}}
\frac{\log N\mathfrak{p}}{N\mathfrak{p}^{m/2}}
\left( \frac{\sqrt{X}\,\log X}{N\mathfrak{p}^{m/2}\,\log N\mathfrak{p}^m} - 1 \right),`
a finite sum over prime-ideal powers of norm below the cutoff.
:::

:::definition "b-sum-rel" (lean := "DedekindResidue.bSumRel")
The **relative** sum $`B_K(X) - B_\mathbb{Q}(X)`: the paper's convention
$`\sum^{K-k}` subtracts the corresponding rational-prime sum ($`k = \mathbb{Q}`),
which removes the pole contribution common to $`\zeta_K` and $`\zeta_\mathbb{Q}`.
Depends on: {uses "b-sum"}[]
:::

:::definition "f-K" (lean := "DedekindResidue.fK")
The computable approximation to $`\log \kappa_K`:
$$`f_K(X) = \frac{3\,\bigl(B_K(X) - B_K(X/9)\bigr)}{2\sqrt{X}\,\log(3X)}`
with $`B_K` the relative sum. The difference at the two cutoffs $`X` and $`X/9`
implements the paper's $`T` vs. $`T - a` trick ($`a = \log 9`), which cancels the
oscillating sine terms of the explicit formula. Depends on: {uses "b-sum-rel"}[]
:::

# The completed zeta function (SP1)

:::theorem "poisson-zn" (lean := "DedekindResidue.tsum_eq_tsum_fourier_zpoint")
**Poisson summation over $`\mathbb{Z}^\iota`.** Let $`g` be a continuous function on
euclidean $`\mathbb{R}^\iota` whose translate norms are summable on compacts and whose
Fourier transform values at lattice points are summable. Then
$$`\sum_{n \in \mathbb{Z}^\iota} g(n) = \sum_{m \in \mathbb{Z}^\iota} \widehat{g}(m).`
:::

:::proof "poisson-zn"
The periodization $`P(x) = \sum_n g(x+n)` descends to a continuous function on the
torus $`(\mathbb{R}/\mathbb{Z})^\iota`; its multidimensional Fourier coefficient at
$`m` is exactly $`\widehat{g}(m)` (unfold the box integral against the character,
interchange sum and integral, and reassemble the box translates into
$`\int_{\mathbb{R}^\iota}`). Evaluating the uniformly convergent Fourier series of
$`P` at $`x = 0` gives the identity.
:::

:::theorem "dual-lattice-covolume" (lean := "DedekindResidue.covolume_dualZLattice_mul")
For a full $`\mathbb{Z}`-lattice $`L` in a euclidean space, the dual lattice
$`L^\sharp = \{y : \langle x, y\rangle \in \mathbb{Z} \ \forall x \in L\}` satisfies
$$`\operatorname{covol}(L^\sharp)\cdot\operatorname{covol}(L) = 1.`
:::

:::theorem "theta-inversion" (lean := "DedekindResidue.thetaLattice_transform")
**Lattice theta inversion.** For a full lattice $`L \subset \mathbb{R}^n` and $`t > 0`,
the Gaussian theta series $`\Theta_L(t) = \sum_{v \in L} e^{-\pi t \lVert v\rVert^2}`
satisfies
$$`\Theta_L(t) = \operatorname{covol}(L)^{-1}\, t^{-n/2}\, \Theta_{L^\sharp}(1/t).`
:::

:::proof "theta-inversion"
Apply Poisson summation {uses "poisson-zn"}[] transported to $`L` by a lattice basis;
the Fourier transform of the Gaussian $`e^{-\pi t\lVert x\rVert^2}` is
$`t^{-n/2} e^{-\pi \lVert \xi\rVert^2 / t}`, and the change of variables produces the
covolume factor and the dual lattice {uses "dual-lattice-covolume"}[].
:::

:::theorem "hecke-theta-inversion" (lean := "DedekindResidue.heckeTheta_inversion, DedekindResidue.heckeG_inversion")
**Hecke theta inversion.** For a fractional ideal $`I` of $`K`, the multivariable
theta series $`\Theta_I(c)` attached to the ideal lattice of $`I` (one Gaussian weight
$`c_v` per infinite place) satisfies the inversion law
$$`\Theta_I(c) = \operatorname{covol}(L_I)^{-1}\Bigl(\prod_v c_v\Bigr)^{-1/2}
\Theta_{I^\vee}(c^\vee),`
where $`I^\vee` is the (conjugated, scaled) trace-dual ideal and $`c^\vee` the dual
weight vector. Averaging over the unit box in logarithmic coordinates yields the
one-parameter function $`g_I(t)` with
$`g_I(t) = \operatorname{covol}(L_I)^{-1} t^{-1/2} g_{I^\vee}(4^{2r_2}/t)`.
Depends on: {uses "theta-inversion"}[]
:::

:::theorem "class-theta-symmetry" (lean := "DedekindResidue.heckeGClass_inversion, DedekindResidue.heckeF")
**The normalised class theta has an exact functional symmetry.** Normalising
$`\widehat{G}_C(x) = g_I\bigl(N(I)^{-2}\beta x\bigr)` with
$`\beta = 4^{r_2}/|\Delta_K|` makes the inversion coefficient exactly $`1`:
$$`\widehat{G}_C(1/x) = \sqrt{x}\; \widehat{G}_{C^\vee}(x).`
Summing over the ideal class group gives the total theta $`f(x)` with
$`f(1/x) = \sqrt{x} f(x)`. Depends on: {uses "hecke-theta-inversion"}[]
:::

:::definition "hecke-fe-pair" (lean := "DedekindResidue.heckeFEPair")
The total theta $`f`, its constant term $`f_0 = h_K \cdot w_K^{-1}\cdot
\operatorname{vol}`, and the symmetry {uses "class-theta-symmetry"}[] assemble into a
`WeakFEPair` with weight $`k = 1/2` and root number $`\varepsilon = 1` — the input to
mathlib's abstract functional-equation machinery, which returns an entire
$`\Lambda_0`, the meromorphic $`\Lambda` with poles exactly at $`\sigma \in \{0, 1/2\}`,
its Mellin representation, and the functional equation
$`\Lambda(1/2-\sigma) = \Lambda(\sigma)`.
:::

:::definition "is-completed-zeta" (lean := "DedekindResidue.IsCompletedDedekindZeta")
A function $`\Lambda : \mathbb{C} \to \mathbb{C}` **is a completed Dedekind zeta
function for $`K`** if (i) on $`\operatorname{Re} s > 1` it agrees with
$`|\Delta_K|^{s/2}\gamma_K(s)\,\zeta_K(s)` (the honest L-series region), and (ii)
there is an entire $`H` with $`H(s) = s(s-1)\Lambda(s)` for all $`s \notin \{0,1\}`.
The two conditions characterise $`\Lambda` off the poles; there are no junk values
or placeholder constructions.
:::

:::theorem "completed-zeta-unique" (lean := "DedekindResidue.IsCompletedDedekindZeta.eqOn")
Any two completed Dedekind zeta functions for $`K` agree away from $`\{0, 1\}`.
:::

:::proof "completed-zeta-unique"
Both entire extensions $`s(s-1)\Lambda(s)` agree on the half-plane
$`\operatorname{Re} s > 1`, a set with an accumulation point, so the identity theorem
forces them to agree everywhere; dividing by $`s(s-1)` off $`\{0,1\}` finishes.
Depends on: {uses "is-completed-zeta"}[]
:::

:::theorem "hecke-existence" (lean := "DedekindResidue.exists_isCompletedDedekindZeta")
**Hecke's theorem.** For every number field $`K` there exists
$`\Lambda : \mathbb{C}\to\mathbb{C}` which is a completed Dedekind zeta function for
$`K`. This makes the GRH predicate quantify over an inhabited class.
:::

:::proof "hecke-existence"
The witness is $`\Lambda(s) = \texttt{heckeAdjust}^{-1}\,\Lambda_{\mathrm{FE}}(s/2)`,
where $`\Lambda_{\mathrm{FE}}` is the abstract Mellin transform of the FE pair
{uses "hecke-fe-pair"}[]. The Mellin of the theta deviation is computed in closed
form: unfolding the unit-box average over the cone of each ideal class, a logarithmic
change of variables splits the integral into per-place $`\Gamma`-factors times
$`|N(y)|^{-2\sigma}`, and counting cone points by norm (torsion cancelling against
the theta's $`w_K^{-1}`) produces exactly
$`\beta^{-\sigma} M_0(\sigma) \sum_{\mathfrak{b}} N\mathfrak{b}^{-2\sigma}`. At real
$`\sigma > 1` this identifies $`\Lambda_{\mathrm{FE}}(s/2)` with the prefactor times
$`\zeta_K(s)` up to the $`s`-independent constant `heckeAdjust`; the identity theorem
extends the agreement, and the pole structure of the abstract $`\Lambda` gives the
entire extension of $`s(s-1)\Lambda`. Depends on: {uses "is-completed-zeta"}[]
{uses "class-theta-symmetry"}[]
:::

:::definition "completed-zeta" (lean := "DedekindResidue.completedDedekindZeta, DedekindResidue.completedDedekindZetaEntire")
The **completed Dedekind zeta function** `completedDedekindZeta` is the Hecke witness
of {uses "hecke-existence"}[], and `completedDedekindZetaEntire` is the entire
function $`H` with $`H(s) = s(s-1)\Lambda(s)` off $`\{0,1\}`, built from the abstract
$`\Lambda_0` plus explicit pole terms. Its zeros are the nontrivial zeros of
$`\zeta_K`.
:::

:::theorem "completed-zeta-fe" (lean := "DedekindResidue.completedDedekindZeta_one_sub")
**The functional equation** $`\Lambda_K(1-s) = \Lambda_K(s)`.
:::

:::proof "completed-zeta-fe"
The abstract functional equation $`\Lambda(1/2-\sigma) = \Lambda(\sigma)` of the FE
pair {uses "hecke-fe-pair"}[] at $`\sigma = s/2`, transported through the definition
of {uses "completed-zeta"}[] (the theta symmetry has coefficient exactly $`1`, so no
root number appears).
:::

:::definition "grh" (lean := "DedekindResidue.GeneralizedRiemannHypothesis")
**The Generalized Riemann Hypothesis for $`K`** (the paper's form): every completed
Dedekind zeta function $`\Lambda` for $`K` is nonvanishing on
$`\operatorname{Re} s > 1/2`, $`s \neq 1`. By the functional equation this pins all
nontrivial zeros to the critical line. Depends on: {uses "is-completed-zeta"}[]
:::

# Analytic control (SP1-AC)

:::theorem "landau-log-deriv" (lean := "DedekindResidue.norm_logDeriv_le_of_norm_le")
**The generic Landau lemma.** Let $`h` be holomorphic and zero-free on a ball
$`B(c, r)` with $`|h| \le m_S` on the ball and $`|h(c)| \ge m_L > 0`. Then on the
smaller ball $`B(c, r - 3/4)`,
$$`\left\lVert \frac{h'}{h} \right\rVert \le 32\,r\Bigl(\log\frac{m_S}{m_L} + 1\Bigr).`
:::

:::proof "landau-log-deriv"
$`\log h` exists on the convex ball (zero-free), its real part is controlled by the
sup bound, so the Borel–Carathéodory inequality bounds $`\log h` itself on an
intermediate ball; the Schwarz-type gradient estimate then bounds the derivative
$`h'/h = (\log h)'` on the smaller ball.
:::

:::theorem "h-strip-decay" (lean := "DedekindResidue.exists_H_strip_decay")
**Strip decay of the entire completion.** There is $`C` with
$$`\lVert H(z)\rVert \le C\,(1+|\operatorname{Im} z|)^{n_K+2}\,
e^{-n_K \pi |\operatorname{Im} z| / 4}`
on the strip $`-1 \le \operatorname{Re} z \le 2`, $`|\operatorname{Im} z| \ge 1`,
where $`H = ` {uses "completed-zeta"}[] (entire form).
:::

:::proof "h-strip-decay"
On the line $`\operatorname{Re} = 2` the Euler product bounds $`\zeta_K` and the
Stirling-free $`\Gamma`-strip uppers (exact $`|\Gamma(1/2+it)|^2 = \pi/\cosh \pi t`
plus a Phragmén–Lindelöf comparator) give a decaying bound; the functional equation
{uses "completed-zeta-fe"}[] transfers it to $`\operatorname{Re} = -1`, and
Phragmén–Lindelöf on the width-3 strip interpolates.
:::

:::theorem "zero-count" (lean := "DedekindResidue.exists_ball_zero_count")
**Jensen zero counting.** There is $`C_K` such that for every height $`T`, the number
of zeros of $`H` (with multiplicity) in the slab-covering ball at $`A + iT` is at most
$`C_K \log(2+|T|)`.
:::

:::proof "zero-count"
Jensen's formula on the normalised ratio $`g = H/H(c)`: the strip decay
{uses "h-strip-decay"}[] (extended to the right of the strip directly) bounds the
numerator, and the Euler product plus $`\Gamma`-lower bounds give the matching lower
bound at the centre, so the ratio is polynomially bounded and Jensen's sum of
$`\log(R/|z_i|)` terms is $`O(\log(2+|T|))`.
:::

:::theorem "partial-fractions" (lean := "DedekindResidue.exists_logDeriv_partial_fractions")
**Landau local partial fractions.** There is $`C` such that for $`|T| \ge A+5` and
$`s` in the slab ball around $`A + iT` with $`H(s) \neq 0`,
$$`\left\lVert \frac{H'}{H}(s) - \sum_{\rho} \frac{m_\rho}{s-\rho} \right\rVert
\le C \log(2+|T|),`
the sum over the zeros $`\rho` of $`H` in the covering ball, with multiplicities.
:::

:::proof "partial-fractions"
Peel the nearby zeros: a two-radius factorisation writes $`H = P \cdot g` with $`P`
the finite product over ball zeros and $`g` zero-free on the larger ball. The
cofactor's sup/centre ratio is controlled by {uses "h-strip-decay"}[] and the peeled
product bounds, so the generic Landau lemma {uses "landau-log-deriv"}[] bounds
$`g'/g`; the zero count {uses "zero-count"}[] keeps the peeled sum finite.
:::

:::theorem "digamma-bound" (lean := "DedekindResidue.exists_norm_digamma_le")
There is $`C` with $`\lVert \psi(\sigma+it)\rVert \le C\log(2+|t|)` for
$`-1 \le \sigma \le 2`, $`|t| \ge 2`, where $`\psi = \Gamma'/\Gamma`.
:::

:::proof "digamma-bound"
$`\psi = \operatorname{logDeriv}\Gamma` and the generic Landau lemma
{uses "landau-log-deriv"}[] on unit balls, fed by the window upper and lower
$`\Gamma`-bounds (downward recurrence for the upper, reflection for the lower).
:::

# The Weil–Poitou explicit formula (SP2)

:::definition "phi-transform" (lean := "DedekindResidue.paperPhi")
For a test function $`F`, its **$`\Phi`-transform** is
$$`\Phi_F(z) = \int_{\mathbb{R}} F(x)\, e^{(z - 1/2)x}\, dx,`
absolutely convergent on the band where $`F`'s exponential weight allows. On the
critical line $`\Phi_F(1/2 + i\gamma) = \widehat{F}(\gamma)` is the paper's Fourier
transform (`paperPhi_half_add_mul_I`), and for even $`F` one has the symmetry
$`\Phi_F(1-z) = \Phi_F(z)` (`paperPhi_one_sub`).
:::

:::theorem "argument-principle" (lean := "DedekindResidue.rectangleIntegral_mul_logDeriv_H")
**Rectangle argument principle.** For $`H` holomorphic and zero-free on the boundary
of a rectangle, and $`\Phi` holomorphic on the closed rectangle,
$$`\oint \Phi \,\frac{H'}{H} = 2\pi i \sum_{\rho} m_\rho\, \Phi(\rho),`
the sum over the divisor of $`H` in the open rectangle.
:::

:::proof "argument-principle"
Peel the zeros on an enlarged rectangle: $`H = (\prod_i (\zeta-\rho_i)^{m_i})\cdot g`
with $`g` zero-free, so $`H'/H = \sum m_i/(\zeta-\rho_i) + g'/g` pointwise. Goursat
kills the cofactor term, and each pole term contributes $`2\pi i\, m_i \Phi(\rho_i)`
by the rectangle Cauchy formula (`rectangleIntegral_cauchy`, proved by a dslope peel
and segment-wise fundamental theorem of calculus with explicit branch bookkeeping).
:::

:::theorem "zeros-in-strip" (lean := "DedekindResidue.re_mem_of_completedDedekindZetaEntire_eq_zero")
Every zero of the entire completion has $`0 \le \operatorname{Re}\rho \le 1`.
:::

:::proof "zeros-in-strip"
$`\zeta_K(s) \neq 0` for $`\operatorname{Re} s > 1` by the Euler product
(`dedekindZeta_ne_zero_of_one_lt_re`, via the Chebotarev project's prime-ideal
product), the prefactor and $`\Gamma`-factors are nonvanishing, so $`H \neq 0` right
of the strip; the functional equation {uses "completed-zeta-fe"}[] reflects the
statement to $`\operatorname{Re} s < 0`.
:::

:::theorem "good-heights" (lean := "DedekindResidue.exists_contour_height")
**Good contour heights.** There is a sequence $`T_n \to \infty` with
$`T_n \in [A+5+n, A+6+n]` along which $`H` is zero-free on the horizontal edges and
$$`\lVert H'/H \rVert \le C \log^2(2+T_n)`
there.
:::

:::proof "good-heights"
The zero count {uses "zero-count"}[] gives at most $`C\log` zeros per unit height, so
a pigeonhole choice of height stays $`\gtrsim 1/\log` away from every ordinate; the
partial-fraction expansion {uses "partial-fractions"}[] then bounds $`H'/H` by the
number of nearby zeros times the separation, i.e. $`\log^2`.
:::

:::theorem "zero-capture" (lean := "DedekindResidue.zero_capture_edge_form")
**Poitou's Proposition 1 (quantitative form).** For a test function whose
$`\Phi`-transform is holomorphic on the band and decays like $`B(T)` on horizontal
edges with $`B(T)\log^2 T \to 0`, the rectangle contour over
$`[-a, 1+a]\times[-T_n, T_n]` captures
$$`\sum_{\rho} m_\rho\,\Phi(\rho) \longrightarrow
\frac{1}{2\pi i}\ \text{(edge integrals)},`
with the horizontal-edge error $`2(1+2a)\,B(T_n)\,C\log^2(2+T_n) \to 0`.
Depends on: {uses "argument-principle"}[] {uses "good-heights"}[]
{uses "zeros-in-strip"}[]
:::

:::theorem "log-deriv-euler" (lean := "DedekindResidue.neg_logDeriv_dedekindZeta_eq_tsum")
On $`\operatorname{Re} s > 1`,
$$`-\frac{\zeta_K'}{\zeta_K}(s)
= \sum_{\mathfrak{p}} \frac{\log N\mathfrak{p}\; N\mathfrak{p}^{-s}}{1 - N\mathfrak{p}^{-s}}
= \sum_{\mathfrak{p}, m} \log N\mathfrak{p}\cdot N\mathfrak{p}^{-ms}.`
:::

:::proof "log-deriv-euler"
Differentiate the Chebotarev prime-ideal Euler product logarithmically through
locally uniform convergence, then expand each factor as a geometric series.
:::

:::definition "prime-side-h" (lean := "DedekindResidue.primeSideH")
**Poitou's prime-side function**
$$`H(u) = \sum_{\mathfrak{p}, m} \log N\mathfrak{p}\cdot N\mathfrak{p}^{-m(1+a)}\,
F\bigl(u + m\log N\mathfrak{p}\bigr)\, e^{(1/2+a)(u + m\log N\mathfrak{p})},`
the weighted sum of translates of the test function that the prime side of the
explicit formula contracts to.
:::

:::theorem "fourier-jordan" (lean := "DedekindResidue.tendsto_fourier_window_jordan")
**Jordan's form of Fourier inversion.** For integrable $`H` of bounded variation
(real and imaginary parts) with one-sided limits at $`0`,
$$`\lim_{T\to\infty} \int_{-T}^{T} \Bigl(\int_{\mathbb{R}} H(u) e^{itu}\,du\Bigr) dt
= 2\pi\,\frac{H(0^+) + H(0^-)}{2}\cdot 2.`
:::

:::proof "fourier-jordan"
Collapse the symmetric window by Fubini to the Dirichlet kernel
$`2\sin(Tu)/u`; split into the far range (Riemann–Lebesgue), a plateau
($`\int \operatorname{sinc} = \pi/2`, built via Frullani and Fubini — not in
mathlib), and a Stieltjes-controlled remainder for the bounded-variation part
(monotone splitting, Fubini against the Lebesgue–Stieltjes measure).
:::

:::theorem "prime-side-limit" (lean := "DedekindResidue.tendsto_prime_side")
**Poitou's Proposition 2.** For $`\operatorname{Re}`-side edges at $`1+a` and the
folded edge, the prime-side pairing converges:
$$`\lim_{T\to\infty} \int_{-T}^{T} \{\Phi(s)+\Phi(1-s)\}
\Bigl(-\frac{\zeta_K'}{\zeta_K}\Bigr)\Big|_{s = 1+a+it}\,dt
= 2\pi\,\bigl(H(0^+) + H(0^-)\bigr).`
:::

:::proof "prime-side-limit"
Insert the Dirichlet series {uses "log-deriv-euler"}[] and integrate term by term:
each prime power contributes a translated exponential window, so the whole integral
is the windowed Fourier transform of {uses "prime-side-h"}[]; Jordan's theorem
{uses "fourier-jordan"}[] gives the two one-sided limits at the origin.
:::

:::theorem "gauss-digamma" (lean := "DedekindResidue.digamma_eq_integral_gauss_one, DedekindResidue.digamma_sub_digamma_eq_integral")
**Gauss's digamma integral** (absent from mathlib):
$$`\psi(z) = \int_0^\infty \Bigl( e^{-x} - (1+x)^{-z} \Bigr)\frac{dx}{x},`
and in the difference form actually consumed (Poitou's eq. (5)):
$$`\psi(w) - \psi(\sigma) = \int_0^\infty
\frac{e^{-\sigma u} - e^{-w u}}{1 - e^{-u}}\, du.`
:::

:::proof "gauss-digamma"
Differentiate the $`\Gamma`-integral, use Frullani's integral
$`\int_0^\infty (e^{-x}-e^{-tx})\,dx/x = \log t` to trade the logarithm, and
apply Fubini. The counterterms cancel in differences, so neither Gauss's second
form nor the Euler–Mascheroni integral is ever needed.
:::

:::theorem "poitou-prop3" (lean := "DedekindResidue.prop3_poitou")
**Poitou's Proposition 3.** For $`\sigma > 0` and an even admissible test function
$`F` with boundary decay,
$$`\lim_{T\to\infty}\int_{-T}^{T} 2\bigl(\operatorname{Re}\psi(\sigma+it)
- \psi(\sigma)\bigr)\,\varphi(t)\,dt
= 4\pi \int_0^\infty e^{-\sigma y}\,\frac{F(0) - F(y)}{1 - e^{-y}}\,dy,`
where $`\varphi = \widehat{F}`.
:::

:::proof "poitou-prop3"
The kernel $`k_\sigma(x) = x e^{-\sigma x}/(1-e^{-x})` (odd extension) has
$`\rho`-transform $`2(\operatorname{Re}\psi(\sigma+it)-\psi(\sigma))` by the digamma
bridge {uses "gauss-digamma"}[]; an integration by parts converts the windowed
pairing to $`-\int \mu \gamma`, and the $`L^2` Plancherel pairing (the pointwise and
$`L^2` Fourier transforms agree a.e. on $`L^1 \cap L^2`, proved via tempered
distributions) evaluates the limit.
:::

:::theorem "gamma-side-limit" (lean := "DedekindResidue.tendsto_IG_gammaFactor")
**The archimedean side $`I_G`.** For admissible even $`F`,
$$`\lim_{T\to\infty}\int_{-T}^{T} 2\operatorname{Re}
\frac{\gamma_K'}{\gamma_K}\Bigl(\tfrac12+it\Bigr)\varphi(t)\,dt
= 2\pi\Bigl\{ -\bigl(n_K(\gamma_E + \log 8\pi) + r_1\tfrac{\pi}{2}\bigr)F(0)
+ n_K \int_0^\infty \frac{F(0)-F(y)}{2\sinh(y/2)}\,dy
+ r_1 \int_0^\infty \frac{F(0)-F(y)}{2\cosh(y/2)}\,dy \Bigr\}.`
:::

:::proof "gamma-side-limit"
Expand $`d\log\gamma_K` into $`\psi(s/2)` and $`\psi(s)` terms per place; apply
Proposition 3 {uses "poitou-prop3"}[] at $`\sigma = 1/2` and the half-scaled variant
at $`\sigma = 1/4`, and evaluate the constants with $`\psi(1/2) = -\gamma_E - 2\log 2`
and $`\psi(1/2)-\psi(1/4) = \pi/2 + \log 2` (proved via the Gauss difference form —
no reflection formula needed). The $`\sinh`/$`\cosh` kernels arise as the
$`(1/2)`-kernel and the average of the $`(1/4, t/2)`–$`(1/2,t)` combination.
:::

:::theorem "weil-explicit-formula" (lean := "DedekindResidue.weil_explicit_formula")
**The Weil–Poitou explicit formula** (Poitou's eq. (6)). For an even test function
$`F` satisfying the admissibility, bounded-variation, band-bound and boundary-decay
hypotheses, there are good heights $`T_n \to \infty` along which
$$`\sum_{\substack{\rho \\ |\operatorname{Im}\rho| < T_n}} m_\rho\,\Phi_F(\rho)
\longrightarrow \Phi_F(0) + \Phi_F(1) + \log\Delta_K\, F(0)
- \bigl(n_K(\gamma_E{+}\log 8\pi) + r_1\tfrac{\pi}{2}\bigr) F(0)
+ n_K \!\int_0^\infty\! \frac{F(0)-F(y)}{2\sinh(y/2)}dy
+ r_1 \!\int_0^\infty\! \frac{F(0)-F(y)}{2\cosh(y/2)}dy
- \bigl(H(0^+) + H(0^-)\bigr).`
:::

:::proof "weil-explicit-formula"
Integrate $`\Phi \cdot \Lambda'/\Lambda` over the expanding rectangles: the zero side
is the capture {uses "zero-capture"}[]; on the edge $`\operatorname{Re} = 1+a` split
$`\Lambda'/\Lambda = \tfrac1s + \tfrac1{s-1} + \tfrac12\log\Delta_K +
\gamma_K'/\gamma_K + \zeta_K'/\zeta_K`; fold the left edge by the symmetry
$`\Phi(1-s) = \Phi(s)` {uses "phi-transform"}[]; the pole piece gives
$`\Phi(0)+\Phi(1)`, the discriminant piece gives $`\log\Delta_K\,F(0)`, the
$`\Gamma`-piece shifts to the critical line and evaluates by
{uses "gamma-side-limit"}[], and the prime piece is {uses "prime-side-limit"}[].
:::

# The auxiliary test function (SP3)

:::theorem "lemma-2" (lean := "DedekindResidue.fourier_auxF, DedekindResidue.fourier_auxF_zero")
**Belabas–Friedman Lemma 2 (eq. (8)).** For $`\operatorname{Re} s > 1/2`,
$`\gamma \neq 0`, $`h = s - 1/2`, $`T = \log X`:
$$`\widehat{F_{s,X}}(\gamma)
= \frac{2h^2 \sin(T\gamma)}{(h^2+\gamma^2)\gamma}
+ \frac{2\bigl(h + 1/T\bigr)\cos(T\gamma)}{h^2+\gamma^2}
- \frac{4}{h^2+\gamma^2}\int_T^\infty \cos(t\gamma)\, F_{s,X}(t)\,
\frac{ht+1}{t^2}\, dt,`
with the $`\gamma = 0` companion obtained by the plateau value
$`\sin(T\gamma)/\gamma \to T`. Depends on: {uses "aux-f"}[]
:::

:::proof "lemma-2"
Reduce by evenness to a half-line integral; two improper integrations by parts
against the derivative formulas of the kernel $`g_s` (eq. (7)) produce the boundary
terms (the sine and cosine pieces at the kink $`t = T`) and the tail integral.
:::

:::definition "admissible" (lean := "DedekindResidue.IsAdmissibleTestFn")
The paper's explicit-formula hypotheses on a test function (p. 3, verbatim): even;
for some $`\varepsilon > 0` the weighted function $`F(x)e^{(1/2+\varepsilon)x}` is of
bounded variation and integrable; the difference quotient $`(F(0)-F(x))/x` is of
bounded variation; and $`F` is the average of its one-sided limits.
:::

:::theorem "aux-admissible" (lean := "DedekindResidue.isAdmissibleTestFn_auxF")
$`F_{s,X}` is admissible for $`\operatorname{Re} s > 1` (with
$`\varepsilon = (\operatorname{Re} s - 1)/2`). Depends on: {uses "admissible"}[]
{uses "aux-f"}[]
:::

:::theorem "band-bound" (lean := "DedekindResidue.exists_band_bound_paperPhi_auxF")
**Uniform band decay of $`\Phi_{F_{s,X}}`** — the main analytic discharge: there is
$`M` with
$$`\lVert \Phi_{F_{s,X}}(\sigma + it) \rVert \le \frac{M}{\max(|t|, 1)}
\qquad (-a \le \sigma \le 1+a),`
which combined with the $`\log^2` edge bounds gives the vanishing horizontal error
in the zero capture.
:::

:::proof "band-bound"
For small $`|t|`, dominate by the $`L^1` majorant of the kernel. For large $`|t|`,
integrate by parts once: the identity
$`w\,\Phi(z) = -\int_{\log X}^\infty F'(x)(e^{wx} - e^{-wx})\,dx` (with
$`w = z - 1/2`) exhibits the transform as $`O(1/|w|)`, and $`|w| \ge |t|` on the
band. Depends on: {uses "phi-transform"}[] {uses "aux-f"}[]
:::

:::theorem "fourier-decay" (lean := "DedekindResidue.exists_norm_fourier_auxF_le")
**Quadratic Fourier decay**: there are $`C, \gamma_0` with
$`\lVert\widehat{F_{s,X}}(\gamma)\rVert \le C/\gamma^2` for $`|\gamma| \ge \gamma_0`
— read directly off the closed form. Depends on: {uses "lemma-2"}[]
:::

:::theorem "weil-at-auxF" (lean := "DedekindResidue.weil_explicit_formula_auxF")
**The explicit formula at $`F_{s,X}`** (the SP3 milestone): for $`1 < X`,
$`0 < a \le 1/4`, $`a < \operatorname{Re} s - 1`, every hypothesis of
{uses "weil-explicit-formula"}[] holds at $`F = F_{s,X}`, and the zero-capture limit
equals Poitou's right-hand side with both prime-side limits equal to $`H(0)`.
:::

:::proof "weil-at-auxF"
Assemble the discharges: integrability and bounded variation of $`F_{s,X}` and its
weighted forms (piecewise-$`C^1` with one kink), the difference-quotient
$`L^2`-membership, the boundary $`\rho\gamma`-decay at $`\sigma = 1/2, 1/4` (from the
$`O(\log)` kernel bound times the $`O(1/t)` transform decay), band-local
differentiability of $`\Phi`, and the band bound {uses "band-bound"}[] with
$`B(T) = M/\max(T,1)`, whose $`\log^2`-product vanishes. Depends on:
{uses "aux-admissible"}[]
:::

:::theorem "prime-side-value" (lean := "DedekindResidue.primeSideH_auxF_zero_eq")
**The prime-side value at the origin**: for any $`a` and $`F`,
$$`H(0) = \sum_{\mathfrak{p},m} \frac{\log N\mathfrak{p}}{N\mathfrak{p}^{m/2}}\,
F(m \log N\mathfrak{p})`
— the band parameter collapses out:
$`N\mathfrak{p}^{-m(1+a)} e^{(1/2+a)m\log N\mathfrak{p}} = N\mathfrak{p}^{-m/2}`.
Depends on: {uses "prime-side-h"}[]
:::

# Toward Theorem 1: the zero side and Lemma 3 (Tier 3)

:::definition "zero-divisor" (lean := "DedekindResidue.zetaZeroDivisor, DedekindResidue.ZetaZeros")
The **global zero divisor** of the entire completion assigns to each $`\rho` its
zero-multiplicity $`m_\rho`; the **zero index** `ZetaZeros` is the (countable)
subtype where it is nonzero. The support is locally finite, and window divisors of
the explicit formula agree with the global divisor on their windows.
Depends on: {uses "completed-zeta"}[]
:::

:::theorem "zeros-critical-line" (lean := "DedekindResidue.ZetaZeros_re_eq_half")
Under GRH every indexed zero has $`\operatorname{Re}\rho = 1/2`, so
$`\rho = 1/2 + i\gamma_\rho`. Depends on: {uses "grh"}[] {uses "zeros-in-strip"}[]
:::

:::theorem "slab-count" (lean := "DedekindResidue.exists_slab_zetaZeroDivisor_sum_le")
**Unit-slab zero count**: there is $`C` with
$`\sum_{n \le |\gamma_\rho| \le n+1} m_\rho \le C\log(3+n)` for every $`n`.
Depends on: {uses "zero-count"}[]
:::

:::theorem "landau-summability" (lean := "DedekindResidue.summable_zetaZeros_inv_sq")
**Landau summability**: for every $`h > 0`,
$$`\sum_{\rho} \frac{m_\rho}{h^2 + \gamma_\rho^2} < \infty.`
:::

:::proof "landau-summability"
Partition the zero index by $`\lfloor|\gamma_\rho|\rfloor`; each slab contributes at
most $`C\log(3+n)/(h^2+n^2)` by {uses "slab-count"}[], and
$`\sum_n \log(3+n)/(h^2+n^2)` converges.
:::

:::theorem "window-limit" (lean := "DedekindResidue.tendsto_finsum_window_zetaZeros, DedekindResidue.finsum_divisor_mul_eq_sum_zetaZeros")
**The zero-capture limit is the honest series.** Under GRH, for any test function
$`\phi` with $`\sum_\rho m_\rho |\phi(\rho)| < \infty` and any heights
$`T_n \to \infty`, the window sums of the explicit formula converge to
$`\sum'_{\rho} m_\rho\, \phi(\rho)` over the full zero index.
:::

:::proof "window-limit"
Each bounded window contains finitely many indexed zeros, and the window finsum
collapses to the finite sum over them (the divisor is supported in the window and
agrees with the global divisor there). Any finite subfamily of the index has bounded
ordinates and — by GRH {uses "zeros-critical-line"}[] — real part $`1/2` inside the
band, so it is eventually captured; the Finset-indexed net of partial sums of the
absolutely summable series therefore converges through the window exhaustion.
:::

:::theorem "log-euler-product" (lean := "DedekindResidue.real_log_dedekindZeta, DedekindResidue.dedekindZeta_eq_exp_tsum_prod")
**The logarithmic Euler product** on the real ray: for $`\sigma > 1`,
$$`\log \zeta_K(\sigma)
= \sum_{\mathfrak{p}, m} \frac{N\mathfrak{p}^{-m\sigma}}{m}.`
:::

:::theorem "zero-sum-summable" (lean := "DedekindResidue.summable_zetaZeros_paperPhi_auxF")
Under GRH, for $`\operatorname{Re} s > 1`, the zero series
$`\sum_\rho m_\rho\, \Phi_{F_{s,X}}(\rho)` converges absolutely.
:::

:::proof "zero-sum-summable"
On the critical line $`\Phi = \widehat{F}` {uses "phi-transform"}[]; glue the
quadratic tail decay {uses "fourier-decay"}[] to the band bound
{uses "band-bound"}[] on the compact range to get
$`\lVert\Phi(1/2+i\gamma)\rVert \le C'/(1+\gamma^2)`, and compare with Landau
summability {uses "landau-summability"}[]. Depends on:
{uses "zeros-critical-line"}[]
:::

:::theorem "explicit-formula-tsum" (lean := "DedekindResidue.tsum_zetaZeros_paperPhi_auxF_eq")
**The explicit formula as an absolutely convergent zero sum.** Under GRH, for
$`1 < X`, $`0 < a \le 1/4`, $`a < \operatorname{Re} s - 1`:
$$`\sum_{\rho}{}' \; m_\rho\, \Phi_{F_{s,X}}(\rho)
= \Phi(0) + \Phi(1) + \log\Delta_K - \bigl(n_K(\gamma_E{+}\log 8\pi)
+ r_1\tfrac{\pi}{2}\bigr) + \text{(archimedean integrals)} - 2H(0),`
i.e. the $`T \to \infty` limit is removed from the explicit formula.
:::

:::proof "explicit-formula-tsum"
The window sums converge both to the Poitou right-hand side (by
{uses "weil-at-auxF"}[]) and to the absolutely convergent series (by
{uses "window-limit"}[] with the summability {uses "zero-sum-summable"}[]);
uniqueness of limits.
:::

:::theorem "zero-sum-split" (lean := "DedekindResidue.tsum_zetaZeros_paperPhi_auxF_split, DedekindResidue.paperFourierIntegral_auxF_split")
**The three zero-series of Lemma 3.** Under GRH at real $`\sigma > 1`, the zero sum
splits into three absolutely convergent series matching the closed form of Lemma 2:
$$`\sum_\rho{}' m_\rho \widehat F(\gamma_\rho)
= \sum_\rho \frac{2h^2\, m_\rho \sin(T\gamma_\rho)}{(h^2+\gamma_\rho^2)\gamma_\rho}
+ \sum_\rho \frac{2(h+\tfrac1T)\, m_\rho \cos(T\gamma_\rho)}{h^2+\gamma_\rho^2}
- \sum_\rho \frac{4 m_\rho}{h^2+\gamma_\rho^2}
\int_T^\infty \cos(t\gamma_\rho) F_{\sigma,X}(t)\frac{ht+1}{t^2}dt.`
:::

:::proof "zero-sum-split"
Each piece is bounded by $`c/(h^2+\gamma^2)`: the sine piece by
$`|\sin(T\gamma)| \le T|\gamma|` (which also handles the removable singularity at
$`\gamma = 0`), the cosine piece trivially, and the integral piece by the integrated
norm of the $`\gamma`-free majorant. Landau summability
{uses "landau-summability"}[] makes each series absolutely convergent, and the
pointwise closed form {uses "lemma-2"}[] splits the terms. Depends on:
{uses "explicit-formula-tsum"}[]
:::

:::theorem "prime-side-split" (lean := "DedekindResidue.primeSideH_auxF_zero_split, DedekindResidue.tsum_kernel_eq_log_zeta")
**$`H(0)` carries $`\log\zeta_K`** (the Lemma 3 bookkeeping): at real $`\sigma > 1`,
$$`H(0) = \sum_{\substack{\mathfrak{p},m \\ m\log N\mathfrak{p} \le T}}
\frac{\log N\mathfrak{p}}{N\mathfrak{p}^{m/2}}
\bigl(1 - f_{\sigma,X}(m\log N\mathfrak{p})\bigr)
+ T\,e^{hT}\,\log\zeta_K(\sigma),`
a finitely-supported plateau defect plus the logarithm: on the tail the weights
collapse, $`\log N\cdot N^{-m/2} f_{\sigma,X}(m\log N) = T e^{hT} N^{-m\sigma}/m`,
and the full kernel sum is the logarithmic Euler product.
Depends on: {uses "prime-side-value"}[] {uses "log-euler-product"}[]
{uses "aux-f"}[]
:::

:::theorem "belabas-friedman-thm1" (lean := "DedekindResidue.belabas_friedman_bound")
**Theorem 1 (Belabas–Friedman).** Let $`K` be a number field of degree $`n > 1`.
Under GRH for $`\zeta_K` and RH for $`\zeta_\mathbb{Q}`, for $`X \ge 69`:
$$`\bigl|\log \kappa_K - f_K(X)\bigr|
\le \frac{2.324\,\log\Delta_K}{\sqrt{X}\log 3X}
\Bigl( \bigl(1 + \tfrac{3.88}{\log(X/9)}\bigr)
\bigl(1 + \tfrac{2}{\sqrt{\log\Delta_K}}\bigr)^2
+ \frac{4.26\,(n-1)}{\sqrt{X}\,\log\Delta_K} \Bigr),`
where $`\kappa_K = \operatorname{Res}_{s=1}\zeta_K` (mathlib's
`NumberField.dedekindZeta_residue`).
:::

:::proof "belabas-friedman-thm1"
(In progress — the remaining spine.) Lemma 3 assembles from
{uses "explicit-formula-tsum"}[], {uses "zero-sum-split"}[] and
{uses "prime-side-split"}[], dividing by $`g_\sigma(T) = e^{-hT}/T`: the bracketed
combination of $`\log\zeta_K(\sigma)` and the truncated prime sum equals the three
zero-series plus the archimedean integrals. Applying it at $`\sigma \to 1^+` for the
two cutoffs $`T` and $`T - \log 9` and subtracting (Lemma 4's difference trick,
eq. (14)) cancels the sine terms; the zero sums are estimated by Lemma 5
($`\sum_\rho m_\rho/(\tfrac14+\gamma_\rho^2) = O(\log\Delta_K)`) and elementary
monotonicity on the exact numerical domains ($`X \ge 69`, $`a = \log 9`), producing
the displayed constants. The residue enters through
$`\log\kappa_{K/\mathbb{Q}} = \lim_{\sigma\to1}\log(\zeta_K/\zeta_\mathbb{Q})(\sigma)`.
Depends on: {uses "f-K"}[] {uses "grh"}[]
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}

# Review brief — Strong Multiplicity One closure plan via Route B

*Prepared 2026-05-16 for the same frontier-LLM reviewer audience as the
prior 2026-05-11 SMO briefs.  Diamond–Shurman conventions throughout.
Self-contained: no repository access required.*

---

## 1. What this brief is about

This is a follow-up to the 2026-05-11 series of SMO briefs (the SMO
overview, the T205-d focused brief, and the T205-d restructured residual
brief).  Those briefs centred on the **Petersson adjoint chain** for the
good-prime Hecke operator at level $\Gamma_1(N)$ — Diamond–Shurman
Theorem 5.5.3 / Miyake Theorem 4.5.4 — as the analytic input for the
Atkin–Lehner Main Lemma via the spectral theorem.

Since the last brief, the project has **switched strategy**.  We now
propose to close the SMO chain without the Petersson adjoint at all,
using **Route B — Miyake / Atkin–Lehner induction** (Miyake §4.6,
Diamond–Shurman §5.7) — which the project's `Eigenforms/` subdirectory
already implements per-character.  A small but important strategic
insight makes this work: `newform_unique` only needs the
**per-character** Main Lemma, not the unconditional one, because both
newforms in the hypothesis live in the same Nebentypus space.  This
sidesteps the character-decomposition inheritance issue that would block
a naïve unconditional argument.

The plan now reduces SMO to **three atomic mathematical obligations**.
We have written every higher-level theorem out as a complete proof
chaining into these three obligations; the proof is axiom-clean (with
respect to `{propext, Classical.choice, Quot.sound}`) once the three
obligations are discharged.

We want the reviewer to weigh in on two fronts:

1. **Soundness check.**  Is the route mathematically valid?  Are the
   three obligations as stated genuinely sufficient to close SMO?  Are
   there hidden subtleties — particularly in the per-character-only
   route to `newform_unique` — that we've missed?
2. **Strategic guidance.**  Which obligation should we tackle first?
   What are realistic LOC estimates for each?  Is there a still-cleaner
   factorisation we haven't seen?

---

## 2. Notation and conventions

We follow Diamond–Shurman throughout.

### 2.1. Groups and Hecke pair

- $\mathrm{GL}_2^+(\mathbb{R}) := \{\alpha \in \mathrm{GL}_2(\mathbb{R}) : \det\alpha > 0\}$.
- $\Gamma(N), \Gamma_0(N), \Gamma_1(N)$ are the standard congruence
  subgroups of $\mathrm{SL}_2(\mathbb{Z})$:
  $\Gamma_0(N) := \{\gamma \equiv \left(\begin{smallmatrix}\ast & \ast \\ 0 & \ast\end{smallmatrix}\right) \bmod N\}$,
  $\Gamma_1(N) := \{\gamma \in \Gamma_0(N) : \gamma \equiv \left(\begin{smallmatrix}1 & \ast \\ 0 & 1\end{smallmatrix}\right) \bmod N\}$.
- $\Delta_0(N) := \{\alpha \in M_2(\mathbb{Z}) : c \equiv 0 \bmod N, \gcd(a, N) = 1, \det\alpha > 0\}$.

### 2.2. Slash action and modular forms

For $\alpha = \left(\begin{smallmatrix}a & b \\ c & d\end{smallmatrix}\right) \in \mathrm{GL}_2^+(\mathbb{R})$
and integer weight $k$:
$$(f|_k \alpha)(\tau) := (\det\alpha)^{k-1} (c\tau + d)^{-k} f(\alpha\tau).$$

- $M_k(\Gamma)$: weight-$k$ holomorphic modular forms invariant under $\Gamma$.
- $S_k(\Gamma) \subseteq M_k(\Gamma)$: cuspidal subspace.
- $S_k(\Gamma_1(N), \chi)$: $\chi$-eigenspace of the diamond operators
  (Nebentypus $\chi$).
- $S_k^{\mathrm{old}}(\Gamma_1(N))$: the **oldform subspace**, spanned by
  $g(d\tau)$ for $d \mid N$ with $d > 1$ and $g \in S_k(\Gamma_1(N/d))$.
- $S_k^{\mathrm{new}}(\Gamma_1(N))$: the **newform subspace**, the
  orthogonal complement of $S_k^{\mathrm{old}}$ with respect to the
  level-$N$ Petersson inner product.

### 2.3. Petersson form

The level-1 Petersson inner product on $S_k(\mathrm{SL}_2(\mathbb{Z}))$ is
$$\langle f, g \rangle := \int_{\mathcal{D}} f(\tau)\overline{g(\tau)}(\mathrm{Im}\,\tau)^k \, \tfrac{dx \, dy}{y^2},$$
with $\mathcal{D}$ the standard $\mathrm{SL}_2(\mathbb{Z})$-fundamental domain.
The level-$N$ form $\langle\cdot,\cdot\rangle_N$ on $S_k(\Gamma_1(N))$ is
defined by the coset sum
$$\langle f, g \rangle_N := \sum_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \int_{\mathcal{D}} (f|_k q^{-1})(\tau) \overline{(g|_k q^{-1})(\tau)} (\mathrm{Im}\,\tau)^k \, \tfrac{dx \, dy}{y^2}.$$

### 2.4. Diamond and Hecke operators

For $d \in (\mathbb{Z}/N)^\times$, the **diamond operator**
$\langle d \rangle$ on $S_k(\Gamma_1(N))$ is the slash by any
$\gamma_d \in \Gamma_0(N)$ whose lower-right entry reduces to $d \bmod N$;
the result is well-defined modulo $\Gamma_1(N)$.

For $p$ prime with $p \nmid N$, the Hecke operator $T_p$ on
$S_k(\Gamma_1(N))$ has the standard $p+1$-coset decomposition.

### 2.5. Newforms

A **newform** at level $N$ is a normalised common eigenform of
$\{T_n, \langle d \rangle : (n, N) = (d, N) = 1\}$ lying in
$S_k^{\mathrm{new}}(\Gamma_1(N))$, with first Fourier coefficient
$a_1 = 1$.  Newforms in a Nebentypus space carry a Dirichlet character
$\chi$.

### 2.6. Dirichlet characters and L-functions

For $\chi : (\mathbb{Z}/N)^\times \to \mathbb{C}^\times$ a Dirichlet
character, write $\tilde\chi$ for its lift to a primitive Dirichlet
character modulo a divisor of $N$ (extended by zero on non-coprime
arguments).  Its L-function $L(s, \tilde\chi) := \sum_{n \ge 1}
\tilde\chi(n) n^{-s}$ converges for $\mathrm{Re}\,s > 1$ and extends to
an entire function for non-trivial $\tilde\chi$.  The completed
L-function is
$$\Lambda(s, \tilde\chi) := N^{s/2} \pi^{-(s+a)/2} \Gamma\!\left(\tfrac{s+a}{2}\right) L(s, \tilde\chi),$$
with $a = 0$ if $\tilde\chi$ is even, $a = 1$ if odd.  The functional
equation is $\Lambda(s, \tilde\chi) = \varepsilon(\tilde\chi) \Lambda(1 - s, \overline{\tilde\chi})$.

---

## 3. References

- **[DS]** Fred Diamond and Jerry Shurman.  *A First Course in Modular
  Forms.*  Graduate Texts in Mathematics 228.  Springer, 2005.
- **[Miy]** Toshitsune Miyake.  *Modular Forms.*  2nd ed.  Springer
  Monographs in Mathematics.  Springer, 2006.
- **[Sh]** Goro Shimura.  *Introduction to the Arithmetic Theory of
  Automorphic Functions.*  Princeton, 1971.
- **[AL]** A. O. L. Atkin and J. Lehner.  "Hecke operators on
  $\Gamma_0(m)$."  *Math. Ann.* **185** (1970), 134–160.
- **[Li]** Wen-Ch'ing Winnie Li.  "Newforms and functional equations."
  *Math. Ann.* **212** (1975), 285–315.
- **[He]** Erich Hecke.  "Über die Bestimmung Dirichletscher Reihen
  durch ihre Funktionalgleichung."  *Math. Ann.* **112** (1936),
  664–699.
- **[Da]** Harold Davenport.  *Multiplicative Number Theory.*  3rd ed.
  Graduate Texts in Mathematics 74.  Springer, 2000.
- **[Iwa]** Henryk Iwaniec.  *Topics in Classical Automorphic Forms.*
  Graduate Studies in Mathematics 17.  AMS, 1997.

Key uses:
- Main Lemma route, sieves, primitive forms — [DS §5.7], [Miy §4.6],
  [AL], [Li].
- Hecke functional equation (B.L3.1) — [He], [DS §5.10], [Miy §4.3].
- Dirichlet L-function zeros (B.L3.2) — [Da Ch. 9, 11], [Miy §4.5.15],
  [Iwa Ch. 5].

---

## 4. The target theorem

**Theorem (Strong Multiplicity One).**
Let $N \ge 1$, $k \in \mathbb{Z}$, and $\chi$ a Dirichlet character
modulo $N$.  Let $f, g$ be two normalised newforms in
$S_k^{\mathrm{new}}(\Gamma_1(N), \chi)$.  Let $S \subset \mathbb{N}$ be
any finite set.  If $\lambda_n(f) = \lambda_n(g)$ for every $n \in
\mathbb{N}_{\ge 1}$ with $\gcd(n, N) = 1$ and $n \notin S$, then $f$ and
$g$ agree as cusp forms.

This is Miyake Theorem 4.6.12 (Diamond–Shurman Theorem 5.8.2).

---

## 5. Strategy: Route B

### 5.1.  Why Route B (Miyake/Atkin–Lehner induction)

Route A — the project's previously pursued strategy via the **spectral
theorem on $S_k^{\mathrm{new}}$** — required the Petersson adjoint
identity for $T_p$ at level $\Gamma_1(N)$ (DS Thm 5.5.3 / Miyake Thm
4.5.4) as analytic input.  That identity is the focus of the 2026-05-11
series of briefs and remains open as a single named residual (the
$\sigma_p$ Q-permutation aggregate identity).

Route B avoids the Petersson adjoint chain entirely.  Miyake's §4.6
inductive proof of the Main Lemma uses **coprime sieving via the
operators $U_p$ and $V_p$**, where:

- $U_p = $ the bad-prime Hecke operator at level $N$ (in the project,
  `heckeT_p_divN`);
- $V_p = $ the level-raising operator $f(\tau) \mapsto f(p\tau)$ (in the
  project, `modularFormLevelRaise`).

The project's `Eigenforms/` subdirectory has already implemented Miyake's
chain in axiom-clean form, **per Nebentypus character**, via the
`SameLevelDivisorProjections` interface (an operator-level packaging of
the per-divisor projection data) and the consumer
`mainLemma_charSpace_of_sameLevelDivisorDecomposition`.  These produce
the conclusion "$f \in S_k^{\mathrm{old}}$" from the hypothesis that $f$
lies in a character space, has coprime-to-$N$ Fourier vanishing at the
cusp $\infty$, and admits a per-divisor decomposition with the right
$q$-support.

### 5.2.  The key strategic insight: `newform_unique` only needs per-character

The standard route to SMO factors through `newform_unique`:

**newform_unique (Atkin–Lehner uniqueness).**
*Two newforms $f, g$ in $S_k(\Gamma_1(N), \chi)$ (same Nebentypus) with
$\lambda_n(f) = \lambda_n(g)$ for every $n$ coprime to $N$ are equal.*

The classical proof:
$f - g \in S_k^{\mathrm{new}}(\Gamma_1(N))$ (both $f, g$ are newforms).
Coprime-equality of eigenvalues plus normalisation gives $a_n(f - g) = 0$
for every $n$ coprime to $N$.  Apply the Main Lemma to deduce
$f - g \in S_k^{\mathrm{old}}(\Gamma_1(N))$.  Combining with
$f - g \in S_k^{\mathrm{new}}(\Gamma_1(N))$ and orthogonality gives
$f - g = 0$.

The project's previous instinct was to apply the **unconditional** Main
Lemma (for any cusp form in $S_k(\Gamma_1(N))$, no fixed character) to
$f - g$.  But $f - g$ already lies in the same Nebentypus space as $f$
and $g$, namely $S_k(\Gamma_1(N), \chi)$.  So the **per-character** Main
Lemma applied to $f - g \in S_k(\Gamma_1(N), \chi)$ suffices, and the
unconditional version is unnecessary.

This matters because the unconditional Main Lemma, attempted via
character decomposition $f = \sum_\chi \pi_\chi f$ followed by the
per-character version, runs into a subtle obstruction:

> **Subtle obstruction (which we sidestep).**  For an arbitrary
> $f \in S_k(\Gamma_1(N))$ with $a_n(f) = 0$ for every $n$ coprime to
> $N$ at the cusp $\infty$, the $\chi$-pieces $\pi_\chi f$ do **not**
> in general inherit coprime-to-$N$ Fourier vanishing at $\infty$.  The
> diamond projection involves slash by $\gamma_d \in \Gamma_0(N) \setminus
> \mathrm{stab}_{\mathrm{SL}_2(\mathbb{Z})}(\infty)$ for $d \not\equiv \pm 1
> \pmod N$, and the slash by such $\gamma_d$ relates the Fourier
> expansion of $\gamma_d \cdot f$ at $\infty$ to the Fourier expansion
> of $f$ at the (in general distinct) cusp $\gamma_d \cdot \infty$.
> So per-coordinate inheritance via $a_n(\pi_\chi f) = \tfrac{1}{|G|}
> \sum_d \bar\chi(d) \, a_n(\gamma_d \cdot f)$ does not collapse to
> "$0 = 0$" without further information about $f$ at other cusps.

Restricting to $f - g$ in a fixed character space sidesteps the
inheritance issue entirely: the per-character Main Lemma applies
directly.

### 5.3.  The three remaining obligations

After applying §5.2, the SMO chain reduces to **three atomic
mathematical obligations** at level 3:

- **(A.L3)** *Per-character Möbius coprime sieve.*  For every Nebentypus
  $\chi$, every cusp form $f \in S_k(\Gamma_1(N), \chi)$ with
  coprime-to-$N$ Fourier vanishing at $\infty$ admits a finite
  decomposition $f = \sum_{d \mid N, d > 1} f_d$, where each $f_d$ has
  $q$-expansion supported on multiples of $d$ and lies in
  $S_k(\Gamma_1(N), \chi)$.
- **(B.L3.1)** *Hecke 1936 functional equation / entire continuation.*
  For every newform $f$, the stripped Dirichlet series
  $L^*(s, f) := \sum_{(n, N) = 1} a_n(f) \, n^{-s}$ extends to an entire
  function of $s \in \mathbb{C}$.
- **(B.L3.2)** *Trivial-zero Dirichlet contradiction.*  Under the
  bad-prime hypothesis ($a_q(f) = 0$ for every prime $q$ coprime to $N$
  outside a finite set $S$), the stripped Dirichlet series $L^*(s, f)$
  does **not** admit entire extension.

Every higher-level claim — Main Lemma in the character space,
`newform_unique`, existence of a good prime with non-vanishing
eigenvalue, and SMO itself — is then a complete formal proof from these
three obligations and the project's existing axiom-clean infrastructure.

---

## 6. Established results (axiom-clean already in the project)

We use the following auxiliary results, **all axiom-clean** with respect
to `{propext, Classical.choice, Quot.sound}`.  Names are mathematically
descriptive; opaque ticket identifiers are dropped.

**Theorem 6.1 (orthogonal decomposition).**
$S_k(\Gamma_1(N)) = S_k^{\mathrm{old}}(\Gamma_1(N)) \oplus S_k^{\mathrm{new}}(\Gamma_1(N))$,
with disjoint summands.

*Sketch.* Standard.  Defines $S_k^{\mathrm{new}}$ as the Petersson
orthogonal complement of $S_k^{\mathrm{old}}$. The decomposition,
disjointness, and reconstruction $f = f_{\mathrm{old}} + f_{\mathrm{new}}$
are formal consequences. ∎

**Theorem 6.2 (Main Lemma from same-level divisor decomposition).**
*Let $\chi$ be a Nebentypus character modulo $N$.  Let $f \in
S_k(\Gamma_1(N), \chi)$ and suppose that $f = \sum_{d \mid N,\,d > 1}
f_d$ is a same-level decomposition such that each $f_d$ has
$q$-expansion supported on multiples of $d$ and lies in
$S_k(\Gamma_1(N), \chi)$.  Then $f \in S_k^{\mathrm{old}}(\Gamma_1(N))$.*

*Sketch.* Each $f_d$ with $q$-support on multiples of $d$ can be
identified with the image $V_d(g_d)$ of some $g_d \in S_k(\Gamma_1(N/d))$
under the level-raising operator $V_d : f(\tau) \mapsto f(d\tau)$ (the
conductor theorem, Miyake Theorem 4.6.4).  Therefore each $f_d$ lies in
$S_k^{\mathrm{old}}(\Gamma_1(N))$.  Finite sums of oldforms are oldforms. ∎

**Theorem 6.3 (Newform uniqueness from new-subspace zero criterion).**
*Suppose: every $h \in S_k^{\mathrm{new}}(\Gamma_1(N))$ with $a_n(h) = 0$
for every $n$ coprime to $N$ is zero.  Then two newforms $f, g \in
S_k^{\mathrm{new}}(\Gamma_1(N), \chi)$ whose Hecke eigenvalues agree at
every $n$ coprime to $N$ satisfy $f = g$.*

*Sketch.* Set $h := f - g \in S_k^{\mathrm{new}}(\Gamma_1(N))$.  The
eigenvalue equality plus Fourier-coefficient–eigenvalue identification
gives $a_n(h) = 0$ for $n$ coprime to $N$.  Apply the hypothesis. ∎

**Theorem 6.4 (Analytic contradiction from entire continuation and
no-extension-under-bad-prime).**
*If $L^*(s, f)$ extends to an entire function for every newform $f$
**and** under the bad-prime hypothesis there is no entire extension,
then for every newform $f$, every Nebentypus $\chi$, every finite set
$S$, there exists a prime $q \notin S$, coprime to $N$, with
$\lambda_q(f) \ne 0$.*

*Sketch.* Contrapositive of the bad-prime hypothesis. ∎

**Theorem 6.5 (Conditional SMO).**
*Suppose `newform_unique` (with all-coprime eigenvalue equality) and the
good-prime non-vanishing of Theorem 6.4 hold.  Then SMO (with
cofinite-coprime eigenvalue equality) holds.*

*Sketch.* For $n$ in the exceptional set, pick a prime $q$ outside
$S \cup \{s / n : s \in S\} \cup \mathrm{primeFactors}(n)$ with
$\lambda_q(f) \ne 0$.  Coprime multiplicativity of eigenvalues gives
$\lambda_{nq}(f) = \lambda_n(f) \lambda_q(f)$ and similarly for $g$.
The cofinite hypothesis at $q$ and $nq$ (both outside $S$) plus
cancellation yields $\lambda_n(f) = \lambda_n(g)$. ∎

---

## 7. The plan in detail

We now state the three level-3 obligations precisely, with their
classical proofs and references.  Above each, we sketch how it feeds
into the SMO chain via the axiom-clean theorems of §6.

### 7.1.  (A.L3) Per-character Möbius coprime sieve

**Statement (A.L3).**
*Let $N \ge 1$, $k \in \mathbb{Z}$, $\chi : (\mathbb{Z}/N)^\times \to
\mathbb{C}^\times$.  Let $f \in S_k(\Gamma_1(N), \chi)$ with $a_n(f) = 0$
for every $n \in \mathbb{N}_{\ge 1}$ coprime to $N$ (Fourier expansion
at $\infty$ with period $1$).  Then there exist cusp forms
$\{f_d\}_{d \mid N,\,d > 1}$ in $S_k(\Gamma_1(N))$ such that:*

1. *$f = \sum_{d \mid N,\,d > 1} f_d$;*
2. *each $f_d$ has $q$-expansion at $\infty$ supported on multiples of
   $d$;*
3. *each $f_d$ lies in $S_k(\Gamma_1(N), \chi)$.*

**Classical proof.**  This is Miyake §4.6.5 + 4.6.7 specialised at
$\ell = N$.  The construction is:
$$f_d := \sum_{T \subseteq \mathrm{primes}(N),\,d = \prod T}\!\!\! (-1)^{|T| - \omega(d)} \prod_{p \in T} V_p \circ U_p \, (f),$$
where $\omega(d)$ counts distinct prime divisors of $d$, $U_p$ is the
bad-prime Hecke operator on $S_k(\Gamma_1(N))$, and $V_p$ is the
level-raising operator $f(\tau) \mapsto f(p\tau)$.  Three properties to
verify:

- *$q$-support.*  Miyake Lemma 4.6.5: the coefficient at index $n$ in
  $f_d$ equals $a_n(f) \cdot \mu_N(d, n)$ where $\mu_N$ is a level-$N$
  Möbius indicator that vanishes unless $d \mid n$.
- *Character invariance.*  Both $U_p$ and $V_p$ commute with the diamond
  operators $\langle d \rangle$ (DS Proposition 5.2.4(a) for $U_p$;
  immediate for $V_p$).  Hence each $V_p \circ U_p$ preserves
  $S_k(\Gamma_1(N), \chi)$, and so does the alternating sum.
- *Reconstruction.*  By Möbius inversion on the indicator
  $[\gcd(n, N) > 1]$ in terms of divisor indicators $[d \mid n]$:
  $[\gcd(n, N) > 1] = \sum_{d \mid N,\,d > 1} \mu_N(d, n) \cdot [d \mid n]$.
  Applied coefficient-by-coefficient, this gives $\sum_d a_n(f_d) =
  a_n(f) \cdot [\gcd(n, N) > 1]$, which equals $a_n(f)$ under the
  vanishing hypothesis $a_n(f) = 0$ for $\gcd(n, N) = 1$.

**How (A.L3) closes the per-character Main Lemma.**  Apply Theorem 6.2:
the decomposition is exactly the hypothesis Theorem 6.2 needs.

### 7.2.  (B.L3.1) Hecke 1936 functional equation

**Statement (B.L3.1).**
*For every newform $f \in S_k(\Gamma_1(N), \chi)$ at level $N$, weight
$k \ge 1$, with $a_1(f) = 1$, the **stripped Dirichlet series**
$$L^*(s, f) := \sum_{n \ge 1,\,\gcd(n, N) = 1} a_n(f) \, n^{-s}$$
extends to an entire function of $s \in \mathbb{C}$.*

**Classical proof (Hecke 1936; see [He], [DS §5.10], [Miy §4.3]).**
Three steps.

*Step 1: Mellin formula.*  On the half-plane $\mathrm{Re}\,s > k/2 + 1$,
the integral $\int_0^\infty f(iy) y^{s - 1} \, dy$ converges absolutely
by exponential decay of $f$, and equals
$$\Lambda(s, f) := N^{s/2} (2\pi)^{-s} \Gamma(s) L(s, f),$$
where $L(s, f) := \sum_{n \ge 1} a_n(f) \, n^{-s}$ is the (un-stripped)
Dirichlet series.

*Step 2: Fricke involution.*  Let $w_N := \left(\begin{smallmatrix} 0 & -1 \\ N & 0 \end{smallmatrix}\right)$.
For $\tau \in \mathfrak{H}$:
$$f\!\left(-\tfrac{1}{N\tau}\right) = i^k \, (N\tau)^k \, (f \mid_k w_N)(\tau).$$

*Step 3: Integral split.*  Write
$$\Lambda(s, f) = \int_0^{1/\sqrt N} f(iy) y^{s-1} \, dy + \int_{1/\sqrt N}^\infty f(iy) y^{s-1} \, dy$$
and apply the Fricke law with the substitution $y \mapsto 1/(Ny)$ to the
first integral.  After the substitution, the first integral becomes
$i^k \cdot N^{k/2 - s} \int_{1/\sqrt N}^\infty (f\!\mid_k w_N)(iy) y^{k - s - 1} \, dy$.

Both integrals from $1/\sqrt N$ to $\infty$ are **entire** in $s$
because cusp decay dominates $y^{s - 1}$ for every $s$.  Therefore
$\Lambda(s, f)$ is entire, and the functional equation
$$\Lambda(s, f) = i^k \cdot N^{k/2 - s} \cdot \Lambda(k - s, f \mid_k w_N)$$
follows from comparing the formula at $s$ and at $k - s$.

*Step 4: Strip the bad Euler factors.*  The stripped Dirichlet series
relates to $L(s, f)$ via $L(s, f) = L^*(s, f) \cdot \prod_{p \mid N}
(1 - a_p(f) p^{-s})^{-1}$ (Euler product, with vanishing
Atkin–Lehner-twisted contribution at primes ramifying in $N$).  For
newforms, the bad Euler factors $(1 - a_p(f) p^{-s})$ are entire and
nowhere vanishing on $\mathbb{C}$, so $L^*$ inherits entirety from $L$.

**How (B.L3.1) closes part of SMO.**  Combined with (B.L3.2) it
discharges the analytic contradiction of Theorem 6.4, hence the existence
of a good prime with non-vanishing eigenvalue.

### 7.3.  (B.L3.2) Trivial-zero Dirichlet contradiction

**Statement (B.L3.2).**
*Let $f$ be a newform in $S_k(\Gamma_1(N), \chi)$.  Let $S \subset
\mathbb{N}$ be a finite set, and suppose $a_q(f) = 0$ for every prime
$q \nmid N$, $q \notin S$.  Then $L^*(s, f)$ does **not** admit an
entire extension.*

**Classical proof.**  Combines three ingredients.

*Step 1: T111 stripped-Dirichlet identity (axiom-clean in the project).*
On the half-plane $\mathrm{Re}\,s > k/2 + 1$, the stripped series
factors as
$$L^*(s, f) = \frac{L(2s - k + 1, \tilde\chi^2) \cdot \prod_{p \in T} \mathrm{Num}_p(s)}{L(2s - k + 1, \tilde\chi) \cdot \prod_{p \in T} \mathrm{Den}_p(s)},$$
where:
- $\tilde\chi$ is the Dirichlet lift of $\chi$ to a primitive character;
- $T \subset S$ is the finite set of "bad-zero" primes (the primes in
  $S$ coprime to $N$);
- $\mathrm{Num}_p$, $\mathrm{Den}_p$ are explicit Euler-factor
  corrections.

This identity is a standard manipulation of the Euler product of $L(s, f)$
under the bad-prime hypothesis: if $a_q(f) = 0$ for $q \notin T$ coprime
to $N$, the resulting Euler factor at such $q$ collapses to
$(1 - \tilde\chi(q) q^{k - 1 - 2s})^{-1}$, leading to the squared-character
quotient.  The project has this identity proven axiom-clean.

*Step 2: Existence of a trivial zero (the "trivial-zero" route).*
For non-trivial Dirichlet character $\tilde\chi$ modulo $N$, the
completed $L$-function $\Lambda(s, \tilde\chi)$ is entire and obeys the
functional equation.  Since
$$\Lambda(s, \tilde\chi) = N^{s/2} \, \pi^{-(s + a)/2} \, \Gamma\!\left(\tfrac{s+a}{2}\right) \, L(s, \tilde\chi)$$
with $a \in \{0, 1\}$ depending on parity, the Γ-factor has simple poles
at $s + a = 0, -2, -4, \ldots$.  Because $\Lambda$ is everywhere finite,
$L(s, \tilde\chi)$ must vanish at these points:
- if $\tilde\chi$ is even ($a = 0$): trivial zeros at $s = 0, -2, -4, \ldots$;
- if $\tilde\chi$ is odd  ($a = 1$): trivial zeros at $s = -1, -3, \ldots$.

This is classical ([Da Ch. 9, Thm 9.1]).

Choose $s_0$ such that $2 s_0 - k + 1$ is a trivial zero of
$L(\cdot, \tilde\chi)$ with $\mathrm{Re}\,s_0 < 1$.  For weight $k \ge 2$,
such a choice exists: take $2 s_0 - k + 1 = -m$ for an integer $m \ge
\max(0, k - 1)$ of the appropriate parity, so $s_0 = (k - 1 - m)/2 \le 0
< 1$.

*Step 3: Numerator non-cancellation.*  At the chosen $s_0$, the
denominator $L(2 s_0 - k + 1, \tilde\chi) = 0$ but the rest of the
denominator factor $\prod_{p \in T} \mathrm{Den}_p(s_0)$ must remain
finite, and the numerator $L(2 s_0 - k + 1, \tilde\chi^2) \cdot \prod_{p \in T}
\mathrm{Num}_p(s_0)$ must remain non-zero.  For generic choice of
trivial-zero index $m$:
- $\tilde\chi^2$ is **distinct** from $\tilde\chi$ (assuming $\tilde\chi$
  is not of order 2), and its evaluation point $2(2 s_0 - k + 1) = -2m$
  differs from any trivial zero of $\tilde\chi^2$ unless $-2m$ is itself
  a trivial zero of $L(\cdot, \tilde\chi^2)$ — which happens at
  $-2m \in \{0, -2, -4, \ldots\}$ for even $\tilde\chi^2$, requiring
  $m$ of even parity.  Choose $m$ of odd parity to avoid this.
- The local Euler factors $\mathrm{Num}_p, \mathrm{Den}_p$ are polynomials
  in $p^{-s}$ that vanish only on a finite set of $s$; for sufficiently
  deep trivial-zero index (large $m$), the chosen $s_0$ avoids these
  finite sets.

*Step 4: Contradiction.*  The RHS has a pole at $s_0$ (denominator
vanishes, numerator does not), while any entire extension of the LHS
$L^*(s, f)$ would force a finite value at $s_0$.  Contradiction.

**Project packaging.**  These ingredients are packaged in the project as
the named structure `Newform.PerNewformFullDirichletData`, with the
trivial-zero / numerator non-cancellation fields as the genuinely
classical inputs.  The project provides axiom-clean consumers reducing
(B.L3.2) to providing these inputs.

---

## 8. Top-level chain

With (A.L3), (B.L3.1), and (B.L3.2) in hand, the SMO chain assembles as
follows (every link below is fully proven in Lean from the predecessors;
no further analytic content is required):

```
(A.L3)
   ↓
Per-character Main Lemma (Theorem 6.2 applied to (A.L3))
   ↓
newform_unique (via §5.2 argument: f - g lies in the same character space)
   ↓
                                              SMO (Theorem 6.5 cofinite-extension)
                                              ↑
(B.L3.1) + (B.L3.2)                          ↑
   ↓                                          ↑
Analytic contradiction (Theorem 6.4)          ↑
   ↓                                          ↑
Existence of good prime with non-vanishing eigenvalue
```

The five theorems on the right-hand vertical (per-character Main Lemma,
`newform_unique`, analytic contradiction, good-prime existence,
SMO-with-cofinite-extension) are **already fully proven in Lean** with
respect to the three obligations.  Discharging the obligations closes
the chain to axiom-cleanliness with respect to the standard triple.

---

## 9. Where we're stuck and what we've checked

We list, in decreasing order of certainty, the points where we'd most
like an expert eye.

### 9.1. Stuck point: the per-character Main Lemma's $q$-support claim

(A.L3) hinges on Miyake Lemma 4.6.5.  We have not yet formalised the
Möbius alternating-sum expression for $f_d$, nor the corresponding
indicator identity at the coefficient level.  The Lean project already
provides:

- $U_p = $ `heckeT_p_divN` (bad-prime Hecke operator), axiom-clean.
- $V_p = $ `modularFormLevelRaise` (level-raising operator), axiom-clean.
- Indicator identity $[\gcd(n, L) = 1] = \sum_{d \mid \gcd(n, L)} \mu(d)$
  — the project's `coprime_indicator_eq_sum_moebius`.
- All the structural support (`qSupportedOnDvdSubmodule N k d`, the
  character-space membership of $U_p$ and $V_p$).

The remaining work is the explicit construction of $f_d$ via the
Möbius sum, verification of $q$-support and character invariance, and
the Möbius reconstruction identity.  Estimate: a few hundred lines of
Lean, primarily arithmetic on $q$-expansions and reuse of existing
infrastructure.

### 9.2. Stuck point: Hecke functional equation

(B.L3.1) requires formalising the Mellin transform of a cusp form, the
Fricke involution law, and the integral-split entire-continuation
argument.  Mathlib provides:

- `StrongFEPair` / `WeakFEPair` (the abstract Mellin-pair API and
  functional-equation continuation argument).
- $\Gamma$-function, $L$-series, and absolute-convergence theory.

The remaining work is to fit a cusp form into the `StrongFEPair`
abstraction.  Estimate: roughly 200–400 lines, dominated by the Mellin
convergence argument and the cuspidal-decay bounds.

### 9.3. Stuck point: existence and selection of a trivial zero

For (B.L3.2), Mathlib has Dirichlet $L$-functions and their
meromorphic continuation but, as far as we know, does not have a single
named lemma "for non-trivial $\tilde\chi$ even, $L(0, \tilde\chi) = 0$"
(trivial zero existence).  Formalising the trivial zero would proceed
via the Γ-pole identification in the functional equation.

The numerator non-cancellation step (Step 3 of §7.3) involves picking
the trivial-zero index $m$ large enough to avoid finitely many
collisions — a finite computation in principle, but somewhat delicate
in practice.

Estimate: 300–600 lines.

### 9.4. The strategic point we're least sure about: route soundness

In §5.2 we claim that `newform_unique` only needs the per-character
Main Lemma, sidestepping the character-decomposition inheritance issue
that would obstruct the unconditional Main Lemma.  We are confident in
the classical mathematics but would like a second opinion on whether
the per-character path has any subtleties we've missed.  Specifically:

- The hypothesis `f - g ∈ S_k(\Gamma_1(N), \chi)` follows from $f$ and
  $g$ both being in $S_k(\Gamma_1(N), \chi)$, but in the project the
  hypothesis on $f, g$ is `f.toCuspForm.toModularForm' ∈
  modFormCharSpace k χ` (membership of the underlying modular form in
  the character space at the ModularForm level, not the CuspForm
  level).  We've verified that the project has a bridge
  `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace`
  identifying the two notions.  Is there a hidden subtlety here?
- The eigenvalue-to-Fourier-coefficient identification
  $a_n(f) = \lambda_n(f)$ for $n$ coprime to $N$ uses the project's
  axiom-clean `Newform.eigenvalue_eq_coeff`.  Standard.
- Disjointness of $S_k^{\mathrm{old}}$ and $S_k^{\mathrm{new}}$ at the
  character-space level: not separately stated in the project, but
  follows from disjointness at the full level.

### 9.5. Loose ends from the previous brief series

For completeness: the Petersson adjoint chain (Route A) is **not used**
in this plan, but the project still carries the partial
infrastructure (2 sorries inside `petN_heckeT_p_symmetric_form`, the
σ_p Q-permutation aggregate identity that was the focus of the 2026-05-11
T205-d briefs).  Route B closure means those sorries become **off the
SMO critical path** but remain useful for downstream applications
(spectral theorem, eigenform basis).

---

## 10. Questions for the reviewer

We ask eight numbered questions.

**Q1 (soundness of the per-character-only route).**
Is the §5.2 strategic insight — that `newform_unique` only needs the
per-character Main Lemma — mathematically correct?  Specifically: given
$f, g \in S_k(\Gamma_1(N), \chi)$ newforms with $\lambda_n(f) =
\lambda_n(g)$ for all $n$ coprime to $N$, is the application of the
per-character Main Lemma to $h := f - g \in S_k(\Gamma_1(N), \chi)$ a
genuinely complete argument for $h \in S_k^{\mathrm{old}}(\Gamma_1(N))$?
Are there any hidden hypotheses in the per-character Main Lemma that
we need separately for $h = f - g$ (versus a generic
$h \in S_k(\Gamma_1(N), \chi)$)?

**Q2 (inheritance obstruction).**
Our §5.2 box note claims that for arbitrary $f \in S_k(\Gamma_1(N))$
with coprime-to-$N$ Fourier vanishing at $\infty$, the $\chi$-pieces
$\pi_\chi f$ do not in general inherit coprime-to-$N$ Fourier vanishing
at $\infty$, because the diamond action by $\gamma_d \in \Gamma_0(N)
\setminus \mathrm{stab}_{\mathrm{SL}_2(\mathbb{Z})}(\infty)$ moves the
cusp.  Is this obstruction real, or is there a classical argument that
recovers inheritance from coprime-to-$N$ vanishing alone?

**Q3 ((A.L3) — sieve construction).**
Is our description of the per-character Möbius coprime sieve (§7.1)
classically correct?  Specifically:
1. Is the explicit alternating-sum formula
   $f_d = \sum_{T \subseteq \mathrm{primes}(N),\,d = \prod T}
   (-1)^{|T| - \omega(d)} \prod_{p \in T} V_p \circ U_p (f)$
   the right one?  Or is there a more standard form (e.g., directly via
   $U_p$/$V_p$ in a different order)?
2. The character-invariance step relies on $U_p$ and $V_p$ commuting
   with all diamond operators.  This is DS Prop 5.2.4(a) for $U_p$ at
   $p \nmid N$ but our $U_p$ here is the **bad-prime** Hecke operator at
   $p \mid N$.  Is the commutation still valid?  (We believe yes via
   direct computation.)

**Q4 ((B.L3.1) — Hecke FE formalisation).**
Has anyone produced a clean Lean / Mathlib formalisation of Hecke's
1936 functional equation for cusp-form L-functions?  Mathlib has
`StrongFEPair` and we plan to fit a cusp form into that abstraction —
is this the right path, or is there a known better route?  Are there
edge cases we should worry about (e.g., wrong sign at $k$ odd,
parity-of-character interactions with the Fricke law)?

**Q5 ((B.L3.2) — trivial zero strategy).**
Our trivial-zero approach (§7.3 Step 2) picks $s_0$ so that
$2 s_0 - k + 1$ is a trivial zero of $L(\cdot, \tilde\chi)$ with
$\mathrm{Re}\,s_0 < 1$.  For weight $k \ge 2$, the parity of the
trivial zero index $m$ has to match the parity of $\tilde\chi$, AND
the numerator $L(\cdot, \tilde\chi^2)$ needs to be non-zero at the
*doubled* point $2(2 s_0 - k + 1) = -2m$.  Is there a clean systematic
choice of $m$ (e.g., "take the smallest $m$ that satisfies …") that
avoids all the finite collisions?  Or do we have to handle case
distinctions on parity of $\chi$, order of $\chi$, etc.?

**Q6 (numerator non-cancellation in T111).**
The T111 identity (§7.3 Step 1) involves finite Euler-factor
corrections at primes in $T$ (the bad-prime set coprime to $N$).  At
our chosen $s_0$, we need $\prod_{p \in T} \mathrm{Num}_p(s_0) \ne 0$.
These factors are polynomials in $p^{-s}$, so they have only finitely
many zeros, and we can pick $s_0$ deep enough to avoid them — but the
"deep enough" requirement creates a circular dependence on the size of
$T$, which depends on the input $S$.  Is there an elegant way to phrase
this dependency, or do we have to do an explicit case split on $T$?

**Q7 (parity / order assumptions on $\chi$).**
Our (B.L3.2) argument requires $\tilde\chi$ to be **non-trivial** for
the trivial zero to exist.  When the bad-prime hypothesis is
non-vacuous, is non-triviality automatic?  Specifically: if $f$ is a
newform with $a_q(f) = 0$ for every prime $q \nmid N$ outside a finite
set $S$, does this force $\tilde\chi \ne 1$?  (If $\tilde\chi = 1$ then
$L(s, \tilde\chi)$ is essentially $\zeta(s)$, which has trivial zeros
but lacks our non-cancellation property.)  We suspect this case is
either handled by other ingredients of the T111 identity or is
mathematically vacuous, but we'd like to confirm.

**Q8 (strategic priority).**
Of the three level-3 obligations, which should we tackle first?  Our
intuition:
- (A.L3) is the most constructive and reuses existing project
  infrastructure ($U_p$, $V_p$, the coprime indicator); plausible to
  close in ~200 lines.
- (B.L3.1) is heavier (Mellin + Fricke + integral split, ~200–400
  lines).
- (B.L3.2) is intricate (trivial zero existence + non-cancellation +
  parity bookkeeping, ~300–600 lines).

Does the reviewer agree with this ordering and cost distribution?  Are
there shared sub-lemmas between any pair of obligations that we should
factor out before starting?

---

## 11. Document metadata

- Project name: LeanModularForms-hecke (Strong Multiplicity One in
  Lean 4 / Mathlib).
- Brief generated: 2026-05-16.
- Audience: the same frontier-LLM reviewer as the 2026-05-11 series
  (SMO overview, T205-d focused, T205-d restructured residual).
- Convention: Diamond–Shurman.
- Length: ~10 pages.
- Build status: compiles cleanly; the SMO plan file carries exactly
  three `sorry`s (the three level-3 obligations in §5.3 / §7); all
  higher-level theorems verify with the standard triple plus
  `sorryAx` (will be `{propext, Classical.choice, Quot.sound}` only
  when the three obligations are filled).
- Strategic change from prior briefs: the project has pivoted from
  Route A (spectral, Petersson-adjoint-dependent) to Route B (Miyake
  induction, adjoint-free).  The 2026-05-11 T205-d residual is now
  **off the SMO critical path** but retained for downstream
  applications.

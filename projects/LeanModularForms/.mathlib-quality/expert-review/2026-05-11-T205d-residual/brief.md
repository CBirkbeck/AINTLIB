# Review brief — T205-d closure strategy: the restructured residual `petN_heckeT_p_symmetric_form`

*Prepared 2026-05-11 (third follow-up). Same reviewer audience as the 2026-05-11 SMO-overview and 2026-05-11 T205-d-focused briefs. Self-contained but assumes the previous briefs and replies are accessible if needed. Conventions follow Diamond–Shurman and Miyake throughout.*

---

## 1. What this brief is about

This brief is a **third pass** on the level-$N$ Petersson-adjoint problem for the good-prime Hecke operator $T_p$, $p \nmid N$ (Diamond–Shurman Theorem 5.5.3 / Miyake Theorem 4.5.4). The first two briefs:

- **2026-05-11 SMO overview**: project-wide architecture, the reviewer's "two-step API" advice (finite-index FD-transport + Hecke-correspondence adjoint).
- **2026-05-11 T205-d focused**: detail on the 8-layer scaffold that had grown around T205-d; the reviewer corrected our brief's confused statement (we asked about the $\alpha^{-1}$ form; the code is in adjugate $\alpha^*$ form) and recommended a four-ticket decomposition (pointwise integrand → integral → double-coset → specialise).

After the previous reply, the project undertook a **restructuring pass** that concentrated the entire residual analytic content of T205-d into a single clean named theorem. That restructuring builds cleanly. **The purpose of this brief is to ask for strategic guidance on what to do next.**

There is now exactly one mathematical residual blocking the level-$N$ DS 5.5.3 chain. We have spelled it out in full mathematical detail below (§5). The previous reviewer-recommended closure paths (direct DS Prop 5.5.2(b) formalisation, AL–Li orthogonality, $U_p$ decomposition) were all categorised as multi-day to multi-week formalisations; none has been started. We want the reviewer to weigh in on three things:

1. **Soundness check** of the restructuring itself: is the chain that derives the unsymmetric DS standard form from the symmetric form mathematically valid?
2. **Strategic guidance** on which closure path to commit to.
3. **Concrete sub-lemma planning**: an explicit list of intermediate lemmas, with estimated cost per step, so we can run the work as a focused multi-session push instead of repeatedly hitting the same wall.

The questions are in §10. The structural and mathematical context fills §2–§9.

---

## 2. Notation and conventions

We restate notation that the prior briefs established. Conventions throughout follow Diamond–Shurman.

### 2.1 Groups and Hecke pair

- $\mathrm{GL}_2^+(\mathbb{R}) = \{\alpha \in \mathrm{GL}_2(\mathbb{R}) : \det\alpha > 0\}$ acts on $\mathfrak{H} = \{\tau \in \mathbb{C} : \mathrm{Im}\,\tau > 0\}$ by Möbius transformations $\alpha\tau = (a\tau+b)/(c\tau+d)$.
- $\Gamma(N) = \ker(\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N))$, $\Gamma_1(N) = \{\gamma : \gamma \equiv \left(\begin{smallmatrix}1&*\\0&1\end{smallmatrix}\right) \bmod N\}$, $\Gamma_0(N) = \{\gamma : c \equiv 0 \bmod N\}$.
- $\Delta_0(N) = \{\alpha \in M_2(\mathbb{Z}) : c \equiv 0 \bmod N,\ \gcd(a,N) = 1,\ \det\alpha > 0\}$ is the level-$N$ Hecke monoid.
- The Hecke pair is $(\Gamma_0(N), \Delta_0(N))$.

### 2.2 Slash action

For $\alpha = \left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right) \in \mathrm{GL}_2^+(\mathbb{R})$ and integer weight $k \geq 1$:
$$(f \mid_k \alpha)(\tau) := (\det\alpha)^{k-1}\,(c\tau+d)^{-k}\,f(\alpha\tau).$$
We use the cocycle $j(\alpha,\tau) := c\tau+d$. Standard identities: $\mathrm{Im}(\alpha\tau) = \det\alpha \cdot \mathrm{Im}\,\tau / |j(\alpha,\tau)|^2$, $j(\alpha\beta,\tau) = j(\alpha,\beta\tau) \cdot j(\beta,\tau)$, $j(\alpha^*,\alpha\tau) = \det\alpha / j(\alpha,\tau)$ where $\alpha^* := \det\alpha \cdot \alpha^{-1}$ is the matrix adjugate.

### 2.3 Petersson products

The integrand on $\mathfrak{H}$ is
$$\mathrm{petersson}_k(f, g)(\tau) := f(\tau)\,\overline{g(\tau)}\,(\mathrm{Im}\,\tau)^k,$$
and the hyperbolic measure is $\mathrm{d}\mu_{\mathrm{hyp}} = (\mathrm{Im}\,\tau)^{-2}\,\mathrm{d}x\,\mathrm{d}y$.

The **level-1 Petersson form** on $S_k(\mathrm{SL}_2(\mathbb{Z}))$ is
$$\langle f, g \rangle := \int_{\mathcal{D}} \mathrm{petersson}_k(f, g)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}$$
where $\mathcal{D}$ is the standard $\mathrm{SL}_2(\mathbb{Z})$-fundamental domain.

The **level-$N$ Petersson form** $\langle\cdot,\cdot\rangle_N$ on $S_k(\Gamma_1(N))$ is defined by
$$\langle f, g \rangle_N := \sum_{[q] \in \mathrm{SL}_2(\mathbb{Z}) / \Gamma_1(N)} \int_{\mathcal{D}} \mathrm{petersson}_k(f \mid_k q^{-1},\ g \mid_k q^{-1})(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}.$$
This is the level-1 form summed over (right-)coset representatives of $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb{Z})$.

### 2.4 Diamond operator and Hecke operator

For $u \in (\mathbb{Z}/N)^\times$, the **diamond operator** $\langle u \rangle$ on $S_k(\Gamma_1(N))$ is slash by any element $\gamma \in \Gamma_0(N)$ whose lower-right entry reduces to $u$ mod $N$. The action is well-defined modulo $\Gamma_1(N)$.

For $p \nmid N$, the **Hecke operator** $T_p$ on $S_k(\Gamma_1(N))$ has the standard $p+1$ coset decomposition
$$T_p f = \sum_{b=0}^{p-1} f \mid_k \begin{pmatrix} 1 & b \\ 0 & p \end{pmatrix} + \langle p \rangle\, f \mid_k \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}.$$

We write $u := \overline{p} \in (\mathbb{Z}/N)^\times$ for the residue class of $p$. So $\langle p \rangle$ in the formula above is shorthand for $\langle u \rangle$.

### 2.5 The $\sigma_p$ Q-permutation

Following Miyake §4.5 and the project's existing code, $\sigma_p \in \Gamma_0(N) \cap \mathrm{SL}_2(\mathbb{Z})$ is a specific element with lower-right entry $\equiv p \bmod N$ — in particular $\sigma_p \in \mathrm{SL}_2(\mathbb{Z})$ realises the diamond action $\langle u \rangle$ on cusp forms (i.e., $f \mid_k \sigma_p = \langle u \rangle f$).

There is a corresponding bijection $\sigma_p^* : \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N) \to \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$ given by $[q] \mapsto [\sigma_p\, q]$. This is the **$\sigma_p$ Q-permutation** used in DS / Miyake's proofs.

### 2.6 The Hecke representatives at level $\Gamma_1(N)$

For $p \nmid N$ and $\alpha = \mathrm{diag}(1, p) \in \Delta_0(N)$, the double coset $\Gamma_1(N)\, \alpha\, \Gamma_1(N)$ has the $p+1$ representatives
$$\beta_b := \begin{pmatrix} 1 & b \\ 0 & p \end{pmatrix} \quad (0 \leq b < p), \qquad \beta_\infty := \gamma_\infty \cdot \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}$$
for a specific $\gamma_\infty \in \Gamma_1(N)$ chosen so that $\beta_\infty \in \Delta_0(N)$.

The **adjugate side**: $\alpha^* = \mathrm{diag}(p, 1)$ has double coset $\Gamma_1(N)\,\alpha^*\,\Gamma_1(N)$, which equals (as a *set*, in $M_2(\mathbb{Z})$) the original $\Gamma_1(N)\,\alpha\,\Gamma_1(N)$ left-translated by an element with diamond character $u^{-1}$. This is the source of the diamond twist in DS 5.5.3.

---

## 3. References

- **[DS]** Fred Diamond and Jerry Shurman. *A First Course in Modular Forms*. Graduate Texts in Mathematics 228. Springer, 2005. (Key: §5.5, particularly Proposition 5.5.2 and Theorem 5.5.3.)
- **[Mi]** Toshitsune Miyake. *Modular Forms*. Springer Monographs in Mathematics, 2nd ed., 2006. (Key: §4.5, Theorems 4.5.4 and 4.5.5.)
- **[Sh]** Goro Shimura. *Introduction to the Arithmetic Theory of Automorphic Functions*. Princeton, 1971. (Key: §3, particularly Theorems 3.20, 3.24, 3.34.)
- **[AL]** A. O. L. Atkin and J. Lehner. "Hecke operators on $\Gamma_0(m)$." *Math. Ann.* **185** (1970), 134–160.
- **[Li]** W.-C. W. Li. "Newforms and functional equations." *Math. Ann.* **212** (1975), 285–315.

---

## 4. The two-step API status (from the prior brief's reply)

The 2026-05-11 reviewer reply recommended a two-step API for T205-d:

> **(Step 1)** Finite-index FD-transport from $\mathrm{PSL}_2(\mathbb{R})$ to $\Gamma_1(N) \backslash \mathfrak{H}$ via $\Gamma_p(\alpha) := \alpha^{-1}\Gamma_1(N)\alpha \cap \Gamma_1(N)$.
>
> **(Step 2)** Hecke-correspondence adjoint identity at level $\Gamma_1(N)$, parametric in $\alpha \in \Delta_0(N)$:
> $$\langle T_\alpha f, g \rangle_N = \langle f, T_{\alpha^*} g\rangle_N$$
> (determinant/character-free at this stage; corrections enter at specialisation).

The reviewer further decomposed Step 2 into:
- **(2a) Pointwise integrand identity** (DS Prop 5.5.2(b) at the integrand level): $\mathrm{petersson}_k(f \mid_k \alpha,\, g)(\tau) = \mathrm{petersson}_k(f,\, g \mid_k \alpha^*)(\alpha\tau)$.
- **(2b) Domain-level integral version**: integrate the above over a measurable domain and apply Möbius change-of-variables.
- **(2c) Double-coset assembly**: aggregate over the $p+1$ Hecke representatives.
- **(2d) Specialisation**: identify the adjugate-side correspondence with $\langle p \rangle^{-1} T_p$ via $\sigma_p$ Q-permutation.

### Status as of this brief:

- **Step 1 (FD-transport)**: DONE, sorry-free, axiom-clean (apart from `propext`, `Classical.choice`, `Quot.sound`).
- **Step 2a (pointwise integrand identity)**: implicit in the existing project lemma that proves the *integral* form (described in §5 below); not yet extracted as a named pointwise lemma.
- **Step 2b (domain-level integral form)**: DONE — the project has this as `peterssonInner_slash_adjoint` (an integrated version of DS Prop 5.5.2(b)), stated with $\alpha^*$ via the adjugate `peterssonAdj`.
- **Step 2c (double-coset assembly)**: OPEN — this is the missing piece.
- **Step 2d (specialisation)**: scaffold present but blocked on 2c.

---

## 5. The restructured residual

After the previous brief's reply was integrated and a marathon session traced the existing 14-layer scaffold, the project performed a **restructuring pass**. The previous sorry, which had been buried inside a per-q decomposition / iUnion-form / σ_p-reindex chain, was concentrated into a **single named theorem**:

> **Target (the sole T205-d residual): `petN_heckeT_p_symmetric_form`.**
> *Let $N \geq 1$, $k \geq 2$, $p$ a prime with $p \nmid N$. Write $u = \overline{p} \in (\mathbb{Z}/N)^\times$. For all cusp forms $f, g \in S_k(\Gamma_1(N))$:*
> $$\langle T_p f,\, g \rangle_N \;=\; \langle \langle u \rangle f,\, T_p g \rangle_N.$$

This is **DS Theorem 5.5.3 in its symmetric form**: $T_p^*$ on $S_k(\Gamma_1(N))$ equals $\langle u \rangle^{-1} T_p$ when we move the diamond to the *first slot*.

### 5.1 Why this is the sole residual

The project has the following downstream chain, all sorry-free apart from this single target:

> **Existing chain (sorry-free given the target above).**
> 1. From `petN_heckeT_p_symmetric_form` and a routine algebraic step (diamond unitarity + $\langle u \rangle \circ \langle u \rangle^{-1} = \mathrm{id}$), one derives the **unsymmetric form**
> $$\langle T_p f,\, g \rangle_N = \langle f,\, \langle u \rangle^{-1}(T_p g) \rangle_N \qquad (\dagger)$$
> via `petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form` (a 50-line composition of the symmetric form with `h_LHS_dist_eq_RHS_absorbed_from_petN_symmetric_form` and `petN_heckeT_p_adjoint_standard_form_via_sum_chain`).
> 2. The unsymmetric form $(\dagger)$ in turn yields the **canonical adjoint identity** $\langle T_p f, g \rangle_N = \langle f, T_p(\langle u \rangle^{-1} g) \rangle_N$ via `heckeT_p_comm_diamondOp` (the well-established Hecke/diamond commutation).
> 3. Both forms give the **spectral input** required for the simultaneous eigenform basis theorem `exists_simultaneous_eigenform_basis` (T207, already done).
> 4. The spectral basis + Hecke-eigenform structure feeds into the Miyake Main Lemma (POST-6) and Strong Multiplicity One (POST-7), both of which depend on this chain.

### 5.2 The restructuring chain in detail

The cleanest description: the entire 14-layer scaffold (per-q decomposition, M_∞ stockpile, iUnion-form residuals, $\sigma_p$ reindex on Hecke-translated tiles) is **bypassed** by the consumer

> **Lemma (existing, no sorry): "DS standard form from symmetric form".**
> *Let $f, g \in S_k(\Gamma_1(N))$. If $\langle T_p f, g \rangle_N = \langle \langle u \rangle f, T_p g \rangle_N$, then*
> $$\langle T_p f, g \rangle_N = \langle f, \langle u \rangle^{-1}(T_p g) \rangle_N.$$

This lemma's proof (already in the project) composes three sub-lemmas:
- `h_LHS_dist_eq_RHS_absorbed_from_petN_symmetric_form` (sum-level identity derived from the symmetric form alone, ~80 lines, no new analytic content);
- `petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain` (the reverse direction, ~120 lines);
- `petN_heckeT_p_adjoint_standard_form_of_LHS_bridge` (~40 lines).

All three are sorry-free and use only:
- Per-$q$ unfolding of $\langle\cdot,\cdot\rangle_N$ over the $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$ coset sum.
- The level-1 Petersson form's behaviour under slash by $\mathrm{SL}_2(\mathbb{Z})$ elements (mathlib's `petersson_slash_SL`).
- The diamond/Hecke commutation `heckeT_p_comm_diamondOp` (standalone, sorry-free).
- The $\sigma_p$ Q-permutation `Gamma1QuotEquivOfGamma0` (mathlib's quotient-equivalence for $\Gamma_1$ inside $\Gamma_0$).
- The diamond unitarity of $\langle\cdot,\cdot\rangle_N$ (i.e., $\langle \langle u \rangle f, \langle u \rangle g \rangle_N = \langle f, g \rangle_N$ for any $u \in (\mathbb{Z}/N)^\times$).

So the *entire* analytic content of T205-d sits in the single target inequality of §5. The reviewer's recommended decomposition (2c) is exactly equivalent to this single named identity.

### 5.3 Why the target identity is non-trivial

Every algebraic manipulation we have tried produces either a tautology (via diamond unitarity and Hecke/diamond commutation) or a circular dependency in the existing chain. Concretely:

- The natural manipulation $\langle T_p f, g \rangle_N = \langle T_p(\langle u \rangle f), \langle u \rangle g\rangle_N$ (apply $\sigma_p$ Q-permutation to the level-$N$ coset sum) combined with $T_p \circ \langle u \rangle = \langle u \rangle \circ T_p$ and diamond unitarity collapses to $\langle T_p f, g \rangle_N$. **Tautology.**
- Hermitian symmetry + the same reindex gives $\langle \langle u \rangle f, T_p g \rangle_N = \overline{\langle T_p g, \langle u \rangle f \rangle_N} = \overline{\langle T_p(\langle u \rangle^{-1} g), f \rangle_N} = \langle f, \langle u \rangle^{-1}(T_p g)\rangle_N$ — which is the *canonical adjoint identity*, i.e., what the symmetric form is *supposed to imply*. So this is a forward derivation of the canonical form from the symmetric form, not a proof of the symmetric form.
- Any approach that derives the symmetric form from the unsymmetric or canonical form is **circular**: the symmetric form is what proves the unsymmetric form in our restructuring.

So the symmetric form is *informationally* equivalent to DS 5.5.3, and any proof of *any equivalent form* will resolve T205-d. The choice of which form to target is a strategic question about formalisation cost.

---

## 6. Closure paths under consideration

### 6.1 Path A — direct DS Prop 5.5.2(b) at sum level

This was the previous reviewer's recommended ticket structure:

**Path A sub-lemmas:**

- **A1. Pointwise integrand identity.** For $\alpha \in \mathrm{GL}_2^+(\mathbb{R})$, $\tau \in \mathfrak{H}$:
$$\mathrm{petersson}_k(f \mid_k \alpha,\, g)(\tau) = \mathrm{petersson}_k(f,\, g \mid_k \alpha^*)(\alpha\tau). \tag{*}$$

  *Status*: implicit in the project's `peterssonInner_slash_adjoint` proof (the integral version). Extracting it as a named pointwise lemma is ~30 lines.

  *Mathematical content*: combines the two cocycle identities $j(\alpha^*,\alpha\tau) = \det\alpha / j(\alpha,\tau)$ and $\mathrm{Im}(\alpha\tau) = \det\alpha \cdot \mathrm{Im}\,\tau / |j(\alpha,\tau)|^2$ with $|j|^{2k} = j^k \overline{j}^k$.

- **A2. Per-(β, q) integrated version.** For each Hecke coset rep $\beta \in \{\beta_b\}_{b<p} \cup \{\beta_\infty\}$ and each $q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$:
$$\int_{\mathcal{D}} \mathrm{petersson}_k(f \mid_k (\beta q^{-1}),\, g \mid_k q^{-1})(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}} = \int_{(\beta q^{-1}) \cdot \mathcal{D}} \mathrm{petersson}_k(f,\, g \mid_k \beta^*)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}.$$

  *Status*: this is `peterssonInner_slash_adjoint` instantiated with $\alpha = \beta q^{-1}$ — already in the project, sorry-free.

- **A3. Sum-over-$q$ tile aggregation.** Sum A2 over $q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$. The union $\bigcup_q \beta q^{-1} \cdot \mathcal{D}$ equals $\beta \cdot \mathcal{F}_N$ where $\mathcal{F}_N := \bigcup_q q^{-1} \cdot \mathcal{D}$ is a $\Gamma_1(N)$-FD; AE-disjointness gives the integral over the union as a sum.

  *Status*: pieces in place (`peterssonInner_iUnion_finite_aedisjoint`, `aedisjoint_pairwise_T_p_family`, etc.); a top-level assembly lemma at ~80 lines.

- **A4. $\sigma_p$ Q-permutation absorption.** Show that $\sum_\beta \langle f \mid_k \beta,\,g \rangle_N$ equals $\sum_\beta \langle \langle u \rangle f,\, g \mid_k \beta \rangle_N$ after applying $\sigma_p$ on the index $(\beta, q)$.

  *Status*: this is the hard step, and it is exactly the "DS Prop 5.5.2(b) at sum level + $\sigma_p$ Q-permutation absorption" the previous brief flagged. The $\sigma_p$ map on the $p+1$ Hecke representatives is well-defined (Miyake §4.5), but the bookkeeping is delicate.

  Estimated: 200–400 lines depending on whether we factor it through DS's own $\sigma_p$-explicit description.

- **A5. Specialisation to $T_p$.** From A4, deduce the symmetric form. ~30 lines.

**Total estimate**: 350–550 lines of Lean.

### 6.2 Path B — Atkin–Lehner–Li orthogonality

Prove the orthogonal decomposition $S_k(\Gamma_1(N)) = S_k^{\mathrm{old}}(\Gamma_1(N)) \oplus^\perp S_k^{\mathrm{new}}(\Gamma_1(N))$ under $\langle\cdot,\cdot\rangle_N$ directly, via Li's explicit basis of $S_k^{\mathrm{old}}$ from $S_k^{\mathrm{new}}(\Gamma_1(M))$ for $M \mid N$, $M < N$, and a termwise integral computation.

The previous reviewer flagged this as likely *circular* with T205-d: Li's argument [Li1975, §2] uses the Hecke adjoint identity as input. We have not independently verified this circularity claim.

### 6.3 Path C — $U_p$ eigenspace decomposition

For $p \mid N$, the operator $U_p$ has known explicit eigenspace structure. This is a bad-prime tool and the previous reviewer noted it does not give the good-prime $T_p$ adjoint identity.

### 6.4 Path D — Use spectrality input from a different source

Per the reviewer's remark in the 2026-05-11 reply: "Future Hecke-theoretic infrastructure (direct integral computation via Hecke double-coset structure, or mathlib's eventual abstract Hecke ring formalization) can supply this hypothesis." We have not investigated whether such mathlib infrastructure is on a contributor's near-term roadmap.

---

## 7. The single named residual: full mathematical statement

For self-containedness we restate the target with full detail:

> **Target identity (`petN_heckeT_p_symmetric_form`).**
> *Let $N \geq 1$, $k \geq 2$, $p$ a prime with $p \nmid N$. Let $u = \overline{p} \in (\mathbb{Z}/N)^\times$. For all $f, g \in S_k(\Gamma_1(N))$:*
> $$\sum_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \int_{\mathcal{D}} \mathrm{petersson}_k(T_p f \mid_k q^{-1},\, g \mid_k q^{-1})(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}(\tau)$$
> $$=\; \sum_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \int_{\mathcal{D}} \mathrm{petersson}_k(\langle u \rangle f \mid_k q^{-1},\, T_p g \mid_k q^{-1})(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}(\tau).$$

Unfolding the LHS via the coset decomposition of $T_p$:

$$T_p f \mid_k q^{-1} = \sum_{b=0}^{p-1} f \mid_k (\beta_b q^{-1}) + f \mid_k (\beta_\infty q^{-1}).$$

After applying the level-1 slash adjoint identity per $(\beta, q)$-summand (justified by `peterssonInner_slash_adjoint` and Möbius change-of-variables; this is the path A2 input above) and aggregating over $q$ (A3), the LHS reduces to
$$\sum_{\beta} \int_{\mathcal{F}_N} \mathrm{petersson}_k(f \mid_k \beta,\, g)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}$$
where the sum is over $\beta \in \{\beta_b\}_{b<p} \cup \{\beta_\infty\}$.

By a parallel manipulation, the RHS reduces to
$$\sum_{\beta} \int_{\mathcal{F}_N} \mathrm{petersson}_k(\langle u \rangle f,\, g \mid_k \beta)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}.$$

The remaining content is to show these two sums are equal:
$$\sum_{\beta} \int_{\mathcal{F}_N} \mathrm{petersson}_k(f \mid_k \beta,\, g)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}} \;=\; \sum_{\beta} \int_{\mathcal{F}_N} \mathrm{petersson}_k(\langle u \rangle f,\, g \mid_k \beta)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}. \tag{**}$$

This is the **central identity** (**) — it does not factor as a per-$\beta$ identity (the per-$\beta$ versions fail individually because the integrand is not $\Gamma_1(N)$-invariant), but the *sum* over the $p+1$ representatives balances via the $\sigma_p$ Q-permutation.

---

## 8. Where work breaks down

### 8.1 Why (**) cannot be proven by single-coset slash-adjoint

For a single $\beta$, by Möbius change of variables and DS Prop 5.5.2(a):
$$\int_{\mathcal{F}_N} \mathrm{petersson}_k(f \mid_k \beta,\, g)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}} \;=\; \int_{\beta \cdot \mathcal{F}_N} \mathrm{petersson}_k(f,\, g \mid_k \beta^*)(\tau)\,\mathrm{d}\mu_{\mathrm{hyp}}.$$

The domain $\beta \cdot \mathcal{F}_N$ is a fundamental domain for $\beta \Gamma_1(N) \beta^{-1}$, not for $\Gamma_1(N)$ — *unless* $\beta \in N_{\mathrm{GL}_2^+(\mathbb{R})}(\Gamma_1(N))$, which fails for $\beta \in \Delta_0(N) \setminus \Gamma_0(N)$.

Therefore $\int_{\beta\cdot \mathcal{F}_N} \mathrm{petersson}_k(f, g \mid_k \beta^*) \neq \int_{\mathcal{F}_N} \mathrm{petersson}_k(f, g \mid_k \beta^*)$ in general, and the per-$\beta$ equality in (**) does *not* hold.

### 8.2 Why the σ_p Q-permutation is needed

The classical proof in DS / Miyake shows that the *sum* $\sum_\beta$ on each side is reorganisable such that domain shifts cancel via the $\sigma_p$ map. Concretely:

For each $\beta$ in the coset transversal of $T_p$, the adjugate $\beta^*$ lies in the **adjugate double coset** $\Gamma_1(N) \alpha^* \Gamma_1(N)$ where $\alpha = \mathrm{diag}(1,p)$, $\alpha^* = \mathrm{diag}(p,1)$. This adjugate double coset is *related* to $\Gamma_1(N) \alpha \Gamma_1(N)$ via the diamond $\langle u^{-1} \rangle$:
$$\Gamma_1(N)\, \mathrm{diag}(p,1)\, \Gamma_1(N) \;=\; \langle u^{-1} \rangle \cdot \Gamma_1(N)\, \mathrm{diag}(1,p)\, \Gamma_1(N)$$
where the LHS denotes the set of matrices $\{\gamma_1 \cdot \mathrm{diag}(p,1) \cdot \gamma_2 : \gamma_i \in \Gamma_1(N)\}$ and equality is as a subset of $M_2(\mathbb{Z})$ after appropriate normalisation.

Iterating this: each $\beta$ has a *canonical paired adjugate-side representative* $\beta'$ such that $\beta^* = \delta_\beta \cdot \beta' \cdot \eta_\beta$ for some $\delta_\beta \in \Gamma_0(N)$ with $\langle \delta_\beta \rangle = \langle u \rangle^{-1}$ and $\eta_\beta \in \Gamma_1(N)$. The map $\beta \mapsto \beta'$ is the **$\sigma_p$ Q-permutation on Hecke representatives** (Miyake §4.5).

The proof of (**) goes through this $\beta \leftrightarrow \beta'$ correspondence: each $\beta$-term on the LHS pairs with the $\beta'$-term on the RHS via a domain shift cancellation involving $\delta_\beta$ and $\eta_\beta$.

This bookkeeping is the genuine analytic content of DS Theorem 5.5.3 — it is not algebraically derivable from any combination of $T_p / \langle u \rangle$ commutation, diamond unitarity, $\sigma_p$ reindex on $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$, and `petersson_slash_SL` that we have tried.

### 8.3 What HAS been verified algebraically

For completeness, we list the algebraic identities that *are* available in the project:

- **`heckeT_p_comm_diamondOp`** (sorry-free): $T_p \circ \langle u \rangle = \langle u \rangle \circ T_p$ for $u \in (\mathbb{Z}/N)^\times$, $p \nmid N$.
- **`petN_slash_invariant`** (sorry-free): for $\gamma \in \Gamma_0(N)$, $\langle f \mid_k \gamma, g \mid_k \gamma \rangle_N = \langle f, g \rangle_N$. Specialised to $\sigma_p \in \Gamma_0(N)$: $\langle \langle u \rangle f, \langle u \rangle g \rangle_N = \langle f, g \rangle_N$ (diamond unitarity).
- **`petN_heckeT_p_Gamma1QuotEquiv_reindex`** (sorry-free, derived from `petersson_slash_SL` + `Gamma1QuotEquivOfGamma0`): for any $\gamma \in \Gamma_0(N)$,
$$\langle T_p f, g \rangle_N = \langle T_p(\langle \gamma\rangle f),\,\langle\gamma\rangle g\rangle_N.$$
Combined with `heckeT_p_comm_diamondOp` and diamond unitarity, this collapses to $\langle T_p f, g\rangle_N$. Tautology.
- **`petN_f_heckeT_p_adjointGamma0Rep_reindex`** (sorry-free): for $\gamma_0 \in \Gamma_0(N)$ with diamond character $u^{-1}$,
$$\langle f, T_p g \rangle_N = \langle \langle u^{-1}\rangle f,\, T_p(\langle u^{-1}\rangle g)\rangle_N.$$
With Hermitian symmetry, this is equivalent to the canonical form $\langle T_p f, g\rangle_N = \langle f, \langle u^{-1}\rangle(T_p g)\rangle_N$ — but this is **circular** in the project's restructuring, where the canonical form is derived from the symmetric form.

We have systematically applied each of these and combinations thereof. Every combination either:
- Yields a tautology after diamond unitarity, OR
- Round-trips to an identity equivalent to (**) (which is what we're trying to prove), OR
- Is circular in the project's Lean elaboration order (forward reference to a downstream theorem).

---

## 9. Status of ticket board

| Ticket | Mathematical statement | Status |
|---|---|---|
| `T205-d-API-1` | Finite-index FD-transport $\mathrm{PSL}_2(\mathbb{R})\!\to\!\Gamma_1(N)\!\backslash\!\mathfrak{H}$ | **done**, axiom-clean |
| `T205-d-API-2-INT` | Domain-level adjugate slash adjoint | **done** (existing `peterssonInner_slash_adjoint`) |
| `T205-d-API-2-DC` | Double-coset adjugate correspondence | **superseded** by restructuring (the symmetric form below subsumes it) |
| `T205-d-API-2-DC-IUNION-M` / `IUNION-T` / `CLOSE` | iUnion-form σ_p absorption residuals | **superseded** (Path A sub-lemmas A3/A4 do the same work) |
| `T205-d` | DS 5.5.3 unsymmetric: $\langle T_p f, g\rangle_N = \langle f, \langle u\rangle^{-1}T_p g\rangle_N$ | **proven conditionally** on `T205-d-SYMM` |
| `T205-d-SYMM` (this brief's target) | DS 5.5.3 symmetric: $\langle T_p f, g\rangle_N = \langle\langle u\rangle f, T_p g\rangle_N$ | **open** — sorry, single named residual |
| `T207` | Simultaneous Hecke eigenform basis on $S_k(\Gamma_1(N), \chi)$ | **done**, depends on `T205-d` as spectral input |
| `T209` | Atkin–Lehner–Li orthogonality | **open**, depends on `T205-d` |
| `T210` | Newform decomposition $S_k(\Gamma_1(N)) = \bigoplus_{M\mid N, d\mid N/M} \alpha_d S_k^{\mathrm{new}}(\Gamma_1(M))$ | **open**, depends on `T209` |
| `POST-6` | Miyake Main Lemma 4.6.8 (sparse Fourier supports) | **open**, depends on `T207` + `T205-d` |
| `POST-7` | Strong Multiplicity One (Miyake 4.6.12) | **conditional version landed**; full SMO depends on `POST-6` + L-function non-vanishing |

The project has exactly **one** open mathematical sorry on the SMO critical path: `T205-d-SYMM` (the symmetric form). Every other ticket in the chain is either done or sorry-free-given-T205-d.

The build is clean (3092 jobs, only warnings).

---

## 10. Questions for the reviewer

We ask seven concrete questions. The reviewer should answer in whatever order they prefer; some may be combinable.

**Q1.** *(Soundness check.)* Is the restructuring chain in §5 mathematically valid? Specifically: the project's existing consumer `petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form` derives the DS unsymmetric form from the symmetric form via:
   - per-$q$ unfolding of $\langle\cdot,\cdot\rangle_N$,
   - `petersson_slash_SL` (mathlib pointwise slash identity for $\mathrm{SL}_2(\mathbb{Z})$ elements),
   - the $\sigma_p$ Q-permutation on $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$,
   - diamond unitarity,
   - `heckeT_p_comm_diamondOp`.

   Is this chain logically correct (i.e., does symmetric form ⇒ unsymmetric form genuinely hold)? Could the reviewer confirm or identify a defect?

**Q2.** *(Path selection.)* Given the current state, which of Paths A, B, C, D (§6) should we commit to? Path A is most explicit (~350–550 lines) but requires careful $\sigma_p$ bookkeeping; Path B might be circular per the previous reply; Path C doesn't apply; Path D is open-ended. The reviewer's previous estimate was 150–300 LOC for "pointwise + few hundred more" — does that estimate revise upward or downward given the restructured target?

**Q3.** *(Sub-lemma plan for Path A.)* We have proposed five sub-lemmas A1–A5 for Path A in §6.1. Is this decomposition correct? Are any sub-lemmas missing? Is the cost distribution realistic (i.e., is A4 the genuine bulk of the work, or are we underestimating A1 or A3)? Concrete intermediate lemma statements would be most helpful.

**Q4.** *(Alternative formulations of the target identity.)* The symmetric form (§5) is *informationally equivalent* to several other forms of DS 5.5.3 (unsymmetric, canonical, Hermitian-flipped). Is there an alternative formulation that is **easier to prove directly**, even if requiring more downstream bookkeeping to convert back? For example: would proving the per-$\beta$ sum identity (**) in §7 directly be easier than the symmetric form?

**Q5.** *(σ_p Q-permutation on Hecke reps.)* The $\sigma_p$ map on $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$ is well-understood. What we need is the **induced map on Hecke representatives** $\beta \mapsto \beta'$ described in §8.2. Is there a clean explicit description (e.g., specific matrix formulas for $\beta_b \mapsto \beta_{b'}$ for $0 \leq b < p$, and $\beta_\infty \mapsto \beta_\infty$ or analogous)? The project has the bridging matrix-algebra lemmas (`peterssonAdj_glMap_M_infty_eq`, `slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower`, `gamma0_T_p_upper_Gamma1_factor`, etc.); is there a cleaner organisation of the σ_p map that would shorten the formalisation?

**Q6.** *(Path B circularity.)* The previous reply said Atkin–Lehner–Li orthogonality "normally depends on the same adjoint/trace structure". Could the reviewer confirm whether Li's 1975 argument [Li1975] explicitly uses $T_p^* = \langle p\rangle^{-1} T_p$ (i.e., DS 5.5.3) as an input? If yes, Path B is fully circular and should be retired. If Li's argument actually uses only a weaker statement (e.g., level-1 self-adjointness + a multiplicativity argument), Path B might be salvageable.

**Q7.** *(Strategic priority.)* The conditional SMO theorem has landed: `strongMultiplicityOne_of_newSubspaceZeroCriterion` reduces SMO to two abstract hypotheses (Miyake Main Lemma 4.6.8 and the Newform-zero criterion). The full SMO theorem requires discharging both, plus an L-function non-vanishing argument for `exists_nonzero_prime_eigenvalue`. Is the right strategic priority:
   - (a) close T205-d-SYMM (this brief's target), unlocking the Hecke-adjoint chain and Main Lemma route to conditional SMO;
   - (b) work on the L-function non-vanishing argument in parallel;
   - (c) something else (e.g., wait for mathlib's abstract Hecke ring formalisation)?

---

## 11. Document metadata

- Project name: LeanModularForms-hecke (Strong Multiplicity One formalisation in Lean 4 / Mathlib).
- Brief generated: 2026-05-11 (third T205-d brief in same day).
- Prior briefs: 2026-05-11 SMO overview; 2026-05-11 T205-d focused.
- Length: ~10 pages.
- Build status: compiles cleanly; 1 sorry on the SMO critical path (`petN_heckeT_p_symmetric_form`); other small sorries in unrelated files (FG.lean, Prototype.lean, etc.) are off the critical path.
- Recent activity: file restructuring concentrating the T205-d sorry to a single named theorem; reviewer reply from prior brief integrated into ticket board.
- Files of interest (for reviewer's mental model only): the residual lives in the project's `AdjointTheory` module; the consumer chain is named `petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form` and is sorry-free given the residual.

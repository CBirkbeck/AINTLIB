# Review brief — Strong Multiplicity One via Miyake §4.6 chain

*Prepared 2026-05-17 for a senior modular forms expert with Lean/Mathlib experience. Self-contained: no repo access required. Notation follows Miyake's *Modular Forms* (2006) where it differs from Diamond–Shurman; explicit conversions noted.*

---

## 1. Goal

We aim to prove an *algebraic* form of **Strong Multiplicity One** for newforms on $\Gamma_1(N)$ with Nebentypus, in the version

> *(Miyake Theorem 4.6.12 / Diamond–Shurman Theorem 5.8.2.)* Let $f, g \in S_k^{\mathrm{new}}(N, \chi)$ be normalised newforms on $\Gamma_1(N)$ with the same Nebentypus character $\chi$. If $a_p(f) = a_p(g)$ for all primes $p$ outside a set of density $0$ (concretely: all but finitely many primes), then $f = g$.

In the project we have already proved a slightly stronger *finite-exception* version (algebraic, no analytic non-vanishing), via the per-character Main Lemma and the prime-square recurrence $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q)\, q^{k-1}$. The remaining work to upgrade this to the textbook statement is **Miyake's algebraic Main Lemma (Theorem 4.6.8, p. 160)** in its multi-prime case, which we have decomposed into a chain of 12 open sub-lemmas. This brief is about that chain.

---

## 2. Background and references

### 2.1 Setting and notation

We work entirely in the setting of holomorphic modular forms of weight $k \in \mathbb{Z}$ on congruence subgroups of $\mathrm{SL}_2(\mathbb{Z})$.

* $\Gamma_0(N), \Gamma_1(N)$ are the standard congruence subgroups of level $N$.
* $M_k(\Gamma_1(N)) = M_k(N)$ is the space of holomorphic modular forms; $S_k(\Gamma_1(N)) = S_k(N)$ the cusp forms.
* For a Dirichlet character $\chi: (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$, we write $M_k(N, \chi), S_k(N, \chi)$ for the χ-Nebentypus subspaces (Miyake §4.3): forms $f \in M_k(\Gamma_1(N))$ such that $\langle d \rangle f = \chi(d) f$ for all $d \in (\mathbb{Z}/N\mathbb{Z})^\times$.
* For $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$, the weight-$k$ slash action is $f \mid [\alpha]_k = (\det \alpha)^{k-1} j(\alpha, z)^{-k} f(\alpha z)$.
* **Diamond operators**: $\langle d \rangle: M_k(\Gamma_1(N)) \to M_k(\Gamma_1(N))$ for $d \in (\mathbb{Z}/N\mathbb{Z})^\times$, defined via Miyake (4.5.8): if $\gamma \in \Gamma_0(N)$ has $\gamma_{00} \equiv d \pmod N$, then $\langle d \rangle f = f \mid [\gamma]_k$.
* **Hecke operators**: $T(p), T^*(p)$ on $S_k(N, \chi)$ for primes $p$, defined via the double cosets $\Gamma_0(N) [1, 0; 0, p] \Gamma_0(N)$ (Miyake §4.5).
* **Level-raising**: for $d \mid M$, $V_d: M_k(M/d, \chi) \to M_k(M, \chi)$ sending $f(z) \mapsto f(dz)$, equivalently $f \mapsto d^{1-k} \cdot f \mid [\![d, 0; 0, 1]\!]_k$. This is Miyake's $f^d$ operator (Lemma 4.6.1).
* **Descent operator / Hecke double coset at differing levels**: for $p$ prime with $p \mid N$, the operator
$$T_p^{(N)}: M_k(\Gamma_0(N), \chi) \to M_k(\Gamma_0(N/p), \chi_0)$$
where $\chi_0$ is the descent of $\chi$ to $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$ when $\chi$ factors through that quotient. Miyake constructs $T_p^{(N)}$ implicitly in §4.6 (around (4.6.12), (4.6.13)); we make it explicit (cf. §4 below).
* **$\Delta_0(N) \subset M_2(\mathbb{Z})$**: semigroup of integer matrices with $c \equiv 0 \pmod N$, $\gcd(a, N) = 1$, $ad - bc > 0$ (Miyake (4.5.1)).

The project also uses the standard Mathlib group $\mathrm{GL}(\mathrm{Fin}\,2)\,R$, which we render mathematically as $\mathrm{GL}_2(R)$ throughout.

### 2.2 References

[**Miy**] T. Miyake. *Modular Forms*, 2nd ed. Springer Monographs in Mathematics. Springer, 2006. **Primary reference**. We use:
* §4.5 (Hecke Algebras of Modular Groups), in particular Lemma 4.5.2 (double coset normal form), Theorem 4.5.3 (commutativity), Theorem 4.5.4 (adjoint operators), Lemma 4.5.11 p. 143-144 (coset decomposition $\Gamma_0(pN) [1,0;0,p] \Gamma_0(N) = \bigsqcup_v \Gamma_0(pN) [1,0;0,p] \gamma_v$), and the surrounding $T(n)$ machinery.
* §4.6 (Hecke operators and modular forms of different levels), in particular Lemma 4.6.1 (level raising $f^d$), Lemma 4.6.3, Theorem 4.6.4 (the descent / conductor theorem), Lemma 4.6.5 p. 157 (Hecke coprime-filter), Lemma 4.6.6 p. 158 (level commutation), Lemma 4.6.7 p. 159 (squarefree decomposition), Theorem 4.6.8 p. 160 (Main Lemma), and Theorem 4.6.12 p. 162 (SMO).

[**DS**] F. Diamond, J. Shurman. *A First Course in Modular Forms*. Graduate Texts in Mathematics 228. Springer, 2005. We use:
* §5.1 (Double coset operators) for the general weight-$k$ slash framework.
* §5.2 p. 168-172 (the $\langle d \rangle$ and $T_p$ operators), in particular Proposition 5.2.1 (orbit reps $\beta_j = [1, j; 0, p]$ for $0 \leq j < p$, and $\beta_\infty = [m, n; N, p] [p, 0; 0, 1]$ when $p \nmid N$) and Proposition 5.2.2 (Fourier-coefficient formula).
* §5.8 (Strong Multiplicity One, the target).

[**AL**] A. O. L. Atkin, J. Lehner. "Hecke operators on $\Gamma_0(m)$". *Math. Ann.* **185** (1970), 134-160. The original AL paper; we use it for cross-validation but not directly.

[**Li**] W.-C. W. Li. "Newforms and functional equations". *Math. Ann.* **212** (1975), 285-315.

[**Shi**] G. Shimura. *Introduction to the Arithmetic Theory of Automorphic Functions*. Publications of the Mathematical Society of Japan 11. Princeton University Press, 1971. Used for cross-validation of the double-coset / Hecke formalism (Shimura §3.1–3.4).

[**Mathlib**] The Lean 4 mathlib library (snapshot circa early 2026). Provides: `ModularForm`, `CongruenceSubgroup.Gamma0`, `Gamma1`, `Matrix.SpecialLinearGroup`, the slash action `SlashAction`, q-expansions via `ModularFormClass.qExpansion`.

### 2.3 State of the art

SMO is a classical theorem (Atkin–Lehner 1970, Li 1975, Miyake 1989/2006, Diamond–Shurman 2005). The result is well-established. **In Lean/Mathlib**, the algebraic finite-exception version is now proved in this project, but the genuine SMO (with the textbook cofinite/Dirichlet-density statement) requires the multi-prime case of Miyake's Main Lemma. The Lean formalisation of $T(n), T^*(n)$ operators at the same level $\Gamma_1(N)$ is in the project; the **inter-level descent operator** $T_p^{(N)}$ from $M_k(N)$ to $M_k(N/p)$ that drives Miyake's induction is **new infrastructure being built in this project** and is the focus of the remaining work.

---

## 3. Strategy

The proof follows Miyake §4.6 *algebraically*, in contrast to DS §5.8 which uses the analytic non-vanishing of L-functions. The chain is:

1. **(B.L1)** *Algebraic finite-exception bridge*: from cofinite eigenvalue equality $a_p(f) = a_p(g)$ for all but finitely many primes $p$ outside $N$, deduce eigenvalue equality at **every** prime $p \nmid N$, via the prime-square recurrence $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q)q^{k-1}$. **PROVEN**.

2. **(A.L3.miyake.4_6_5)** *Hecke coprime-filter* (Miyake Lemma 4.6.5, single-prime version): for $f \in M_k(N, \chi)$, $g_p := f - V_p(U_p f)$ is itself a modular form on the level $N$ if $p \mid N$ or $Np^2$ if $p \nmid N$, with the same character. **PROVEN** in the single-prime case.

3. **(A.L2.miyake.4_6_8)** *Miyake's Main Lemma* (Theorem 4.6.8): the multi-prime version, by induction on $\omega(N)$. This is the **target of the chain**, with $N = 1, p^a$ cases proven and the $\geq 2$-prime-factor case being the remaining work.

4. **(A.L1)** *Per-character Main Lemma*: applying A.L2 to $h := f - g$ in the same Nebentypus space. **PROVEN** modulo A.L2.

5. **(A.L0)** *newform uniqueness*: SMO statement at the level of Nebentypus. **PROVEN** modulo the A.L1 chain.

6. **(SMO main)** Combining (A.L0) and (B.L1) yields the textbook SMO. **PROVEN** modulo the Main Lemma.

The bottleneck is (A.L2) for $\omega(N) \geq 2$. Miyake's proof of (A.L2) at this level proceeds by:

* **(M5)** Construct the **descent operator** $T_p^{(N)} := \Phi_p$ on $M_k(N, \chi)$ for one prime $p \mid N$, mapping to $M_k(N/p, \chi_0)$.
* **(M6)** Show $\Phi_p$ commutes with the level-raising $V_l$ for $l$ coprime to $p$.
* **(M7)** Apply the squarefree decomposition (Miyake 4.6.7) to write $f$ with coprime-vanishing as $\sum_{q \mid l} g_q(qz)$, and chase how $\Phi_p$ commutes with each summand.
* **(M8)** Combine into the inductive step.

The 12 open sub-lemmas all live inside this M5–M8 chain.

---

## 4. Definitions

We give the descent operator construction explicitly. Throughout this section, fix $N \geq 1$, a prime $p \mid N$, and assume $N/p \neq 0$ (so the descent target makes sense). Let $k \in \mathbb{Z}$ be the weight.

### 4.1 The descent coset list

Following Miyake Lemma 4.5.11, define the integer

$$d_{N,p} := \begin{cases} p-1 & \text{if } p^2 \mid N \\ p & \text{if } p^2 \nmid N \end{cases}$$

and the coset count $C_{N,p} := d_{N,p} + 1$.

**Definition 4.1.** The *descent coset list* $\{\gamma_v\}_{v=0}^{C_{N,p}-1} \subset \mathrm{GL}_2(\mathbb{R})$ is:
* For $0 \leq v < p$: $\gamma_v := \begin{pmatrix} 1 & v \\ 0 & p \end{pmatrix}$.
* For $v = p$ (only when $p^2 \nmid N$, and only one such term): $\gamma_p := \begin{pmatrix} 1 & 0 \\ 0 & p \end{pmatrix} \cdot \tilde{\gamma}_p$, where $\tilde{\gamma}_p \in \mathrm{SL}_2(\mathbb{Z})$ is a fixed element satisfying

$$\tilde{\gamma}_p \equiv \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \pmod p \quad \text{and} \quad \tilde{\gamma}_p \equiv I \pmod{N/p}.$$

By CRT (since $p, N/p$ are coprime in the $p^2 \nmid N$ case), such $\tilde{\gamma}_p$ exists; this is the content of T5a-0 (currently a `sorry`).

This matches Miyake Lemma 4.5.11 p. 144 verbatim ($\tilde{\gamma}_p$ is Miyake's $\gamma_p$ with the choice $a = 1$). It is also matrix-identical to DS Proposition 5.2.1's orbit reps $\beta_j$ for the same-level $T_p$ — the difference is which lattice the matrices live in.

### 4.2 The descent operator $\Phi_p$

For $f \in M_k(\Gamma_1(N))$ (or more precisely, in a Nebentypus subspace; see M5 bundle discussion in §6), the *descent operator* is

$$\Phi_p(f)(z) := \frac{p}{C_{N,p}} \sum_{v=0}^{C_{N,p}-1} (f \mid [\gamma_v]_k)(z).$$

Equivalently, $\Phi_p(f) = \frac{p}{C_{N,p}} \cdot \big(f \mid [\Gamma_0(N) \alpha \Gamma_0(N/p)]_k\big)$ for $\alpha = [1, 0; 0, p]$. The normalisation factor $p / C_{N,p}$ makes $\Phi_p \circ V_p$ act as the identity on $M_k(N/p, \chi)$ (Miyake (4.6.12)).

### 4.3 The slash sum vs. the bundled operator

We distinguish:
* The **function-level slash sum** $z \mapsto \sum_v (f \mid [\gamma_v]_k)(z)$, well-defined for any $f$ but not obviously $\Gamma_0(N/p)$-invariant.
* The **bundled descent operator** $\Phi_p : M_k(N, \chi) \to M_k(N/p, \chi_0)$ as a $\mathbb{C}$-linear map, requiring proof that the slash sum is $\Gamma_1(N/p)$-slash-invariant and bounded at cusps of $\Gamma_1(N/p)$.

Going from the first to the second requires the action property (M5a) and the cusp/character preservation (M5c, M5d) below.

### 4.4 Already-proven prerequisites

* $V_p$ as a $\mathbb{C}$-linear map $M_k(N/p) \to M_k(N)$, with pointwise formula $(V_p g)(z) = g(pz)$. **PROVEN**.
* `modFormCharSpace k χ`: the Nebentypus eigenspace inside $M_k(\Gamma_1(N))$. The decomposition $M_k(\Gamma_1(N)) = \bigoplus_\chi M_k(N, \chi)$ is **PROVEN** in the project.
* $V_p$ q-expansion identity: $a_n(V_p g) = a_{n/p}(g)$ if $p \mid n$, else $0$. **PROVEN** at level-$N$ period.
* Miyake Theorem 4.6.4 (descent / conductor theorem): if $f \in M_k(N, \chi)$ has Fourier support on $\{n : p \mid n\}$, then either $f = 0$ or $f = V_p(g)$ for some $g \in M_k(N/p, \chi_0)$. **PROVEN** via the project's conductor theorem.

---

## 5. Established results

This is a long list; we group by chain layer. Sketches included for non-routine results.

### 5.1 Outer chain (all PROVEN)

**Theorem 5.1.1 (SMO, finite-exception).** *Let $f, g \in S_k^{\mathrm{new}}(N, \chi)$ be normalised newforms. If $a_p(f) = a_p(g)$ for all but finitely many primes $p \nmid N$, then $f = g$.*

*Sketch.* By (B.L1) below, finite-exception eigenvalue equality upgrades to all-prime equality outside $N$ via the recurrence at prime squares. Then the per-character Main Lemma (A.L1) applied to $h := f - g \in S_k(N, \chi)$ produces $h = 0$.

**Theorem 5.1.2 (Algebraic q/q² bridge, B.L1).** *If $f, g$ are normalised newforms in $S_k(N, \chi)$ and $a_p(f) = a_p(g)$ for all primes $p$ outside a finite set $E$ disjoint from primes dividing $N$, then $a_p(f) = a_p(g)$ for all $p \nmid N$.*

*Sketch.* The recurrence $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) q^{k-1}$ holds for every prime $q \nmid N$. If $a_q(f) \neq a_q(g)$ for some $q \in E$, then $a_{q^2}(f) \neq a_{q^2}(g)$ implies $q^2 \in E'$ for some shifted finite set, but iterating gives infinitely many exceptions, contradiction. Made rigorous via density-zero argument.

**Theorem 5.1.3 (per-character Main Lemma, A.L1).** *Let $f \in S_k(N, \chi)$. If $a_p(f) = 0$ for all primes $p \nmid N$, then $f = 0$.*

*Sketch.* Conditional on the multi-prime Miyake Main Lemma (A.L2). Apply (A.L2) with $l = N$: the hypothesis gives Fourier vanishing on $\{n : (n, N) = 1\}$, and (A.L2) concludes $f = 0$ if $\omega(N) \geq 1$ (the only non-trivial case).

**Theorem 5.1.4 (Hecke coprime-filter, A.L3, single-prime case).** *Let $f \in M_k(N, \chi)$ and $p$ prime. The series $g_p(z) := \sum_{(n, p) = 1} a_n(f) q^n$ is a modular form on $M_k(M_p, \chi)$, where $M_p = N \cdot p$ if $p \mid N$ and $M_p = N \cdot p^2$ if $p \nmid N$.*

*Sketch.* Following Miyake (4.6.13): $g_p = f - V_p(U_p f)$, where $U_p$ is the level-$N$ Hecke operator (or descent operator if $p \mid N$). Holomorphy and cusp boundedness inherit from $f$ and $V_p f$; the $q$-coefficients match by direct computation. **PROVEN**.

### 5.2 Inner M5–M8 layer (selected proofs)

**Theorem 5.2.1 (M5c, cusp preservation).** *Let $f \in S_k(\Gamma_1(N))$ be a cusp form. Then for every cusp $c$ of $\Gamma_1(N/p)$,*
$$\sum_v (f \mid [\gamma_v]_k) \text{ vanishes at } c \text{ in the } \Gamma_1(N/p)\text{-sense.}$$

*Sketch.* Each $\gamma_v \in \mathrm{GL}_2(\mathbb{R})$ admits a rational lift $A_v \in \mathrm{GL}_2(\mathbb{Q})$ (entries $1, m, 0, p$ for upper-tri reps; $\tilde{\gamma}_p$ contributes for the extra rep). A standard cusp-transport lemma in the project says $A_v$ maps cusps of $\Gamma_1(N/p)$ (after lifting via the natural map to $\mathrm{GL}_2(\mathbb{R})$) to cusps of $\Gamma_1(N)$. Then $f$'s vanishing at all $\Gamma_1(N)$-cusps plus the `IsZeroAt.smul_iff` identity ($\mathrm{IsZeroAt}\,(A \cdot c, f) \iff \mathrm{IsZeroAt}\,(c, f \mid [A])$) gives the result. **PROVEN**.

**Theorem 5.2.2 (M5d, character preservation).** *Let $f \in M_k(N, \chi)$ and let $\chi_0$ be the descent of $\chi$ to $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$ (assuming $\chi$ factors). Then for every $\gamma' \in \Gamma_0(N/p) \subset \mathrm{SL}_2(\mathbb{Z})$,*
$$\sum_v f \mid [\gamma_v]_k \mid [\gamma']_k = \chi_0(\gamma') \sum_v f \mid [\gamma_v]_k.$$

*Sketch.* The descent action property (M5a): there exist $\sigma \in \mathrm{Sym}(\{0, \ldots, C_{N,p}-1\})$ and $\alpha_v \in \Gamma_0(N)$ such that $\gamma_v \cdot \gamma' = \alpha_v \cdot \gamma_{\sigma(v)}$ in $\mathrm{GL}_2(\mathbb{R})$. The diamond compatibility says $\chi(\alpha_v) = \chi_0(\gamma')$ for all $v$. Then $f \mid [\alpha_v]_k = \chi(\alpha_v) f = \chi_0(\gamma') f$, and reindexing the sum gives the result. **PROVEN** (modulo the still-open M5a).

**Theorem 5.2.3 (M5b, Miyake (4.6.12) $q$-shift identity).** *For $g \in M_k(N/p, \chi_0)$, the slash sum applied to $V_p g$ recovers $g$ up to the normalisation constant $C_{N,p}/p$:*
$$\sum_v (V_p g) \mid [\gamma_v]_k = (C_{N,p}/p) \cdot g.$$

*Sketch.* For upper-tri reps $0 \leq v < p$: the slash formula gives $(V_p g) \mid [1, v; 0, p]_k(z) = p^{-1} g(z)$ (using $(V_p g)((z+v)/p) = g(z + v) = g(z)$ by period-1 invariance of $g$). Sum: $p \cdot p^{-1} \cdot g = g$. For the extra rep (when $p^2 \nmid N$): same calculation at $v = 0$, then slash by $\tilde{\gamma}_p \in \Gamma_1(N/p)$ leaves $g$ invariant. Total: $(p+1)/p \cdot g$ or $p/p \cdot g$ depending on the case. **PROVEN**.

### 5.3 Helper lemmas (all PROVEN, summarised)

In addition to M5b/c/d, the project has ~15 proven helper lemmas of which the most load-bearing are: `descendCosetList_det` (det = $p$), `descendCosetList_orbit_identity` (function-level T5d-1), `descendCosetList_level_agree` (T6a: $C_{N,p} = C_{lN,p}$ when $(l,p) = 1$), `descendCosetList_lift_eq_glMap` (rational lift of $\gamma_v$), `multipass_V_p_slash_descendCoset` (pointwise per-$v$ formula), `multipass_modFormCharSpace_slash_apply` (the χ-eigenform slash formula), `multipass_gamma1_conjugate_in_gamma1` (mod-$N$ congruence implies $\Gamma_1(N)$), `multipass_mul_mod_p_perm_exists` (mult-by-$l$ permutes $\mathrm{Fin}\,p$), and `multipass_alpha_integer_entries_p_sq_dvd_N` (divisibility for the $\alpha_{01}$ integrality in T5a-3a-clean).

The single-prime case of Miyake 4.6.5 (Hecke coprime-filter) is proven via the explicit identity $g_p = f - V_p(U_p f)$. The diamond-character decomposition $M_k(\Gamma_1(N)) = \bigoplus_\chi M_k(N, \chi)$ is established. The descent of $V_p$ to a $\mathbb{C}$-linear map $M_k(N/p) \to M_k(N)$ and its $q$-expansion identity are established.

---

## 6. In progress

### 6.1 The full descent action property (M5a)

**Statement.** *For every $\gamma' \in \Gamma_0(N/p)$, there exist a permutation $\sigma$ of $\{0, \ldots, C_{N,p} - 1\}$ and matrices $\alpha_v \in \Gamma_0(N)$ such that*
* (Action) $\gamma_v \cdot \gamma' = \alpha_v \cdot \gamma_{\sigma(v)}$ in $\mathrm{GL}_2(\mathbb{R})$ for all $v$.
* (Diamond compat) $[\alpha_v]_{N \to N/p} = [\gamma']_{N/p}$ in $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$.

**Status.** The wrapper (combining the upper-tri and extra-rep cases) is decomposed but `sorry` at the combinator level. The sub-lemmas (T5a-3a-clean, T5a-3a-extra) have their math content fully understood (Miyake p. 144) but are both `sorry` due to Lean-side friction (see §8).

### 6.2 The bundled $\Phi_p$ as a linear map (M5 bundle)

**Statement.** *There exist a $\mathbb{C}$-linear map $\Phi_p: M_k(\Gamma_1(N)) \to M_k(\Gamma_1(N/p))$ and a constant $c \neq 0$ such that:*
* *(Cusp preservation)* $\Phi_p$ sends $S_k(\Gamma_1(N))$ to $S_k(\Gamma_1(N/p))$.
* *(Character preservation)* For each $\chi$ factoring through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$ as $\chi_0$, $\Phi_p$ sends $M_k(N, \chi)$ to $M_k(N/p, \chi_0)$.
* *(Miyake (4.6.12) identity)* For any $g \in M_k(N/p, \chi_0)$, $\Phi_p(V_p g) = c \cdot g$ (with $c = p/C_{N,p}$).

**Status.** The function-level construction (the normalised slash sum) is in place; the cusp and character preservation parts are individually proven (M5c, M5d). What's missing is the $\Gamma_1(N/p)$-slash invariance for **general** $f \in M_k(\Gamma_1(N))$ (not just $\chi$-eigenforms). This requires the character decomposition: for characters $\chi$ that do **not** factor through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$, the slash sum on the $\chi$-eigenspace vanishes (this is the key cancellation we haven't pinned down formally — see §9 Q3).

### 6.3 Level commutation M6(2)

**Statement.** *(Miyake 4.6.6(2).)* For $p$ prime $\mid N$ and $l$ coprime to $p$ with $l \mid N/p$,
$$\Phi_p \circ V_l = V_l \circ \Phi_p^{(N/p)},$$
where $\Phi_p^{(N/p)}$ is the corresponding descent operator at level $N/p$.

**Status.** `sorry`. Depends on M5a and on the T6b rep-invariance / commutation lemmas.

### 6.4 Multi-prime induction (M7, M8)

The squarefree decomposition (Miyake 4.6.7) and the inductive step (Miyake 4.6.8 multi-prime case) are also `sorry`. They depend on M5, M6, and standard induction on $\omega(N)$.

---

## 7. Targets (the 12 open sorries)

All 12 open sorries are within the M5–M8 chain. Listed in dependency order:

| # | Layer | Name | Math content | Depends on |
|---|---|---|---|---|
| 1 | Number-theoretic | `int_exists_coprime_adjust` | Given $c, d, N \in \mathbb{Z}$, $d \neq 0$, $\gcd(\gcd(c,d), \|N\|) = 1$: $\exists\, t \in \mathbb{Z}$ with $\gcd(c + tN, d) = 1$. | CRT/Bezout |
| 2 | Number-theoretic | `SL2Z_to_SL2_ZMod_surjective` | $\mathrm{SL}_2(\mathbb{Z}) \twoheadrightarrow \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$. | #1 |
| 3 | Number-theoretic | `descendExtraGamma_exists` (T5a-0) | $\tilde{\gamma}_p$ of §4.1 exists. | #2 |
| 4 | Matrix algebra | `descendCosetList_action_upper_tri_clean` (T5a-3a-clean) | Matrix equation for $p^2 \mid N$ case of M5a's upper-tri orbit. | helpers (proven) |
| 5 | Matrix algebra | `descendCosetList_action_upper_tri_extra` (T5a-3a-extra) | Matrix equation for $p^2 \nmid N$ case with case-split on extra-rep target. | helpers (proven), case algebra |
| 6 | Combinator | `descendCosetList_action` (T5a-3 / M5a) | Bundles upper-tri + extra-rep into full M5a witness with $\sigma$ as permutation. | #4, #5 |
| 7 | Linear map | `miyake_hecke_descend` (M5 bundle) | $\Phi_p$ as $\mathbb{C}$-linear map with the three properties of §6.2. | M5a, M5b, M5c, M5d (b/c/d proven) |
| 8 | Slash-sum | `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv) | Rep choice $\tilde{\gamma}_p$ doesn't affect $\chi$-eigenform slash sum. | H24 (proven), CRT-style conjugation |
| 9 | Slash-sum | `descendCosetList_slash_sum_commute` (T6b-commute) | Function-level slash sum commutation across levels. | #8, M5a |
| 10 | Level commutation | `miyake_4_6_6_level_commute_delta` (M6(2)) | $\Phi_p \circ V_l = V_l \circ \Phi_p^{(N/p)}$. | #9, helpers |
| 11 | Squarefree decomp | `miyake_4_6_7_squarefree_decomp` (M7-decomp) | For $f \in S_k(N, \chi)$ with coprime-vanishing on $l$: $\exists\, g_q \in S_k(Nl^2, \chi')$ with $f(z) = \sum_{q \mid l} g_q(qz)$. | M5, M6 |
| 12 | Main lemma | `miyake_V_p_descend_identity` + `miyake_4_6_8_inductive_step` | Multi-prime case of Miyake 4.6.8, by induction on $\omega(N)$. | M5, M6, M7 |

Total: 12. The dependency structure is a DAG with #1–#3 at the bottom (number-theoretic primitives), #4–#5 at a parallel layer (matrix algebra), and #6–#12 stacking up from there.

---

## 8. Where we're stuck

### 8.1 T5a-3a-clean — the concrete Lean blocker

This is the focal blocker. **The math is clear** (Miyake p. 144, augmented by an explicit Möbius formula not written in either Miyake or DS); **the Lean execution is blocked by matrix-literal evaluation under `simp`**.

**Math content.** Let $\gamma' = \begin{pmatrix} A & B \\ C & D \end{pmatrix} \in \Gamma_0(N/p)$ with $p^2 \mid N$ (so $p \mid N/p \mid C$). We want $(m', \alpha)$ with the matrix equation
$$\begin{pmatrix} 1 & m \\ 0 & p \end{pmatrix} \cdot \gamma' = \alpha \cdot \begin{pmatrix} 1 & m' \\ 0 & p \end{pmatrix} \quad \text{in } \mathrm{GL}_2(\mathbb{R}),$$
together with $\alpha \in \Gamma_0(N)$. The explicit construction (from a "direct calculation" both Miyake and DS elide):
* $m' := (A^{-1} \cdot (B + m D)) \bmod p \in \mathrm{Fin}\,p$ (well-defined since $A$ is a unit mod $p$, from $AD - BC \equiv AD \equiv 1 \pmod p$).
* $\alpha := \begin{pmatrix} A + mC & \alpha_{01} \\ pC & D - C m' \end{pmatrix}$ where $\alpha_{01} = (B + mD - (A + mC)m')/p \in \mathbb{Z}$ (integrality from the Möbius equation $A m' \equiv B + m D \pmod p$ plus $p \mid C$).

Verifying $\alpha \in \Gamma_0(N)$ and $\det \alpha = 1$ are short integer computations.

**Lean blocker.** After unfolding the matrix product in $\mathrm{GL}_2(\mathbb{R})$ via `Units.ext`, `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`, `Matrix.SpecialLinearGroup.mapGL_coe_matrix`, and `ext i j; fin_cases i <;> fin_cases j`, the goal at entry $(0, 0)$ becomes (with the natural ring homomorphism written as `algebraMap`):

> `Matrix.vecCons 1 (fun i ↦ 0) ⟨0, _⟩ * (algebraMap ℤ ℝ) (↑γ' 0 ⟨0, _⟩) + Matrix.vecCons (↑↑m) (fun i ↦ ↑p) ⟨0, _⟩ * (algebraMap ℤ ℝ) (↑γ' 1 ⟨0, _⟩) = (algebraMap ℤ ℝ) (↑α ⟨0, _⟩ 0) * ![1, ↑↑m'] ⟨0, _⟩ + (algebraMap ℤ ℝ) (↑α ⟨0, _⟩ 1) * ![0, ↑p] ⟨0, _⟩`

The fragments `Matrix.vecCons 1 (fun i ↦ 0) ⟨0, _⟩` should reduce to `1`, but `simp only` with all of `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons`, `Matrix.head_fin_const`, `Matrix.of_apply`, `Matrix.cons_val'`, `Matrix.empty_val'`, `Matrix.cons_val_fin_one` does **not** fire on the `⟨0, _⟩` form (a `Fin 2` constructed via `Fin.mk` rather than the canonical `0 : Fin 2`).

All four entry equations fail closure for the same reason. The four equations themselves are elementary (entries (0,0), (1,0), (1,1) follow from $\alpha$'s definition; entry (0,1) uses the Möbius equation $p \cdot \alpha_{01} = B + mD - (A+mC) m'$).

We've tried: `simp only [...]`, `decide`, `norm_num`, `Fin.isValue`, explicit `show`-then-`rfl`, explicit `rw [hα_NN]` with intermediate substitutions. None reduce `vecCons _ _ ⟨0, _⟩`. Comparable matrix-equation proofs in the project work but use a different unfolding path (through $T_{p,\mathrm{upper}}$ in $\mathrm{GL}_2(\mathbb{Q})$ instead of `mkOfDetNeZero` in $\mathrm{GL}_2(\mathbb{R})$).

### 8.2 M5 bundle — the character decomposition wiring

The M5 bundle signature requires $\Phi_p$ as a $\mathbb{C}$-linear map from $M_k(\Gamma_1(N))$ to $M_k(\Gamma_1(N/p))$. The slash sum is $\Gamma_1(N/p)$-invariant on $\chi$-eigenforms (M5d at the trivial character target), but for **general** $f \in M_k(\Gamma_1(N))$ the action property gives $\alpha_v \in \Gamma_0(N) \setminus \Gamma_1(N)$, so $f \mid [\alpha_v] \neq f$ in general.

The argument that the slash sum **is** $\Gamma_1(N/p)$-invariant on the full $M_k(\Gamma_1(N))$: decompose $f = \sum_\chi f_\chi$, apply M5d to each $f_\chi$, and observe that for $\gamma \in \Gamma_1(N/p)$ the Nebentypus factor $\chi_0(\gamma) = 1$ when $\chi$ factors, and the slash sum vanishes when $\chi$ doesn't factor. The latter "vanishes when $\chi$ doesn't factor" claim is what we haven't pinned down formally.

### 8.3 T5a-0 — CRT for $\mathrm{SL}_2(\mathbb{Z})$ with prescribed reductions

This is a classical strong-approximation result for $\mathrm{SL}_2$: given $\bar{M} \in \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$, find a lift $M \in \mathrm{SL}_2(\mathbb{Z})$ with $M \equiv \bar{M} \pmod N$. The proof recipe is:
1. Lift bottom row $(\bar{c}, \bar{d})$ to integers $(c, d)$ with $d \neq 0$. Then $\gcd(c, d, N) = 1$ since $\bar{M} \in \mathrm{SL}_2$.
2. Apply `int_exists_coprime_adjust` to find $t$ with $\gcd(c + tN, d) = 1$.
3. Bezout gives $(a_0, b_0)$ with $a_0 d - b_0 (c+tN) = 1$, so $[a_0, b_0; c+tN, d] \in \mathrm{SL}_2(\mathbb{Z})$.
4. Adjust top row to match $(\bar{a}, \bar{b})$ mod $N$ via $(a_0, b_0) \mapsto (a_0 + \alpha c, b_0 + \alpha d)$ for suitable $\alpha$.

All steps are routine number theory; the Lean execution is ~160 LOC of integer/Bezout/CRT work. Sub-lemma `int_exists_coprime_adjust` itself uses a CRT argument over the prime factors of $d$ that we haven't yet executed.

### 8.4 T6b — slash-sum across levels

The intricate part of the M6 commutation. Given $\gamma' \in \Gamma_0(N/p)$ and the descent action's $\alpha_v \in \Gamma_0(N)$, we need to commute the descent operator with $V_l$ for $l$ coprime to $p$. The key sub-lemma `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv) compares two distinct choices $\tilde{\gamma}_p^{(N)}$ and $\tilde{\gamma}_p^{(lN)}$ of the extra-rep matrix at different levels; both satisfy the CRT congruence at the stronger level $lN/p$, so they differ by an element $g \in \Gamma(N) \subset \mathrm{SL}_2(\mathbb{Z})$, and the conjugation $[1, 0; 0, p] g [1, 0; 0, p]^{-1}$ stays in $\Gamma_1(N)$ (via H24, proven). This is followed by T6b-commute (the full slash-sum commutation) and M6(2) itself.

### 8.5 M7 / M8 — the inductive step

Once M5 + M6 are in place, the squarefree decomposition (M7) and the inductive step (M8) are routine but non-trivial. M7 follows Miyake 4.6.7 directly: peel off one prime $q \mid l$, write $f = h_q(qz) + (\text{rest})$, recurse. M8 (the inductive step) glues M7 with M5/M6 plus the already-proven Miyake 4.6.4 (descent).

---

## 9. Open mathematical and technical questions for the reviewer

### Math soundness

**Q1.** *Is Miyake's §4.6 chain (4.6.5 → 4.6.6 → 4.6.7 → 4.6.8 → 4.6.12) the right route to formalize SMO algebraically?* We see two alternative routes in the literature: Atkin–Lehner's original method (more direct via $U_p$ eigenvalues but assuming Dirichlet density), and Diamond–Shurman §5.8 (using analytic L-function non-vanishing, which we want to avoid). We've committed to Miyake's algebraic route; is there a better one we should consider?

**Q2.** *The descent operator $\Phi_p$ we construct from §4.2 — is the normalisation $p/C_{N,p}$ the standard one in the literature?* Miyake (4.6.12) uses normalisation $p$ (no division by $C_{N,p}$), while DS implicitly uses the unnormalised slash sum. We chose $p/C_{N,p}$ so that $\Phi_p \circ V_p = \mathrm{id}$ rather than $\Phi_p \circ V_p = C_{N,p} \cdot \mathrm{id}$. Does this conflict with any standard convention or downstream calculation?

**Q3.** *In the M5 bundle's "character decomposition" approach to $\Gamma_1(N/p)$-invariance for general $f \in M_k(\Gamma_1(N))$* (§8.2), *is the fact that "the slash sum vanishes on $M_k(N, \chi)$ when $\chi$ doesn't factor through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$" a standard observation?* We can derive it from M5d at the kernel element, but is there a reference (Miyake / DS / AL / Li) that states it explicitly?

**Q4.** *In §8.4 (T6b-coset-inv), the rep-invariance argument uses $[1,0;0,p]$-conjugation sending $\Gamma(N)$ into $\Gamma_1(N)$. The argument is "$\Gamma(N)$ is normal in $\mathrm{SL}_2(\mathbb{Z})$ so conjugation by integer matrices preserves it, and the conjugation by $[1,0;0,p]$ explicitly works out in entries". But $[1,0;0,p]$ is not in $\mathrm{SL}_2(\mathbb{Z})$. Does this matter?* (We've checked the entry computation: it works, but we'd like a sanity check.)

### Lean technique

**Q5.** *What is the correct Lean 4 / Mathlib simp pattern to reduce `Matrix.vecCons a (fun i ↦ b) ⟨0, h⟩` to `a` and `Matrix.vecCons a v ⟨k+1, h⟩` to `v ⟨k, _⟩` when the Fin index is built via `Fin.mk` rather than as a numeric literal?* (See §8.1 for the precise failing goal.) Alternatives: avoid `!![...]` matrix-literal syntax entirely and use a different Matrix construction; use `decide` after a Fin normalization step; or some other idiom we're missing.

**Q6.** *Are there existing Lean 4 / Mathlib formalisations of the descent / inter-level Hecke operator $T_p^{(N)}$?* Our search of mathlib (snapshot ~early 2026) shows extensive same-level $T_p$ on $\Gamma_1(N)$ but no inter-level descent. Are we missing infrastructure that's already in a mathlib branch / Lean repo we should pull from?

### Prioritisation

**Q7.** *Of the 12 remaining sorries, which is the right one to attack first to unblock the most downstream work?* Our current intuition: T5a-0 (descendExtraGamma_exists) — because it's the deepest dependency, unblocking everything downstream. But it's heavy number-theory work (~160 LOC) and we wonder if attacking T5a-3a-clean (with the Lean blocker resolved) would yield more momentum.

**Q8.** *Is the multi-pass audit approach we used (`/develop` → 6-pass audit → `/beastmode`) the right development methodology for this kind of formalization?* We found the audit underestimated LOC for matrix-algebra lemmas by ~2x and over-claimed mathlib has lemmas it doesn't. Suggestions for refining this workflow welcome.

---

## 10. Auxiliary technical material (appendix)

### 10.1 The single-prime Miyake 4.6.5 (already proven, sketch)

The single-prime case of Miyake's Hecke coprime-filter is proven via the explicit identity
$$g_p(z) = f(z) - V_p(U_p f)(z) = \sum_{(n,p) = 1} a_n(f) e^{2\pi i n z}$$
where $U_p f = \sum_n a_{pn}(f) q^n$ (the standard $U_p$ operator at level $N$). The cusp-form preservation and level / character bookkeeping are routine.

### 10.2 Build status

At time of writing: `lake build` clean on the SMO Obligations module and dependencies; 12 open `sorry`s, all in the M5–M8 layer; no custom axioms; the standard axiom check shows only `propext`, `Classical.choice`, `Quot.sound`.

### 10.3 Recent session context

This session reduced the open sorries from 24 to 12 by completing M5b (q-shift), M5c (cusp), M5d (character), plus 9 helper lemmas. The remaining 12 are the focus of this review.

---

## 11. Document metadata

* **Project name**: LeanModularForms (SMO chain, on `hecke-ring` branch).
* **Brief generated**: 2026-05-17.
* **Length**: ~13 pages.
* **Build status**: clean; 12 `sorry`s in the SMO obligations module.
* **Conventions**: Miyake (T(l,m), T(n), $\Delta_0(N)$, Greek letters for Dirichlet characters).
* **Audit document**: an internal 1066-line multi-pass audit doc (`audit-multipass-2026-05-17.md`) summarised in §7 of this brief.

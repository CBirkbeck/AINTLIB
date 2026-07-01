# Review brief — Strong Multiplicity One for elliptic modular forms

*Prepared 2026-05-11 for a frontier LLM reviewer (ChatGPT/Claude/Gemini). Self-contained: no repository access required. Conventions follow Diamond–Shurman and Miyake throughout.*

---

## 1. Goal

We are formalizing **Miyake's Strong Multiplicity One theorem** for elliptic modular forms (Miyake, *Modular Forms*, Theorem 4.6.12):

> **Theorem (Strong Multiplicity One).** *Let $f \in S_k(N_1, \chi)$ and $g \in S_k(N_2, \chi)$ be normalized newforms of weight $k \geq 1$, levels $N_1, N_2 \geq 1$, and the same nebentypus character $\chi$, lifted to a common level $N = \mathrm{lcm}(N_1, N_2)$. Suppose there exists a finite set of primes $S$ such that for every prime $p \notin S$ we have $a_p(f) = a_p(g)$. Then $f = g$ (in particular $N_1 = N_2$).*

The classical statement allows the exceptional set to be *infinite* on a density-zero set; Miyake's formulation with a finite exceptional set is what we formalize. The result is the cornerstone uniqueness statement for the theory of automorphic L-functions in dimension 2 and is the entry point into Atkin–Lehner theory, the Jacquet–Langlands correspondence, and the modular base-change apparatus.

Our intermediate goals are the supporting structural theorems: the full algebraic theory of the abstract Hecke algebra (Shimura, Theorems 3.20, 3.24, 3.34, 3.35), the commutativity of $T_n$ on $M_k(\Gamma_1(N))$, the Petersson adjoint theory (Diamond–Shurman §5.5, Theorem 5.5.3), the spectral decomposition into common eigenforms, and the Miyake Main Lemma (Theorem 4.6.8) on cusp forms with sparse Fourier supports.

---

## 2. Background and references

### 2.1 Setting and notation

We work throughout with **elliptic** modular forms (rank-2 case, $\mathrm{SL}_2(\mathbb{Z})$ and its congruence subgroups), so all matrices are $2 \times 2$.

**Groups.**
- $\mathrm{GL}_2^+(\mathbb{R}) = \{\alpha \in \mathrm{GL}_2(\mathbb{R}) : \det \alpha > 0\}$ acting on the upper half-plane $\mathfrak{H}$ by $\alpha\tau = \tfrac{a\tau+b}{c\tau+d}$.
- $\Gamma(N) = \ker(\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N))$, $\Gamma_1(N)$ defined by $a \equiv d \equiv 1$, $c \equiv 0 \pmod N$, and $\Gamma_0(N)$ defined by $c \equiv 0 \pmod N$.
- $\Delta_0(N) = \{\alpha \in M_2(\mathbb{Z}) : c \equiv 0 \pmod N,\ \gcd(a,N) = 1,\ \det \alpha > 0\}$ is Shimura's level-$N$ Hecke monoid. The pair $(\Gamma_0(N), \Delta_0(N))$ forms a *Hecke pair*: $\Gamma_0(N) \leq \Delta_0(N) \leq \mathrm{Comm}_{\mathrm{GL}_2^+(\mathbb{Q})}(\Gamma_0(N))$ (Shimura, Lemma 3.10).

**Slash operator (Miyake / Diamond–Shurman normalization).** For $\alpha = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \mathrm{GL}_2^+(\mathbb{R})$ and weight $k$,
$$(f \mid_k \alpha)(\tau) = (\det \alpha)^{k-1} \, (c\tau+d)^{-k} \, f(\alpha\tau).$$
The factor $(\det\alpha)^{k-1}$ rather than $(\det\alpha)^{k/2}$ is the Diamond–Shurman / Miyake convention; it has the effect of making the level-raising map $V_d : f(\tau) \mapsto f(d\tau)$ equal to $d^{1-k}\, (f \mid_k \alpha_d)$ where $\alpha_d = \mathrm{diag}(d,1)$.

**Adjugate anti-involution.** For $g = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \mathrm{GL}_2$, we write $g^* = \left(\begin{smallmatrix} d & -b \\ -c & a \end{smallmatrix}\right)$. Then $g^{**} = g$, $(gh)^* = h^* g^*$, $\det g^* = \det g$, and $g^* = g^{-1}$ when $\det g = 1$. The Hecke action uses $g^*$ rather than $g^{-1}$ because conjugation by $g^*$ preserves integrality.

**Hecke operators.** For $p$ prime and $\gcd(p,N) = 1$, $T_p$ on $M_k(\Gamma_1(N))$ is defined via the standard $p+1$ coset decomposition of $\Gamma_1(N) \mathrm{diag}(1,p) \Gamma_1(N)$:
$$T_p f = \sum_{b=0}^{p-1} f \mid_k \left(\begin{smallmatrix} 1 & b \\ 0 & p \end{smallmatrix}\right) + \langle p \rangle f \mid_k \left(\begin{smallmatrix} p & 0 \\ 0 & 1 \end{smallmatrix}\right),$$
where $\langle p \rangle$ is the diamond operator. We extend to $T_n$ for all $n \geq 1$ by the recurrence $T_{p^{r+2}} = T_p T_{p^{r+1}} - p^{k-1} \langle p \rangle T_{p^r}$ and the multiplicative law $T_{mn} = T_m T_n$ when $\gcd(m,n) = 1$.

**Petersson inner product (level 1).** For $f, g \in S_k(\mathrm{SL}_2(\mathbb{Z}))$,
$$\langle f, g \rangle = \int_{\mathcal{D}} f(\tau)\overline{g(\tau)} \, y^k \, \frac{dx\,dy}{y^2},$$
with $\mathcal{D}$ the standard fundamental domain and $\mu_{\mathrm{hyp}} = y^{-2} dx\,dy$.

**Level-$N$ Petersson inner product (our definition).** For $f, g \in S_k(\Gamma_1(N))$,
$$\langle f, g \rangle_N = \sum_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \int_{\mathcal{D}} (f \mid_k q^{-1})(\tau) \, \overline{(g \mid_k q^{-1})(\tau)} \, y^k \, \frac{dx\,dy}{y^2}.$$
This sums the level-1 Petersson form pulled back via coset representatives. It is unnormalized; the spectral theorem only needs positive-definiteness and Hermitian symmetry, both of which are unaffected by scaling.

### 2.2 References

**Primary mathematical sources.**

- **[DS]** Fred Diamond and Jerry Shurman. *A First Course in Modular Forms.* Graduate Texts in Mathematics 228. Springer, 2005. (Primary for §5.2–5.5: slash action, Petersson inner product, Hecke adjoint theorem 5.5.3.)
- **[Miy]** Toshitsune Miyake. *Modular Forms.* Springer Monographs in Mathematics, 2nd printing, Springer, 2006. (Primary for §4.5–4.6: eigenforms, primitive forms, Main Lemma 4.6.8, Strong Multiplicity One 4.6.12.)
- **[Shi]** Goro Shimura. *Introduction to the Arithmetic Theory of Automorphic Functions.* Princeton University Press, 1971. (Primary for the abstract Hecke ring of §3.1–3.4: Theorems 3.20, 3.24, 3.34, 3.35; commensurability; the formal commutativity argument via anti-involution.)
- **[AL]** A. O. L. Atkin and J. Lehner. "Hecke operators on $\Gamma_0(m)$." *Math. Annalen* 185 (1970), 134–160.
- **[Hec]** Erich Hecke. "Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung." *Math. Annalen* 112 (1936), 664–699. (Functional equation for the L-function of a cusp form.)

**Background analytic.**
- Robert Rankin, *Modular Forms and Functions* (1977) — used for the Rankin–Selberg convergence bounds.

### 2.3 State of the art

Strong Multiplicity One is a classical theorem with multiple proofs in the literature:
1. **Miyake's elementary argument** (Theorem 4.6.12): combines the Atkin–Lehner uniqueness theorem (DS Theorem 5.8.2 / Miyake 4.6.11) on a fixed level with the Main Lemma (Theorem 4.6.8) on Fourier-coefficient supports. This is the route we formalize.
2. **L-function / converse theorem route** (Weil 1967, Casselman): use the functional equation and analytic continuation to reduce to coefficient-wise uniqueness.
3. **Adelic route** (Jacquet–Langlands 1970): part of the general representation-theoretic uniqueness for $\mathrm{GL}_2$ automorphic representations.

To our knowledge, no full formalization of this theorem exists in any proof assistant. The recent Mathlib effort has formalized:
- modular forms with respect to congruence subgroups (the `ModularForm` and `CuspForm` types);
- $q$-expansions and the $q$-expansion principle;
- the slash action;
- Hecke operators $T_p$ at level $\mathrm{SL}_2(\mathbb{Z})$;
- $\mathrm{SL}_2(\mathbb{Z})$ as the modular group with its standard fundamental domain.

Our project picks up where Mathlib leaves off, building the level-$N$ Hecke algebra and the analytic apparatus required for SMO.

---

## 3. Strategy

The project is organized into a **9-phase plan** (mathematical phases) implemented as **5 development epics** (work-package boundaries).

**Phase 1 (Hecke pair for $\Gamma_1(N)$).** Establish the abstract Hecke pair $(\Gamma_1(N), \Delta_1(N))$ as a special case of an arithmetic Hecke pair $(H, \Delta)$ inside a commensurator. — Done.

**Phase 2 (Diamond, twisted slash, $T_p$).** Build the diamond operators $\langle d \rangle$ for $d \in (\mathbb{Z}/N)^*$, the character spaces $M_k(\Gamma_1(N), \chi)$, and the explicit Hecke operator $T_p$ via the $p+1$ coset formula. — Done.

**Phase 3 ($T_n$ and Fourier coefficients).** Extend $T_p$ to $T_n$ via the standard recurrence; prove the formula for the $m$-th Fourier coefficient of $T_n f$. — Done.

**Phase 4 (Petersson inner product).** Define and study $\langle \cdot, \cdot \rangle_N$; prove positive-definiteness, Hermitian symmetry, and Hilbert-space machinery. — Done (positive-definite, Hermitian, complete inner product structure via Mathlib's `InnerProductSpace.ofCore`).

**Phase 5 (Hecke adjoint theory; spectral decomposition).** Prove the Diamond–Shurman adjoint formula $T_p^* = \langle p \rangle^{-1} T_p$ (Theorem 5.5.3) and the consequence that the family $\{T_n : \gcd(n,N)=1\}$ admits a simultaneous orthonormal eigenbasis on each character space. — **Active**; two sorries remain.

**Phase 6 (Newforms / oldforms).** Define oldforms (image of level raising from proper divisors), newforms (Petersson-orthogonal complement), prove the Atkin–Lehner uniqueness theorem (DS Theorem 5.8.2), and show that the Hecke operators preserve both subspaces. — Mostly done; one sorry (the "main lemma" coupling new/old to vanishing-coprime Fourier coefficients) blocked on Phase 5.

**Phase 7 (L-functions and Euler products).** Define $L(s, f) = \sum_n a_n(f)\, n^{-s}$; prove convergence; prove the Euler product factorization characterization of normalized eigenforms; prove a non-vanishing/non-zero-eigenvalue lemma. — **Foundational definitions in place; Euler product and non-vanishing open.**

**Phase 8 (Miyake Main Lemma 4.6.8).** Prove the structural decomposition: if $f \in S_k(N,\chi)$ has $a_n(f) = 0$ for all $n$ coprime to a fixed $L$, then $f$ decomposes as a sum of forms $f_p(p\tau)$ with $p$ ranging over primes dividing $\gcd(L, N/\mathrm{cond}(\chi))$. — Substantially done (~12 KLOC of supporting machinery, the Möbius-inverted sieve, prime-power sieves, the conductor-lowering theorem, the support decomposition via Atkin–Lehner ideas). One reverse-direction lemma open (`isSupportedOnDvd_iff_in_levelRaise_image`).

**Phase 9 (Strong Multiplicity One).** Combine the Atkin–Lehner uniqueness theorem (DS 5.8.2 / Miyake 4.6.11) with the Main Lemma to handle the finite exceptional set. — Stated as a theorem (unconditional form), proved conditionally on three Phase-5 / Phase-7 inputs that are currently sorries.

The 9 phases group into **5 work-package epics**:

- **Epic A**: Phases 1–3 algebraic side (Hecke ring foundations, Shimura's results). ✅ done.
- **Epic B**: Phase 3 module-theoretic side (heckeRingHom into $\mathrm{End}(M_k)$; commutativity). ✅ done.
- **Epic C**: Phase 2 character-space side (Shimura Prop 3.34 and Hecke action on $M_k(\Gamma_1(N), \chi)$). Mostly done, with one structural blocker for the abstract general-$\chi$ ring homomorphism.
- **Epic D**: Phase 5 (Hecke adjoint and spectral theorem). **Active.**
- **Epic E**: Phases 6–9 (newforms, L-functions, Main Lemma, SMO).

The critical path to SMO is

$$ \text{Epic D (adjoint, spectral)} \longrightarrow \text{POST-4 (mainLemma)} \longrightarrow \text{POST-6 (Miyake 4.6.8)} \longrightarrow \text{POST-7 (SMO).} $$

Phase 7 (L-functions, ticket POST-3) is a parallel independent track that unblocks POST-5 (non-vanishing of Hecke eigenvalues), which is the remaining input into Phase 9.

---

## 4. Definitions

### 4.1 Abstract Hecke pair and Hecke algebra (Shimura §3.1)

**Definition 4.1 (Hecke pair).** A *Hecke pair* in a group $G$ is a triple $(G, H, \Delta)$ where $H$ is a subgroup of $G$, $\Delta$ is a submonoid of $G$ satisfying $H \leq \Delta \leq \mathrm{Comm}_G(H)$. The commensurator condition guarantees that each double coset $H \alpha H$ ($\alpha \in \Delta$) decomposes into finitely many left $H$-cosets.

**Definition 4.2 (double-coset quotient).** For $\alpha \in \Delta$, write $H_\alpha = H \cap \alpha H \alpha^{-1}$ (the *stabilizer*). The *decomposition quotient* of $\alpha$ is $H / H_\alpha$; it is finite, and writing $\{\sigma_i\}$ for representatives, $H \alpha H = \bigsqcup_i \sigma_i \alpha H$.

**Definition 4.3 (Hecke ring).** The *Hecke ring* $\mathcal{T}(G, H, \Delta; \mathbb{Z})$ is the free $\mathbb{Z}$-module on double cosets $[H \alpha H]$, with multiplication
$$[H \alpha H] \cdot [H \beta H] = \sum_{[H\gamma H]} \mu(\alpha, \beta; \gamma) \cdot [H \gamma H],$$
where $\mu$ counts the pairs $(\sigma_i, \tau_j)$ in the respective decomposition quotients with $\sigma_i \alpha \tau_j \beta \in H \gamma H$ (Shimura, Proposition 3.2). The product is associative (Shimura, Theorem 3.6).

**Definition 4.4 (degree).** The *degree* $\deg : \mathcal{T} \to \mathbb{Z}$ sends $[H \alpha H]$ to the number of left cosets in $H \alpha H$, i.e. $|H/H_\alpha|$. It is a ring homomorphism (Shimura, Proposition 3.3).

### 4.2 The level-$N$ Hecke pair

**Definition 4.5.** $\Delta_0(N) = \{\alpha \in M_2(\mathbb{Z}) \cap \mathrm{GL}_2^+(\mathbb{Q}) : c \equiv 0 \pmod N,\ \gcd(a, N) = 1\}$. The pair $(\mathrm{GL}_2^+(\mathbb{Q}), \Gamma_0(N), \Delta_0(N))$ is a Hecke pair (Shimura, Lemma 3.10).

**Definition 4.6.** The *level-$N$ Hecke algebra* is $\mathcal{T}_N := \mathcal{T}(\mathrm{GL}_2^+(\mathbb{Q}), \Gamma_0(N), \Delta_0(N); \mathbb{Z})$. It is commutative (Shimura, Proposition 3.8, via the Atkin–Lehner anti-involution $g \mapsto w_N g^* w_N^{-1}$ where $w_N = \mathrm{diag}(1, N)$).

**Notation.** $T(a, d)$ for the double coset of $\mathrm{diag}(a, d)$ when $a | d$ (so $T(1, p) = [\Gamma_0(N) \, \mathrm{diag}(1,p) \, \Gamma_0(N)]$); $T(m) = \sum_{a | m} T(a, m/a)$; $T(p, p)$ the "scalar" double coset.

### 4.3 The polynomial-ring isomorphism (Shimura Theorem 3.20)

For a prime $p$ and $n \geq 1$, the *$p$-local Hecke ring* $R_p^{(n)} \subseteq \mathcal{T}(\mathrm{GL}_n^+(\mathbb{Q}), \mathrm{SL}_n(\mathbb{Z}), \Delta_p)$ is the subring generated by the double cosets of diagonal matrices $\mathrm{diag}(p^{a_1}, \ldots, p^{a_n})$ with $a_1 \leq \cdots \leq a_n$. Shimura's Theorem 3.20 states:
$$R_p^{(n)} \cong \mathbb{Z}[X_1, \ldots, X_n]$$
where $X_k$ corresponds to the double coset of $\mathrm{diag}(\underbrace{1,\ldots,1}_{n-k},\underbrace{p,\ldots,p}_{k})$ (the *generator* of weight $k$).

### 4.4 The slash action and Hecke operators on modular forms

**Definition 4.7 (slash action, weight $k$).** For $\alpha \in \mathrm{GL}_2^+(\mathbb{R})$ and $f : \mathfrak{H} \to \mathbb{C}$,
$$(f \mid_k \alpha)(\tau) = (\det \alpha)^{k-1} \, (c\tau + d)^{-k} \, f(\alpha\tau).$$

**Definition 4.8 (Hecke operator).** For a double coset $D = [H\alpha H]$ with left-coset decomposition $H\alpha H = \bigsqcup_i \sigma_i H$, the Hecke operator $T_D$ on $f : \mathfrak{H} \to \mathbb{C}$ is
$$T_D f = \sum_i f \mid_k \sigma_i.$$
On $\Gamma_1(N)$-invariant forms this is well-defined modulo the choice of representatives.

**Definition 4.9 (diamond operator).** For $d \in (\mathbb{Z}/N)^*$ and any lift $\gamma \in \Gamma_0(N)$ with $a(\gamma) \equiv d \pmod N$, $\langle d \rangle f = f \mid_k \gamma$. This is independent of the lift (since $\Gamma_1(N) \trianglelefteq \Gamma_0(N)$).

**Definition 4.10 (nebentypus / character space).** For a Dirichlet character $\chi : (\mathbb{Z}/N)^* \to \mathbb{C}^*$,
$$M_k(\Gamma_1(N), \chi) = \{f \in M_k(\Gamma_1(N)) : \langle d \rangle f = \chi(d) f \text{ for all } d \in (\mathbb{Z}/N)^*\}.$$
Equivalently, the $\chi$-isotypic component of $M_k(\Gamma_1(N))$ for the action of $(\mathbb{Z}/N)^*$.

### 4.5 The Hecke operator $T_p$ on $\Gamma_1(N)$ (explicit form)

For $p$ prime with $\gcd(p, N) = 1$ and $f \in M_k(\Gamma_1(N))$,
$$T_p f = \sum_{b=0}^{p-1} f \mid_k T_p^{\mathrm{upper}}(b) + (\langle p \rangle f) \mid_k T_p^{\mathrm{lower}},$$
where
$$T_p^{\mathrm{upper}}(b) = \left(\begin{smallmatrix} 1 & b \\ 0 & p \end{smallmatrix}\right), \quad T_p^{\mathrm{lower}} = \left(\begin{smallmatrix} p & 0 \\ 0 & 1 \end{smallmatrix}\right).$$
This is the Diamond–Shurman formula (DS Proposition 5.2.1). Note the canonical $\langle p \rangle$-twist on the final summand: if one were to write the formula without the diamond twist, the resulting operator would *not* preserve the character space $M_k(\Gamma_1(N), \chi)$.

### 4.6 Newforms and oldforms (DS §5.6, Miyake §4.6)

**Definition 4.11 (level-raising).** For $M \mid N$ and $d \mid N/M$, the *level-raising operator* $\iota_d : M_k(\Gamma_1(M)) \to M_k(\Gamma_1(M d))$ is $\iota_d f = d^{1-k} (f \mid_k \mathrm{diag}(d, 1))$. In coordinates, $(\iota_d f)(\tau) = f(d\tau)$.

**Definition 4.12 (oldforms / newforms).**
$$S_k^{\text{old}}(\Gamma_1(N)) = \sum_{\substack{M \mid N, M \neq N \\ d \mid N/M}} \iota_d \bigl( S_k(\Gamma_1(M)) \bigr), \qquad S_k^{\text{new}}(\Gamma_1(N)) = S_k^{\text{old}}(\Gamma_1(N))^{\perp},$$
the orthogonal complement with respect to $\langle \cdot, \cdot \rangle_N$.

**Definition 4.13 (eigenform / newform).** $f$ is an *eigenform* if $T_n f = a_n(f) \cdot f$ for all $n$ coprime to $N$. A *newform* of level $N$ is an eigenform $f \in S_k^{\text{new}}(\Gamma_1(N))$ normalized by $a_1(f) = 1$.

---

## 5. Established results

We organize by epic (work package). All results below have full formal proofs unless explicitly noted.

### 5.1 Epic A: Hecke ring foundations (Shimura §3.1–§3.2)

**Theorem 5.1 (Hecke pair for $\mathrm{GL}_n$, level $N$).** *For each $N \geq 1$, $(\Gamma_0(N), \Delta_0(N))$ is a Hecke pair in $\mathrm{GL}_2^+(\mathbb{Q})$.*

*Sketch.* $\Gamma_0(N) \leq \Delta_0(N)$ is direct (entries are integers, $\det = 1 > 0$, $c \equiv 0$). $\Delta_0(N) \leq \mathrm{Comm}(\Gamma_0(N))$: for $\alpha \in \Delta_0(N)$, the intersection $\alpha \Gamma_0(N) \alpha^{-1} \cap \Gamma_0(N)$ contains $\Gamma_0(N \cdot \det\alpha)$, hence is finite-index (Shimura Lemma 3.10). $\blacksquare$

**Theorem 5.2 (degree is a ring homomorphism; Shimura Prop 3.3).** *The map $\deg : \mathcal{T}_N \to \mathbb{Z}$ sending $[H\alpha H]$ to the cardinality of its left-coset decomposition is a ring homomorphism.*

**Theorem 5.3 (Shimura's Theorem 3.20, $n = 2$).** *The $p$-local Hecke algebra $R_p^{(2)} = \mathbb{Z}[T(1,p), T(p,p)]$ is isomorphic to a polynomial ring in two variables over $\mathbb{Z}$.* Proved fully for $n = 1, 2$ (the $n = 2$ case via Kronecker-delta evaluation: a generic monomial $T(1,p)^a T(p,p)^b$ has a unique non-zero coefficient at the basis element $T(p^b, p^{a+b})$, with value $1$).

**Theorem 5.4 (Shimura's Theorem 3.24, $n = 2$).** *The multiplication identities*
$$T(p) T(1, p^k) = T(1, p^{k+1}) + c_k \cdot T(p, p^k), \qquad c_k = \begin{cases} p+1 & k = 1 \\ p & k \geq 2 \end{cases}$$
*and*
$$T(p^r) T(p^s) = \sum_{t=0}^{\min(r,s)} p^t \cdot T(p^t, p^t) \cdot T(p^{r+s-2t})$$
*hold in $R_p^{(2)}$.*

**Theorem 5.5 (Shimura's Theorem 3.35, level-$N$ multiplication law).** *For $\gcd(mn, N) = 1$,*
$$T(m) T(n) = \sum_{\substack{d \mid \gcd(m,n) \\ \gcd(d, N) = 1}} d \cdot T(d, d) \cdot T(mn/d^2),$$
*in $\mathcal{T}_N$. In particular the $T(m)$ with $\gcd(m, N) = 1$ pairwise commute.*

*Sketch.* Apply the level-1 identities (Theorem 5.4) under the surjection $\mathcal{T}_{1} \twoheadrightarrow \mathcal{T}_N$ that sends each double coset to its $\Gamma_0(N)$-double-coset image. Surjectivity at the $p$-component for $p \nmid N$ comes from the CRT-style splitting $\Gamma_0(p^k) \cdot \Gamma_0(N) = \mathrm{SL}_2(\mathbb{Z})$ (relative-index argument). $\blacksquare$

**Theorem 5.6 (commutativity).** *$\mathcal{T}_N$ is a commutative ring.*

*Sketch.* Shimura, Proposition 3.8: the Atkin–Lehner anti-involution $g \mapsto w_N \, g^\top \, w_N^{-1}$ (with $w_N = \mathrm{diag}(1, N)$) preserves $\Delta_0(N)$ entrywise (note $w_N$ acts as integer scaling on the lower-left entry) and fixes every double coset; hence $[H \alpha H] \cdot [H \beta H] = [H \beta H] \cdot [H \alpha H]$. $\blacksquare$

### 5.2 Epic B: Hecke operators on modular forms; commutativity

**Theorem 5.7 (heckeRingHom at level 1).** *The map $\mathcal{T}(\mathrm{SL}_2(\mathbb{Z}); \mathbb{Z}) \to \mathrm{End}_\mathbb{C}(M_k(\mathrm{SL}_2(\mathbb{Z})))$ sending $[H\alpha H]$ to the operator $f \mapsto T_{[H\alpha H]} f$ is a ring homomorphism.*

*Sketch.* The slash action is invariant under the choice of left-coset representatives, so $T_D$ is well-defined on $\Gamma_1(N)$-invariant functions. Composition $T_{D_1} \circ T_{D_2}$ corresponds to the product double-coset sum, which on the basis equals $D_1 \cdot D_2$ in the Hecke ring (Shimura Proposition 3.30). $\blacksquare$

**Theorem 5.8 (heckeRingHom at level $N$, $\chi = 1$).** *The map $\mathcal{T}_N \to \mathrm{End}_\mathbb{C}(M_k(\Gamma_1(N), \mathbf{1}))$ (where $\mathbf{1}$ is the trivial character) is a ring homomorphism. Equivalently, the Hecke operators $T_n$ ($\gcd(n,N)=1$) act on the trivial-character subspace and pairwise commute.*

*Sketch.* The level-$N$ Hecke action on $f \in M_k(\Gamma_1(N), \mathbf{1})$ matches the abstract Hecke action $\mathcal{T}_N \curvearrowright M_k$ defined via $f \mid_k g^*$ over double-coset representatives (the *abstract slash action* `heckeSlash_gen`). Commutativity follows from commutativity of $\mathcal{T}_N$ (Theorem 5.6). $\blacksquare$

**Theorem 5.9 (commutativity of all $T_n$ on $M_k(\Gamma_1(N))$).** *For all $m, n \geq 1$, $T_m T_n = T_n T_m$ on $M_k(\Gamma_1(N))$.*

*Sketch.* Decomposition into character spaces $M_k(\Gamma_1(N)) = \bigoplus_\chi M_k(\Gamma_1(N), \chi)$ (commutativity of $\{T_n\}$ with diamonds gives each $M_k(\Gamma_1(N), \chi)$ as a $\{T_n\}$-stable submodule). On each character space, transfer to $\mathcal{T}_N$ via the explicit formula (with diamond twist on the lower summand) and use commutativity of $\mathcal{T}_N$. Diamond commutativity is direct from $(\mathbb{Z}/N)^*$ being abelian. The Atkin–Lehner anti-involution argument above closes the loop. $\blacksquare$

### 5.3 Epic C: Character spaces and Shimura Proposition 3.34

**Theorem 5.10 (character decomposition).** *For all $k \geq 0$ and $N \geq 1$,*
$$M_k(\Gamma_1(N)) = \bigoplus_{\chi : (\mathbb{Z}/N)^* \to \mathbb{C}^*} M_k(\Gamma_1(N), \chi).$$
*The same decomposition holds for $S_k$.*

*Sketch.* The diamond representation of $(\mathbb{Z}/N)^*$ on $M_k(\Gamma_1(N))$ is semisimple over $\mathbb{C}$ (each diamond has finite order, so the minimal polynomial divides $X^n - 1$ which is separable). Joint diagonalization gives the eigenspace decomposition. Non-multiplicative coefficient functions $\chi$ contribute trivially. $\blacksquare$

**Theorem 5.11 (Shimura Proposition 3.34, good-prime case).** *Let $g \in \Delta_0(N)$ with $\gcd(\det g, N) = 1$, and let $h \in \Gamma_0(N)$. Then $g^* h g \in \Gamma_0(N)$ and the nebentypus map $\Gamma_0(N) \to (\mathbb{Z}/N)^*$, $\gamma \mapsto (a(\gamma) \bmod N)$, is preserved: $a(g^* h g) \equiv a(h) \pmod N$.*

*Sketch.* Direct entry-wise calculation: if $g = \left(\begin{smallmatrix} a & b \\ Nc & d \end{smallmatrix}\right)$ and $h = \left(\begin{smallmatrix} \alpha & \beta \\ N\gamma & \delta \end{smallmatrix}\right)$, then $(g^* h g)_{11} = a d \delta + N \cdot (\text{integer combination})$ and modulo $N$ this is $a d \delta \equiv \det g \cdot \delta \cdot a/a = \det g \cdot \delta \pmod N$. With $\gcd(\det g, N) = 1$, multiplication by $\det g$ is invertible mod $N$. $\blacksquare$

**Theorem 5.12 (stabilizer surjectivity on diagonal cosets).** *For $g = \mathrm{diag}(1, k)$ with $\gcd(k, N) = 1$, the nebentypus map restricted to the stabilizer $\Gamma_0(N) \cap g \Gamma_0(N) g^{-1}$ surjects onto $(\mathbb{Z}/N)^*$.*

*Sketch.* Given $d \in (\mathbb{Z}/N)^*$, lift to $\hat d \in (\mathbb{Z}/kN)^*$ (the natural surjection $(\mathbb{Z}/kN)^* \twoheadrightarrow (\mathbb{Z}/N)^*$ is surjective since $\gcd(k,N) = 1$). Realize $\hat d$ as the nebentypus of an element of $\Gamma_0(kN)$. This element automatically lies in the stabilizer of $\mathrm{diag}(1, k)$ inside $\Gamma_0(N)$ (the stabilizer is precisely $\Gamma_0(kN)$). $\blacksquare$

**Theorem 5.13 ($\chi$-equivariance of $T_p$).** *For $p$ prime with $\gcd(p, N) = 1$, $f \in M_k(\Gamma_1(N), \chi)$, and $g \in \Gamma_0(N)$ with nebentypus $d$,*
$$T_p f \mid_k g = \chi(d) \cdot T_p f.$$
*In particular $T_p f \in M_k(\Gamma_1(N), \chi)$.*

*Sketch.* The Hecke operator commutes with diamonds (`orbit_sum_comm`): $T_p (\langle d \rangle f) = \langle d \rangle (T_p f)$. Apply to $f \in M_k(\Gamma_1(N), \chi)$, where $\langle d \rangle f = \chi(d) f$, to get $\chi(d) \cdot T_p f = \langle d \rangle (T_p f) = (T_p f) \mid_k g$. $\blacksquare$

### 5.4 Epic D: Hecke adjoint theory (Diamond–Shurman §5.5)

**Theorem 5.14 (Diamond–Shurman Proposition 5.5.2(a)).** *For $\alpha \in \mathrm{GL}_2^+(\mathbb{R})$, any measurable $D \subseteq \mathfrak{H}$, and $f, g \in M_k(\Gamma_1(N))$ with the relevant integrals finite,*
$$\int_D (f \mid_k \alpha)(\tau) \, \overline{g(\tau)} \, y^k \, d\mu_{\mathrm{hyp}} = \int_{\alpha D} f(\tau) \, \overline{(g \mid_k \alpha^*)(\tau)} \, y^k \, d\mu_{\mathrm{hyp}}.$$

*Sketch.* Substitute $\tau \mapsto \alpha^{-1} \tau$ in the LHS, using $\mathrm{GL}_2^+(\mathbb{R})$-invariance of $\mu_{\mathrm{hyp}}$ and the identity $(\mathrm{Im}\,\alpha^{-1}\tau)^k = (|\det \alpha|^{-1} \cdot |c\tau + d|^2 \cdot \mathrm{Im}\,\tau / |c\tau + d|^2)^k$ (where $\alpha = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$). Recognize the resulting integrand as $f \cdot \overline{g \mid_k \alpha^*}$. $\blacksquare$

**Theorem 5.15 (level-$N$ slash adjoint).** *For $\alpha \in \mathrm{GL}_2^+(\mathbb{R})$ normalizing $\Gamma_1(N)$, and $f, g \in S_k(\Gamma_1(N))$,*
$$\langle f \mid_k \alpha, \, g \rangle_N = \langle f, \, g \mid_k \alpha^* \rangle_N.$$

*Sketch.* Apply Theorem 5.14 to each coset summand $\int_{q^{-1}\mathcal{D}}$ in the definition of $\langle \cdot, \cdot \rangle_N$; sum over $[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$. The collection $\{\alpha \cdot (q^{-1}\mathcal{D})\}_{[q]}$ tiles a $\Gamma_1(N)$-fundamental domain because $\alpha$ normalizes $\Gamma_1(N)$, so the sum reconstructs $\langle f, g \mid_k \alpha^* \rangle_N$. $\blacksquare$

**Theorem 5.16 (per-coset slash adjoint).** *For $\beta \in \mathrm{GL}_2^+(\mathbb{R})$ and $[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$,*
$$\int_{\mathcal{D}} (f \mid_k q^{-1} \mid_k \beta)(\tau) \, \overline{(g \mid_k q^{-1})(\tau)} \, y^k \, d\mu_{\mathrm{hyp}} = \int_{\beta\mathcal{D}} (f \mid_k q^{-1})(\tau) \, \overline{(g \mid_k q^{-1} \mid_k \beta^*)(\tau)} \, y^k \, d\mu_{\mathrm{hyp}}.$$

This is the per-summand version, applied separately to each $q$.

**Theorem 5.17 (diamond unitarity).** *For $d \in (\mathbb{Z}/N)^*$, $\langle \langle d \rangle f, \langle d \rangle g \rangle_N = \langle f, g \rangle_N$.*

*Sketch.* $\langle d \rangle$ acts by slash via $\gamma_d \in \Gamma_0(N)$ with $\det \gamma_d = 1$, so $\gamma_d^* = \gamma_d^{-1}$. Apply Theorem 5.15 with $\alpha = \gamma_d$ (which normalizes $\Gamma_1(N)$). $\blacksquare$

**Theorem 5.18 (triple-product identity for $T_p^{\mathrm{lower}}$).** *For $p$ prime with $\gcd(p, N) = 1$, there exist $\gamma_0 \in \Gamma_0(N)$ with nebentypus $\langle p \rangle^{-1}$ and $\gamma_1^{-1} \in \Gamma_1(N)$ such that*
$$T_p^{\mathrm{lower}} = \gamma_1^{-1} \cdot T_p^{\mathrm{upper}}(0) \cdot \gamma_0.$$
*Explicitly, with $u v - p w N = 1$ a Bézout relation: $\gamma_0 = \left(\begin{smallmatrix} p & -u \\ Nw & v \end{smallmatrix}\right)$, $\gamma_1^{-1} = \left(\begin{smallmatrix} pv & u \\ -N & 1 \end{smallmatrix}\right)$.*

This is the central combinatorial identity used to reduce the level-$N$ adjoint computation: since $\gamma_1^{-1} \in \Gamma_1(N)$ acts trivially on $\Gamma_1(N)$-forms by slash, $f \mid_k T_p^{\mathrm{lower}} = (f \mid_k T_p^{\mathrm{upper}}(0)) \mid_k \gamma_0$.

**Theorem 5.19 ($T_n$ commutes with diamonds).** *For $n \geq 1$ and $d \in (\mathbb{Z}/N)^*$, $T_n \langle d \rangle = \langle d \rangle T_n$.*

*Sketch.* On $T_p$ for $p \nmid N$, direct from $\langle d \rangle T_p f = \sum_b (\langle d \rangle f) \mid_k T_p^{\mathrm{upper}}(b) + \cdots$ and the explicit conjugation $(T_p^{\mathrm{upper}}(b) \cdot \gamma_d) = (\gamma_d \cdot T_p^{\mathrm{upper}}(b'))$ for $b' = bd^{-1} \bmod p$. Extend to $T_n$ by multiplicativity and the recurrence. $\blacksquare$

**Theorem 5.20 (composite-$n$ adjoint).** *For $\gcd(n, N) = 1$ and $f, g \in S_k(\Gamma_1(N))$,*
$$\langle T_n f, g \rangle_N = \langle f, \langle n \rangle^{-1} T_n g \rangle_N,$$
*assuming the prime case $\langle T_p f, g \rangle_N = \langle f, \langle p \rangle^{-1} T_p g \rangle_N$ holds.*

*Sketch.* Strong induction on $n$. Case $n = 1$: $T_1 = 1$, $\langle 1 \rangle = 1$. Inductive case: factor $n = p^v \cdot m$ with $\gcd(m, p) = 1$. Use multiplicativity $T_n = T_{p^v} T_m$, commutativity (Theorem 5.9), the prime-power recurrence $T_{p^{r+2}} = T_p T_{p^{r+1}} - p^{k-1} \langle p \rangle T_{p^r}$, and the inductive hypothesis. $\blacksquare$

**Theorem 5.21 (normality of $T_n$).** *For $\gcd(n, N) = 1$, $T_n (\langle n \rangle^{-1} T_n) = (\langle n \rangle^{-1} T_n) T_n$ on $S_k(\Gamma_1(N))$. Hence $T_n^* T_n = T_n T_n^*$ (normality).*

*Sketch.* Direct from $T_n \langle d \rangle = \langle d \rangle T_n$ (Theorem 5.19) and commutativity of distinct $T_n$ (Theorem 5.9). $\blacksquare$

**Theorem 5.22 (triangularizability).** *For each $\chi$, each $T_n$ acts triangularizably on $S_k(\Gamma_1(N), \chi)$ over $\mathbb{C}$.*

*Sketch.* Finite-dimensional operator over algebraically closed $\mathbb{C}$: triangularizability is automatic via Mathlib's `iSup_maxGenEigenspace_eq_top`. $\blacksquare$

### 5.5 Epic E: Newforms, support decomposition, and Miyake's structural lemmas

**Theorem 5.23 (smith decomposition in $\Delta_0(N)$).** *For each primitive $\alpha \in \Delta_0(N)$ (i.e., $\gcd$ of entries equals 1) with positive determinant,*
$$\alpha = P \, \mathrm{diag}(m, 1) \, Q$$
*for some $P, Q \in \mathrm{SL}_2(\mathbb{Q})$ and $m = \det \alpha \in \mathbb{Z}^+$.*

This is the classical Smith normal form, packaged for the Hecke-action setting. Used in the proof of Theorem 5.27 (Hecke's Lemma).

**Theorem 5.24 (Hecke's Lemma; Miyake 4.6.3).** *Let $f \in M_k(\Gamma_1(N), \chi)$. If there exists $\alpha \in \Delta_0(N)$ with $\det \alpha > 1$, $\gcd(\det \alpha, N) = 1$, $\alpha$ primitive, and $f \mid_k \alpha \in M_k(\Gamma_1(N), \chi)$, then $f = 0$.*

*Sketch.* Use Theorem 5.23 to write $\alpha = P \cdot \mathrm{diag}(m,1) \cdot Q$. Reduces to the diagonal case $f(m\tau)$ being a level-$N$ form for $m > 1$ coprime to $N$, which forces $f = 0$ by comparing $q$-expansion supports (the level raise puts support on multiples of $m$, but level-$N$ membership at level $N$ alone forces full support). $\blacksquare$

**Theorem 5.25 (Conductor Theorem; Miyake 4.6.4).** *Let $f \in M_k(\Gamma_1(N), \chi)$ be a form with period 1 (i.e., $f(\tau + 1) = f(\tau)$). Suppose $g(\tau) = f(\ell \tau) \in M_k(\Gamma_1(N), \chi)$ for some integer $\ell \geq 1$. Then either $f \in M_k(\Gamma_1(N/\ell), \chi)$ (descent to lower level), or $f = 0$.*

*Sketch.* Combinatorial slash computation: $f \mid_k \widetilde{\gamma} = \chi(d_\gamma) f$ for each $\gamma \in \Gamma_1(N)$ (where $\widetilde \gamma$ is the conjugate of $\gamma$ by the level-raising matrix); the conjugation makes the lower-left entry decrease by a factor of $\ell$, which is consistent with $\Gamma_1(N/\ell)$-membership only when $\ell \mid (N/\mathrm{cond}(\chi))$ or $f$ vanishes. $\blacksquare$

**Theorem 5.26 (coprime sieving; Miyake 4.6.5).** *Let $f \in M_k(\Gamma_1(N), \chi)$ and $L \geq 1$. Define $g \in \mathbb{C}[[q]]$ by $g(\tau) = \sum_{\gcd(n, L) = 1} a_n(f) q^n$. Then $g$ is the $q$-expansion of a form in $M_k(\Gamma_1(NL'), \chi)$, where $L' = L \cdot \prod_{p \mid L, p \mid N} p$.*

*Sketch.* By Möbius inversion, $g(\tau) = \sum_{d \mid L} \mu(d) \cdot f \mid V_d \cdot U_d$ where $V_d : f(\tau) \mapsto f(d\tau)$ and $U_d$ is the standard Hecke operator. Each summand is a level-$NL'$ form; the alternating sum is too. $\blacksquare$

**Theorem 5.27 (radical reduction; Miyake 4.6.7).** *If $L = p_1^{e_1} \cdots p_r^{e_r}$ and $f \in M_k(\Gamma_1(N), \chi)$ has $a_n(f) = 0$ for all $\gcd(n, L) = 1$, then $f \in M_k(\Gamma_1(N \cdot \mathrm{rad}(L)/L), \chi)$ has the same property with $L$ replaced by $\mathrm{rad}(L) = p_1 \cdots p_r$.*

**Theorem 5.28 (support-decomposition forward direction).** *For each $d \mid N$, the image of $\iota_d : M_k(\Gamma_1(N/d)) \to M_k(\Gamma_1(N))$ has $q$-expansion supported on multiples of $d$.*

*Sketch.* Direct from the formula $(\iota_d f)(\tau) = f(d\tau)$. $\blacksquare$

**Theorem 5.29 (newform uniqueness; DS 5.8.2 / Miyake 4.6.11).** *If $f, g \in S_k^{\mathrm{new}}(\Gamma_1(N), \chi)$ are normalized newforms with $a_n(f) = a_n(g)$ for all $n$ coprime to $N$, then $f = g$.*

*Sketch.* $f - g \in S_k^{\mathrm{new}}$ and (by considering Fourier coefficients at $n$ coprime to $N$, which are determined by the eigenvalues) $f - g$ has $a_n = 0$ for all $\gcd(n, N) = 1$. The Main Lemma (Theorem 5.31, currently sorry'd as POST-4) would conclude that $f - g \in S_k^{\mathrm{old}}$. Combined with $S_k^{\mathrm{new}} \cap S_k^{\mathrm{old}} = 0$, we get $f - g = 0$. $\blacksquare$

---

## 6. In progress

### 6.1 Working on: spectral theorem for the Hecke family (ticket `T207`, `exists_simultaneous_eigenform_basis`)

**Statement.** *For each character $\chi$ and weight $k$, there exists a finite set $B \subseteq S_k(\Gamma_1(N), \chi)$ such that (i) each $f \in B$ is a common eigenfunction of all $T_n$ with $\gcd(n, N) = 1$, (ii) elements of $B$ are pairwise $\langle \cdot, \cdot \rangle_N$-orthogonal, and (iii) $B$ spans $S_k(\Gamma_1(N), \chi)$.*

**Current status.** Sorry. The proof is a pure assembly once `T205-d` (Section 6.2) lands: triangularizability (Theorem 5.22) + commutativity (Theorem 5.9) + Mathlib's `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute` gives the joint generalized-eigenspace decomposition $\bigoplus_{\mathbf{e}} \bigcap_i \ker(T_i - e_i)$. Semisimplicity (proved) upgrades generalized eigenspaces to eigenspaces. Orthogonality of distinct joint eigenvalues follows from Theorem 5.20 (the adjoint formula). Within a single joint eigenspace, Gram–Schmidt on the inner product structure provides the orthogonal basis.

**Depends on.** `T205-d` (for the adjoint formula); the rest is Mathlib API assembly. Estimate ~80–120 lines once unblocked.

### 6.2 Working on: the $T_p$ Petersson adjoint (ticket `T205-d`, `petN_heckeT_p_diamond_shift_core`)

**Statement.** *For $p$ prime with $\gcd(p, N) = 1$ and $f, g \in S_k(\Gamma_1(N))$,*
$$\langle T_p f, g \rangle_N = \langle \langle p \rangle f, T_p g \rangle_N. \tag{$\star$}$$

This is the symmetric form of $T_p^* = \langle p \rangle^{-1} T_p$ (Diamond–Shurman Theorem 5.5.3, swapped via diamond unitarity Theorem 5.17). This is **the single most important blocker in the project.** Everything in Phases 6–9 depends on it: the composite-$n$ adjoint (Theorem 5.20) is in place but only conditionally, the spectral theorem ($T207$) cascades from it, and `mainLemma` ($T204$ / POST-4) needs spectral decomposition.

**Current state.** The proof scaffold has expanded $\langle T_p f, g \rangle_N$ on both sides into explicit sums over the Hecke double-coset tiles $\{M_\infty, T_p^{\mathrm{upper}}(0), \ldots, T_p^{\mathrm{upper}}(p-1)\}$ each crossed with the $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$ coset index. Both sides reduce, using Theorems 5.16, 5.17, 5.18 and a Hermitian-swap, to an aggregate four-term identity in which the matrices $\gamma_0, \gamma_1^{-1}$ from Theorem 5.18 are exposed.

**Where it is stuck.** The residual is a *combinatorial coset bijection on $\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$* that absorbs $\gamma_0$ into a reindexing of the coset sum, combined with a matrix identity $T_p^{\mathrm{lower}} \cdot T_p^{\mathrm{upper}}(b) = p \cdot \mathrm{shift}(b)$ with $\mathrm{shift}(b) \in \Gamma_1(N)$ to fold the upper-triangular $b$-sum into a single representative on both sides.

The intended structure: define a bijection $\sigma : \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N) \to \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)$ by $\sigma([q]) = [q \cdot \gamma_0^{-1}]$ on representatives, and match summands LHS$(b, q) \leftrightarrow$ RHS$(c, \sigma(q))$ where $c = c(b, q)$ comes from decomposing $\gamma_0^{-1} \cdot T_p^{\mathrm{upper}}(b) \cdot q^{-1} \cdot \sigma(q)^{-1} \in \Gamma_1(N)$.

**Approaches that didn't work.**
1. Direct application of `petN_slash_invariant` with $\gamma = \gamma_0$ — circular, because the slash invariance is what we're trying to prove.
2. Per-summand application of Theorem 5.14 to drive each integral to a "common form" and then identify — both sides are individually invariant under the available local moves; the difference is a global topological/combinatorial constraint.
3. Per-individual-$\alpha$ "tile balance" identities — these were *attempted* (decommissioned helpers remain in the code) and are *mathematically unsatisfiable in isolation*: only the aggregate sum over all $p+1$ Hecke cosets balances, with cross-cancellations from the diamond twist.

**What we believe is the right framing.** The cleanest analytic statement is:

> *For each $\alpha \in \{T_p^{\mathrm{upper}}(0), \ldots, T_p^{\mathrm{upper}}(p-1), T_p^{\mathrm{lower}}\}$, the union $\bigcup_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \alpha \cdot (q^{-1} \mathcal{D})$ is, up to measure zero, a fundamental domain for $\Gamma_p(\alpha) := \alpha \Gamma_1(N) \alpha^{-1} \cap \Gamma_1(N)$. The finite-index relation $[\Gamma_1(N) : \Gamma_p(\alpha)] = p$ allows tiling the standard $\Gamma_1(N)$-fundamental domain $\mathcal{D}_N$ by $p$ coset translates of this domain.*

Given this finite-index FD-transport theorem, Theorem 5.14 applied across cosets gives ($\star$) directly. The transport theorem is the genuine residual.

**Estimated work.** 80–150 lines of $\sigma$-reindex + matrix bookkeeping, *given* the finite-index FD-transport lemma (which is the "Tertiary support" alluded to in the codebase, also open).

### 6.3 Working on: Miyake Main Lemma at general $L$ (ticket `POST-4` / `mainLemma`)

**Statement.** *If $f \in S_k(\Gamma_1(N), \chi)$ and $a_n(f) = 0$ for all $n$ with $\gcd(n, N) = 1$, then $f \in S_k^{\mathrm{old}}(\Gamma_1(N))$.*

**Current status.** Sorry. Conditional on `T205-d` (Section 6.2) and on `T207` (Section 6.1), the proof is the standard orthogonality argument: decompose $f = f^{\mathrm{old}} + f^{\mathrm{new}}$; for each common-eigenform basis vector $h$ of $S^{\mathrm{new}}_k(\Gamma_1(N), \chi)$, write $\langle f, h \rangle_N = \sum_n \overline{a_n(h)} \cdot a_n(f) \cdot (\text{Rankin–Selberg coefficient})$. The vanishing of $a_n(f)$ for $\gcd(n, N) = 1$ plus the Atkin–Lehner property that $a_n(h) = 0$ for $\gcd(n, N) > 1$ (a multiplicative property of normalized newforms) forces $\langle f, h \rangle_N = 0$, hence $f^{\mathrm{new}} = 0$. *Substantial supporting infrastructure exists in `Eigenforms/MainLemma.lean` (~3450 lines): the Möbius-inverted sieve apparatus, prime-power sieve theorems, the squarefree/radical reductions (Theorems 5.26, 5.27 above) — all proved.* The remaining piece is the spectral-decomposition consumer.

### 6.4 Working on: L-function infrastructure (ticket `POST-3`)

**Statement.** *Build the L-function module: define $L(s, f) = \sum_n a_n(f) n^{-s}$; prove convergence for $\mathrm{Re}(s)$ in a half-plane determined by $k$; prove that the Euler product*
$$L(s, f) = \prod_{p \text{ prime}} (1 - a_p p^{-s} + \chi(p) p^{k-1-2s})^{-1}$$
*holds iff $f$ is a normalized eigenform; provide non-vanishing of $L(s, f)$ on the appropriate line.*

**Current status.** A foundational module exists with the basic definitions and convergence bounds (the half-plane $\mathrm{Re}(s) > k/2 + 1$ for cusp forms via Hecke's bound). The Euler product and non-vanishing are not yet started. This is fully independent of `T205-d` and can run in parallel.

### 6.5 Working on: existence of a non-vanishing Hecke eigenvalue (ticket `POST-5`)

**Statement.** *For any normalized newform $f \in S_k(\Gamma_1(N), \chi)$ and any finite set of primes $S$, there exists a prime $q \notin S$ with $\gcd(q, N) = 1$ and $a_q(f) \neq 0$.*

**Current status.** Sorry. Blocked on `POST-3` (Euler product + analytic continuation + non-vanishing of $L(s, f)$). Classical proof uses Hecke's functional equation: if $a_q = 0$ for cofinitely many $q$, then the Euler factor at each such $q$ contributes only $(1 - 0 + \chi(q)q^{k-1-2s})^{-1}$, forcing $L(s, f)$ to factor as a polynomial in $\chi(q) q^{k-1-2s}$ for all but finitely many $q$, contradicting the analytic behavior (in particular non-vanishing) at $\mathrm{Re}(s) = k/2 + 2$. The conditional theorem `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction` packages this dependency as a propositional input.

---

## 7. Targets (not yet attempted, or only stated)

### 7.1 Strong Multiplicity One (ticket `POST-7`)

**Statement.** As in Section 1: two normalized newforms in the same character space, agreeing on Hecke eigenvalues outside a finite set $S$, are equal.

**Status.** The theorem is *stated* in the codebase as `strongMultiplicityOne` (Phase 9), in two unconditional forms and several conditional forms parameterized by the analytic input from Phase 7. The conditional versions compile sorry-free; the unconditional version is sorry'd, blocked on the open Phase 5 and Phase 7 items.

**Proof skeleton** (post-Phase-5, post-Phase-7).
1. For each $n \in S$, use `POST-5` to find a prime $q \notin S$ with $\gcd(q, n N) = 1$ and $a_q(f) \neq 0$.
2. The relation $a_{nq}(f) = a_n(f) \cdot a_q(f)$ (multiplicativity of the eigenvalue, from Theorem 3.41/Miyake 4.5.4) gives $a_n(f) = a_{nq}(f) / a_q(f)$ when $a_q \neq 0$.
3. Since $nq$ is coprime to $N$ and to all elements of $S$ (by construction), $nq$ lies in the "agreeing" range, so $a_{nq}(f) = a_{nq}(g)$. Similarly $a_q(f) = a_q(g)$.
4. Hence $a_n(f) = a_n(g)$ for each $n \in S$, extending agreement to *all* $n$ coprime to $N$.
5. Apply Atkin–Lehner uniqueness (Theorem 5.29) to conclude $f = g$.

Estimated work after Phase 5, Phase 7 are done: ~80–100 lines.

### 7.2 General-$\chi$ ring homomorphism (`POST-1`; currently blocked)

**Statement.** *For each character $\chi$, there is a ring homomorphism*
$$\mathrm{Hk}_\chi : \mathcal{T}_N \to \mathrm{End}_\mathbb{C}(M_k(\Gamma_1(N), \chi))$$
*sending each double coset $D = [\Gamma_0(N) \alpha \Gamma_0(N)]$ to the Hecke operator $T_D$ defined via Definition 4.8.*

**Status.** Stated; for $\chi = \mathbf{1}$ (trivial character), it is fully proved (Theorem 5.8). For general $\chi$, it is currently *not provable* via the existing abstract definition of $T_D$ (see Section 8.2 for the obstruction). The downstream applications avoid this — the *explicit* Hecke operator at level $N$, defined via the formula in Section 4.5, is fully proved $\chi$-equivariant (Theorem 5.13), and the Hecke action on $M_k(\Gamma_1(N), \chi)$ is constructed by direct restriction of the explicit operator rather than by the abstract one. We retain `POST-1` as a target for *architectural* cleanup — having a uniform ring-hom story over all $\chi$ would simplify the codebase by replacing the case-split between trivial and general $\chi$ with a single abstract theorem.

### 7.3 Reverse of the support-decomposition (open gap in Phase 8)

**Statement.** *If $f \in S_k(\Gamma_1(N))$ has $q$-expansion supported on multiples of $d$ (where $d \mid N$), then $f$ lies in the image of $\iota_d : S_k(\Gamma_1(N/d)) \to S_k(\Gamma_1(N))$.*

**Status.** Stated as `isSupportedOnDvd_iff_in_levelRaise_image` in the Atkin–Lehner module; the forward direction is proved (Theorem 5.28). The reverse direction is open and requires the *trace operator* $\mathrm{Tr}_{N/d}^N : S_k(\Gamma_1(N)) \to S_k(\Gamma_1(N/d))$ (averaging over coset representatives) as a left inverse of $\iota_d$ on $d$-supported forms. This is not on the critical path to SMO (the Main Lemma decomposition route doesn't need it), but is needed for a complete Atkin–Lehner story.

### 7.4 Trace operator and Atkin–Lehner involution

**Status.** A skeleton module exists; the trace operator is defined and basic compatibility lemmas are in place. The full Atkin–Lehner involution $W_N : S_k(\Gamma_0(N)) \to S_k(\Gamma_0(N))$ is not yet formalized; it would package the explicit conjugation $g \mapsto w_N g^* w_N^{-1}$ used in the Theorem 5.6 proof, and would give a more conceptual proof of $T_n$-commutativity.

### 7a. Ticket board (compact view)

| Ticket name | Mathematical statement | Status | Depends on |
|---|---|---|---|
| `Hecke pair Gamma0_N` | $(\Gamma_0(N), \Delta_0(N))$ is a Hecke pair | done | — |
| `Shimura 3.20 n=2` | $R_p^{(2)} \cong \mathbb{Z}[X_1, X_2]$ | done | — |
| `Shimura 3.24 mult law` | $T(p) T(1, p^k)$ recurrence | done | Shimura 3.20 |
| `Shimura 3.35 level-N` | Level-$N$ multiplication law (good primes) | done | Shimura 3.24 |
| `Hecke ring commutativity` | $\mathcal{T}_N$ is commutative | done | Shimura 3.35 |
| `heckeRingHom (trivial $\chi$)` | $\mathcal{T}_N \to \mathrm{End}(M_k(\Gamma_1(N), \mathbf{1}))$ | done | — |
| `Shimura 3.34 good prime` | Nebentypus preserved by adjugate conjugation | done | — |
| `$\chi$-equivariance of $T_p$` | $T_p f \in M_k(\Gamma_1(N), \chi)$ for $f \in M_k(\Gamma_1(N), \chi)$ | done | — |
| `Petersson level-N positive-definite` | $\langle \cdot, \cdot \rangle_N$ is an inner product | done | — |
| `diamondOp unitary` | $\langle \langle d \rangle f, \langle d \rangle g \rangle_N = \langle f, g \rangle_N$ | done | — |
| `peterssonInner_slash_adjoint` | DS Prop 5.5.2(a) | done | — |
| `petN_slash_adjoint_GL2` | Level-$N$ version of Prop 5.5.2(a) | done | — |
| `triple-product-T_p-lower` | $T_p^{\mathrm{lower}} = \gamma_1^{-1} T_p^{\mathrm{upper}}(0) \gamma_0$ | done | — |
| `T205-d / heckeT_p_adjoint_core` | $\langle T_p f, g \rangle = \langle \langle p \rangle f, T_p g \rangle$ | **open (combinatorial bijection)** | finite-index FD transport |
| `T207 / eigenform basis` | Common orthogonal eigenbasis | open | T205-d |
| `heckeT_n_adjoint` | $\langle T_n f, g \rangle = \langle f, \langle n \rangle^{-1} T_n g \rangle$ | done (conditional on T205-d) | T205-d |
| `heckeT_n_normal` | $T_n T_n^* = T_n^* T_n$ | done (conditional) | T205-d |
| `newform_unique` | DS 5.8.2 / Miyake 4.6.11 | done | mainLemma |
| `POST-4 / mainLemma` | Vanishing coprime-$N$ Fourier coefficients ⇒ oldform | open | T207 |
| `Hecke's Lemma (Miyake 4.6.3)` | Diagonal slash forcing zero | done | — |
| `Conductor theorem (Miyake 4.6.4)` | Level descent or vanishing | done | — |
| `Coprime sieving (Miyake 4.6.5)` | Möbius inversion of sieves | done | — |
| `Miyake 4.6.7 (radical reduction)` | Reduce $L$ to $\mathrm{rad}(L)$ | done | — |
| `Miyake 4.6.8 / Main Lemma` | Decomposition $f = \sum f_p(p\tau)$ | substantially done; final assembly open | the open pieces above |
| `POST-3 / L-functions` | Euler product + non-vanishing | open | — |
| `POST-5 / nonzero-eigenvalue` | $a_q(f) \neq 0$ for some $q$ off $S$ | open | POST-3 |
| `POST-7 / SMO` | Miyake 4.6.12 | stated; sorry'd | T207, POST-4, POST-5 |
| `POST-1 / general-$\chi$ ring hom` | Abstract $\mathrm{Hk}_\chi$ | blocked | structural issue (see §8.2) |
| `Trace operator + Atkin–Lehner involution` | $W_N$ machinery | partial | — |
| `Reverse support-decomposition` | $d$-supported ⇒ in $\iota_d$ image | open | trace operator |

The board has ~26 done tickets, ~5 conditionally-closed pending Phase 5, ~6 open, and ~3 blocked.

---

## 8. Where we're stuck

This section is the heart of the brief. Each stuck point describes the mathematical obstacle, our attempts so far, and what we'd like the reviewer to weigh in on.

### 8.1 The $T_p$ Petersson adjoint and the finite-index FD-transport lemma

**The obstacle.** Proving Theorem 5.14 ($\star$) at level $N$ reduces, after using diamond unitarity, the explicit $T_p$ formula, the triple-product identity (Theorem 5.18), and the per-coset adjoint (Theorem 5.16), to an *aggregate combinatorial identity* in which:

$$\sum_{[q] \in \mathrm{SL}_2(\mathbb{Z}) / \Gamma_1(N)} \int_{q^{-1} \mathcal{D}} (\text{integrand involving } T_p^{\mathrm{upper}}(b), T_p^{\mathrm{lower}}) = \sum_{[q]} \int_{q^{-1} \mathcal{D}} (\text{symmetric integrand with } f, g \text{ swapped}).$$

Each per-coset integrand can be analyzed via Theorems 5.14 and 5.16, but the bijection between summands on the two sides is *non-trivial*: it absorbs the $\gamma_0$ from Theorem 5.18 by reindexing $[q] \mapsto [q \gamma_0^{-1}]$ on $\mathrm{SL}_2(\mathbb{Z}) / \Gamma_1(N)$ and changes the upper-triangular parameter $b \mapsto c(b, q)$ in a way determined by a Bézout-style relation.

We have not been able to *individually balance* each summand: per-individual-$\alpha$ attempts produce identities that are *only correct in aggregate*, with cross-cancellations among the $p+1$ matrices.

The cleanest abstract statement we believe is needed is the following:

> **Open lemma (finite-index FD-transport).** *Let $\Gamma_p(\alpha) := \alpha \Gamma_1(N) \alpha^{-1} \cap \Gamma_1(N)$ for $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$. Then $[\Gamma_1(N) : \Gamma_p(\alpha)]$ is finite, and a Borel fundamental domain for $\Gamma_p(\alpha)$ acting on $\mathfrak{H}$ tiles a $\Gamma_1(N)$-fundamental domain by the action of a coset transversal.*

This lemma is essentially classical (Borel) but we have not yet found a frictionless Mathlib path; the Lean infrastructure has Mathlib's `IsFundamentalDomain` API and Mathlib's `Subgroup.relIndex_le_index`, but composing them into the FD-tiling claim needs careful AE-measurability bookkeeping.

**Questions for the reviewer (see Section 9):** Q1, Q3.

### 8.2 The general-$\chi$ ring homomorphism obstruction (POST-1)

**The setup.** The abstract Hecke operator $T_D$ for a double coset $D \subseteq \Gamma_0(N) \alpha \Gamma_0(N)$ is defined by
$$T_D f = \sum_{[\sigma] \in \Gamma_0(N) / \Gamma_0(N)_\alpha} f \mid_k (\sigma \cdot \alpha^*)$$
where $\sigma$ ranges over representatives of the decomposition quotient. (We use $\alpha^*$ rather than $\alpha$ to ensure preservation under the slash action with the $\mathrm{GL}_2^+(\mathbb{R})$-embedded representation.)

The choice of representatives $\sigma$ is mediated, in our Lean formalization, by the `Quotient.out` operator (a Classical.choice-backed selection function from each equivalence class to one of its representatives). For $\chi = \mathbf{1}$, this is harmless: different choices of $\sigma$ differ by elements of $\Gamma_0(N)_\alpha$, on which the slash action is trivial (constant character).

For $\chi \neq \mathbf{1}$, different choices of $\sigma$ differ by elements of $\Gamma_0(N)_\alpha \subseteq \Gamma_0(N)$, whose nebentypus is *not always trivial*, so the slash action picks up a $\chi$-factor depending on the representative. The choice mediated by `Quotient.out` carries no canonical relationship to the nebentypus, so the sum $\sum_{[\sigma]} f \mid_k (\sigma.out \cdot \alpha^*)$ for general $\chi$ does not equal the *explicit* Hecke operator $T_p$ defined by the $p+1$ coset formula in Section 4.5.

**Why this is not fundamentally a problem.** The downstream applications use the *explicit* operator, defined directly via the formula in Section 4.5 with the canonical $\langle p \rangle$-twist on the $T_p^{\mathrm{lower}}$ summand. This operator does satisfy $\chi$-equivariance (Theorem 5.13), and on it we build everything: Hecke action on $M_k(\Gamma_1(N), \chi)$, commutativity (Theorem 5.9), and the spectral theorem.

**The diagnostic.** A short lemma proven in `HeckeSlashExplicit.lean` shows that for $\chi = \mathbf{1}$, the abstract and explicit Hecke operators agree (the `bridge lemma`). For $\chi \neq \mathbf{1}$, the two operators *do not coincide* — the abstract one's representative choices propagate $\chi$-factors that the explicit one absorbs into the diamond twist. This is not a bug; it is the structural reason the abstract operator is not the right object for the character-space setting.

**Question for the reviewer (see Section 9):** Q2.

### 8.3 The $\Gamma_0(N)$ pivot (Epic B history)

**The history.** The original plan (early Epic B) was to construct a ring homomorphism
$$\mathcal{T}(\mathrm{GL}_2^+(\mathbb{Q}), \Gamma_1(N), \Delta_1(N); \mathbb{Z}) \to \mathrm{End}_\mathbb{C}(M_k(\Gamma_1(N)))$$
directly, via an abstract Hecke pair on $\Gamma_1(N)$. This *failed structurally*: the adjugate of $\mathrm{diag}(1, p)$ in $\Delta_0(N)$ is $\mathrm{diag}(p, 1)$, and these define *different* $\Gamma_1(N)$-double cosets for $p \not\equiv 1 \pmod N$. Specifically:
$$\Gamma_1(N) \cdot \mathrm{diag}(1, p) \cdot \Gamma_1(N) \neq \Gamma_1(N) \cdot \mathrm{diag}(p, 1) \cdot \Gamma_1(N) \quad \text{when } p \not\equiv 1 \pmod N.$$
The abstract slash action via `heckeSlash_gen` sums over the $\Gamma_1(N)$-double-coset structure, and the adjugate move thus produces a Hecke operator that doesn't match the explicit $T_p$ — it differs by a permutation of double cosets reflecting the level-$N$ congruence on the upper-left entry.

**The pivot.** We pivoted to using the *coarser* $\Gamma_0(N)$-double-coset structure throughout, then recovering the $\Gamma_1(N)$ action by character decomposition (Theorem 5.10). At the $\Gamma_0(N)$ level the adjugate move sends $\mathrm{diag}(1, p)$ to $\mathrm{diag}(p, 1)$, both of which lie in the *same* $\Gamma_0(N)$-double coset. The cardinality of the decomposition quotient is $p+1$ at $\Gamma_0(N)$, matching the level-1 picture (Shimura 3.35 surjection has trivial kernel at good primes).

The pivot has been validated: all of Epic B's commutativity and ring-hom theorems went through cleanly via $\mathcal{T}_N$ (the $\Gamma_0(N)$-Hecke algebra). Theorem 5.6 (commutativity of $\mathcal{T}_N$) is proved via the standard Atkin–Lehner anti-involution, and the heckeRingHom statement (Theorem 5.7, level-1; Theorem 5.8, level-$N$, trivial $\chi$) lifts to the $\Gamma_1(N)$ setting via character decomposition.

**What we're checking.** Did we make the right structural choice? Is there an alternative path through $\Gamma_1(N)$ that we missed?

**Question for the reviewer:** Q4.

### 8.4 Phase 8 sub-ticket decomposition

**The setup.** The 2026-04-17 plan decomposes Phase 8 (Miyake's Main Lemma 4.6.8) into five sub-tickets:
- POST-6a (Miyake 4.6.3 / Hecke's Lemma): $f \in M_k(\Gamma_1(N), \chi)$, $\alpha \in \Delta_0(N)$ primitive with $\det > 1$, and $f \mid_k \alpha \in M_k(\Gamma_1(N), \chi)$ ⇒ $f = 0$.
- POST-6b (Miyake 4.6.4 / Conductor Theorem): period-1 + level-$\ell$ scaling ⇒ descend or vanish.
- POST-6c (Miyake 4.6.5 / Coprime Sieving): Möbius inversion of coefficient sieves.
- POST-6d (Miyake 4.6.7 / Squarefree Decomposition).
- POST-6e: Final assembly of Main Lemma 4.6.8.

**Current state.** Substantial code (~12 KLOC) exists across `Eigenforms/MainLemma.lean`, `Eigenforms/HeckeLemma.lean`, `Eigenforms/ConductorTheorem.lean`, `Eigenforms/AtkinLehner.lean`, etc., that *implements* most of these sub-results (Theorems 5.23–5.28 above). The implementation, however, is not strictly split along POST-6a/b/c/d/e lines — the lemmas are interleaved across files and use slightly different notation (the support-decomposition approach via `IsSupportedOnDvd` and `qSupportedOnDvdSubmodule` rather than the direct Möbius-inverted-sieve approach in Miyake).

**Question we want answered.** Is our existing decomposition (support-based, Atkin–Lehner-style) a cleaner organization of the Main Lemma than Miyake's classical decomposition, or have we fragmented something that would be more transparent if kept together? Specifically, the reverse-direction lemma `isSupportedOnDvd_iff_in_levelRaise_image` is currently open and *would not be needed* if we followed Miyake's classical squarefree induction more directly.

**Question for the reviewer:** Q5.

---

## 9. Open mathematical questions for the reviewer

We ask the reviewer for **substantive guidance on the following numbered questions.** Mix of user-supplied (Q1–Q4) and agent-surfaced (Q5–Q7).

### Q1. Is our $\Gamma_0(N)$-pivot structurally optimal?

We abandoned the direct abstract Hecke ring of $\Gamma_1(N)$ (because the adjugate moves $\mathrm{diag}(1,p) \to \mathrm{diag}(p,1)$, which are *distinct* $\Gamma_1(N)$-double cosets for $p \not\equiv 1 \pmod N$). We instead built the abstract Hecke ring on $\Gamma_0(N)$ and recover the $\Gamma_1(N)$ action via character decomposition.

Is this the cleanest structural choice for formalization? Is there a known framework — perhaps via Hecke pairs on $\Gamma_0(N) \cdot Z$ where $Z$ is the centralizer, or via the Atkin–Lehner adelic framework — that would unify the level-$N$ Hecke algebra into a single ring-hom story without needing the character split?

### Q2. Should the general-$\chi$ ring homomorphism (POST-1) be unblocked, or can we permanently skip it?

The abstract Hecke ring $\mathcal{T}_N$ acts on $M_k(\Gamma_1(N))$ uniformly. But when restricted to $M_k(\Gamma_1(N), \chi)$ for general $\chi$, the abstract `heckeSlash_gen D f` (defined via Classical.choice-mediated coset representatives) does *not* equal the explicit $T_p$ (defined via the standard $p+1$ coset formula with the canonical $\langle p \rangle$-twist).

Our workaround: use the explicit operator throughout the character-space setting, which is $\chi$-equivariant by construction. The downstream theorems all go through this route.

Is the abstract general-$\chi$ ring hom worth pursuing as a *clean architectural object*, perhaps via a redefinition of the abstract action that bakes in the $\langle p \rangle$-twist? Or is the current bifurcation (abstract for $\chi = \mathbf{1}$, explicit for general $\chi$) actually the right pedagogical and mathematical state? We could argue either way, and would benefit from an outside perspective.

### Q3. Is the combinatorial bijection in T205-d the right framing for the $T_p$ Petersson adjoint?

We are stuck on the symmetric form $\langle T_p f, g \rangle_N = \langle \langle p \rangle f, T_p g \rangle_N$ at the level of an aggregate $\sigma$-reindex on $\mathrm{SL}_2(\mathbb{Z}) / \Gamma_1(N)$ combined with a matrix identity $T_p^{\mathrm{lower}} \cdot T_p^{\mathrm{upper}}(b) = p \cdot \mathrm{shift}(b)$ inside $\Gamma_1(N)$ (see Section 6.2 / 8.1).

Diamond–Shurman's classical proof (DS 5.5.3) follows Petersson's original 1939 argument: it goes through the *change-of-variables for the integral over a fundamental domain*, using the explicit Smith decomposition of $T_p^{\mathrm{upper}}(b)$ and $T_p^{\mathrm{lower}}$. Miyake gives a more direct (Lemma 4.5.4) proof via the *trace formula* on the local Hecke ring.

Are we attacking this from the wrong angle? Should we instead:
- (a) Bypass the explicit combinatorial bijection and use the abstract slash adjugate $\alpha^*$ + global Hecke ring trace? 
- (b) Use the L-function functional equation (Phase 7) to prove the adjoint, which classically gives a one-line proof? (At the cost of completing POST-3 first.)
- (c) Stick with the current σ-reindex but find a slicker presentation that doesn't require the finite-index FD-transport lemma as a residual?

What's the cleanest path forward?

### Q4. Is splitting Phase 8 into POST-6a/b/c/d/e correct given existing code?

We have ~12 KLOC of Phase 8 code that does *not* strictly follow Miyake's classical sub-decomposition (4.6.3 → 4.6.4 → 4.6.5 → 4.6.7 → 4.6.8). Instead it follows a support-based / Atkin–Lehner-style decomposition via `IsSupportedOnDvd` and `qSupportedOnDvdSubmodule`. The latter has one open reverse-direction lemma (`isSupportedOnDvd_iff_in_levelRaise_image`) that Miyake's route avoids.

Is the support-based organization (which exposes the level-raising image as a natural submodule and makes Atkin–Lehner involutions transparent) genuinely better, or have we built unnecessary machinery? Should we restructure to follow Miyake more directly, accept the existing organization with the open lemma as a feature, or take a hybrid path?

### Q5. Critical-path realism

The critical path to SMO is

$$ T205\text{-d} \longrightarrow T207 \longrightarrow \text{POST-4} \longrightarrow \text{POST-7}, $$
with POST-3 / POST-5 as a parallel track unblocking POST-5 and POST-7's full version.

Are we right to treat T205-d as the *single* critical blocker? Or are we underestimating the complexity of POST-3 (L-function infrastructure, ~500 LOC of new code starting from minimal foundations)? Should we be running POST-3 *now* with higher priority?

### Q6. Choice of foundations: Mathlib's `Module.End.iSup_iInf_maxGenEigenspace_eq_top` vs. a more direct argument

For T207 (the simultaneous eigenform basis), we plan to use Mathlib's pre-existing API for joint eigenspace decompositions of commuting operators. Specifically `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`. This requires showing each $T_n$ is *triangularizable* (which we have: Theorem 5.22) and that the $T_n$ *pairwise commute* (which we have: Theorem 5.9).

An alternative is to prove the spectral theorem from scratch by induction on dimension, using the orthogonality of distinct eigenspaces (from the adjoint formula) and Gram–Schmidt for the intra-eigenspace basis. This avoids depending on Mathlib's heavy linear-algebra API.

Which is preferable from a *mathematical conceptual* standpoint? Mathlib's API gives a quick win but obscures the role of normality; a from-scratch proof is more transparent but ~3× longer in LOC.

### Q7. Generality of the formalization

Our formalization specializes to elliptic ($\mathrm{GL}_2$) modular forms throughout. Miyake's Main Lemma and SMO have generalizations to:
- $\mathrm{GL}_n$ automorphic forms (Jacquet–Shalika 1981);
- modular forms over totally real fields (Hilbert modular forms);
- Maass forms (with the full Selberg trace formula).

We do *not* intend to formalize these generalizations within this project. The question is structural: are our definitions (abstract Hecke pair, decomposition quotient, slash action, adjugate) modular enough that someone extending the project to $\mathrm{GL}_n$ or Hilbert modular forms could reuse them, or have we baked in $\mathrm{GL}_2$-specific assumptions that would require substantial rework?

---

## 10. Auxiliary technical results (appendix)

Lemmas and definitions the reviewer doesn't need to read carefully, but may want to spot-check.

### 10.1 Diamond representation semisimplicity

**Lemma.** *For each $d \in (\mathbb{Z}/N)^*$, the diamond operator $\langle d \rangle$ on $M_k(\Gamma_1(N))$ is semisimple over $\mathbb{C}$.*

*Sketch.* $(\mathbb{Z}/N)^*$ is a finite group, and the diamond representation is the restriction of a finite-group representation; over $\mathbb{C}$ this is automatically semisimple (Maschke's theorem). Concretely, the minimal polynomial of $\langle d \rangle$ divides $X^{|d|} - 1$ (where $|d|$ is the order of $d$), which is separable over $\mathbb{C}$.

### 10.2 Gamma1 vs Gamma0 fundamental domain transport

**Lemma.** *A fundamental domain $\mathcal{D}_{\Gamma_0(N)}$ for $\Gamma_0(N)$ acting on $\mathfrak{H}$ admits a $[ \Gamma_0(N) : \Gamma_1(N) ] = \varphi(N)$-to-1 lift to a fundamental domain $\mathcal{D}_{\Gamma_1(N)}$ via coset translates.*

### 10.3 Smith decomposition

**Lemma.** *Each $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$ admits a decomposition $\alpha = P \cdot \mathrm{diag}(m, 1) \cdot Q$ with $P, Q \in \mathrm{SL}_2(\mathbb{Q})$ and $m \in \mathbb{Q}^+$. If $\alpha \in \Delta_0(N)$ is primitive, then $m \in \mathbb{Z}^+$.*

### 10.4 Möbius inversion of coefficient sieves

**Lemma.** *For any function $a : \mathbb{N}^+ \to \mathbb{C}$ and any $L \geq 1$,*
$$\sum_{\gcd(n, L) = 1} a_n = \sum_{d \mid L} \mu(d) \sum_{n : d \mid n} a_n.$$

### 10.5 Hermitian symmetry of $\langle \cdot, \cdot \rangle_N$

**Lemma.** $\langle f, g \rangle_N = \overline{\langle g, f \rangle_N}$.

### 10.6 Linearity of $\mathrm{Hk}_\chi$ in the eigenvalue indexing

**Lemma.** *For $f \in M_k(\Gamma_1(N), \chi)$ a Hecke eigenform with $T_n f = a_n f$, the function $n \mapsto a_n$ on $\gcd(n, N) = 1$ is completely multiplicative in the sense that $a_{mn} = a_m \cdot a_n$ when $\gcd(m, n) = 1$, and on prime powers satisfies the recurrence $a_{p^{r+2}} = a_p a_{p^{r+1}} - \chi(p) p^{k-1} a_{p^r}$.*

---

## 11. Document metadata

- **Project name:** LeanModularForms-hecke
- **Branch:** `hecke-ring`
- **Brief generated:** 2026-05-11
- **Approximate length:** ~14 pages (~9,000 words)
- **Definitions stated:** 13 (Sections 4.1–4.6)
- **Theorems established:** 29 (Section 5)
- **In-progress lemmas:** 5 (Section 6)
- **Targets and blocked items:** 4 (Section 7)
- **Stuck points:** 4 (Section 8)
- **Open questions for reviewer:** 7 (Section 9)
- **References:** 6 with full citations
- **Build status:** clean (`lake build` succeeds); 31 sorries scattered across the open and conditionally-closed lemmas listed above
- **Recent activity:** active work on T205-d ("petN_heckeT_p_diamond_shift_core") through late April–early May 2026; the last 15 commits incrementally introduce alignment helpers, AE-disjoint family lemmas, integrability bridges, and aggregate-level reductions for the bijection.

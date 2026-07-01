# Review brief — T205-d: the Petersson adjoint at level $N$ for $T_p$

*Prepared 2026-05-11 (follow-up to the 2026-05-11 brief). Same reviewer audience as before. Self-contained: no repository access required. Conventions follow Diamond–Shurman and Miyake throughout.*

---

## 1. What this brief is about

This is a **focused follow-up** to the 2026-05-11 review of the Strong Multiplicity One (SMO) formalization project. The previous reply gave a two-step API for the level-$N$ Petersson adjoint identity for $T_p$ at primes $p \nmid N$:

> **(Step 1)** Finite-index FD-transport from $\mathrm{PSL}_2(\mathbb{R})$ to $\Gamma_1(N) \backslash \mathfrak{H}$ via $\Gamma_p(\alpha) = \alpha^{-1} \Gamma_1(N) \alpha \cap \Gamma_1(N)$.
>
> **(Step 2)** Hecke-correspondence adjoint identity at level $\Gamma_1(N)$, parametric in $\alpha \in \Delta_0(N)$:
> $$\langle T_\alpha f, g \rangle_N = \langle f, T_{\alpha^*} g \rangle_N \cdot (\det \alpha)^{1-k} \cdot \text{(character correction)}.$$
>
> Then specialise to $\alpha = \mathrm{diag}(1,p)$ to recover $T_p^* = \langle p \rangle^{-1} T_p$, i.e. Diamond–Shurman Theorem 5.5.3.

Step 1 has been **fully formalized** (the FD-transport theorem `Gamma_p_α_PSL_R_FD_finite_index_decomp_auto` is sorry-free, axiom-clean apart from `propext`, `Classical.choice`, `Quot.sound`). Step 2 remains the **single live blocker** for SMO. The relevant Lean declaration is

> **Target Theorem (T205-d, "level-$N$ Petersson adjoint for $T_p$"):**
> *For all weights $k \geq 2$, levels $N \geq 1$, characters $\chi \bmod N$, primes $p \nmid N$, and cusp forms $f, g \in S_k(\Gamma_1(N))$,*
> $$\langle T_p f, g \rangle_N = \langle p \rangle^{-1} \langle f, T_p g \rangle_N.$$

We have spent several weeks on a particular reduction strategy (the **"8-layer chain"** described in §6 below) that turned out, in retrospect, to be the wrong organising principle. We have stripped it back; only the few salvageable lemmas remain. We have set up the **Hecke-correspondence adjoint** scaffold per the reviewer's recommendation (called `peterssonInner_slash_adjoint_coset` in the code; see §4) and identified the genuine analytic content that is now blocking us. The blocker is **DS Proposition 5.5.2(b)**:

> **DS Prop 5.5.2(b).** *Let $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$ and $\Gamma$ a congruence subgroup. For $f \in S_k(\Gamma)$ and $g \in S_k(\alpha^{-1} \Gamma \alpha)$,*
> $$\int_{\Gamma \backslash \mathfrak{H}} f(\tau) \overline{(g \mid_k \alpha^{-1})(\tau)} \, y^k \, \mathrm{d}\mu_{\mathrm{hyp}} = (\det \alpha)^{k-1} \int_{\alpha^{-1} \Gamma \alpha \backslash \mathfrak{H}} (f \mid_k \alpha)(\tau) \overline{g(\tau)} \, y^k \, \mathrm{d}\mu_{\mathrm{hyp}}.$$

This is a change-of-variables identity for the level-$N$ Petersson form under the slash action. It is the *single* non-trivial analytic fact that any reasonable proof of T205-d must use; we have not yet found a formalization route through it that does not blow up.

**Purpose of this brief.** We want guidance on how to bridge the 8-layer chain (or what remains of it) to closure of T205-d, with a particular focus on:

1. The **concrete proof** of DS Prop 5.5.2(b) at the integrand level, in a form amenable to formalization in Lean/Mathlib.
2. Whether to **drop more layers** of the chain or salvage the remaining ones.
3. Concrete **tickets** for sub-proofs that we should be planning.
4. **Alternative routes** to T205-d that bypass DS Prop 5.5.2(b) (Atkin–Lehner–Li orthogonality, the $U_p$ eigenspace decomposition, the abstract Petersson adjoint via Hilbert-space duality, …).

This brief is long — there is a lot of detail in §6 about what has been tried — but the **operative content** is in §4 (status of the two-step API), §7 (where work breaks down), and §10 (the seven numbered questions).

---

## 2. Notation, conventions, setting

We restate notation that the prior brief established, so this document is fully self-contained.

### 2.1 Groups and Hecke pair

- $\mathrm{GL}_2^+(\mathbb{R}) = \{\alpha \in \mathrm{GL}_2(\mathbb{R}) : \det \alpha > 0\}$ acts on the upper half-plane $\mathfrak{H} = \{\tau \in \mathbb{C} : \mathrm{Im}\,\tau > 0\}$ by Möbius transformations $\alpha\tau = (a\tau+b)/(c\tau+d)$.
- $\Gamma(N) = \ker(\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N))$, $\Gamma_1(N) = \{\gamma : \gamma \equiv \left(\begin{smallmatrix}1&*\\0&1\end{smallmatrix}\right) \bmod N\}$, $\Gamma_0(N) = \{\gamma : c \equiv 0 \bmod N\}$.
- $\Delta_0(N) = \{\alpha \in M_2(\mathbb{Z}) : c \equiv 0 \bmod N,\ \gcd(a,N) = 1,\ \det \alpha > 0\}$ is the level-$N$ Hecke monoid. The pair $(\Gamma_0(N), \Delta_0(N))$ is a Hecke pair (Shimura Lemma 3.10).

For $\alpha \in \Delta_0(N)$ we use the shorthand
$$\Gamma_p(\alpha) := \alpha^{-1} \Gamma_1(N) \alpha \cap \Gamma_1(N).$$
When $\alpha = \mathrm{diag}(1,p)$ with $p \nmid N$, $\Gamma_p(\alpha)$ has index $p$ in $\Gamma_1(N)$ and index $p+1$ in $\Gamma_p$ (which we use only as a name in the code; see code identifier `Gamma_p_α`).

### 2.2 Slash action

For $\alpha = \left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right) \in \mathrm{GL}_2^+(\mathbb{R})$ and integer weight $k \geq 1$:
$$(f \mid_k \alpha)(\tau) := (\det\alpha)^{k-1} (c\tau + d)^{-k} f(\alpha\tau).$$

This is the Diamond–Shurman / Miyake convention. With this normalisation the level-raising map $V_p : f(\tau) \mapsto f(p\tau)$ equals $p^{1-k}\, (f\mid_k \mathrm{diag}(p,1))$.

### 2.3 Petersson product

The level-1 Petersson form on $S_k(\mathrm{SL}_2(\mathbb{Z}))$ is
$$\langle f, g \rangle = \int_{\mathcal{D}} f(\tau) \overline{g(\tau)} \, y^k \, \mathrm{d}\mu_{\mathrm{hyp}}$$
with $\mathcal{D}$ the standard fundamental domain and $\mathrm{d}\mu_{\mathrm{hyp}} = y^{-2}\,\mathrm{d} x\,\mathrm{d} y$.

For level $N$, the form we work with is
$$\langle f, g \rangle_N := \sum_{[q] \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)} \int_{\mathcal{D}} (f \mid_k q^{-1})(\tau) \, \overline{(g \mid_k q^{-1})(\tau)} \, y^k \, \mathrm{d}\mu_{\mathrm{hyp}}.$$
This sums the level-1 Petersson form over (right) coset representatives of $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb{Z})$. It is unnormalised; spectrality requires only positive-definiteness and conjugate-symmetry, which are preserved.

In the code this is `petN k N f g`.

### 2.4 The Hecke operator $T_p$ and the "triple-product identity"

For $p \nmid N$, Shimura's $T_p$ on $S_k(\Gamma_1(N))$ has the coset decomposition
$$T_p f = \sum_{b=0}^{p-1} f \mid_k \left(\begin{smallmatrix}1&b\\0&p\end{smallmatrix}\right) + \langle p \rangle f \mid_k \left(\begin{smallmatrix}p&0\\0&1\end{smallmatrix}\right).$$

The "upper-triangular" piece $\sum_{b=0}^{p-1} f \mid_k \left(\begin{smallmatrix}1&b\\0&p\end{smallmatrix}\right)$ is what we call $\widetilde{T}_p^{\mathrm{upper}}(0)$; the "lower-triangular" piece $\langle p \rangle f \mid_k \mathrm{diag}(p,1)$ is what we call $\widetilde{T}_p^{\mathrm{lower}}$.

A standard manipulation (Miyake 4.5.5; "triple-product identity") relates the upper and lower pieces:
$$\widetilde{T}_p^{\mathrm{lower}} = \gamma_1^{-1} \cdot \widetilde{T}_p^{\mathrm{upper}}(0) \cdot \gamma_0,$$
where $\gamma_0, \gamma_1 \in \mathrm{SL}_2(\mathbb{Z})$ are chosen so that conjugation by them sends $\mathrm{diag}(p,1)$ to $\mathrm{diag}(1,p)$ up to a determinant correction. We use this identity to swap the lower piece for the upper, at the cost of an extra slash action.

### 2.5 The Petersson adjoint $M^*$

For $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$, define
$$M^* := (\det\alpha)\, \alpha^{-1} = \alpha^{\mathrm{adj}}.$$
(In code: `peterssonAdj α`.) For $\alpha = \mathrm{diag}(1,p)$ we get $M^* = \mathrm{diag}(p,1)$. The identity we are trying to prove (DS Theorem 5.5.3 specialised) says that $T_p^*$, the *operator-theoretic* adjoint of $T_p$ on $S_k(\Gamma_1(N))$ for $\langle\cdot,\cdot\rangle_N$, equals $\langle p \rangle^{-1} T_p$. This is the level-$N$ generalisation of DS Theorem 5.5.3.

### 2.6 What "M_∞" means in the code

`M_∞` is our shorthand for the upper-piece slash operator $\widetilde{T}_p^{\mathrm{upper}}(0) = \sum_{b=0}^{p-1} f \mid_k \left(\begin{smallmatrix}1&b\\0&p\end{smallmatrix}\right)$, viewed as a single linear endomorphism of $S_k(\Gamma_1(N))$. Under the triple-product identity and the $M^*$-bookkeeping, it is the central object that propagates through the reductions in §6. In a few places the code computes $\mathrm{peterssonAdj}(M_\infty)$, the adjugate of the $\mathrm{diag}(1,p)$ piece composed with a Q-permutation $\sigma_p$.

---

## 3. Primary references

- **[DS]** Fred Diamond and Jerry Shurman. *A First Course in Modular Forms*. Graduate Texts in Mathematics 228. Springer, 2005. **Theorem 5.5.3** (the statement of $T_p^*$ in terms of diamond operators), **Proposition 5.5.2** (the change-of-variables identity at the integrand level), and **Theorem 5.5.4** (full multiplicativity).
- **[Mi]** Toshitsune Miyake. *Modular Forms*. Springer Monographs in Mathematics, 2nd ed., Springer, 2006. **Theorem 4.5.4** (Hecke ring at level $N$), **Theorem 4.5.5** (coset decomposition for $\Gamma_1(N)\,\mathrm{diag}(1,p)\,\Gamma_1(N)$ for $p \nmid N$), **Theorem 4.6.8** (Main Lemma on sparse Fourier supports), **Theorem 4.6.12** (Strong Multiplicity One).
- **[Sh]** Goro Shimura. *Introduction to the Arithmetic Theory of Automorphic Functions*. Princeton, 1971. **Theorems 3.20, 3.24, 3.34, 3.35** (the abstract Hecke algebra), and **Proposition 3.39** (the Petersson adjoint at level $\Gamma_0(N) \cap \Gamma^1(N)$).
- **[AL]** A. O. L. Atkin and J. Lehner. "Hecke operators on $\Gamma_0(m)$." *Math. Ann.* **185** (1970), 134–160. The classical orthogonality of oldforms and newforms.
- **[Li]** W.-C. W. Li. "Newforms and functional equations." *Math. Ann.* **212** (1975), 285–315. Generalisation of Atkin–Lehner to $\Gamma_1(N)$ with character.

---

## 4. The two-step API: current status

The reviewer's 2026-05-11 reply recommended a two-step API. We restate it and report status.

### 4.1 Step 1 — Finite-index FD-transport from $\mathrm{PSL}_2(\mathbb{R})$ to $\Gamma_1(N) \backslash \mathfrak{H}$

> **Theorem 4.1 (Step 1, "FD-transport").** *Let $N \geq 1$, $\alpha \in \Delta_0(N)$, and write $\Gamma_p(\alpha) = \alpha^{-1} \Gamma_1(N) \alpha \cap \Gamma_1(N)$. Then $\Gamma_p(\alpha) \leq \Gamma_1(N)$ has finite index, the action of $\Gamma_p(\alpha)$ on $\mathfrak{H}$ admits a fundamental domain $\mathcal{F}_p \subset \mathfrak{H}$, and for every $h \in L^1(\mathcal{F}_p, \mathrm{d}\mu_{\mathrm{hyp}})$ we have*
> $$\int_{\mathcal{F}_p} h(\tau) \, \mathrm{d}\mu_{\mathrm{hyp}} = \sum_{[\gamma] \in \Gamma_1(N) / \Gamma_p(\alpha)} \int_{\gamma \cdot \mathcal{F}_p^\Gamma} h(\gamma^{-1} \tau) \, \mathrm{d}\mu_{\mathrm{hyp}},$$
> *where $\mathcal{F}_p^\Gamma$ is a fundamental domain for $\Gamma_1(N)$ on $\mathfrak{H}$.*

**Status: DONE.** The Lean declaration is `Gamma_p_α_PSL_R_FD_finite_index_decomp_auto` in `AdjointTheory.lean` near line 1596. Its axiom imprint is the standard `[propext, Classical.choice, Quot.sound]`. The proof uses:
- The general "fundamental-domain transport along subgroup_iUnion_out_smul" machinery in mathlib.
- The fact that $\Gamma_p(\alpha) \leq \Gamma_1(N)$ has finite index for $\alpha \in \Delta_0(N)$ with $p \nmid N$ — proved separately as `Gamma_p_α_finite_index`.
- Möbius-action-invariance of the hyperbolic measure $\mathrm{d}\mu_{\mathrm{hyp}}$ on $\mathfrak{H}$.

This is the level-$N$ generalisation of the standard FD-transport, and **the cornerstone the rest builds on**.

### 4.2 Step 2 — Hecke-correspondence adjoint at level $\Gamma_1(N)$

> **Target Theorem 4.3 (Step 2, "Hecke-correspondence adjoint").** *Let $N \geq 1$, $k \geq 2$, $\chi$ a Dirichlet character mod $N$, and $\alpha \in \Delta_0(N)$ with $\det\alpha$ coprime to $N$. Then for all $f, g \in S_k(\Gamma_1(N), \chi)$,*
> $$\langle T_\alpha f, g \rangle_N = (\det \alpha)^{k-1} \cdot \chi(\alpha)^{-1} \cdot \langle f, T_{\alpha^*} g \rangle_N,$$
> *where $T_\alpha$ is the Hecke operator associated to the double coset $\Gamma_1(N)\,\alpha\,\Gamma_1(N)$ and $\alpha^*$ is the adjugate $(\det\alpha)\alpha^{-1}$.*

**Status: OPEN.** This is the live blocker. We have the **scaffold** in place — the function `peterssonInner_slash_adjoint_coset` at line 3730 in `AdjointTheory.lean` is the per-coset, per-$\alpha$ transfer between the LHS and RHS integrals. It is parametric in $\alpha$. What we are missing is the **integrand-level identity (DS Prop 5.5.2(b))** that powers it; see §7.

### 4.3 Step 3 — Specialise to $\alpha = \mathrm{diag}(1,p)$

> **Target Theorem 4.4 (Step 3, "DS 5.5.3 specialised").** *For $N \geq 1$, $k \geq 2$, $\chi$ mod $N$, and $p \nmid N$:*
> $$\langle T_p f, g \rangle_N = \langle p \rangle^{-1}\, \langle f, T_p g \rangle_N \qquad \text{for } f, g \in S_k(\Gamma_1(N), \chi).$$

**Status: OPEN, but mechanical given Target 4.3.** The double coset $\Gamma_1(N)\,\mathrm{diag}(1,p)\,\Gamma_1(N)$ has the standard $p+1$ representatives (Miyake 4.5.5). The adjugate of $\mathrm{diag}(1,p)$ is $\mathrm{diag}(p,1)$, whose double coset is $\Gamma_1(N) \mathrm{diag}(p,1) \Gamma_1(N) = p \cdot \Gamma_1(N)\,\mathrm{diag}(1,p)\,\Gamma_1(N)$ (modulo scaling). After tracking determinant factors $p^{k-1}$ and the character correction $\chi(p)^{-1}$, this reduces to the statement in 4.4. This step is **almost entirely bookkeeping**: it is the case that 4.4 follows from 4.3 by routine identifications, but the routine identifications themselves need formalising (matrix arithmetic, the $\sigma_p$ permutation of cosets, the $\det^{k-1}$ factor cancellation).

---

## 5. What's been done since the previous reviewer reply

A great deal — but largely "infrastructure", not closure of 4.3 or 4.4.

### 5.1 FD-tiling and finite-index FD-transport — DONE

As noted in §4.1, Step 1 of the two-step API is formalised. This includes:
- A general "subgroup-iUnion-out-smul" library: for $H \leq G$ finite-index and $\mathcal{F}_G$ a fundamental domain for $G$, the set $\bigcup_{[\gamma] \in G/H} \gamma \cdot \mathcal{F}_G$ is a fundamental domain for $H$.
- Specialisation to $\Gamma_p(\alpha) \leq \Gamma_1(N)$ with $\alpha \in \Delta_0(N)$, $p \nmid N$.
- $\mathrm{PSL}_2(\mathbb{R})$-action-invariance of the hyperbolic measure, propagated to the level of $\Gamma_p(\alpha)$-FDs.

This gives us the *equality-of-integrals* identity that any change-of-variables proof must end at. It is the formalisation of "we can move from $\Gamma$-FD to $\alpha^{-1} \Gamma \alpha$-FD by tiling".

### 5.2 The spectral theorem for commuting Hecke operators — DONE

The previous brief flagged the spectral theorem T207 as the structural payoff. It has been fully closed (sorry-free, axiom-clean) via:
- `DirectSum.IsInternal` + `stdOrthonormalBasis` to decompose the cusp form space.
- The character spaces `cuspFormCharSpace k χ` are jointly stable under all Hecke operators $T_n$ for $\gcd(n,N) = 1$ (the **Hecke action well-definedness** at level $N$).
- The maximal generalised eigenspace decomposition for the commuting family $\{T_n\}_{(n,N)=1}$ gives the spectral basis on each character space.
- The χ-Hecke adjoint condition $T_n^* = \chi(n)^{-1} T_n$ is **the input** to spectrality on each $S_k(\Gamma_1(N), \chi)$ — this is exactly what T205-d (= Target 4.4) provides.

So **T205-d is the bottleneck that produces simultaneous-eigenform existence**, which in turn is the bottleneck for Atkin–Lehner–Li (T209), the newform decomposition (T210), and Strong Multiplicity One.

### 5.3 Conditional SMO landed

`strongMultiplicityOne_of_newSubspaceZeroCriterion` in `Newforms.lean` reduces SMO to two abstract hypotheses:
1. Every newform of $\Gamma_1(N)$ with all $a_p = 0$ for $p \nmid N$ is zero (the "Newform zero criterion").
2. The Miyake Main Lemma (DS Theorem 5.8.2 / Miyake 4.6.8): a cusp form whose Fourier coefficients vanish on a set with positive lower density is zero.

Both hypotheses are part of the post-SMO ticket queue (POST-6, POST-7); they don't block the *abstract* statement of SMO, only its dischargeability.

### 5.4 Hecke-correspondence adjoint scaffold landed

The per-coset transfer
$$\langle f \mid_k \beta_j, g \rangle_N \stackrel{?}{=} (\text{det factor}) \cdot \langle f, g \mid_k \beta_j^* \rangle_N$$
for $\beta_j$ a coset representative of $\Gamma_1(N)\,\alpha\,\Gamma_1(N)$ is **the** statement; we have it as `peterssonInner_slash_adjoint_coset`. The proof of this single equality reduces to DS Prop 5.5.2(b). See §7.

### 5.5 The "8-layer chain" — see §6 for what we tried and what survived

---

## 6. The legacy 8-layer reduction chain

Before adopting the reviewer's two-step API, we attempted a different reduction. We document it here for the reviewer's sense of where time has gone and what is recoverable.

The original idea was to massage T205-d directly, using the triple-product identity $\widetilde{T}_p^{\mathrm{lower}} = \gamma_1^{-1} \cdot \widetilde{T}_p^{\mathrm{upper}}(0) \cdot \gamma_0$ to express $T_p$ as a sum of *upper-triangular* slash actions, then transfer the inner product term by term.

We layered 8 reductions:

> **Layer 0.** $\langle T_p f, g \rangle_N = \langle p \rangle^{-1} \langle f, T_p g \rangle_N$ — the target.
>
> **Layer 1 (Standard form).** Replace LHS and RHS by their per-$q$-coset expansions using the level-$N$ Petersson product.
>
> **Layer 2 (Triple-product unfold).** Use Miyake 4.5.5 to write $T_p f = \widetilde{T}_p^{\mathrm{upper}}(0) f + \langle p \rangle \widetilde{T}_p^{\mathrm{lower}} f$ and apply $\widetilde{T}_p^{\mathrm{lower}} = \gamma_1^{-1} \widetilde{T}_p^{\mathrm{upper}}(0) \gamma_0$.
>
> **Layer 3 (Σ-permutation).** The lower-triangular slash $\widetilde{T}_p^{\mathrm{lower}}$ permutes the $q$-cosets (i.e. there is a bijection $\sigma_p : Q \to Q$ between the $\Gamma_0(N)/\Gamma_1(N)$ coset space and itself induced by right-multiplication by $\mathrm{diag}(1,p)$ adjusted by $\gamma_0, \gamma_1$). Reindex.
>
> **Layer 4 (Double-adjoint swap).** Apply the level-1 Petersson adjoint identity $\langle f \mid_k g, h \rangle = \langle f, h \mid_k g^* \rangle$ (Diamond–Shurman 5.5.2(a)) on each tile.
>
> **Layer 5 (M_∞ stockpile).** Collect the $p+1$ slash-action terms into a single endomorphism $M_\infty$ acting on the source side.
>
> **Layer 6 (iUnion balance).** Identify the union of $\sigma_p$-translated tiles with the union of original tiles, modulo a $\Gamma_p$-translation.
>
> **Layer 7 (Branches).** Decompose the equality of unions into branch-wise equalities, indexed by the $\Gamma_p$-translations of original tiles.
>
> **Layer 8 (Branch closure).** Each branch reduces to the integrand-level $\alpha^{-1}$-slash identity — *which is just DS Prop 5.5.2(b)*.

In other words, **we built an 8-layer formal reduction whose terminal residue is exactly the input the two-step API expected from the start**.

What survives (and is worth keeping) from the 8-layer chain:
- The triple-product identity formalisation (Layer 2). This is a piece of algebra that the two-step API also needs.
- The $\sigma_p$ Q-permutation (Layer 3). This is needed for Step 3 (specialisation).
- `peterssonInner_slash_adjoint_coset` (Layer 4, level-1 case). This is the input to Step 2.
- The iUnion-form bookkeeping (Layers 6–7). This is the LHS-side of the Step 1 FD-transport.

What does **not** survive:
- The "M_∞ stockpile" framing (Layer 5) — it is an organisational principle for a proof that no longer goes through it.
- The "branch closure" decomposition (Layer 8) — it pushes the integrand identity to a slightly different shape than what DS Prop 5.5.2(b) produces directly, with an unnecessary $\Gamma_p$-tiling factor.

We are willing to **delete** Layers 5–8 wholesale if the reviewer agrees this is the right call. The decision blocks ~500 LOC of Lean infrastructure and several stockpiled `iUnion`-form lemmas; we'd rather not delete it preemptively if there is a chance it can re-enter the proof.

---

## 7. Where work breaks down

The single remaining analytic fact is DS Prop 5.5.2(b):

> **DS Prop 5.5.2(b) (the change-of-variables identity).** *Let $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$, $\Gamma$ a congruence subgroup. For $f \in S_k(\Gamma)$ and $g \in S_k(\alpha^{-1}\Gamma\alpha)$,*
> $$\int_{\Gamma \backslash \mathfrak{H}} f(\tau)\, \overline{(g \mid_k \alpha^{-1})(\tau)} \, y^k \, \mathrm{d}\mu_{\mathrm{hyp}} = (\det\alpha)^{k-1} \int_{\alpha^{-1}\Gamma\alpha \backslash \mathfrak{H}} (f \mid_k \alpha)(\tau)\, \overline{g(\tau)} \, y^k\, \mathrm{d}\mu_{\mathrm{hyp}}.$$

Diamond and Shurman prove this via the following sequence (DS pp. 184–185):
1. Substitute $\tau = \alpha \tau'$ on the LHS. The hyperbolic measure $y^{-2}\,\mathrm{d} x\,\mathrm{d} y$ is $\mathrm{GL}_2^+(\mathbb{R})$-invariant.
2. The factor $y^k$ transforms as $y^k = |\det\alpha|^k\, |c\tau' + d|^{-2k}\, (y')^k$ where $y' = \mathrm{Im}\,\tau'$.
3. The integrand $f(\tau) \overline{(g \mid_k \alpha^{-1})(\tau)}$ transforms as $(f \mid_k \alpha)(\tau') \cdot \overline{g(\tau')} \cdot (c\tau'+d)^k \cdot (\det\alpha)^{1-k} \cdot |c\tau'+d|^{2k} \cdot (\det\alpha)^{2(k-1)}$ after careful bookkeeping (the conjugate of $(g \mid_k \alpha^{-1})$ is the most delicate piece).
4. The domain transforms as $\Gamma \backslash \mathfrak{H} \to \alpha^{-1} \Gamma \alpha \backslash \mathfrak{H}$.

The fact that this is a 4-step argument hides the fact that **the integrand bookkeeping (step 3) is the analytic heart of the proof**. The $(c\tau'+d)^k$ in the slash factor and the $|c\tau'+d|^{-2k}$ in $y^k$'s transformation conspire to cancel almost everything, leaving a factor of $(\det\alpha)^{k-1}$. But "almost everything cancels" is one of the hardest things to encode in Lean: it is *exactly* the case where we run into normalisation issues, complex-conjugate-vs-real-absolute-value issues, $(\det\alpha)^k$ vs $|\det\alpha|^k$ issues, and the half-dozen Möbius-derivative formulas we need.

Our current formalisation route through DS Prop 5.5.2(b) takes the form:

> **Lemma 7.1 (integrand identity, draft).** *For $\alpha \in \mathrm{GL}_2^+(\mathbb{R})$ with $\det\alpha > 0$ and $\tau \in \mathfrak{H}$,*
> $$f(\alpha\tau) \cdot \overline{(g \mid_k \alpha^{-1})(\alpha\tau)} \cdot (\mathrm{Im}\,\alpha\tau)^k = (\det\alpha)^{k-1} \cdot (f \mid_k \alpha)(\tau) \cdot \overline{g(\tau)} \cdot (\mathrm{Im}\,\tau)^k.$$

This is the **pointwise** version of DS Prop 5.5.2(b) (no integral signs). It is what we'd like to compile, because everything else (change-of-variables, hyperbolic-measure-invariance, FD-transport) is then standard mathlib machinery.

We have not been able to compile Lemma 7.1 yet. The obstacles are:

**Obstacle 1.** The slash factor for $\alpha^{-1}$ on $\alpha\tau$ is $(\det\alpha^{-1})^{k-1} \cdot (c'(\alpha\tau) + d')^{-k}$ where $\alpha^{-1} = \left(\begin{smallmatrix}a'&b'\\c'&d'\end{smallmatrix}\right)$. Translating between this and $(c\tau+d)^k$ (the inverse Möbius derivative) requires the cocycle identity $(c\tau+d)(c'(\alpha\tau)+d') = \det\alpha$, which is well-known but its formalisation is currently scattered across several lemmas in different conventions.

**Obstacle 2.** $\mathrm{Im}\,\alpha\tau = \mathrm{Im}\,\tau \cdot \det\alpha \cdot |c\tau+d|^{-2}$. This is the Möbius-derivative identity. Combining with the slash factor cancels almost everything but leaves a remainder that should be exactly $(\det\alpha)^{k-1}$. Our calculation produces $(\det\alpha)^{k-1} \cdot |c\tau+d|^{-2k} \cdot (c\tau+d)^k \cdot \overline{(c\tau+d)^k} \cdot ?$ — and the question mark is the bit we can't simplify because $|c\tau+d|^{-2k}$ doesn't directly cancel the *holomorphic* $(c\tau+d)^k$ on the slash side.

**Obstacle 3.** The Hecke representatives don't normalise $\Gamma_1(N)$. (The 2026-05-11 reviewer flagged this in their reply.) For $\alpha = \mathrm{diag}(1,p)$, the conjugate group $\alpha^{-1} \Gamma_1(N) \alpha$ is *not* $\Gamma_1(N)$ itself but a different congruence subgroup containing $\Gamma_p(\alpha)$. So Lemma 7.1, applied to $f \in S_k(\Gamma_1(N))$, gives an integral over $\alpha^{-1}\Gamma_1(N)\alpha \backslash \mathfrak{H}$, not over $\Gamma_1(N) \backslash \mathfrak{H}$. We need a second step ("FD-reconstruction") to bring the integral back to $\Gamma_1(N) \backslash \mathfrak{H}$ — this is what Step 1 (the FD-transport) accomplishes, but only **modulo** Lemma 7.1 being available in the first place.

In short: we have the FD-transport (Step 1), we have the per-coset scaffold (Step 2 framework), we have the algebraic reductions (Layers 2–4 of the 8-chain). What we don't have is the **pointwise integrand identity** that all of these reduce to. The remaining work is concentrated on this single identity.

---

## 8. Status of ticket board

The current state of our work tracker:

| Ticket | Mathematical statement | Status | Notes |
|---|---|---|---|
| `T205-d-API-1` | Step 1 of two-step API: FD-transport $\mathrm{PSL}_2(\mathbb{R}) \to \Gamma_1(N) \backslash \mathfrak{H}$ along $\Gamma_p(\alpha)$ | **DONE** | sorry-free, axiom-clean |
| `T205-d-API-2` | Step 2: Hecke-correspondence adjoint identity at $\Gamma_1(N)$, parametric in $\alpha$ | **OPEN** | needs Lemma 7.1 |
| `T205-d` | Step 3 (DS 5.5.3 specialised): $T_p^* = \langle p \rangle^{-1} T_p$ on $S_k(\Gamma_1(N))$ | **OPEN** | mechanical after `T205-d-API-2` |
| `T207` | Spectral theorem for commuting $T_n$ on $S_k(\Gamma_1(N), \chi)$ | **DONE** | depends on `T205-d` (used as input to spectrality) |
| `T209` | Atkin–Lehner–Li orthogonality of oldforms and newforms | **OPEN** | follows from `T205-d` + spectral theorem |
| `T210` | Newform decomposition: $S_k(\Gamma_1(N)) = \bigoplus_{M | N} \bigoplus_{d | N/M} \alpha_d \cdot S_k^{\mathrm{new}}(\Gamma_1(M))$ | **OPEN** | depends on `T209` |
| `POST-6` | Miyake Main Lemma 4.6.8: sparse Fourier supports | **OPEN** | needed for full SMO |
| `POST-7` | Strong Multiplicity One (Miyake 4.6.12) | **OPEN, conditional version landed** | conditional on POST-6 and `T210` |

We declared T205-d itself **B3 OFF-TRACK** in beastmode last week because direct closure is published-paper-scale; we judged this brief is a more efficient use of time than continuing on it solo.

---

## 9. Where to focus the reviewer's attention

We see four broad lines of work that the reviewer could comment on.

### 9.1 The general adjoint

Confirm or refute: is the right pivot to formalise **Lemma 7.1 directly** (the pointwise integrand identity for the general Hecke correspondence at level $\Gamma_1(N)$)? If so, what is the most natural Lean-friendly statement?

We have considered three statements:
- (a) **Symmetric form**: $f(\alpha\tau) \overline{(g \mid_k \alpha^{-1})(\alpha\tau)} (\mathrm{Im}\,\alpha\tau)^k = (\det\alpha)^{k-1} (f \mid_k \alpha)(\tau) \overline{g(\tau)} (\mathrm{Im}\,\tau)^k$ (per §7).
- (b) **Asymmetric form**: $f(\alpha\tau) \overline{g(\tau)} (\mathrm{Im}\,\alpha\tau)^k = (f \mid_k \alpha)(\tau) \overline{g(\tau)} (\mathrm{Im}\,\tau)^k (\det\alpha)^{k-1} (c\tau+d)^k / |c\tau+d|^{2k} \cdot \cdots$ — the calculation that doesn't quite cancel.
- (c) **Reformulated via $M^*$**: replace the conjugation $\alpha^{-1}$ on the right with $M^* = (\det\alpha) \alpha^{-1}$, so the determinant factors come out cleanly.

The reviewer's previous reply suggested route (c). We agree but have not yet executed it — partly because we are unsure whether to formulate this as "$T_\alpha^* = $ a specific Hecke operator on $S_k(\Gamma_1(N), \chi)$" (an operator-level identity, requires the Hecke ring to be defined first) or as "the inner product of two slash actions equals a different inner product" (a pointwise identity, requires only the slash action). Strongly prefer the former for downstream usage but it requires more infrastructure.

### 9.2 The 8-layer chain salvage

Is the 8-layer chain (§6) recoverable, partially, or should we delete Layers 5–8 wholesale and proceed only via the two-step API? Specifically:
- Is there a single mathematical fact that, if proved, brings the 8-layer chain back from the brink (e.g., a different organisation of Layers 5–7 that doesn't introduce the unnecessary $\Gamma_p$-tiling factor)?
- Or is the right call to scrap Layers 5–8 and concentrate entirely on the two-step API?

We lean towards scrapping but want a second opinion.

### 9.3 The $\sigma_p$ Q-permutation

This is the bookkeeping that takes us from Target 4.3 to Target 4.4 (Step 3 in §4.3). The 2026-05-11 reviewer flagged the "scalar normalisation" issue: $\alpha = \mathrm{diag}(1,p)$ has $\alpha^* = \mathrm{diag}(p,1)$, and the double coset $\Gamma_1(N)\,\mathrm{diag}(p,1)\,\Gamma_1(N)$ is **not** the same as $\Gamma_1(N)\,\mathrm{diag}(1,p)\,\Gamma_1(N)$ — but it is $p \cdot$ that double coset modulo the centre. Tracking the $p^{k-1}$ scalar factor that comes from this and matching it with the $(\det \alpha)^{k-1}$ from Lemma 7.1 needs care. Could the reviewer comment on the **cleanest** organisation of this bookkeeping?

In particular: the standard route is via $\sigma_p : \Gamma_0(N)/\Gamma_1(N) \to \Gamma_0(N)/\Gamma_1(N)$, the multiplication-by-$\bar p$ map (where $\bar p$ is the residue of $p$ in $(\mathbb{Z}/N)^\times$). Is this the *cleanest* way to handle Step 3, or is there a less indexing-heavy approach?

### 9.4 Alternative routes that bypass DS Prop 5.5.2(b)

There are at least two routes in the literature that *avoid* the pointwise integrand identity:

**Route A (Atkin–Lehner–Li direct orthogonality).** Li's 1975 paper proves the orthogonality of $S_k^{\mathrm{old}}(\Gamma_1(N))$ and $S_k^{\mathrm{new}}(\Gamma_1(N))$ under $\langle\cdot,\cdot\rangle_N$ directly, by exhibiting an explicit basis for $S_k^{\mathrm{old}}$ from $S_k^{\mathrm{new}}(\Gamma_1(M))$ for $M | N$, $M < N$, and computing $\langle f, g \rangle_N$ termwise. The Hecke adjoint $T_p^* = \langle p \rangle^{-1} T_p$ then drops out as a corollary of the orthogonal joint-eigenform decomposition.

**Route B ($U_p$ eigenspace decomposition).** For $p | N$, the operator $U_p$ (not $T_p$) has a known explicit eigenspace structure (eigenvalues $\pm p^{(k-1)/2}$ on newforms, etc.). One can sometimes piece together the Hecke adjoint identity from a finite collection of such per-prime decompositions.

Does the reviewer believe one of these alternative routes is **easier to formalise** than the direct DS-Prop-5.5.2(b) approach? Specifically: if we prove Atkin–Lehner–Li orthogonality directly (Route A), does it give us T205-d "for free" — or is there a circularity (in Li's paper, T205-d is used to prove orthogonality)?

We believe Li's argument is *circular* with respect to T205-d, but we'd appreciate the reviewer's read.

---

## 10. Questions for the reviewer

We ask seven concrete questions. The reviewer should answer in whatever order they prefer; some may be combinable.

**Q1.** *(Integrand identity formulation.)* What is the cleanest formulation of Lemma 7.1 for a Lean formalisation? Specifically, comparing the three candidates (a), (b), (c) in §9.1, which would the reviewer recommend? Are there other natural framings we are not seeing? For instance, would framing the identity in terms of the **operator-valued** map $\alpha \mapsto T_\alpha^*$ (as opposed to a per-$(\alpha,f,g)$ pointwise identity) be cleaner — or is the pointwise version preferred?

**Q2.** *(Obstacle 2.)* The calculation in Obstacle 2 of §7 produces a term $|c\tau+d|^{-2k} \cdot (c\tau+d)^k \cdot \overline{(c\tau+d)^k}$ that should simplify to $1$ (since $|c\tau+d|^{2k} = (c\tau+d)^k \overline{(c\tau+d)^k}$). In a hand-written proof, this is a one-line cancellation, but in Lean it requires several rewrites to bring the holomorphic and conjugate-holomorphic factors into juxtaposition. Is there a standard organisational principle for this style of calculation in formalisation projects (e.g., as a single lemma "the conjugate-slash factor times the $y^k$ transform factor equals $(\det\alpha)^{k-1}$")?

**Q3.** *(8-layer chain salvage.)* Should we scrap Layers 5–8 of the 8-layer chain (§6) and proceed entirely via the two-step API, or is there a salvage path that preserves the chain's bookkeeping? Are the iUnion-form residuals (Layer 6) worth keeping for downstream use (e.g., for Atkin–Lehner–Li orthogonality T209), or are they specific to this proof attempt and should be deleted?

**Q4.** *(Tickets.)* What sub-tickets should we plan for Target 4.3 (Hecke-correspondence adjoint identity)? We currently see two:
- (i) "Pointwise integrand identity" (Lemma 7.1, as drafted).
- (ii) "FD-reconstruction from $\alpha^{-1}\Gamma\alpha \backslash \mathfrak{H}$ back to $\Gamma \backslash \mathfrak{H}$ for $\Gamma = \Gamma_1(N)$, $\alpha \in \Delta_0(N)$."

Are there others the reviewer would recommend factoring out? In particular, do we need a separate ticket for **the cocycle identity** $(c\tau+d)(c'(\alpha\tau)+d') = \det\alpha$ at the matrix-arithmetic level (Obstacle 1 in §7), or can it ride along as a step inside the integrand identity?

**Q5.** *(Specialisation Step 3.)* In §4.3 we said "specialisation to $\alpha = \mathrm{diag}(1,p)$ is mechanical given Target 4.3". Is this *truly* mechanical, or does the $\sigma_p$ Q-permutation (§9.3) bring its own non-trivial bookkeeping? Concretely, what's the cleanest way to handle the fact that $\mathrm{diag}(p,1)$'s double coset is not the same as $\mathrm{diag}(1,p)$'s double coset, but it equals it after multiplication by $\bar p^{-1} \in (\mathbb{Z}/N)^\times$?

**Q6.** *(Alternative routes.)* In §9.4 we sketched two alternative routes. Does the reviewer believe Route A (direct Atkin–Lehner–Li orthogonality) gives T205-d for free, or is the route circular as we suspect? Is Route B (per-prime $U_p$ decomposition) viable as a *partial* substitute (proving T205-d for $p | N$ separately from the $p \nmid N$ case)? Are there other routes the reviewer would point us at?

**Q7.** *(Sanity check on scale.)* We estimate that formalising Lemma 7.1 (the pointwise integrand identity) at the level of generality required for Target 4.3 will take ≈500–1000 LOC of careful Lean, even with all the Möbius-derivative and complex-conjugate plumbing in mathlib. Does this estimate seem right to the reviewer? If we underestimate, what is the actual scale, and what's the most painful sub-step? If we overestimate, what tools in mathlib would short-circuit the calculation?

---

## 11. Metadata

- **Prepared:** 2026-05-11 (second brief of the day, following T205-d "B3 OFF-TRACK" declaration in beastmode).
- **Reviewer audience:** Same as 2026-05-11 brief — frontier LLM acting as a senior mathematical advisor for the modular forms formalisation project.
- **Notation conventions:** Diamond–Shurman.
- **Length budget:** Long; the reviewer asked for full detail.
- **Brief location:** `REVIEW_BRIEF.md` (project root, this file). Internal copy and state snapshot saved to `.mathlib-quality/expert-review/2026-05-11-T205d/`.
- **Project context:** This brief is a focused **follow-up** to the 2026-05-11 brief. The previous reviewer reply has been integrated into the current ticket board (see `.mathlib-quality/expert-review/2026-05-11/integration.md`).

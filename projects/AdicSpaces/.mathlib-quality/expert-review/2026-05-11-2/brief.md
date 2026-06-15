# Review brief — Mathlib infrastructure for adic-completion / localization commutation

*Prepared 2026-05-11 for ChatGPT Pro (senior generalist mathematician). Self-contained:
no repo access required.*

*This brief asks for guidance on which Mathlib-level theorem to develop in order to
unblock the formalization of Wedhorn Theorem 8.28(b) (Tate acyclicity). It is a
follow-up to a previous brief on the project's overall strategy (which is settled);
the present brief is focused on a specific infrastructure decision.*

---

## 1. Goal

The project is a Lean 4 + Mathlib formalization of **Tate acyclicity** for strongly
noetherian Tate rings — Wedhorn *Adic Spaces*, Theorem 8.28(b). Concretely: for a
finite rational covering $\mathcal C = \{R(T_i/s_i)\}_i$ of the rational subset
$R(T_0/s_0) \subseteq \operatorname{Spa}(A, A^+)$, the augmented Čech complex of the
structure presheaf is exact.

After a substantial multi-session formalization push, **one structural blocker
remains**: the proof requires the natural ring map between presheaf values to be a
**localization** in the sense of `IsLocalization.Away`. The corresponding theorem is
Wedhorn Proposition 8.15. The mathematical content is settled in the literature
(several proofs exist); the question is which version is the cleanest **Mathlib**
target, both as a closure of this sorry and as a useful piece of upstream
infrastructure.

This brief explains the precise content of the blocker, the four candidate
Mathlib-level routes, and asks for guidance on the canonical reference and target
formulation.

---

## 2. Background and references

### 2.1. Setting and notation

We use **mixed Wedhorn / Stacks conventions** — Wedhorn (Huber) for the adic-space
side, Stacks for the algebraic-completion side.

**Adic-space side (Wedhorn):**
- $A$ is a **Tate ring**: a Huber ring containing a *topologically nilpotent unit* $\pi \in A^\times$ (i.e., $\pi^n \to 0$).
- $A^+ \subseteq A$ is a *ring of integral elements* (open, integrally closed, contained in the power-bounded subring $A^\circ$).
- $A_0 \subseteq A$ is a *ring of definition*: open subring with an *ideal of definition* $I = \pi A_0$ such that the $I$-adic topology induces the topology of $A$.
- $\operatorname{Spa}(A, A^+)$ is the adic spectrum.
- For $T \subseteq A$ finite, $s \in A$ with $T \cdot A = A$, the **rational subset** is $R(T/s) = \{v \in \operatorname{Spa}(A, A^+) : v(t) \leq v(s) \neq 0, \,\forall t \in T\}$.
- $A\langle X_1, \dots, X_n\rangle$ is the Tate algebra (restricted power series with coefficients tending to zero).
- The **structure presheaf value** $\mathcal O_X(R(T/s))$ is the topological completion of $A[1/s]$ in the **localization topology**: the coarsest ring topology making $s$ invertible and each $t/s$ power-bounded.

In Lean we denote this $\mathrm{presheafValue}\, D$, where $D = (P, T, s)$ packages a pair of definition $P = (A_0, I)$, the numerators $T$, and the denominator $s$.

**Algebraic-completion side (Stacks/Mathlib):**
- $R$ a commutative ring.
- $\mathfrak a \subseteq R$ an ideal.
- $\widehat R_\mathfrak a = \varprojlim_n R / \mathfrak a^n$ the $\mathfrak a$-adic completion.
- $R[1/x]$ the algebraic localization (Mathlib: `Localization.Away x`).
- $\mathrm{IsLocalization.Away}\, x\, S$: predicate that $S$ realises $R[1/x]$ universally, i.e., every $s \in S$ has the form $r / x^n$ for some $r \in R$, $n \in \mathbb N$.

### 2.2. References

**Adic spaces / non-archimedean geometry:**

- **[Wedhorn 2019]** T. Wedhorn. *Adic Spaces*. Lecture notes, arXiv:1910.05934. Primary reference; we follow §6–§8. The result we need is **Proposition 8.15** (sometimes split across §8.1).

- **[Huber 1996]** R. Huber. *Étale cohomology of rigid analytic varieties and adic spaces*. Aspects of Mathematics E30, Vieweg, 1996. Sections §1.1–§1.5. The adic-space framework's original treatment; Wedhorn cites Huber for the localization property.

- **[BGR 1984]** S. Bosch, U. Güntzer, R. Remmert. *Non-Archimedean Analysis*. Grundlehren 261, Springer, 1984. §2.8.2, §3.7.3, §3.7.5. The **Banach Open Mapping** for k-affinoid algebras. The proof uses an explicit non-archimedean norm.

- **[Bosch 2014]** S. Bosch. *Lectures on Formal and Rigid Geometry*. Lecture Notes in Mathematics 2105, Springer, 2014. §4.1 Theorem 4 (Banach Open Mapping); §4.3 (localization in rigid geometry). Modern textbook exposition of BGR-era results.

- **[Schneider 2002]** P. Schneider. *Nonarchimedean Functional Analysis*. Springer Monographs in Mathematics, 2002. §8. Treats Banach / Fréchet spaces over non-archimedean fields.

**Topological group Open Mapping:**

- **[Pettis 1950]** B. J. Pettis. *On continuity and openness of homomorphisms in topological groups*. Annals of Mathematics 52 (1950), 293–308. Original paper; first non-locally-compact Open Mapping theorem for topological groups. Two theorems: (I) Open Mapping for Baire-on-source + second-countable target, and (II) "if $A$ has the Baire property and is non-meagre, $A \cdot A^{-1}$ contains a neighbourhood of the identity".

- **[Kechris 1995]** A. Kechris. *Classical Descriptive Set Theory*. GTM 156, Springer, 1995. Theorem 9.10 (Pettis I), Theorem 9.11 (Open Mapping for Polish topological groups). Standard modern reference.

- **[Bourbaki TG]** N. Bourbaki. *Topologie Générale*, Chapitre IX, §5.3 Théorème 1. Open mapping for complete metric topological groups.

**Adic completion / localization commutation:**

- **[Stacks Project]** *The Stacks Project*. Tags `00MA`, `00MB`, `0BNT`. Noetherian adic completion is exact + faithfully flat; commutation with localization at a fixed element (Tag `0AHQ` in the noetherian context).

- **[Bourbaki AC]** N. Bourbaki. *Algèbre Commutative*, Chapitre III, §2.13–§3.4. Adic topologies, completion, and the relation to localization (linearly topologized rings).

- **[ZS II]** O. Zariski, P. Samuel. *Commutative Algebra, Volume II*. Van Nostrand, 1960; Springer reprint 1975. Chapter VIII §4 on completion of noetherian rings.

### 2.3. State of the art

The mathematical content (Wedhorn Prop 8.15) is **completely settled** in the literature
— versions of this localization-completion identity have been used since Tate
(1962) and Huber (1996). It is a routine theorem to prove on paper for an expert in
rigid analytic geometry. The question is **not** whether the result is true, but
which **formalised version** is the right Mathlib target.

In Mathlib, the closest existing pieces are:

- $\mathrm{AdicCompletion.flat\_of\_isNoetherian}$ — flat module over $\mathfrak a$-adic completion (noetherian).
- $\mathrm{AddMonoidHom.isOpenMap\_of\_sigmaCompact}$ — Open Mapping for sigma-compact topological abelian groups (too restrictive — our spaces are not sigma-compact).
- $\mathrm{ContinuousLinearMap.isOpenMap}$ — Banach Open Mapping for normed spaces over `NontriviallyNormedField` (Archimedean only).
- $\mathrm{IsLocalization.Away}$ — the algebraic localization predicate.

**Mathlib has no:**
- Open Mapping theorem for Polish topological groups (the Pettis version).
- Non-archimedean Banach Open Mapping.
- Direct adic-completion / localization commutation lemma.

So the relevant infrastructure needs to be developed as a new Mathlib contribution.

---

## 3. Strategy

The Tate acyclicity proof factors into four mathematical milestones (the Wedhorn route, settled after a 2026-04-08 reviewer audit replacing an earlier strict-exactness route):

1. **Common base (Example 6.38 in the Tate case).** Identify $\mathcal O_X(R(T/s)) \cong A\langle X\rangle / (1 - sX)$ as topological rings. *Status: algebraic iso landed in the project; topological iso landed for principal pairs.*

2. **Lane A — Laurent overlap (Example 6.39 / Lemma 8.33).** For $f \in A$, the two-element Laurent cover at $f$ acyclicity reduces to a $3 \times 3$ diagram chase on Tate-algebra quotients. *Status: algebraic core (`row3_exact`) sorry-free; Wedhorn 2.13 overlap transport now landed sorry-free (`presheafValue_iteratedOverlap_equiv`); bivariate continuity landed sorry-free; Lane A finish theorem unconditional.*

3. **Lane B — Corollary 8.32 (faithful flatness of the product restriction).** Routes through **Wedhorn Proposition 8.15** to get componentwise flatness. *Status: Cor 8.32 abstract theorems landed; **the Prop 8.15 closure is the blocker of this brief**.*

4. **Lane C — Wedhorn Lemma 8.34 / Hübner Lemma 3.8 (geometric reduction).** Standard cover refinement + Laurent-cover induction. *Status: structural infrastructure landed; per-`E` direct assembly proved.*

The remaining sorries — `tateAcyclicity` Part 1 (separation), Part 2 (gluing), and the `IsSheafy.embedding` field — all chain through Wedhorn Prop 8.15 via **Cor 8.32**'s use of `restrictionMap_isLocalization`. Closing Prop 8.15 sorry-free is therefore the **single remaining critical-path blocker** for the whole theorem.

---

## 4. Definitions (the precise setup)

For the reviewer's reference, the exact mathematical setting of the blocker.

**Definition 4.1 (rational localization datum).** A *rational localization datum* over $A$ is a tuple $D = (P, T, s)$ where $P = (A_0, I)$ is a pair of definition, $T \subseteq A$ finite, $s \in A$, and the rational subset $R(T/s) \subseteq \operatorname{Spa}(A, A^+)$ is open with $A_0[T/s] \subseteq A[1/s]$ well-defined.

**Definition 4.2 (presheaf value).** $\mathcal O_X(D) := $ the topological completion of $A[1/s]$ in the **localization topology** $\tau_D$: the coarsest topology on $A[1/s]$ such that
- the inclusion $A \hookrightarrow A[1/s]$ is continuous,
- $s$ is a unit (with continuous inverse),
- each $t/s$ for $t \in T$ is power-bounded.

Equivalently: $\tau_D$ has a $0$-neighbourhood basis given by $\{ I^n \cdot A_0[T/s] \}_{n \geq 0}$ (the ideals $I^n$ inside $A_0$ extended to $A_0[T/s] \subseteq A[1/s]$).

**Definition 4.3 (restriction map).** Given $D_0 \subseteq D$ (i.e., $R(T/s) \subseteq R(T_0/s_0)$), there is a canonical continuous ring map
$$\sigma_D^{D_0} \;:\; \mathcal O_X(D_0) \;\longrightarrow\; \mathcal O_X(D)$$
extending the algebraic map $A[1/s_0] \to A[1/s]$ (well-defined because $T \cdot A = A$ forces $s_0$ to be invertible in $A[1/s]$ when $D \subseteq D_0$).

**Definition 4.4 (canonical map).** $\kappa_D : A \to \mathcal O_X(D)$ is the natural ring hom obtained by composing $A \hookrightarrow A[1/s]$ with the completion embedding.

The element $\kappa_D(s) \in \mathcal O_X(D)$ is a **unit** (it has a continuous inverse, being a unit at the algebraic level + completion).

---

## 5. Established results (project state)

This section lists the substantive theorems already proved sorry-free that the reviewer should be aware of.

### 5.1 Common base (Example 6.38)

**Theorem 5.1 (algebraic Example 6.38).** *The algebraic localization $A[1/s]$ fits into a ring isomorphism $A[1/s] \cong A[X]/(1 - sX)$. After completion in the appropriate topologies, this lifts to a continuous ring map $A\langle X\rangle/(1 - sX) \to \mathcal O_X(D)$ with dense image.*

*Sketch.* Standard universal property of localizations; completion functor preserves the algebraic iso on dense subrings. ∎

**Theorem 5.2 (topological Example 6.38, principal pair).** *For a principal pair of definition $P = (A_0, (\pi))$, the natural map $A\langle X\rangle/(1 - sX) \to \mathcal O_X(D)$ is a **topological** ring isomorphism.*

*Sketch.* Combine the algebraic iso with closedness of $(1 - sX)$ via Wedhorn 6.17 (closed ideals in noetherian Tate rings) and the canonical Tate-algebra topology. Banach open mapping at the principal-pair level. ∎

### 5.2 Laurent acyclicity (Lemma 8.33 algebraic core)

**Theorem 5.3 ($3 \times 3$ row exactness, `row3_exact`).** *For any commutative ring $B$ and any $g \in B$, the sequence*
$$0 \to B \xrightarrow{\varepsilon} B\langle X\rangle/(g - X) \times B\langle X\rangle/(1 - gX) \xrightarrow{\delta} B\langle X, X^{-1}\rangle/(g - X) \to 0$$
*is exact in the category of $B$-modules.*

*Sketch.* Direct diagram chase; uses Laurent polynomial decomposition and polynomial division. Purely algebraic, requires only commutative ring axioms. ∎

**Theorem 5.4 (Flatness, Wedhorn Lemma 8.31).** *For strongly noetherian Tate $A$ and any $f \in A$, the rings $A\langle X\rangle$, $A\langle X\rangle/(f - X)$, $A\langle X\rangle/(1 - fX)$ are flat over $A$.*

*Sketch.* Flatness of $A\langle X\rangle$ over $A$ via Artin-Rees for the pair-of-definition ring (Mathlib's `AdicCompletion.flat_of_isNoetherian`). Flatness of quotients uses regularity of $f - X$ and $1 - fX$ on $A\langle X\rangle$. ∎

### 5.3 Lane A — overlap bridge (newly landed)

**Theorem 5.5 (overlap transport, Wedhorn 2.13).** *For strongly noetherian Tate $A$, a rational datum $D_0$, and $f \in A$ (with appropriate Laurent normalization), there is a canonical ring isomorphism*
$$\mathcal O_X(\text{laurentOverlapDatum}(D_0, f)) \;\cong\; \mathcal O_X(\text{iteratedOverlapDatum}_B(D_0, f))$$
*where $B = \mathcal O_X(D_0)$ and the right-hand side is the overlap datum on $B$ at $\kappa_{D_0}(f)$. As a `RingEquiv`, both completions of $A[1/(s_0 f)] \cong B[1/\kappa_{D_0}(f)]$, with matching localization topologies.*

*Sketch.* Mirrors `presheafValue_iteratedMinus_equiv` (the minus-shape transport, already landed). Construction: forward/backward loc homs at the algebraic level (with extra generator handling for $T = \{1, b, b^2\}$ on the $B$-side); continuity via `locTopology_continuous_lift`; completion-level extension homs; round trips via `UniformSpace.Completion.ext'` + the uncompleted round-trip identity. Sorry-free, ~1350 lines. ∎

**Theorem 5.6 (bivariate eval continuity).** *For any strongly noetherian Tate ring $B$ with pair of definition $P_B$ and element $b \in B$, the bivariate evaluation hom $B\langle X, Y\rangle \to \mathcal O_X(\mathrm{overlapDatum}(B, P_B, b))$ is continuous from the canonical Tate topology on $B\langle X, Y\rangle$ to the presheaf-value topology. Quotient-lift gives continuity of the corresponding map factoring through $B\langle X, Y\rangle / (b - X,\, 1 - bY)$.*

*Sketch.* Bivariate analog of the univariate `tateEvalPresheafHom_continuous_canonical`. Standard argument: reduce to continuity at $0$, extract open subgroup $W$, use power-boundedness of `canonicalMap b` and `invS` to get $U$ with $U \cdot (\text{bivariate-range}) \subseteq W$; continuity of `canonicalMap` pulls back to a Tate nhd; bivariate coefficient bound + summability + closed open subgroup. ∎

**Theorem 5.7 (Lane A finish — unconditional).** *Combining Theorem 5.5 and Theorem 5.6, the Lane A bridge $\tau_{preBiv}$ — the presheaf-level bivariate iso required by the Laurent gluing assembly — is constructible unconditionally, with no parametric residual hypotheses.*

### 5.4 Closed quotients of Tate rings

**Theorem 5.8.** *Let $R$ be a noetherian Tate ring and $I \subseteq R$ an ideal (with closedness needed for $T_2$/completeness of the quotient but not the Tate-ring structure itself). Then $R/I$ with the quotient topology is a Tate ring, with ring of definition the image of $R$'s ring of definition and ideal of definition the image of the pseudo-uniformizer's principal ideal.*

*Sketch.* Image-of-pair construction; topologically nilpotent unit descends under the continuous quotient map; $T_2$ and completeness from quotienting a complete $T_2$ ring by a closed ideal. ∎

### 5.5 Cor 8.32 abstract — product faithful flatness

**Theorem 5.9 (Cor 8.32 abstract).** *Suppose $\mathcal C = (D_i)_{i \in I}$ is a finite rational cover of $D_0$, and that
(i) each individual restriction map $\sigma_i := \sigma_{D_i}^{D_0}$ exhibits $\mathcal O_X(D_i)$ as a localization $\mathrm{IsLocalization.Away}(\kappa_{D_0}(s_i))$ over $\mathcal O_X(D_0)$;
(ii) the $\operatorname{Spec}$-image of $\prod_i \mathcal O_X(D_i)$ surjects onto $\operatorname{Spec}(\mathcal O_X(D_0))$.
Then $\prod_i \mathcal O_X(D_i)$ is faithfully flat over $\mathcal O_X(D_0)$, and in particular the product restriction is injective.*

*Sketch.* Componentwise flatness from (i) + `IsLocalization.flat`. Finite product flatness assembles. Spectrum surjectivity (ii) gives faithful flatness via Mathlib's `Module.FaithfullyFlat.of_comap_surjective`. ∎

**This Theorem 5.9 is exactly where Wedhorn Prop 8.15 enters the chain**: it requires hypothesis (i), i.e., that each individual restriction map is an `IsLocalization.Away`. Without Prop 8.15, hypothesis (i) cannot be discharged.

---

## 6. The blocker — Wedhorn Proposition 8.15

The single residual sorry in the critical path is the **localization property** of the restriction maps.

### 6.1 Statement

**Theorem (Wedhorn Prop 8.15, target).** *Let $D_0, D$ be rational data over a strongly noetherian Tate ring $A$ with $R(T/s) \subseteq R(T_0/s_0)$. Set $\sigma := \sigma_D^{D_0} : \mathcal O_X(D_0) \to \mathcal O_X(D)$ (the restriction map) and $u := \sigma(\kappa_{D_0}(s)) \in \mathcal O_X(D)$ (which is a unit by Definition 4.4). Then $\sigma$ exhibits $\mathcal O_X(D)$ as a localization of $\mathcal O_X(D_0)$ at $\kappa_{D_0}(s)$, in the sense of `IsLocalization.Away`. Concretely:*

> *(i) $\sigma(\kappa_{D_0}(s))$ is a unit in $\mathcal O_X(D)$;*
>
> *(ii) (Surjectivity-up-to-powers) for every $z \in \mathcal O_X(D)$, there exist $n \in \mathbb N$ and $a \in \mathcal O_X(D_0)$ with $z \cdot u^n = \sigma(a)$;*
>
> *(iii) (Torsion kernel) for every $c \in \mathcal O_X(D_0)$ with $\sigma(c) = 0$, there exists $n \in \mathbb N$ with $\kappa_{D_0}(s)^n \cdot c = 0$ in $\mathcal O_X(D_0)$.*

Conditions (i) and (iii) are landed (Mathlib infrastructure + project work). **Condition (ii) — the surjection-up-to-powers — is the single remaining sorry.**

### 6.2 Why the obvious approaches fail

We summarise the routes that **don't work** (so the reviewer can short-circuit).

**Route A — apply Pettis Open Mapping to $\sigma$ directly.** Pettis I says: a continuous surjective homomorphism between Polish topological groups is open. But $\sigma$ is **not** surjective (that's precisely (ii), but only after multiplication by $u^n$). Circular.

**Route B — apply Pettis to the algebraic localization $\to \mathcal O_X(D)$ hom.** The map $\mathcal O_X(D_0)[1/\kappa_{D_0}(s)] \to \mathcal O_X(D)$ (induced by the universal property of `Localization.Away`) is what we want to be surjective. Pettis would conclude open if it were surjective — still circular.

**Route C — uniform inducing.** The desired conclusion would follow if $\sigma$ were a uniform-inducing map from $\mathcal O_X(D_0)$ to $\mathcal O_X(D)$: range would be complete in $\mathcal O_X(D)$, hence closed, plus density gives surjectivity. **This is FALSE in general**, by a counterexample of Conrad (project's record, 2026-04-03): take $A = \mathbb Q_p \langle X \rangle$, $D_0 = $ trivial datum, $D = R(\{p, X\}/p)$. Then $X^m$ is small in $\mathcal O_X(D)$ but bounded away from zero in $A = \mathcal O_X(D_0)$, so $\sigma$ is not uniform-inducing.

**Route D — Pettis II (subgroup form).** Pettis's second theorem: a non-meagre subgroup of a topological group with the Baire property contains a neighbourhood of the identity. Apply to $S := \bigcup_n u^{-n} \cdot \mathrm{range}(\sigma)$ — an additive subgroup, dense in $\mathcal O_X(D)$ (this is established in the project). For Pettis II to apply, $S$ would need to be non-meagre. Density + Fσ in a Baire space does **not** imply non-meagre (e.g., $\mathbb Q \subset \mathbb R$). So we need additional structure beyond density.

### 6.3 What does work — the literature routes

Three approaches in the literature **do** close Wedhorn 8.15:

**Approach (i) — BGR/Bosch norm-based Banach Open Mapping.** In the strict $k$-affinoid setting, $\mathcal O_X(D)$ carries a Banach $k$-algebra norm (the Gauss / spectral semi-norm). The natural map $\mathcal O_X(D_0)[1/s]^{\mathrm{norm.\,completion}} \to \mathcal O_X(D)$ is a continuous surjection between Banach $k$-algebras; by BGR §2.8.2 Theorem 4 (Banach Open Mapping for $k$-Banach algebras, proved via Baire on the norm balls), it's a topological isomorphism. Hence every element of $\mathcal O_X(D)$ has the form $\sigma(a)/u^n$ for some bounded $a, n$.

**Approach (ii) — Huber's universal-property argument (no norm needed).** In the adic-space framework of Huber 1996 §1.5, $\mathcal O_X(D)$ is **defined** as the universal complete topological $A$-algebra making $s$ a unit and $t/s$ power-bounded for $t \in T$. By the universal property, the natural map $\mathcal O_X(D_0)[1/s] \to \mathcal O_X(D)$ (algebraic) factors uniquely through the appropriate complete topological ring, and Huber's framework verifies that this factorization is an isomorphism by checking the universal property on both sides.

**Approach (iii) — Stacks-style completion-localization commutation.** For a noetherian ring $R$, an ideal $\mathfrak a \subseteq R$, and an element $x \in R$, there's a continuous ring iso
$$\bigl(R[1/x]\bigr)^{\widehat{\;}}_{\!\mathfrak a R[1/x]} \;\cong\; \widehat R_\mathfrak a [1/x]$$
(under mild noetherian hypotheses; sees, e.g., Stacks tag `0AHQ` for the noetherian flat case). Applied to $R = $ ring of definition of $\mathcal O_X(D_0)$, $\mathfrak a = $ ideal of definition, $x = s$, this directly gives Wedhorn 8.15 because:
- $\mathcal O_X(D_0)$ is (up to the Tate-ring structure) the $\mathfrak a$-adic completion of a localization of $A$.
- $\mathcal O_X(D)$ similarly, with $s$ inverted.
- The completion-localization commutation exactly bridges the two.

---

## 7. The four candidate Mathlib routes

Given the above, there are **four** candidate Mathlib infrastructure targets, each of which would close the blocker:

### 7.1 Candidate **P** — Pettis-style Open Mapping for Polish topological groups

```
Theorem (Pettis, Kechris 9.11). Let f : G → H be a continuous surjective
homomorphism of Polish topological groups. Then f is open.
```

**Mathlib-suitable form:**

> **Theorem.** Let $G, H$ be topological abelian groups with $G$ Baire, $H$ second-countable and $T_2$. Then any continuous surjective homomorphism $G \to H$ is open.

**Pros:** very general; useful for many things beyond adic spaces. Single theorem.

**Cons:** **does NOT directly close our sorry** because $\sigma$ is not surjective. Would require an additional bootstrap argument (e.g., the project's `S := \bigcup_n u^{-n} \cdot \mathrm{range}\,\sigma$ argument) that itself needs non-meagre Sub-Pettis (Pettis II), which has the same gap.

**Implementation: 300-500 lines** (Kechris 9.10/9.11 proofs are textbook-standard).

### 7.2 Candidate **B** — Non-archimedean Banach Open Mapping for k-affinoid algebras

```
Theorem (BGR 2.8.2.4 / Bosch §4.1 Theorem 4). Let A, B be strict
k-affinoid algebras with k a non-archimedean valued field, f : A → B
a continuous surjective k-algebra homomorphism. Then f is open.
```

**Mathlib-suitable form:**

> **Theorem.** Let $k$ be a non-archimedean valued field, $A, B$ strict $k$-affinoid algebras (in some Mathlib formulation of "Tate algebra over $k$"). Any continuous $k$-algebra surjection $A \to B$ is open.

**Pros:** the closest analogue of the classical BGR theorem; uses the norm structure explicitly. Well-documented proof via Baire on norm balls.

**Cons:** requires putting a **norm structure** on `presheafValue D`, which is non-trivial. The adic-space approach in Wedhorn/Huber **deliberately avoids** norms (since adic spaces work over arbitrary Huber rings, not just $k$-affinoid algebras over a non-arch field). Adopting BGR norms would tie us to the $k$-affinoid setting, restricting downstream applicability.

**Implementation: 500-800 lines** (norm setup + Baire argument + the localization application).

### 7.3 Candidate **H** — Huber-style universal-property characterisation

```
Theorem (Huber 1996, §1.5). For a Huber pair (A, A⁺) and rational
subsets V ⊆ U ⊆ Spa(A, A⁺), O_X(V) is the universal complete topological
A-algebra in which s_V is invertible and each t/s_V is power-bounded.
Hence the natural map O_X(U)[1/s_V] → O_X(V) is the localization at s_V.
```

**Mathlib-suitable form:** prove the universal property directly, working at the level of complete topological rings rather than going through Open Mapping.

**Pros:** the most "adic-space-native" formulation. Directly matches Huber's framework.

**Cons:** requires substantial Lean infrastructure for "universal complete topological ring with property X" — Mathlib does have `UniformSpace.Completion` but the universal-property approach with extra constraints (power-boundedness conditions) needs careful packaging. Could be a substantial Mathlib contribution (universal completions with side conditions are not in Mathlib).

**Implementation: 600-1000 lines** (mostly infrastructure-design work).

### 7.4 Candidate **S** — Stacks-style completion-localization commutation

```
Theorem (Stacks tag 0AHQ-style). For a noetherian ring R, an ideal
𝔞 ⊆ R, and an element x ∈ R, the natural ring map
  (R[1/x])^∧_{𝔞·R[1/x]}  →  (R̂_𝔞)[1/x]
is a continuous ring iso.
```

**Mathlib-suitable form:**

> **Theorem.** Let $R$ be a noetherian ring, $\mathfrak a \subseteq R$ an ideal, $x \in R$. Equip the localizations with the $\mathfrak a$-adic-induced topologies. Then the natural map from the $\mathfrak a$-adic completion of $R[1/x]$ to the $x$-localization of the $\mathfrak a$-adic completion of $R$ is a continuous ring iso.

**Pros:**
- **Directly closes the sorry** by identifying $\mathcal O_X(D) \cong \mathrm{Localization.Away}(\kappa_{D_0}(s))(\mathcal O_X(D_0))$ as topological rings.
- Stacks-style: Mathlib has many lemmas in this style (`AdicCompletion.flat_of_isNoetherian`, etc.). Fits cleanly into existing Mathlib infrastructure.
- Reusable for many other adic-space / formal-scheme formalisations.

**Cons:**
- Requires the noetherian hypothesis (which we have) — but the result fails for non-noetherian rings, so this restricts generality compared to candidates **P** and **B**.
- The proof needs careful adic-completion machinery (Artin-Rees + filtration arguments). Mathlib has `AdicCompletion` basics but the localization-commutation lemma itself is new.

**Implementation: 300-500 lines** (proof structure follows Stacks closely; uses existing Mathlib `AdicCompletion` API).

---

## 8. Where we're stuck — the precise sorry

For the reviewer's full clarity, the exact statement that's open in the project:

**Stuck point 8.1.** *The surjection-up-to-powers in Wedhorn Prop 8.15.*

We need: for every $z \in \mathcal O_X(D)$, there exist $n \in \mathbb N$ and $a \in \mathcal O_X(D_0)$ such that $z \cdot u^n = \sigma(a)$.

**What we have**:
- $\sigma$ continuous ring hom.
- $u$ unit in $\mathcal O_X(D)$.
- $\mathcal O_X(D_0)$ and $\mathcal O_X(D)$ both complete metrisable Hausdorff topological rings (BaireSpace, first-countable).
- The image of $D_0$'s coeRingHom is dense in $\mathcal O_X(D)$.
- For elements $x \in A[1/s]$ (the dense subring), we have explicit $n, a$ via $\mathrm{IsLocalization.surj}$ at the algebraic level (`h_dense` lemma in the project).

**What we don't have**:
- Any version of an Open Mapping theorem that applies to non-σ-compact Polish topological groups.
- A normed structure on $\mathcal O_X(D)$ over a non-archimedean field $k$ (would require fixing $k$).
- The completion-localization commutation theorem.

The project's planned proof outline (recorded in code, lines 1239–1271 of the source file) uses Approach (i) — Pettis-style Baire argument — but fails on the step "range of $\sigma$ is closed", which would require either uniform-inducing (false by Conrad) or a normed structure (we don't have).

---

## 9. Open mathematical questions for the reviewer

**Q1. Which of the four candidate Mathlib routes (P, B, H, S in §7) closes the sorry most directly?**

We have, in particular, identified that **Candidate P (Pettis)** does NOT close the sorry directly (despite our earlier suspicion) because the source map is not surjective. **Candidate S (Stacks completion-localization)** appears to close it cleanly via topological-ring iso. Are we right that S is the right choice, or is one of the others better suited (e.g., closer to existing Mathlib infrastructure, more reusable, more amenable to formalization)?

**Q2. What is the canonical reference for the completion-localization commutation theorem (Candidate S)?**

We've cited Stacks tag `0AHQ` and Bourbaki AC III §2.13, but neither states the theorem in the exact "Mathlib-PR-ready" form. Is there a textbook reference (BGR, Bosch, Huber, ZS, or other) that states this in the cleanest way? In particular, what hypotheses does the theorem actually need — noetherian + adic + finitely generated, or weaker?

**Q3. What's the right generality target for Mathlib?**

Specifically: should the Mathlib contribution target the most general (Pettis-style Open Mapping for Polish groups, Candidate **P**) for maximum future reusability, or the focused completion-localization commutation (Candidate **S**) that closes our specific sorry but is more specialized? There's a maintainability trade-off: P is more general but less useful for our specific application; S is specialized but directly applicable.

Related: Is the right "natural home" for the theorem $\mathrm{AdicCompletion}$ (Mathlib's existing namespace) or $\mathrm{Localization}$, or should it be a new file entirely?

**Q4. Are there existing Mathlib hooks we should use to keep the contribution lightweight?**

The Mathlib pieces we know about:
- `AdicCompletion` (in `Mathlib/RingTheory/AdicCompletion/`) — has `flat_of_isNoetherian`, the basic completion functor, and the flat / faithfully flat infrastructure.
- `IsLocalization.Away` (algebraic side) — universal property of localization.
- `UniformSpace.Completion.extensionHom` — extending uniformly continuous ring homs to completions.
- `BaireSpace.of_completelyPseudoMetrizable` — gives Baire property for free.

Is there infrastructure we're missing that would make the contribution easier? In particular, is there any work-in-progress in Mathlib (currently open PRs or branches) targeting non-archimedean / adic topology that we should be aware of?

---

## 10. Auxiliary technical results (appendix)

For completeness, the project has the following infrastructure that may be useful context:

- **`presheafValue_baireSpace`** (sorry-free) — `presheafValue D` is a Baire space, via the `BaireSpace.of_completelyPseudoMetrizable` Mathlib instance + first-countability of the localization topology.
- **`isUnit_s_in_presheafValue`** (sorry-free) — $\kappa_D(s)$ is a unit in $\mathcal O_X(D)$.
- **`restrictionMapHom_canonicalMap`** (sorry-free) — the restriction-canonical compatibility identity.
- **`presheafValue_iteratedMinus_equiv`** and **`presheafValue_iteratedOverlap_equiv`** (sorry-free) — Wedhorn 2.13 iterated rational identifications.
- **`Wedhorn.isClosed_ideal_of_noetherian`** (sorry-free, project-internal) — Proposition 6.17: ideals in noetherian Tate rings are closed.
- **`AdicCompletion.faithfullyFlat_of_le_jacobson_bot`** (sorry-free, project-internal) — the Stacks 00MA generic theorem for adic completions.

The project's overall build status: **compiles cleanly with 3112 jobs**. The single remaining critical-path sorry is exactly the Wedhorn Prop 8.15 issue described above; there is one additional sorry on a separate non-critical chain (`locLift_open_on_image_at_zero`, the Artin-Rees translation for individual restriction kernels), which is independent and not the focus of this brief.

---

## 11. Document metadata

- Project name: Adic Spaces — Lean 4 formalization of Wedhorn (2019).
- Brief generated: 2026-05-11 (second session of the day; previous brief was about the overall strategy, now settled).
- Length: ~13 pages, ~5,200 words.
- Build status: project compiles cleanly. 1 critical-path sorry remaining (Wedhorn Prop 8.15) + several non-critical-path sorries (e.g., in `ScottishBook` problem statements that are deliberately left for users).
- Recent commit context: multi-session marathon closed Lane A bridge (Wedhorn 2.13 overlap transport), T-NEW-1 and T-NEW-2 — both unconditional. Currently parked at the Wedhorn Prop 8.15 blocker, which is the subject of this brief.
- Previous brief reference: an earlier brief (2026-05-11 morning session) covered the project-level strategy. ChatGPT Pro confirmed: Lane A → Lane C → final assembly, with Lane B (Cor 8.32) consumed via product-level only. That strategy is settled. This brief asks specifically about closing the Wedhorn Prop 8.15 piece of the Cor 8.32 application.

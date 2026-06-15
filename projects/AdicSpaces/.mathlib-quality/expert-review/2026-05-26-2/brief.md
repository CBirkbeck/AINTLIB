# Review brief — Sheafy structure presheaf on the adic spectrum (Wedhorn 8.28(b))

*Prepared 2026-05-26 for a senior algebraic geometer specialising in adic spaces / Tate rings (Huber–Wedhorn area, same audience as previous rounds). Self-contained: no repo access required. Standard Wedhorn notation throughout.*

*This is **round 4** of the consultation on this project. Rounds 1–3 ended with the reviewer recommending Route C (Banach open mapping theorem against the section equalizer). We have implemented the Route C scaffold and have hit a precise mathematical blocker which forces a planning-level decision; this brief asks for guidance on that decision.*

---

## 1. Goal

We are formalising in Lean 4 / Mathlib the apex result of Wedhorn's *Adic Spaces* §8, namely **sheafiness of the structure presheaf** $\mathcal{O}_X$ on the adic spectrum $X = \mathrm{Spa}(A, A^+)$ for a complete strongly noetherian Tate affinoid ring $A$, in the strong topological form (sheaf of complete topological rings, not just of rings).

Concretely, we want the keystone theorem:

> **Theorem (target — Wedhorn 8.28(b)).** *Let $(A, A^+)$ be a complete strongly noetherian Tate affinoid ring. Then $\mathcal{O}_X$ is a sheaf of complete topological rings on the basis of rational subsets of $X = \mathrm{Spa}(A, A^+)$.*

In our class definition, this unpacks (per Wedhorn Remark 8.20) into two assertions about every rational covering $\mathcal{C}$ of every rational subset $\mathcal{C}.\mathrm{base}$:

1. **Embedding:** the canonical map $\rho_{\mathcal{C}} : \mathcal{O}_X(\mathcal{C}.\mathrm{base}) \to \prod_{D \in \mathcal{C}.\mathrm{covers}} \mathcal{O}_X(D)$ is a topological embedding (injective + induces the source topology as the subspace topology from the product).
2. **Gluing:** every compatible family in $\prod_D \mathcal{O}_X(D)$ has a unique preimage in $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$.

## 2. Background and references

### 2.1. Setting

Throughout, $A$ is a topological commutative ring; $A^+ \subseteq A$ is an integrally closed subring of power-bounded elements (a plus-subring); the pair $(A, A^+)$ is a Huber pair (the topology is f-adic, so the ring of definition $A_0 \subseteq A$ carries an ideal of definition $I \subseteq A_0$ with $A_0$ open and $I$-adic in $A$). The ring $A$ is *Tate* if it contains a topologically nilpotent unit $\pi$ (a *pseudo-uniformizer*); equivalently, the ideal of definition contains a unit of $A$. The ring $A$ is *strongly noetherian* if the Tate algebra $A\langle X_1, \ldots, X_k\rangle$ is noetherian for every $k \geq 0$.

The adic spectrum $X = \mathrm{Spa}(A, A^+)$ is the set of equivalence classes of continuous valuations $v$ on $A$ with $v(a) \leq 1$ for all $a \in A^+$, topologised by the rational subsets

$$R(T/s) = \{v \in X : v(t) \leq v(s) \neq 0 \text{ for all } t \in T\}$$

indexed by finite $T \subseteq A$ and $s \in A$ with $T \cdot A$ open in $A$. The structure presheaf takes value

$$\mathcal{O}_X(R(T/s)) := A\langle T/s\rangle$$

where $A\langle T/s\rangle$ is the completion of the localisation $A[T/s] := A[t/s : t \in T] \subseteq A[1/s]$ in the natural Tate topology (the localisation topology built from the ideal of definition of $A_0[T/s]$). We use the shorthand $\mathrm{presheafValue}(D) := A\langle D.T/D.s\rangle$ for the value at a rational locality datum $D = (T, s)$.

A *rational covering* $\mathcal{C}$ of base datum $(T_0, s_0)$ is a finite family of rational data $(T_D, s_D)$ such that each $R(T_D/s_D) \subseteq R(T_0/s_0)$ and the family covers $R(T_0/s_0)$ pointwise.

### 2.2. References

- **[Wed19]** Torsten Wedhorn. *Adic Spaces*. arXiv:1910.05934v1, 2019. Our primary textual reference. Key items: Lemma 6.16 (Banach OMT for Tate rings), Lemma 6.17 (noetherian $\Leftrightarrow$ ideals closed), Proposition 6.18 (unique fg-module topology), Definition 7.14 (Spa), Lemma 7.31 (small-element existence), Corollary 7.32 (dominating-unit), Lemma 7.45 (Spa points over primes), Proposition 7.46 (analytic morphisms), Proposition 8.15 (rational restriction is localisation), Remark 8.20 (sheaf of topological rings characterisation), Definition 8.21 (affinoid adic space), Definition 8.26 (sheafy), Theorem 8.28 (sheafiness in three cases), Corollary 8.32 (faithful flatness of product restriction), Lemma 8.31 (flatness), Lemma 8.33 (Laurent acyclicity), Lemma 8.34 (refinement transfer).
- **[Hu1]** Roland Huber. "Continuous valuations." *Math. Z.* 212 (1993). Foundational for the valuation spectrum and continuity of valuations.
- **[Hu2]** Roland Huber. "A generalization of formal schemes and rigid analytic varieties." *Math. Z.* 217 (1994). The original construction of the category of adic spaces and structure sheaf framework.
- **[Hu3]** Roland Huber. *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*. Aspects of Mathematics E30, Vieweg, 1996. Chapter 1 ("Adic spaces", pp. 36–107) is the polished reference. Per Round-3 advice, this is where Huber's topological structure-sheaf argument lives.
- **[Bou-TG]** Nicolas Bourbaki. *Topologie Générale*, Chapter III §3 no. 3 Théorème 1. The classical Banach open mapping theorem for topological abelian groups: a continuous surjective homomorphism between Hausdorff topological abelian groups whose topologies are defined by countable fundamental systems of neighbourhoods of $0$, both complete, is open. **Crucially, Bourbaki's statement requires neither sigma-compactness nor separability of the source.**
- **[BGR84]** Siegfried Bosch, Ulrich Güntzer, Reinhold Remmert. *Non-Archimedean Analysis*. Grundlehren 261, Springer, 1984. The standard reference for the Banach-algebra machinery underlying Tate algebras; §3.7 in particular uses Banach OMT as a prerequisite without re-proving it.
- **[Hüb16]** Katharina Hübner. "The adic Nullstellensatz" (and subsequent works on adic spaces). Cited in our internal plan documents but with a partial title; the precise reference appears in Round 2 as a discharger of a pointwise-basis intermediate step.

### 2.3. State of the art

Wedhorn 8.28(b) is proved in Wedhorn's text loc. cit.; the argument is purely algebraic at the level of Čech complex exactness via Lemma 8.34 (refinement transfer) + Corollary 8.32 (faithful flatness) + Lemma 8.33 (single-step Laurent acyclicity). The **topologised** variant, where the sheaf condition demands a topological embedding rather than just an injection, is the part that Wedhorn does not give in full detail; per the Round-3 reply, this content lives in [Hu3] Chapter 1, and the topological strictness uses Banach's open mapping theorem as the substantive analytical input.

To our knowledge no full formalisation of this theorem exists in any proof assistant. The closest mathlib-level facts that touch the surrounding machinery are: continuous valuations and the Huber pair structure (we have built these); Banach OMT for sigma-compact topological groups (mathlib has `MonoidHom.isOpenMap_of_sigmaCompact`); and various completion / localisation utilities. The non-sigma-compact form of Banach OMT — the Bourbaki form — is **not** in mathlib.

## 3. Strategy

The project's `IsSheafy` class has two fields:
1. **embedding** — for every rational covering $\mathcal{C}$, the canonical map $\rho_{\mathcal{C}}$ is a topological embedding.
2. **gluing** — every compatible family glues.

We have closed the **algebraic side** of both fields (separation $=$ injectivity of $\rho_{\mathcal{C}}$, and gluing $=$ existence of a preimage) via the Wedhorn Cor 8.32 + Stacks 023N descent route. This is already done; see §5.

The remaining open content is the **topological inducing** in the embedding field: it is not enough that $\rho_{\mathcal{C}}$ is injective; the topology on the source must coincide with the subspace topology pulled back from the product.

Three routes to this topological inducing have been explored over the past rounds:

- **Route A — Direct Wedhorn 8.34.** Use Wedhorn's purely-algebraic acyclicity argument and read off the topological strictness from it. Round 1 verdict: Route A closes only the algebraic content; it does not deliver the topological embedding.

- **Route B — Lane C / LaurentTree (pointwise refinement).** A project-specific decomposition that builds a balanced binary tree of Laurent refinements, transports topological inducing through the tree via single-step inducing $\Rightarrow$ refinement inducing $\Rightarrow$ tree-rooted inducing. Substantial in scope ($\sim 30{,}000$ LOC across $\sim 130$ files), with about ten residual sub-sorries clustered in the $\sigma$-walk / tree-existence content. Round-2 verdict: keep Route B and finish the residual sub-sorries via a coordinated parametric-propagation pass.

- **Route C — Banach OMT against the section equalizer.** The route the Round-3 reviewer recommended, on the grounds that it could collapse Route B's tens of thousands of lines into one open-mapping argument. We have now implemented the Route C scaffold and have closed almost all of its sub-sorries, but have hit a precise blocker that we describe below.

This brief is asking for guidance on the precise blocker and the architectural decision it forces.

## 4. Definitions

### 4.1. The keystone class

**Definition 4.1 (IsSheafy).** Let $A$ be a Huber ring with a plus-subring $A^+$. The class `IsSheafy A` consists of:

(embedding) For every rational covering $\mathcal{C}$ of a rational locality datum $\mathcal{C}.\mathrm{base}$, the canonical map

$$\rho_{\mathcal{C}} : \mathcal{O}_X(\mathcal{C}.\mathrm{base}) \to \prod_{D \in \mathcal{C}.\mathrm{covers}} \mathcal{O}_X(D)$$

is a *topological embedding*: injective, and the topology on $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$ equals the subspace topology pulled back from the product.

(gluing) For every rational covering $\mathcal{C}$ and every compatible family $(f_D)_D$ with $f_D \in \mathcal{O}_X(D)$, there exists $x \in \mathcal{O}_X(\mathcal{C}.\mathrm{base})$ with $\rho_D(x) = f_D$ for all $D$.

Throughout this brief, the **target hypothesis set** for the keystone theorem is

$$[A\text{ Tate}],\ [A\text{ noetherian as a ring}],\ [A\text{ strongly noetherian}],\ [A\text{ is }T_2],\ [A\text{ nonarchimedean}].$$

We do **not** include $[A$ complete$]$, $[A$ compatible plus-subring$]$, $[A$ separable$]$, $[A$ sigma-compact$]$ in this hypothesis set, because none of them are present in Wedhorn 8.28(b)'s actual statement.

### 4.2. The section equalizer (Route C)

**Definition 4.2 (sectionEqualizer).** Given a rational covering $\mathcal{C}$, define

$$E_{\mathcal{C}} := \Big\{f \in \prod_{D \in \mathcal{C}.\mathrm{covers}} \mathcal{O}_X(D) : \forall D_1, D_2 \in \mathcal{C}.\mathrm{covers},\ \forall D_3 \subseteq D_1 \cap D_2,\ \rho_{D_1 \to D_3}(f_{D_1}) = \rho_{D_2 \to D_3}(f_{D_2})\Big\}$$

where $\rho_{D_i \to D_3}$ are the natural restriction maps between rational locality data. By the cocycle/compatibility of the restriction maps ($\rho_{\mathrm{base} \to D_3} = \rho_{D_i \to D_3} \circ \rho_{\mathrm{base} \to D_i}$, established sorry-free in our code), $E_{\mathcal{C}}$ is a subring of the finite product, and the image of $\rho_{\mathcal{C}}$ lies in $E_{\mathcal{C}}$.

We carry through the codomain-restricted map

$$\tilde\rho_{\mathcal{C}} : \mathcal{O}_X(\mathcal{C}.\mathrm{base}) \to E_{\mathcal{C}}$$

and reduce the topological inducing of $\rho_{\mathcal{C}}$ to a homeomorphism statement for $\tilde\rho_{\mathcal{C}}$.

## 5. Established results

The results below are all *closed in the formalisation* (have real proof bodies, not stubs).

### 5.1. Algebraic acyclicity (separation + gluing) — DONE

**Theorem 5.1 (algebraic separation, Wedhorn-exact).** *Let $A$ be strongly noetherian Tate, $\mathcal{C}$ a rational covering with non-empty $\mathcal{C}.\mathrm{covers}$. If $x \in \mathcal{O}_X(\mathcal{C}.\mathrm{base})$ has $\rho_D(x) = 0$ for all $D \in \mathcal{C}.\mathrm{covers}$, then $x = 0$.*

*Sketch.* By Wedhorn Cor 8.32 (faithful flatness of the product restriction over the base presheafValue), the algebra map $\mathcal{O}_X(\mathcal{C}.\mathrm{base}) \to \prod_D \mathcal{O}_X(D)$ is injective. The proof of 8.32 goes via Wedhorn Prop 8.15 (rational restriction is a localisation, hence flat by `IsLocalization.flat`) and a Spec-surjectivity argument (every prime of $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$ is the comap of a prime of some $\mathcal{O}_X(D)$, via Wedhorn Lemma 7.45 / the Spa-point construction over non-open primes). $\square$

**Theorem 5.2 (algebraic gluing, Stacks 023N descent).** *Same hypotheses. Every compatible family $(f_D)_D \in \prod_D \mathcal{O}_X(D)$ lifts to a unique $x \in \mathcal{O}_X(\mathcal{C}.\mathrm{base})$.*

*Sketch.* Stacks 023N (faithfully flat descent equaliser) applied to the product algebra map. The cocycle map $S \otimes_R S \to \prod_D \mathcal{O}_X(D \otimes \cdot)$ whose kernel-equal-to-image-of-base is exactly the equaliser condition is closed as our `faithfullyFlat_descent_equalizer` theorem; the substantive content (Stacks 023N theorem) is delegated as a single deep sorry inside, but the chain itself is structurally closed at the keystone. $\square$

### 5.2. Spa-point existence for non-open primes — DONE

**Theorem 5.3 (Wedhorn 7.45 + companion).** *Let $A$ be a complete strongly noetherian Tate ring with a compatible plus-subring. For every prime $p \subseteq A$ and every $s \in A$ with $s \notin p$, there exists $v \in R(T, s) \subseteq \mathrm{Spa}(A, A^+)$ with $p \subseteq v.\mathrm{supp}$.*

*Sketch.* Case-split on whether $p$ is open. Open case: trivial valuation on $\mathrm{Frac}(A/p)$. Non-open case: Wedhorn 7.45 (analytic-point construction using the chosen pair of definition) plus a rational-open membership lift using the localisation topology. The infrastructure ingredients (`IsAdicComplete` instance for the principal pair, $A^+ \subseteq P.A_0$ alignment) are isolated as named sub-lemmas. $\square$

### 5.3. Route C infrastructure — DONE (5 of 6 sub-lemmas closed)

The section equalizer $E_{\mathcal{C}}$ has been built and its mathematical properties closed:

**Theorem 5.4 (Route C, sub-lemmas $E_{\mathcal{C}}$).** *Under the keystone hypotheses, $E_{\mathcal{C}}$ is a closed subring of the finite product $\prod_D \mathcal{O}_X(D)$. The subring $E_{\mathcal{C}}$ is complete (closed subspace of a finite product of complete topological rings is complete). The codomain-restricted map $\tilde\rho_{\mathcal{C}} : \mathcal{O}_X(\mathcal{C}.\mathrm{base}) \to E_{\mathcal{C}}$ is continuous, injective, and surjective.*

*Sketch.*
- **Closedness:** $E_{\mathcal{C}}$ is the intersection over all $(D_1, D_2, D_3, h_{31}, h_{32})$ of the preimages of the diagonal in $\mathcal{O}_X(D_3) \times \mathcal{O}_X(D_3)$ under the continuous map $f \mapsto (\rho_{D_1 \to D_3}(f_{D_1}), \rho_{D_2 \to D_3}(f_{D_2}))$. The diagonal is closed in $T_2$ targets, each preimage is closed, the intersection is closed.
- **Completeness:** finite products of complete uniform spaces are complete; closed subspaces of complete spaces are complete.
- **Continuity of $\tilde\rho_{\mathcal{C}}$:** a map into a subspace is continuous iff its composition with the inclusion is. The composition is $\rho_{\mathcal{C}}$, which is the $\Pi$-product of continuous restriction maps.
- **Injectivity of $\tilde\rho_{\mathcal{C}}$:** Theorem 5.1.
- **Surjectivity of $\tilde\rho_{\mathcal{C}}$:** Theorem 5.2 — the cocycle condition defining $E_{\mathcal{C}}$ is exactly the gluing-compatibility hypothesis.
- **Topology on the uniform side:** $\mathcal{O}_X(\mathcal{C}.\mathrm{base}) = A\langle T_0/s_0\rangle$ is the completion of the localisation $A[T_0/s_0]$ in the localisation topology, hence carries a complete metric structure inherited from `UniformSpace.Completion.instMetricSpace`. Its uniformity is countably generated (basis at $0$ indexed by $\mathbb{N}$ via powers of the ideal of definition of $A_0[T_0/s_0]$). Similarly for each $\mathcal{O}_X(D)$. The uniformity on $E_{\mathcal{C}}$ is countably generated as a subspace of a finite product of countably-generated spaces. $\square$

The five established structural facts above are formalised sorry-free at the keystone declaration site.

### 5.4. Banach OMT in mathlib (the available form)

Mathlib provides the following form of the Banach open mapping theorem for topological groups:

**Theorem 5.5 (mathlib `MonoidHom.isOpenMap_of_sigmaCompact`).** *Let $G, H$ be Hausdorff topological abelian groups. Assume:*
- *$G$ is sigma-compact;*
- *$H$ is Baire and $T_2$.*

*Then every continuous surjective additive group homomorphism $f : G \to H$ is open.*

This is the form on which all current Banach OMT consumers in the project (including the topological-strictness step in Route C) rely.

Bourbaki TG III.3 Théorème 1 (the form Huber implicitly cites in [Hu2]) does **not** require sigma-compactness of $G$. It requires only complete + countable fundamental system of neighbourhoods of $0$ on both sides. **That non-sigma-compact form is not in mathlib.** The project has the building-block sub-lemmas for Bourbaki's proof (symmetric absorption, interior-of-sum-of-interiors, Baire-nonempty-interior, Cauchy builder, Cauchy limit in neighbourhood, translation), but the main theorem assembly delegating to those sub-lemmas instead of to mathlib's sigma-compact variant has not been written.

## 6. In progress

### 6.1. `productRestrictionSub_isInducing_tate` — the keystone (Route C scaffold)

**Status:** real proof body, no direct `sorry` at the declaration site. Two transitive sorries via named sub-lemmas (see §8).

**Mathematical statement:** under the target hypothesis set (see Definition 4.1), $\rho_{\mathcal{C}}$ is a topological inducing for every rational covering $\mathcal{C}$.

**Current proof body.** Case-split on $\mathcal{C}.\mathrm{covers}$ non-empty:

- **Non-empty case:** the codomain-restricted map $\tilde\rho_{\mathcal{C}}$ is continuous (Theorem 5.4), injective (Theorem 5.4 / Theorem 5.1), and surjective (Theorem 5.4 / Theorem 5.2). If we additionally know that $\tilde\rho_{\mathcal{C}}$ is *open*, then it is a topological isomorphism $\mathcal{O}_X(\mathcal{C}.\mathrm{base}) \cong E_{\mathcal{C}}$. Composed with the inclusion $E_{\mathcal{C}} \hookrightarrow \prod_D \mathcal{O}_X(D)$ (which is inducing by definition of the subspace topology), this gives the inducing for $\rho_{\mathcal{C}}$. Openness of $\tilde\rho_{\mathcal{C}}$ is supplied by Banach OMT applied to $\tilde\rho_{\mathcal{C}}$ viewed as a continuous surjective additive group homomorphism.

- **Empty cover case:** the target $\prod_D \mathcal{O}_X(D)$ is a singleton (empty product). For the inducing claim to hold we need the source to be subsingleton; this holds when $\mathcal{C}.\mathrm{base}.s = 0$ (then $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$ is the zero ring). The other branch ($s \neq 0$ + empty cover) is mathematically impossible by Wedhorn's covering condition + Spa-point existence over a prime not containing $s$, but the contradiction needs additional typeclass assumptions (compatible plus-subring + completeness) that are not in the keystone signature. The upstream consumer of the keystone (`isSheafy_ofStronglyNoetherianTate`) case-splits on $s = 0$ before invoking the keystone, so the impossible branch is never reached in practice; this branch remains as a named sub-lemma `sorry` with a documented justification.

### 6.2. Dispatch board (ticket names; structural only)

The Route C decomposition consists of seven sub-tickets:

| Ticket name | Mathematical statement | Status | Depends on |
|---|---|---|---|
| `route-c-refactor` | Move the Route C block in the source tree past the algebraic acyclicity infrastructure so the equalizer-side proofs can reference the algebraic content directly | done | – |
| `productRestrictionSubToEqualizer_injective` | Injectivity of $\tilde\rho_{\mathcal{C}}$ via algebraic separation (Theorem 5.1) | done | algebraic separation |
| `productRestrictionSubToEqualizer_surjective` | Surjectivity of $\tilde\rho_{\mathcal{C}}$ via algebraic gluing (Theorem 5.2) | done | algebraic gluing |
| `presheafValue_uniformity_isCountablyGenerated` | The uniformity on $\mathcal{O}_X(D)$ is countably generated | done | locBasis countable |
| `presheafValue_sigmaCompactSpace` | $\mathcal{O}_X(D)$ is sigma-compact | **B2** (statement false; see §8) | – |
| `sectionEqualizer_uniformity_isCountablyGenerated` | The uniformity on $E_{\mathcal{C}}$ is countably generated | done | the previous + finite product + subspace |
| `productRestrictionSub_isInducing_tate_empty` | The empty-cover edge case | partial (only $s = 0$ branch closed) | – |

## 7. Targets (not yet attempted)

Beyond the keystone, the project plans to discharge the consumer chain that uses `IsSheafy A`:
- Affinoid adic spaces ($\mathrm{Spa}(A, A^+)$ as a category-theoretic object in $\mathcal{V}^{\mathrm{pre}}$).
- Adic spaces (Definition 8.22) and morphisms.
- The étale site / cohomology eventually.

These all consume `IsSheafy A` as a hypothesis and are unaffected by the choice of internal proof route, so we defer them.

## 8. Where we're stuck

### 8.1. The keystone blocker: sigma-compactness in Route C

The keystone's non-empty-cover branch reduces, after the bijection $\tilde\rho_{\mathcal{C}}$ is identified, to applying Banach OMT to obtain openness. The only Banach OMT in mathlib that applies in our setting (Theorem 5.5 above) demands $G = \mathcal{O}_X(\mathcal{C}.\mathrm{base})$ to be **sigma-compact**.

To deliver sigma-compactness of $\mathcal{O}_X(\mathcal{C}.\mathrm{base}) = A\langle T_0/s_0\rangle$ from the keystone's hypothesis set is **mathematically impossible in general**. Counterexample: let $A = \mathbb{C}((t))$ with the $t$-adic topology and $A^+ = \mathbb{C}[\![t]\!]$. Then $(A, A^+)$ is a complete strongly noetherian Tate affinoid ring, $T_2$, nonarchimedean. But $\mathbb{C}((t))$ has residue field $\mathbb{C}$, which is uncountable; the ring of integers $\mathbb{C}[\![t]\!]$ is not locally compact (every neighbourhood of $0$ contains a homeomorphic copy of the uncountable disconnected set $\mathbb{C}$); hence not sigma-compact. So $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$, for the trivial cover datum $(T_0, s_0) = (\{1\}, 1)$, is $A$ itself, which is not sigma-compact.

This means `presheafValue_sigmaCompactSpace` as stated is **mathematically false**: the keystone hypotheses do not entail sigma-compactness.

The keystone *statement itself* remains true (Wedhorn 8.28(b) does not require sigma-compactness; the topological inducing for $\rho_{\mathcal{C}}$ holds for $\mathbb{C}((t))$). What fails is Route C's *proof route*.

This blocker forces an architectural decision. We see four resolutions:

(a) **Add `[SigmaCompactSpace A]` to the keystone hypothesis set.** Per BINDING-RULE (b) of our internal rules — adding a hypothesis to a theorem whose result is false without it — this is technically allowed for the sub-lemma `presheafValue_sigmaCompactSpace`. But to thread it through to the keystone, the keystone itself would need the assumption. This *strengthens* the keystone beyond Wedhorn 8.28(b)'s actual statement, narrowing the class of affinoid rings to which it applies (excluding for example $\mathbb{C}((t))$). The narrowing has consequences for downstream consumers and may not be acceptable as the project's final claim.

(b) **Add `[SeparableSpace A]` to the keystone.** Weaker than sigma-compactness (separable + complete metric $\Rightarrow$ Polish $\Rightarrow$ Lindelöf $\Rightarrow$ countable subcover from any open cover; this is enough for the Bourbaki/BGR proof of Banach OMT, replacing the role of sigma-compactness). Many concrete adic spaces of interest are separable (e.g., over $\mathbb{Q}_p$ or $\mathbb{F}_p((t))$); some are not. Still narrows the keystone but more permissively than (a).

(c) **Write a Baire-based Banach OMT in the project, bypassing the mathlib sigma-compact form.** The classical Bourbaki argument (TG III.3, Théorème 1) needs only: (i) source is complete with countable fundamental system of neighbourhoods of $0$; (ii) target is Baire. Both are satisfied by $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$ and $E_{\mathcal{C}}$ under the keystone hypotheses (we have `presheafValue_baireSpace` already done; Baire follows from the completion's metric structure). The proof building-blocks (symmetric absorption, interior-of-sum-of-interiors, Baire-nonempty-interior, Cauchy builder, Cauchy limit in neighbourhood, translation) are already in the project sorry-free; only the main assembly remains to be written. Estimate: 150–300 lines of careful filter manipulation, no new mathematical content beyond Bourbaki. This is the cleanest fix and keeps the keystone signature pristine.

(d) **Switch the topological-inducing route entirely back to Route B (Lane C / LaurentTree).** Substantial undertaking (Route B has ~30,000 lines across ~130 files with ~10 residual sorries clustered in the $\sigma$-walk content from Wedhorn 8.34 step (ii)). Round-3 advised keeping Route C as a sprint and falling back to Route B if Route C fails; the present blocker is plausibly that failure point, though Route C is much closer to closing than Route B.

### 8.2. The empty-cover edge case

A secondary residual sorry is the $s \neq 0$ branch of the empty-cover case. For valid rational coverings, the combination "empty cover + non-zero $s$" is impossible — Wedhorn's covering condition then forces $R(T_0, s_0) = \emptyset$, which is contradicted by Spa-point construction over a prime not containing $s_0$ when $s_0$ is not nilpotent. The proof requires `[CompatiblePlusSubring A]` and `[CompleteSpace A]`, which are not in the keystone hypothesis set. Our upstream consumer (`isSheafy_ofStronglyNoetherianTate`) case-splits on $s = 0$ before invoking the keystone, so the impossible branch is unreached in practice. We have left this as a named sub-lemma `sorry` with the contradiction proof sketched in the docstring.

This residual is benign: it does not affect any downstream use, and a routine future addition of the necessary plus-subring instance to the empty-cover branch would close it. It is also independent of the §8.1 architectural decision, so we are not asking the reviewer about it here.

### 8.3. What we have ruled out

We have ruled out Route A (algebraic only) — it does not deliver the topological embedding, only the algebraic injection and gluing (Round 1 verdict, confirmed Round 3).

We have not yet abandoned Route B — it remains the documented fallback per Round 3.

We have not abandoned Route C — the Route C scaffold is closed except for the sigma-compactness blocker, and resolution (c) above would complete it cleanly.

## 9. Open mathematical questions for the reviewer

**Q1.** Is it acceptable, in the spirit of the project's final claim of *"sheafiness for strongly noetherian Tate $(A, A^+)$"*, to add `[SigmaCompactSpace A]` as a hypothesis to the keystone? Or does that narrowing of the hypothesis set move outside the class of adic spaces the project is supposed to serve? In particular: are the typical examples of strongly noetherian Tate rings that arise in arithmetic-geometric applications (Tate algebras over $\mathbb{Q}_p$, $\mathbb{Z}_p$-affinoids, perfectoid-pre algebras) sigma-compact, or do we lose substantial families by adding this hypothesis?

**Q2.** Is the weaker `[SeparableSpace A]` (resolution (b)) acceptable? Concretely: every Tate algebra over a complete discretely-valued field with countable residue field (so $\mathbb{Q}_p$-affinoids, but not $\mathbb{C}((t))$-affinoids) is separable. This is a substantially larger class than the sigma-compact class but still narrows from the bare strongly-noetherian-Tate setting. Is separability a hypothesis the community would accept for an adic-space sheafiness theorem?

**Q3.** Is resolution (c) — writing the Bourbaki-form Baire-based Banach OMT in the project — the right move? The proof is classical (Bourbaki TG III.3 Théorème 1), the source assumptions match what we naturally have on $\mathcal{O}_X(\mathcal{C}.\mathrm{base})$ (complete + countable nhds-of-$0$ basis), and it would let us keep the keystone signature exactly as Wedhorn 8.28(b) states it. The downside is the engineering cost (~200 lines of careful filter work). Two specific concerns:

(i) Does the reviewer know of a published formal statement (in any proof assistant) of the Bourbaki-form Banach OMT for topological abelian groups, or of an unpublished mathlib branch where this lives? Saves a re-prove.

(ii) Is there a *subtle* mathematical reason the Bourbaki form is harder or shakier than the sigma-compact form? Our reading of Bourbaki is that the two are essentially the same theorem with the sigma-compactness assumption replaced by an explicit countable cover via a dense subset; but in formalisation it may turn out that the actual Bourbaki form needs separability or some other assumption we have not noticed.

**Q4.** Is there a *different* OMT route entirely that we have not considered? For instance: a Banach OMT proven directly via the metric structure on completions (every $\mathcal{O}_X(D)$ has a complete metric via `UniformSpace.Completion.instMetricSpace`); or a Stacks-style argument that avoids invoking OMT altogether and proves the topological inducing more directly via a quotient-topology comparison; or a Wedhorn-internal route (Wedhorn 6.18 — unique fg-module topology + maps strict — which the project has partially proven and which encodes a form of OMT for the noetherian Tate case).

**Q5.** If after Q1–Q4 the right answer is "switch back to Route B", does the reviewer have any concrete advice on which of Route B's residual $\sigma$-walk sub-sorries to attack first? The Round-2 reply listed several (W1, W2, W3, I.1 in our internal labelling) — at this point we have not made fresh progress on them. Route B is mathematically valid but engineering-heavy; Route C's appeal was that it would collapse Route B entirely.

**Q6.** A meta question: from where you are standing, is the bridging gap between the Wedhorn-style algebraic argument (Cor 8.32 + Lemma 8.34) and the Huber-style topological argument (the [Hu3] Chapter 1 inducing argument) something we should be trying to *formalise faithfully* (i.e., faithfully translate Huber's argument or Wedhorn's argument-extended), or is the right move to *re-do* the bridge ourselves with whatever proof technology is cleanest in Lean (which currently is Banach OMT against the equalizer)? The two perspectives lead to slightly different priorities: faithful translation argues for Route B (closer to the published proofs); cleaner re-derivation argues for Route C with the sigma-compact issue resolved.

## 10. Auxiliary technical results (appendix)

The following structural facts are formalised sorry-free in the project and are listed here for the reviewer to spot-check the underlying machinery. Statements only; no sketches.

- The Spa-points lying-over construction (Wedhorn 7.45 + companion): every prime of $A$ has a Spa-point above it in every rational open not containing $s$ in its support.
- The completion of the localisation $A[T/s]$ in the localisation topology is a complete topological ring with countably-generated uniformity (via the `RingSubgroupsBasis` indexed by $\mathbb{N}$).
- The product restriction is faithfully flat (Wedhorn Cor 8.32) for strongly noetherian Tate $A$.
- The Stacks 023N descent equaliser (specialised to a finite product of presheafValue's): the cocycle kernel equals the image of the base algebra map, under faithful flatness.
- `presheafValue_baireSpace`: $\mathcal{O}_X(D)$ is a Baire space (via the completion's metric structure).
- The Tate algebra $A\langle T_0/s_0\rangle$ is noetherian (Wedhorn 6.18 corollary, the strongly noetherian inductive step).
- $A^+ \subseteq A^\circ$ (compatible plus-subring is contained in the power-bounded subring) — proved when the project assumes `[CompatiblePlusSubring A]` (a project-internal typeclass; not in Wedhorn but used as a standing assumption for the consumers above).

## 11. Document metadata

- **Project name:** Adic spaces formalisation (Lean 4 / Mathlib).
- **Brief generated:** 2026-05-26.
- **Length:** approximately 9 pages.
- **Build status:** clean (3144 jobs, `lake build` succeeds end-to-end, no errors, ~10 named sub-lemma `sorry`'s across the keystone vicinity, most documented in the project's `b2_log.jsonl`).
- **Recent activity:** Round 3 of this consultation closed 2026-05-23 with Route C as the recommended sprint. Between 2026-05-23 and the present (2026-05-26), we executed the Round-3 plan: built the section equalizer, proved closedness / completeness / continuity / bijectivity, refactored the proof to chain through algebraic acyclicity, and hit the sigma-compactness blocker on the final OMT step. The keystone now has a real Route C proof body modulo the §8.1 architectural decision and the §8.2 benign edge case.
- **Previous rounds:** Round 1 (2026-05-15), Round 2 (2026-05-23), Round 3 (2026-05-26 reply). The session state and reply files are archived locally for cross-reference.

# Review brief — Faithful formalisation of Wedhorn's Theorem 8.28(b) (sheafiness of the adic structure presheaf)

*Prepared 2026-06-18 for a senior expert in adic spaces (Huber–Wedhorn theory). Self-contained: no repository access required. The project is a Lean 4 / Mathlib formalisation, but this brief is purely mathematical — the only "formalisation" content is one genuine design question (§9, Q1) about how to encode the notion of a ring of integral elements.*

---

## 1. Goal

We are formalising, faithfully to Wedhorn's *Adic Spaces* lecture notes, the theorem that the adic structure presheaf is a sheaf:

> **Theorem (Wedhorn 8.28(b)).** Let $(A, A^+)$ be a complete, strongly noetherian Tate affinoid ring, and $X = \operatorname{Spa}(A, A^+)$. Then the structure presheaf $\mathcal{O}_X$ on the rational subsets of $X$ is a sheaf (in fact $\check{\mathrm C}$-acyclic) of complete topological rings.

"Faithfully" is the operative word: each lemma must mirror Wedhorn's actual argument, with the same hypotheses, citing the same source results — not a Lean-convenient detour. The present brief asks for strategic confirmation that the decomposition we are using is the right one, and for guidance on one definitional encoding question that has surfaced as the last obstruction on one branch.

---

## 2. Background and references

### 2.1. Setting and notation

We use Wedhorn's conventions throughout.

- $A$ is an **f-adic (Huber) ring**: a topological ring with an open subring $A_0$ (a *ring of definition*) whose topology is $I$-adic for a finitely generated ideal of definition $I \subseteq A_0$.
- $A^\circ$ = the subring of **power-bounded** elements; $A^{\circ\circ}$ = the (open) set of **topologically nilpotent** elements.
- $A$ is **Tate** if it has a topologically nilpotent unit $\varpi$ (a *uniformiser*). Equivalently $A_0$ has $I = (\varpi)$ up to radical and $\varpi$ is a unit of $A$.
- A **ring of integral elements** is a subring $A^+ \subseteq A$ that is **open, integrally closed in $A$, and contained in $A^\circ$** (Wedhorn Def. 7.14(1)).
- An **affinoid ring** is a pair $(A, A^+)$ with $A^+$ a ring of integral elements (Def. 7.14(2)). $\operatorname{Spa}(A,A^+) = \{ v \in \operatorname{Cont}(A) : v(f) \le 1\ \forall f \in A^+ \}$, the continuous valuations bounded by $1$ on $A^+$ (Def. 7.23). $\operatorname{supp}(v) = v^{-1}(0)$ is a prime ideal.
- For $s \in A$ and a finite $T \subseteq A$ with $T \cdot A$ open, the **rational subset** $R(T/s) = \{ x \in X : x(t) \le x(s) \ne 0,\ \forall t \in T\}$. The **structure presheaf** value is $\mathcal{O}_X(R(T/s)) = A\langle T/s\rangle$, the completion of the localisation $A[1/s]$ for the topology making the images of $T/s$ power-bounded.
- **Strongly noetherian**: $A\langle X_1,\dots,X_n\rangle$ is noetherian for all $n$.

For a rational subset $U \subseteq V$, restriction $\mathcal{O}_X(V) \to \mathcal{O}_X(U)$ is the canonical map of completed localisations.

### 2.2. References

- **[Wedhorn]** T. Wedhorn, *Adic Spaces*, lecture notes, arXiv:1910.05934v1 (2019). Primary source. All result numbers (6.x, 7.x, 8.x, A.x) below refer to this.
- **[Hu1]** R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477.
- **[Hu2]** R. Huber, *Bewertungsspektrum und rigide Geometrie*, Regensburger Math. Schriften 23 (1993). (Wedhorn's Prop. 7.18 cites [Hu2] Lemma 3.3; Prop. 7.48 cites [Hu2] 3.9.)
- **[Hu3]** R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Math. E30 (1996). (Wedhorn's Lemma 7.54 = [Hu3] 2.6.)
- **[Henkel 2014]** J. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*, arXiv:1407.5647. (Used for the Banach open-mapping step, Wedhorn 6.16/6.18.)
- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer 1984.

### 2.3. State of the art

The result is Huber's; Wedhorn's notes give a complete textbook proof. Nothing here is new mathematics — the contribution is a machine-checked proof. The deep external inputs Wedhorn himself black-boxes ([Hu2] 3.3 = integral/power-bounded criterion; [Hu2] 3.9 = Prop. 7.48; [Hu3] 2.6 = Lemma 7.54) we likewise treat as cited leaves rather than reprove. The project is otherwise self-contained on top of Mathlib's commutative algebra and topology.

---

## 3. Strategy

We follow Wedhorn's proof of 8.28(b) (p. 81–84) literally. By Prop. A.4 the sheaf property for the Def.-7.29 rational topology reduces to two assertions on every rational covering $\{U_i\}$ of a rational subset $V$:

1. **(Embedding / separation, via Cor. 8.32.)** $\mathcal{O}_X(V) \to \prod_i \mathcal{O}_X(U_i)$ is a topological embedding (injective + inducing the topology). Injectivity comes from **faithful flatness** of the family of restriction maps; the topological "inducing" half comes from the **Banach open mapping theorem** for complete Tate rings (Wedhorn 6.18, built on 6.16).
2. **(Gluing / $\check{\mathrm C}$-acyclicity, via Lemma 8.34.)** Compatible families glue; equivalently the Čech complex of a rational cover is acyclic. Wedhorn reduces an arbitrary rational cover to iterated **Laurent (two-)covers** (8.34(i)–(iv)), whose acyclicity is an explicit chain computation (Prop. A.3), after a refinement step (Lemma 7.54 = [Hu3] 2.6).

Both branches rest on **flatness of restriction maps** $\mathcal{O}_X(D) \to \mathcal{O}_X(D')$ (Prop. 8.30), which is the technical heart and the part we have most recently completed. Wedhorn proves it via **Remark 7.55**: any rational subset $U = R(T/s) \subseteq \operatorname{Spa} B$ sits in a chain
$$\operatorname{Spa} B \supseteq X_0 \supseteq X_1 \supseteq \cdots \supseteq X_n = U,$$
where $X_0 = \{x : 1 \le x(s/u)\}$ (a "dominating unit" locale where $s$ becomes a unit) and $X_i = X_{i-1} \cap \{x : x(t_i) \le x(s)\}$. Each one-step inclusion is a *simple* rational localisation whose flatness is elementary, and flatness composes along the chain.

The elementary per-step input is **Wedhorn 7.52** applied in the completion $B' = \mathcal{O}_X(D')$:
- **(7.52(2), unit criterion)** $s$ becomes a unit in $B'$, because $s$ has no zero on $\operatorname{Spa} B'$;
- **(7.52(1), bounded criterion)** the new generator $t_i/s$ is power-bounded in $B'$, because it has valuation $\le 1$ everywhere on $\operatorname{Spa} B'$.

These two facts are bundled, in the formalisation, into a single hypothesis-class we call the *localisation-lift / power-bounded* property of the base ring. The recent work (and the question motivating this review) is about discharging that bundle faithfully.

---

## 4. Key definitions (as formalised)

**Definition 4.1 (ring of integral elements — Wedhorn 7.14(1)).** A subring $A^+ \subseteq A$ is a *ring of integral elements* if it is open, integrally closed in $A$, and $A^+ \subseteq A^\circ$. We have formalised this predicate faithfully, including the result **Remark 7.15(1): $A^\circ$ is itself the largest ring of integral elements**, so every ring of integral elements is $\subseteq A^\circ$.

**Definition 4.2 (the `A⁺` carrier — the encoding under question).** Throughout the bulk of the development, $A^+$ is supplied not via Definition 4.1 but via a *bare* type-class that records **only** that $A^+$ is *some* subring of $A$ — it does **not** record the three Def.-7.14 axioms (open, integrally closed, $\subseteq A^\circ$). This was an early simplification. The faithful predicate of Definition 4.1 exists in the project but is **not currently linked** to this carrier and is used nowhere. This disconnect is the root of the obstruction in §8.1.

**Definition 4.3 (`CompatiblePlusSubring`).** A strengthening occasionally assumed: $A^+ \subseteq (A_0)_D$ for *every* rational-localisation datum $D$, where $(A_0)_D$ is a chosen ring of definition. This is much stronger than $A^+ \subseteq A^\circ$ and, crucially, is **false in general for completions** $B = \mathcal{O}_X(D)$ (the completed plus-subring of a completion need not sit inside any single ring of definition coming from the construction). The headline theorem assumes `CompatiblePlusSubring A` on the *outer* base $A$; the difficulty is at the *inner*, completion level.

**Definition 4.4 (localisation-lift bundle).** For a fixed base ring $B$ we bundle: (i) for all rational data $D \subseteq D'$ over $B$, the denominator $s_D$ maps to a unit in $\mathcal{O}_{\operatorname{Spa} B}(D')$; (ii) each $t/s_D$ ($t \in T_D$) lifts to a power-bounded element of $\mathcal{O}_{\operatorname{Spa} B}(D')$. This is exactly Wedhorn 7.52(2) + 7.52(1) for the affinoid ring $B$.

---

## 5. Established results

**Theorem 5.1 (headline, assembled).** Under the hypotheses "complete, strongly noetherian Tate, plus the technical class of Def. 4.4 on $A$ and `CompatiblePlusSubring A`", $\mathcal{O}_X$ is a sheaf. *This is assembled* from the embedding leaf (Cor. 8.32) and the gluing leaf (Lemma 8.34); it compiles, modulo the open leaves in §8.

**Theorem 5.2 (Prop. 8.30 restriction flatness — Leaf A, complete).** For rational $D' \subseteq D$ over a complete strongly-noetherian Tate base, $\mathcal{O}_X(D) \to \mathcal{O}_X(D')$ is flat. *Sketch.* Reduce (Wedhorn's "we may assume $X = V$", Prop. 8.2 base change) to the whole-space image piece; run the Remark-7.55 chain $X_0 \supseteq \cdots \supseteq X_n$; each step is the single-generator localisation $B \to \mathcal{O}_B(\text{unit datum})$, flat by transporting the noetherian flatness of $B\langle X\rangle/(f-X)$ across the Example-6.38 quotient comparison; compose along the chain via the relative-piece equivalence (Prop. 8.2 / 8.16). The chain's per-step uses Def. 4.4 for the base $B$. **This branch is complete and the project builds green.** ∎

**Theorem 5.3 (Def.-4.4 bundle for a base — the faithful unit + bounded criteria).** For a complete affinoid $B$:
- *(unit, 7.52(2))* the image of $s$ in a rational completion $\mathcal{O}_B(D')$ is a unit, since every $w \in \operatorname{Spa}\mathcal{O}_B(D')$ pulls back into $R(T/s)$ where $s$ does not vanish;
- *(bounded, 7.52(1))* each $t/s$ is power-bounded, since it has valuation $\le 1$ on all of $\operatorname{Spa}\mathcal{O}_B(D')$ — reducing to the single external criterion [Hu2] 3.3 ($|f(x)|\le 1\ \forall x \Rightarrow f \in B^\circ \Rightarrow$ power-bounded).

We recently **re-wired the flatness chain to use this faithful bundle** in place of an earlier opaque placeholder, so the chain's localisation-lift now rests on exactly two source-justified leaves: [Hu2] 3.3 and the Spa-point existence below.

**Theorem 5.4 (Spa-point existence, containment form — Wedhorn 7.45 + 7.51, axiom-clean).** For a complete affinoid $(A,A^+)$ *equipped with a ring of definition $P$ with $A^+ \subseteq P_0$*, and a maximal ideal $\mathfrak{m}$, there exists $v \in \operatorname{Spa}(A,A^+)$ with $\mathfrak{m} \le \operatorname{supp}(v)$. *Sketch.* If $\mathfrak m$ is open, the trivial valuation on $A/\mathfrak m$ works. If not, Wedhorn 7.45 (analytic-point existence: a non-open prime is dominated by an analytic height-1 continuous valuation, built via the convex-subgroup retraction $\operatorname{Spv}(A) \to \operatorname{Spv}(A, I)$ of 7.1.2) gives $v$ with $\mathfrak m \le \operatorname{supp} v$. **This containment form is fully proved (no `sorry`) in the project**, under the hypothesis $A^+ \subseteq P_0$. ∎

**Theorem 5.5 (unit criterion 7.52(2), containment form — axiom-clean).** For a complete affinoid with $A^+ \subseteq P_0$: $f$ is a unit iff $v(f) \ne 0$ for all $v \in \operatorname{Spa}$. *Sketch.* A non-unit $f$ lies in a maximal $\mathfrak m$; Theorem 5.4 gives $v$ with $\mathfrak m \le \operatorname{supp} v$, so $f \in \operatorname{supp} v$, i.e. $v(f) = 0$. **Only the containment $\mathfrak m \le \operatorname{supp} v$ is used** — not exact support — so no rank-1 domination is needed. ∎

**Theorem 5.6 (Banach OMT — Wedhorn 6.16, σ-compactness-free).** For complete Tate $A$, a surjective continuous $A$-linear map between finite free modules is open. *Sketch.* The "units tend to 0" dilation cover replaces the σ-compactness hypothesis (unfulfillable for $A^n$ over a Tate algebra); matrix Nakayama + the dilation argument. **Proved, axiom-clean.** This feeds the inducing half of the embedding leaf (6.18).

### Recent activity
The flatness branch (Leaf A) and the faithful localisation-lift bundle were completed/re-wired in the last several sessions; the project builds (≈ 9800 compilation units) with the remaining gaps isolated as named leaves (§8). The containment-form Spa-point and unit criteria are axiom-clean.

---

## 6. In progress / 7. Targets — the three leaves of the headline

| Leaf | Mathematical content | Wedhorn | Status |
|---|---|---|---|
| **Leaf A — restriction flatness** | $\mathcal{O}_X(D)\to\mathcal{O}_X(D')$ flat | Prop. 8.30 + Rem. 7.55 | **Complete**, modulo the two §8 criteria leaves below |
| **Leaf A′ — localisation-lift bundle** | $s$ a unit, $t/s$ power-bounded in completions | Prop. 7.52 | Reduced to [Hu2] 3.3 (external) + Spa-point existence (§8.1) |
| **Leaf B — embedding** | $\mathcal{O}_X(V)\hookrightarrow\prod\mathcal{O}_X(U_i)$ topological embedding | Cor. 8.32 | Injective half rests on Leaf A (faithful flatness, maximals criterion); inducing half on Banach OMT 6.18 (built on the proved 6.16) |
| **Leaf C — gluing / acyclicity** | Čech complex of a rational cover is acyclic | Lemma 8.34 + Prop. A.3 + Lem. 7.54 | Whole-space chain proved sorry-free; general-base via R2-transport (Prop. 8.16) |

The injective half of Leaf B and Leaf C both consume Leaf A. So **Leaf A′ (the localisation-lift bundle) is the current pacing item**, and within it, the single unresolved branch is the Spa-point existence at completion level (§8.1) — everything else is either proved or a Wedhorn-external cite.

---

## 8. Where we're stuck

### 8.1. The `A⁺ ⊆ A°` encoding gap (the main question)

The faithful unit criterion (Theorem 5.3, unit half) needs, for the affinoid ring $B' = \mathcal{O}_X(D')$ on which it is applied, a Spa-point $v$ with $\mathfrak m \le \operatorname{supp} v$ **lying in $\operatorname{Spa}(B', (B')^+)$**, i.e. with $v((B')^+) \le 1$. The axiom-clean containment result (Theorem 5.4) delivers exactly this — *but only under the hypothesis $A^+ \subseteq P_0$ for a ring of definition $P$* (call this the "pair hypothesis").

The trouble: $B'$ is a **completion** (and in the flatness chain, a *two-level* completion — a rational localisation of a completion). For such $B'$ the strong pair hypothesis $A^+ \subseteq P_0$ (our `CompatiblePlusSubring`, Def. 4.3) is **false**. So the faithful path was written "pair-free", which pushed the obligation onto a *bare* Spa-point existence statement
$$\text{(bare) } \mathfrak m \text{ maximal, non-open } \Rightarrow \exists\, v \in \operatorname{Spa}(A, A^+),\ \operatorname{supp} v = \mathfrak m,$$
stated only with the bare-subring class of Definition 4.2.

This bare statement is **false as written**, because the bare class allows $A^+ = A$ (the whole ring is a subring), and for a Tate ring $\operatorname{Spa}(A, A) = \varnothing$ (the uniformiser $\varpi$ has $v(\varpi) < 1$, forcing $v(\varpi^{-1}) > 1$, violating $v(A^+) \le 1$; concretely $A = \mathbb{Q}_p$, $A^+ = A$, $\mathfrak m = (0)$). So it has a genuine counterexample.

But — and this is the user's observation that prompted the review — **the counterexample is not a real affinoid ring**: $A^+ = A \not\subseteq A^\circ$ violates Definition 7.14(1). The *correct* hypothesis is the **weak, always-true-by-definition** condition $A^+ \subseteq A^\circ$ (Remark 7.15(1)), which is strictly weaker than the false pair hypothesis $A^+ \subseteq P_0$. With $A^+ \subseteq A^\circ$ in hand, any *continuous* valuation $v$ automatically satisfies $v(A^+) \le v(A^\circ) \le 1$ (a power-bounded element cannot have valuation $> 1$ for a continuous valuation), so the analytic point from Wedhorn 7.45 lands in $\operatorname{Spa}(A, A^+)$ without needing the pair hypothesis at all.

So the fix is to thread the **definitional** condition $A^+ \subseteq A^\circ$ (Definition 4.1) rather than the false-for-completions $A^+ \subseteq P_0$ (Definition 4.3). The remaining design question (§9, Q1) is *how* to carry $A^+ \subseteq A^\circ$ in the encoding, and (Q2) whether the completed plus-subring of $\mathcal{O}_X(D)$ provably satisfies it.

### 8.2. Deep external leaves (cited, not reproved — confirm these are legitimate black boxes)
- **[Hu2] 3.3** (Wedhorn 7.18(1)): $|f(x)| \le 1\ \forall x \in \operatorname{Spa} \Rightarrow f \in A^\circ$. Wedhorn cites it without proof.
- **[Hu2] 3.9** (Wedhorn 7.48): the completion map $\operatorname{Spa}\hat A \to \operatorname{Spa} A$ injectivity used in the rational-subset comparison.
- **[Hu3] 2.6** (Wedhorn 7.54): the cover-refinement lemma feeding Leaf C.

### 8.3. Banach OMT inducing-half wiring (Leaf B)
The σ-compactness-free 6.16 is proved (Theorem 5.6); the closure-form 6.18(2) and its use in the embedding's "inducing" half is the remaining wiring on Leaf B (a Pettis-type lift step, for which we are following [Henkel 2014]).

---

## 9. Open questions for the reviewer

**Q1 — Encoding the ring-of-integral-elements axiom.** We need $A^+ \subseteq A^\circ$ (Def. 7.14(1)) available wherever Spa-point existence / the unit criterion is used. Three options:
  (a) **bundle** the three Def.-7.14 axioms (open, integrally closed, $\subseteq A^\circ$) into the basic `A⁺` carrier, so every affinoid ring carries them automatically;
  (b) carry "**$A^+$ is a ring of integral elements**" as a separate hypothesis on the lemmas that need it, discharged per use-site;
  (c) **derive** it for each concrete instance.
  Mathematically all three are sound (the condition is always true for a genuine affinoid ring). Is there a reason, from how the theory is *used* downstream (e.g. morphisms of affinoid rings, base change, the perfectoid layer), to prefer one? In Wedhorn's own development the condition is simply part of the definition of an affinoid ring and never re-derived — does that argue for (a)?

**Q2 — Is the completion provably affinoid?** The structure presheaf value $\mathcal{O}_X(D) = A\langle T/s\rangle$ carries a plus-subring defined as the topological closure of the integral elements' images (the "completed plus-subring"). For the fix in §8.1 we need this to be a **ring of integral elements of $\mathcal{O}_X(D)$** — i.e. open, integrally closed, and $\subseteq \mathcal{O}_X(D)^\circ$. The "$\subseteq{}^\circ$" part is what we need; is it automatic (closure of power-bounded images is power-bounded, since $\mathcal{O}_X(D)^\circ$ is closed), or is there a subtlety — particularly at the **two-level / iterated completion** (a rational localisation of a completion) that the flatness chain produces? Is there a clean statement "$\widehat{A^+}$ is a ring of integral elements of $\hat A$" we should be citing (Wedhorn 7.47 handles rings of definition / integral elements under completion — does it give exactly this)?

**Q3 — Exact support vs. containment for a maximal ideal.** An internal note claimed that obtaining the *exact* support $\operatorname{supp} v = \mathfrak m$ (rather than the containment $\mathfrak m \le \operatorname{supp} v$) requires the height-1/rank-1 domination theorem. We believe this is **wrong for a maximal $\mathfrak m$**: since $\operatorname{supp} v$ is a prime ideal $\ne A$ (as $v(1)=1$) and $\mathfrak m$ is maximal, $\mathfrak m \le \operatorname{supp} v \subsetneq A$ already forces $\operatorname{supp} v = \mathfrak m$ — no rank-1 input. (Rank-1 domination is only needed for exact support of a *general* prime.) Is this correct? And for the sheaf proof, is the containment form (which is all the unit criterion consumes) genuinely sufficient everywhere, or is there a downstream consumer that needs exact support of a non-maximal prime?

**Q4 — Pair-free routing: $A^+ \subseteq A^\circ$ vs. $A^+ \subseteq A_0$.** The flatness chain operates on completions, where $A^+ \subseteq A_0$ (a single ring of definition) **fails**, but $A^+ \subseteq A^\circ$ **holds**. Our fix routes the unit/Spa-point criteria through the weaker $A^+ \subseteq A^\circ$. Is this the correct faithful reading of Wedhorn — i.e. does Wedhorn's 7.45/7.51 argument really only use $A^+ \subseteq A^\circ$ (via "continuous $\Rightarrow v(A^\circ) \le 1$"), and is the appearance of a specific ring of definition $A_0$ in the formalised 7.45 an artifact of our proof rather than of the mathematics? More broadly: is there any place in the 8.28(b) proof where a single ring of definition containing $A^+$ is genuinely needed (so that the "pair-free" reformulation is actually *unfaithful* and we should instead prove that completions do admit such a ring of definition)?

**Q5 (strategic, optional).** Is the overall decomposition — sheafiness $\Leftarrow$ (embedding via Cor. 8.32 + flatness) $\wedge$ (gluing via Lemma 8.34 + Laurent-cover acyclicity), with flatness via the Remark-7.55 chain — the cleanest route, or would you reduce 8.28(b) differently (e.g. directly via Tate's acyclicity for the standard rational cover, or via a descent argument that sidesteps the per-step localisation-lift bundle)?

---

## 10. Document metadata

- Project: faithful Lean 4 / Mathlib formalisation of Wedhorn's adic spaces, targeting Theorem 8.28(b).
- Brief generated: 2026-06-18.
- Build status: compiles (~9800 units); open leaves are isolated named results — Spa-point existence at completion level (§8.1), the three external cites (§8.2), the Leaf-B inducing wiring (§8.3).
- Recent context: Leaf A (restriction flatness) completed; faithful localisation-lift bundle re-wired into the chain; containment-form Spa-point/unit criteria are axiom-clean; the `A⁺ ⊆ A°` encoding gap (§8.1) is the current decision point.

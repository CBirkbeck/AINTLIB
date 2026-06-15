# Review brief — Lean 4 formalisation of adic spaces (Wedhorn 8.28(b) / sheafy critical path)

*Prepared 2026-05-27 for a senior expert in adic spaces / rigid analytic geometry. Self-contained: no repo access required. Standard Wedhorn / Huber notation throughout (Spa, Spv, R(T/s), A⁺, A°, A∘∘).*

*This is round 5 of the consultation on this project. Rounds 1–4 produced the Route C / Banach OMT scaffold for the embedding clause of `IsSheafy` and confirmed the Tate-absorbing OMT path (Henkel 2014 = Bourbaki BTVS Ch. I §3 Lemma 2). The Tate-absorbing OMT chain is now axiom-clean. The current session ran a Round-7 sub-ticket decomposition for the remaining IsContinuous and Hom-presheaf obligations and surfaced two ticket-statement defects. This brief asks for strategic guidance.*

---

## 1. Goal

We are formalising adic spaces in Lean 4 (built on Mathlib), following Wedhorn's *Adic Spaces*. The principal target is **Wedhorn Theorem 8.28(b)**: for a strongly noetherian Tate affinoid ring $(A, A^+)$, the structure presheaf $\mathcal{O}_X$ on $X = \operatorname{Spa}(A, A^+)$ is a sheaf — i.e. $(A, A^+)$ is *sheafy*. The intermediate landing is the `IsSheafy` typeclass: a pair $(A, A^+)$ is sheafy when the product-restriction map for every rational covering $\mathcal{C}$ is a topological embedding (separation + closed image) AND every compatible family of sections glues uniquely.

The embedding (separation) clause is being attacked via the Banach open-mapping route — the closed-image side reduces to (i) injectivity of the product restriction (Wedhorn Cor 8.32 + faithful flatness) and (ii) openness of the corestricted map onto the equalizer (Tate-absorbing OMT). The gluing clause reduces via Wedhorn 8.34 / Hübner Lemma 3.8 standard-cover reduction to flat descent on Laurent refinements.

Roughly half of the project's currently open obligations are on this critical path; the other half are upstream support (valuation spectra, continuous valuations, Huber rings, localisation topology) which is essentially in place.

We are asking for **strategic guidance**: at ~125 remaining sorries, are we attacking 8.28(b) the right way, or is there a cleaner architectural approach we are missing? Two specific ticket-statement defects, surfaced during the current session, also need a resolution route.

---

## 2. Background and references

### 2.1. Setting

Standing notation (Wedhorn / Huber):

- $A$ — a topological commutative ring. We work with `IsHuberRing A` (= f-adic) and `IsTateRing A` (Huber + topologically nilpotent unit).
- $A^+ \subseteq A$ — a ring of integral elements, supplied by a `PlusSubring A` instance.
- $A^\circ \subseteq A$ — the subring of power-bounded elements; $A^{\circ\circ}$ its ideal of topologically nilpotent elements.
- $\operatorname{Spv}(A)$ — the valuation spectrum (equivalence classes of valuations $v : A \to \Gamma_v \cup \{0\}$).
- $\operatorname{Spa}(A, A^+) \subseteq \operatorname{Spv}(A)$ — the adic spectrum: continuous valuations $v$ with $v(A^+) \le 1$. Topologised by rational opens.
- $R(T/s) := \{ v \in \operatorname{Spa}(A, A^+) : \forall t \in T,\ v(t) \le v(s) \ne 0 \}$ — rational open for a finite set $T \subseteq A$ and $s \in A$ with $T$ generating an open ideal modulo a pair of definition.
- $v(a)$ — the value; $v.\mathrm{supp} := \{a : v(a) = 0\}$ — the support, a prime ideal of $A$; $\Gamma_v$ — value group.
- $\mathcal{O}_X$ — the presheaf $U \mapsto \mathcal{O}_X(U)$ on $X = \operatorname{Spa}(A, A^+)$, valued in `CompleteTopCommRingCat` (complete topological commutative rings). On a rational open $U = R(T/s)$, $\mathcal{O}_X(U) = A\langle T/s \rangle$ (completed localisation).

The project carries a `PairOfDefinition` $P = (A_0, I)$ — a ring of definition $A_0 \subseteq A$ (an open subring with an open finitely-generated ideal $I$) — and uses $P.I$, $P.A_0$, $P.\mathrm{idealOfDefinition}$ throughout. Rational localisation data is bundled as `RationalLocData A` carrying $P$, a finite $T \subseteq A$, an $s \in A$, and an `hopen` witness that $P.I^N \cdot A \subseteq P.A_0[T/s, 1/s]$ for some $N$.

### 2.2. References

- **[Wedhorn 2019]** Torsten Wedhorn. *Adic Spaces.* Lecture notes, arXiv:1910.05934v1. Primary reference, especially §6 (Banach OMT for rings with zero unit sequence), §7 (Spv, continuous valuations, valuation rings), §8 (Spa, structure presheaf, sheafiness).
- **[Huber 1994]** Roland Huber. "A generalization of formal schemes and rigid analytic varieties." *Math. Z.* 217, 513–551. Lemma 2.4(i) confirms the Bourbaki BTVS Banach OMT route for Tate rings.
- **[BGR]** Siegfried Bosch, Ulrich Güntzer, Reinhold Remmert. *Non-Archimedean Analysis*. Grundlehren 261, Springer 1984. §3.7.2/1 (BGR Banach OMT) and §3.7.2/2 (noetherian iff every submodule closed) are the upstream sources for Wedhorn 6.16 and 6.17.
- **[Henkel 2014]** Timo Henkel. "An Open Mapping Theorem for rings which have a zero sequence of units." arXiv:1407.5647v2. Student of Wedhorn; writes out the full proof of the Tate-absorbing OMT, generalising Bourbaki *Topological Vector Spaces* (BTVS) Ch. I §3 Lemma 2. Used as the source for our `_sub_lemma_pettis_lift`.
- **[Bourbaki BTVS]** N. Bourbaki. *Topological Vector Spaces*, Chapter I §3 Lemma 2. The classical Cauchy-lift metric proof of the open mapping theorem; the actual source (we had previously and mistakenly cited Bourbaki *General Topology*).
- **[Hübner 2021]** Katharina Hübner. "Adic spaces and perfectoid algebras." Lemma 3.8 = the `localBasisHyp` content (locally, rational opens admit a basis of plus-pieces over the base of a rational covering).
- **[Zavyalov 2024]** "Sheaf condition for affinoid adic spaces." §2.3 standard-cover reduction; cited alongside Hübner Lemma 3.8.
- **[Stacks Project, tag 023N]** Flat descent equalizer (faithful flatness ⇒ equalizer = pullback).

### 2.3. State of the art

Wedhorn 8.28(b) is proved in the literature (Wedhorn, Huber, Hübner, Zavyalov). Our project is a *formalisation* in Lean 4, not a new mathematical result. The novelty (insofar as there is any) is the structural organisation: the project deliberately splits Wedhorn 8.28(b) into a Cor-8.32-via-faithful-flatness separation clause and a Wedhorn-8.34 / Hübner-Lemma-3.8 standard-cover gluing clause, threading the two through a Lean `IsSheafy` typeclass that downstream consumers can rely on.

No part of the formalisation depends on the strongly noetherian assumption in a deep way; the assumption is needed for the Hübner / Zavyalov standard-cover existence (the "local basis hypothesis" `LocalBasisHyp C`) and to get $P.A_0$ noetherian inside the Banach OMT calls. Whether the strongly noetherian assumption can be relaxed (e.g. to noetherian + a topological condition) is an open architectural question; see Q6 below.

---

## 3. Strategy

The plan, as reconstructed from the ticket board and ~6 months of development:

1. **Foundations (DONE).** Define $\operatorname{Spv}(A)$, $\operatorname{Spa}(A, A^+)$, continuous valuations, rational opens, the presheaf $\mathcal{O}_X$ on rational opens. Show $\mathcal{O}_X$ takes values in `CompleteTopCommRingCat` with the localisation topology completed.

2. **Banach OMT machinery (DONE).** Implement the Tate-absorbing Banach OMT following Henkel 2014. The chain `_sub_lemma_pettis_lift → isOpenMap_of_tate_absorbing → RingHom.isOpenMap_of_topologicallyNilpotent_unit` is now axiom-clean (only the standard `propext, Classical.choice, Quot.sound`).

3. **Separation via faithful flatness (Cor 8.32, MOSTLY DONE).** Show the product restriction $\mathcal{O}_X(\operatorname{Spa}(A, A^+)) \to \prod_{D \in \mathcal{C}} \mathcal{O}_X(D)$ is faithfully flat for every rational covering $\mathcal{C}$, hence injective. Used in Lane A of the separation clause. Closed under additional `[IsNoetherianRing P.A_0]` hypothesis (path alpha — see §8.3).

4. **Gluing via flat descent + Laurent refinement (Wedhorn 8.28(b) Part 2, PARTIALLY DONE).** Reduce arbitrary rational covers to Laurent covers via Wedhorn 8.34. Discharge Laurent covers via flat descent (Stacks 023N) applied to Cor 8.32. The reduction's "local basis hypothesis" is the `localBasisHyp_of_strongly_noetherian` leaf (Hübner Lemma 3.8 content).

5. **Topological-inducing keystone via Banach OMT (Route C, MOSTLY DONE).** Show the product restriction onto the equalizer subring is an open map via the Tate-absorbing OMT, giving topological inducing. Combined with closed-image (from separation + completion), this gives the `IsEmbedding` field of `IsSheafy`.

6. **Wedhorn 7.45 dominating-valuation lift (PARTIALLY DONE).** Given a dominating valuation subring $B$ of $\mathrm{FractionRing}(A/\mathfrak{p})$, produce a Spa-point of $A$ in any rational open with support $\ge \mathfrak{p}$. Four of five sub-conditions explicitly proven (~50 LOC inline); the remaining sub-condition is *continuity of the pulled-back valuation* via convex-subgroup restriction.

7. **Path alpha for noetherian rings of definition (CURRENT POLICY).** Take `(P : PairOfDefinition A) [IsNoetherianRing P.A_0]` as an explicit parameter at every Wedhorn-clean sheafy theorem, since strongly noetherian Tate alone does NOT imply $P.A_0$ noetherian (Nagata-style counterexample).

---

## 4. Definitions

### 4.1. Huber and Tate rings

**Definition 4.1.** A topological commutative ring $A$ is a **Huber ring** (= *f-adic*) if there exists an open subring $A_0 \subseteq A$ and a finitely generated ideal $I \subseteq A_0$ such that $\{ I^n : n \in \mathbb{N} \}$ is a fundamental system of open neighbourhoods of $0$ in $A_0$ (and hence in $A$). The pair $(A_0, I)$ is a **pair of definition**.

**Definition 4.2.** A Huber ring $A$ is **Tate** if it admits a topologically nilpotent unit $\pi \in A^\times$.

**Definition 4.3 (PlusSubring class).** A `PlusSubring A` is a choice of subring $A^+ \subseteq A^\circ$ that is open and integrally closed. The project uses this as an abstract typeclass; we do not impose alignment with the canonical $A^\circ$ except where explicitly hypothesised.

### 4.2. Valuation spectrum

**Definition 4.4.** $\operatorname{Spv}(A)$ — the set of equivalence classes of valuations $v : A \to \Gamma_v \cup \{0\}$ where $\Gamma_v$ is a totally ordered abelian group. Topologised by the sets $\{ v : v(a) \le v(b) \ne 0 \}$ as $a, b$ range over $A$.

**Definition 4.5.** $\operatorname{Spa}(A, A^+) := \{ v \in \operatorname{Spv}(A) : v \text{ continuous}, v(a) \le 1 \text{ for all } a \in A^+ \}$.

**Definition 4.6.** For finite $T \subseteq A$ and $s \in A$ with $T \cdot A$ open in $A$, the **rational open** is $R(T/s) := \{ v \in \operatorname{Spa}(A, A^+) : v(t) \le v(s) \ne 0 \text{ for all } t \in T \}$.

### 4.3. Localisation and structure presheaf

**Definition 4.7.** For $D = (P, T, s) \in \mathrm{RationalLocData}\ A$ (a pair of definition $P = (A_0, I)$, a finite $T \subseteq A$, an $s \in A$ with $\exists N,\ \forall b \in P.I^N,\ b/s \in A_0[T/s] \subseteq A[1/s]$), the **local subring** is $\mathrm{locSubring}(D) := A_0[T/s, 1/s] \subseteq A[1/s]$ with the $I$-adic topology induced via the inclusion. The **presheaf value** $\mathrm{presheafValue}(D)$ is the completion of $A[1/s]$ with respect to this topology — equivalently, $A\langle T/s \rangle$ in Wedhorn's notation.

**Definition 4.8.** A **rational covering** of $\operatorname{Spa}(A, A^+)$ is a finite collection $\mathcal{C} = \{D_i\}$ of rational opens with base $D_{\mathrm{base}}$ such that $\bigcup_i R(D_i.T / D_i.s) = R(D_{\mathrm{base}}.T / D_{\mathrm{base}}.s)$.

**Definition 4.9 (IsSheafy).** A pair $(A, A^+)$ is **sheafy** if for every rational covering $\mathcal{C}$:
- (**embedding**) The product restriction $\mathrm{presheafValue}(D_{\mathrm{base}}) \to \prod_{D \in \mathcal{C}} \mathrm{presheafValue}(D)$ is a topological embedding (separation + closed image with the subspace topology).
- (**gluing**) Every compatible family $(f_D)_{D \in \mathcal{C}}$ extends uniquely to a section over $D_{\mathrm{base}}$.

### 4.4. Convex subgroups and restriction

**Definition 4.10.** A **convex subgroup** $H$ of $\Gamma^\times$ (a totally ordered abelian group) is a subgroup closed under the "convexity" property: $a, b \in H$, $a \le x \le b$ imply $x \in H$.

**Definition 4.11 (restrictToConvex).** Given a valuation $v : R \to \Gamma_0$ with $v(r) \le 1$ globally and a convex subgroup $H \subseteq \Gamma^\times$, the **restriction to $H$** is the valuation $v|_H : R \to \mathrm{WithZero}(H)$ defined by
$$v|_H(r) = \begin{cases} 0 & v(r) = 0, \\ v(r) & v(r) \ne 0,\ \mathrm{Units.mk_0}(v(r)) \in H, \\ 0 & v(r) \ne 0,\ \mathrm{Units.mk_0}(v(r)) \notin H. \end{cases}$$

This is the project's `Valuation.restrictToConvex`. The variant `restrictToConvexBounded` weakens the global $v \le 1$ hypothesis to require only that $H$ contains every $v(a)$ with $v(a) \ge 1$.

**Definition 4.12 (convexGenerated).** For $y > 1$ in $\Gamma^\times$, the **convex subgroup generated by $y$** is
$$\mathrm{convexGenerated}(y) := \{ h : \exists n \in \mathbb{N},\ y^{-n} \le h \le y^n \}.$$
This is the smallest convex subgroup containing $y$.

---

## 5. Established results

The project has substantial sorry-free infrastructure. Highlights, ordered by mathematical foundation:

### 5.1. Foundational landings

- **Spv / Spa, rational opens, continuous valuations** (modules ValuationSpectrum, ContinuousValuations, AdicSpectrum, RationalSubsets) — all sorry-free.
- **Huber and Tate rings, localisation topology, presheafValue on rational opens** (HuberRings, LocalizationTopology, Presheaf, AffinoidRings) — substantially sorry-free; remaining sorries are downstream.

### 5.2. The Tate-absorbing Banach Open Mapping Theorem

**Theorem 5.1 (Tate-absorbing OMT, axiom-clean).** Let $f : G \to H$ be a continuous surjective additive group homomorphism between complete topological abelian groups with countably generated uniformities and $H$ Hausdorff, where $G$ and $H$ carry the action of a "Tate-absorbing" pair $(\pi_G, \pi_H)$ — endomorphisms with $\pi_H$ topologically nilpotent on $H$, intertwining $f$, with $\pi_H$ acting absorbingly (every neighbourhood of $0$ in $H$ contains $\pi_H^n y$ for $n$ large enough). Then $f$ is open.

*Sketch.* The proof follows Henkel 2014 = Bourbaki BTVS Ch. I §3 Lemma 2. Step 1 (Prop 1.9, at-every-scale closure-image-nbhd): split a symmetric neighbourhood $V$, use Baire on $H$ ($H = \bigcup_n \pi_H^{-n}(\overline{f(V)})$ via absorption, so by Baire one of these is not meagre, hence has nonempty interior; symmetrising and adding then gives that $\overline{f(V)}$ is a neighbourhood of $0$). Step 2 (Prop 1.10, metric Cauchy lift): for $y \in \overline{f(V_0)}$, build $\sigma_n \in G$ recursively so that $y - f(\sigma_n) \in \overline{f(V_n)}$ where $V_n$ is an antitone basis of nhds of $0$ in $G$; the Cauchy property of $\sigma_n$ uses the radius-halving of the $V_n$, and the limit in $G$ (using $G$ complete) maps to $y$. ∎

This theorem, with its consumer `RingHom.isOpenMap_of_topologicallyNilpotent_unit` for ring homs into Tate rings, is the keystone of the Banach-OMT-route for Wedhorn 8.28(b)'s embedding clause.

### 5.3. Spa-point construction from a non-open prime

**Theorem 5.2 (`exists_spa_point_via_restrictToConvex`).** Let $A$ be a Huber ring with pair of definition $P = (A_0, I)$, and $\mathfrak{p}$ a non-open prime of $A$ with $A^+ \subseteq A_0$. Then there exists $v \in \operatorname{Spa}(A, A^+)$ with $\mathfrak{p} \le v.\mathrm{supp}$ and $P.I \not\subseteq v.\mathrm{supp}$.

*Sketch.* By the project's `exists_valuationSubring_of_prime`, we obtain a valuation subring $V_0$ of $\mathrm{FractionRing}(A/\mathfrak{p})$ that dominates the image of $A_0$ and has the image of $P.I \cdot A_0$ in its non-units. We extract an element $a_0 \in P.I$ with $V_0(\phi(a_0)) \ne 0$ (non-open prime hypothesis), set $u_{\max} := V_0(\phi(a_0))$ (after possibly replacing $a_0$ by a sup over $P.I$ generators), and form the convex subgroup $H := \mathrm{convexGenerated}(u_{\max}^{-1})$. The restricted valuation $v_r := (V_0 \circ \phi)|_H$ extends from $A_0$ to $A$ by the `vExtFun` construction (Wedhorn Lemma 7.44(3): $v_{\mathrm{ext}}(a) := v_r(s^n a) \cdot v_r(s)^{-n}$ for $a \in A$ and $n$ large enough that $s^n a \in A_0$). Continuity of $v_{\mathrm{ext}}$ follows from $H$ being generated by $u_{\max}^{-1}$ — the cofinal property `exists_inv_pow_lt_of_mem_convexGenerated` gives that powers of $u_{\max}$ are cofinal at $0$ in $\mathrm{WithZero}(H)$, which together with $P.I$ bounded by $u_{\max}$ gives the topological condition. ∎

This is `Lemma745.exists_spa_point_via_restrictToConvex` (~500 LOC) and is the project's most substantial sorry-free Spa-point existence theorem.

### 5.4. Wedhorn Theorem 6.16 (BGR Banach OMT for $A$-modules)

Proved sorry-free using the additive-group form: any continuous surjective $A$-linear map between complete countably-generated topological $A$-modules is open. The $A$-linearity is not used in the openness proof.

### 5.5. Faithful flatness of the product restriction (Cor 8.32 chain)

**Theorem 5.3 (`productRestriction_faithfullyFlat_tate`).** For a strongly noetherian Tate affinoid $A$ with $P.A_0$ noetherian, the product restriction $\mathrm{presheafValue}(D_{\mathrm{base}}) \to \prod_{D \in \mathcal{C}} \mathrm{presheafValue}(D)$ over a rational covering is faithfully flat.

*Status.* Closed under `[IsNoetherianRing P.A_0]` explicit hypothesis. The injective corollary `productRestriction_injective_tate_via_prime_extension_closed` discharges the Lane-A separation, with one pointwise-closedness hypothesis on prime extensions in the localisation topology.

### 5.6. Standard-cover reduction (Wedhorn 8.34)

**Theorem 5.4 (`tateAcyclicity_Part2_end_to_end`).** For a strongly noetherian Tate affinoid with a local-basis hypothesis on the rational covering $\mathcal{C}$, the gluing clause of `IsSheafy` holds for $\mathcal{C}$.

*Status.* The standard-cover machinery is in place (Lane C). The remaining content is `localBasisHyp_of_strongly_noetherian` (currently sorried) which encodes Hübner Lemma 3.8 / Wedhorn 8.34's local-basis property.

---

## 6. In progress

### 6.1. Wedhorn 7.45 dominating-valuation-subring lift (`T-PRESHEAF-VALUATIONSUBRING-CHAIN`, PARTIAL)

**Statement.** Given a valuation subring $B$ of $\mathrm{FractionRing}(A/\mathfrak{p})$ with conditions (a) $B$ dominates the image of $A_0$, (b) the image of each $t/s$ for $t \in T$ lies in $B$, and (c) the image of $P.I \cdot A_0$ lies in $B.\mathrm{nonunits}$: produce $v \in R(T/s)$ with $\mathfrak{p} \le v.\mathrm{supp}$.

**Status.** Four of five sub-conditions explicitly proven inline (~50 LOC):
- $\mathrm{supp} \ge \mathfrak{p}$ — via $v$.comap_supp pulling $\mathfrak{p}$ back.
- $A^+ \to 1$ — via $A^+ \subseteq A_0$ and $B.\mathrm{valuation\_le\_one}$ of the dominating $B$.
- $T \le s$ — by hypothesis (b) plus valuation multiplicativity.
- $s \ne 0$ — by hypothesis (b) ($s$ lies in $B$'s range giving $B.\mathrm{valuation}(s) \ne 0$ unless $s \in \mathfrak{p}$, which contradicts the rational-open condition).

The **fifth sub-condition (continuity of the pulled-back valuation)** is the remaining sub-sorry and was decomposed in the current session via a sub-decomposition pass ("Round-7") into three sub-tickets `T-WED-745-CONT-A/B/C`. Sub-ticket A turned out to have a defective signature (see §8.1).

### 6.2. Artin-Rees no-Noeth witness existence (`T-PRESHEAFTATE-ARTIN-REES`, IN PROGRESS)

**Statement.** For each source depth $n$, find a target depth $m$ such that for every $\alpha \in A$ and $k_a \in \mathbb{N}$ with $\mathrm{locLift}_{D_0 \to D}(\mathrm{algebraMap}(\alpha) \cdot (1/D_0.s)^{k_a}) \in \mathrm{locNhd}(D, m)$, there exists $\alpha' \in P.I^{n + k_a \cdot D_0.\mathrm{hopen}}$ with $\mathrm{algebraMap}_A^{A[1/D.s]}(\alpha) = \mathrm{algebraMap}_A^{A[1/D.s]}(\alpha')$.

**Status.** Recently decomposed into four sub-tickets `T-AR-1..T-AR-4`:
- `T-AR-1` Artin-Rees specialisation to $A[1/D_0.s]$ for any ideal $K$ — **DONE this session** (~20 LOC, axiom-clean) via mathlib's `Ideal.exists_pow_inf_eq_pow_smul`.
- `T-AR-2` radical-relation denominator lift — **DONE this session** (~30 LOC, axiom-clean) using uniqueness of inverses + the project's `algebraMap_mul_pow_divByS_eq_one_of_radical_relation`.
- `T-AR-3` per-$n$ witness extraction in $A_0$ — OPEN, the deep step (~100–150 LOC of depth bookkeeping).
- `T-AR-4` final assembly — one-liner once `T-AR-3` lands.

The sub-sorry at the parent theorem `locLift_preimage_target_witness_existence_no_noeth` is the **single root sorry** for the Artin-Rees chain (multiple downstream files delegate to it). Closing `T-AR-3` closes ~5 transitive sorries.

### 6.3. Structure sheaf via Hom-presheaves (`T-STRUCTURESHEAF-ISSHEAF-RESIDUAL`, IN PROGRESS)

**Statement.** The structure presheaf $\mathcal{O}_X$ valued in `CompleteTopCommRingCat` is a sheaf in the sense of mathlib's `Presheaf.IsSheaf`.

**Status.** Refactored this session via `T-SP-SHEAF-A`: the goal reduces (definitionally) to "for every $E \in$ `CompleteTopCommRingCat`, the Hom-presheaf $U \mapsto \mathrm{Hom}(E, \mathcal{O}_X(U))$ is a sheaf of types". The sub-ticket `T-SP-SHEAF-B` would discharge this Hom-presheaf condition but turned out to have a defective signature (see §8.2).

### 6.4. Convex-subgroup IsContinuous chain (`T-WED-745-CONT-A/B/C`, BLOCKED)

See §8.1.

### 6.5. Henkel Prop 1.10 sub-sorry (`T-PETTIS-PROP-1-10`, DONE)

~115 LOC of metric Cauchy lift, completing the Tate-absorbing OMT chain (§5.2). Done in the immediately preceding session.

---

## 7. Targets (not yet attempted)

- `T-LEGACY-TATEACYCLICITY-MIGRATE`: multi-file refactor to migrate two callers (`tateAcyclicity_gluing_via_refinement` and `tateAcyclicity` Part 1) off the B2-FALSE `restrictionMapHom_injective` deprecated theorem toward the correct cover-level `productRestriction_injective_tate_via_prime_extension_closed`. Requires propagating a per-$E$ separation hypothesis through ~30 downstream consumers.
- `T-PRESHEAF-MULARCH-RANKONE`: Wedhorn 7.40(6) rank-1 value-group analyticity chain. Depends on Wedhorn Remark 4.12 (convex subgroup ↔ vertical generizations in $\operatorname{Spv}(K(x))$) which is NOT in Mathlib.
- `T-PRESHEAF-7-42-RESIDUALS`: Wedhorn 7.42 forward/reverse residuals (microbial / height-1).
- Multiple Stacks 00MA chain leaves (AdicCompletionNoetherian).
- ~18 Spv($A$, $I$) spectrality leaves (Sierpinski-vs-Bool topology issues — flagged B2 mostly).

### 7a. Ticket board snapshot (compact)

| Ticket | Mathematical statement | Status |
|---|---|---|
| `T-PETTIS-PROP-1-10` | Metric Cauchy lift (Bourbaki BTVS / Henkel 1.10) | DONE |
| `T-ROUTE-C-OMT` | Tate-absorbing Banach OMT | DONE |
| `T-ROUTE-C-WIRE` | Wire OMT into Route C topological-inducing | DONE |
| `T-AR-1` | Artin-Rees in $A[1/D_0.s]$ for any ideal | DONE (this session) |
| `T-AR-2` | Radical-relation denominator lift | DONE (this session) |
| `T-SP-SHEAF-A` | Presheaf.IsSheaf via Hom-presheaves | DONE (this session) |
| `T-AR-3` | Per-$n$ witness extraction (Artin-Rees deep step) | OPEN |
| `T-AR-4` | Final assembly for no-Noeth witness existence | OPEN |
| `T-LEGACY-TATEACYCLICITY-MIGRATE` | Off-ramp deprecated single-map injectivity | OPEN |
| `T-WED-745-CONT-A/B/C` | Convex-subgroup IsContinuous chain for 7.45 lift | **SIGNATURE-DEFECTIVE** |
| `T-SP-SHEAF-B` | Hom-presheaves of structure sheaf are sheaves of types | **SIGNATURE-DEFECTIVE** |
| `T-PRESHEAF-VALUATIONSUBRING-CHAIN` | Wedhorn 7.45 lift parent (4/5 done; IsContinuous remains) | PARTIAL |
| `T-PRESHEAFTATE-ARTIN-REES` | Parent Artin-Rees chain | PARTIAL |
| `T-STRUCTURESHEAF-ISSHEAF-RESIDUAL` | $\mathcal{O}_X$ sheaf in CompleteTopCommRingCat | PARTIAL |
| `T-PRESHEAFTATE-SURJ/INJ-RESIDUAL` | Single-map surj/inj (B2-FALSE deprecated) | B2-SUPERSEDED |
| `T-PRESHEAF-MULARCH-RANKONE` | Wedhorn 7.40(6) rank-1 microbial theory | OPEN |
| `T-PRESHEAF-7-42-RESIDUALS` | Wedhorn 7.42 forward/reverse | OPEN |
| `T-PRESHEAF-LOCLIFT-COMPLETION` | Wedhorn 7.41 application | OPEN |
| `T-PRESHEAF-SPA-NONOPEN` | Architecturally downstream (Cor 8.32 chain) | OPEN |

Current sorry total: ~125 across the project. About 70 are on the IsSheafy critical path (Wedhorn 7.45 chain, Artin-Rees chain, structure sheaf, Cor 8.32 leaves, standard-cover reduction). The remainder are orthogonal work (ScottishBook puzzles, FarguesFontaine, Perfectoid, CompletedAlgClosure, IntegralStructureSheaf).

---

## 8. Where we're stuck

### 8.1. Defect #1 — Convex-subgroup signature for Wedhorn 7.45 lift IsContinuous (`T-WED-745-CONT-A`)

The Round-7 decomposition proposed the following sub-lemma to enable the `restrictToConvexBounded` construction for the dominating-$B$ lift:

> **Claimed Lemma.** Let $P$ be a pair of definition for $A$, $\mathfrak{p}$ a prime, $B$ a valuation subring of $\mathrm{FractionRing}(A/\mathfrak{p})$ with $P.I$-image in $B.\mathrm{nonunits}$. Then there exists a convex subgroup $H \subseteq B.\Gamma^\times$ such that:
> (i) for every $a \in A_0$ with $1 \le B.\mathrm{valuation}(\phi(a)) \ne 0$, $\mathrm{Units.mk_0}(B.\mathrm{valuation}(\phi(a))) \in H$;
> (ii) for every $a \in P.I$ with $B.\mathrm{valuation}(\phi(a)) \ne 0$, $\mathrm{Units.mk_0}(B.\mathrm{valuation}(\phi(a))) \notin H$.

The intended candidate, mirroring `Lemma745.exists_spa_point_via_restrictToConvex`, is $H := \mathrm{convexGenerated}(u_{\max}^{-1})$ with $u_{\max}$ the finite supremum of valuations on $P.I$'s generators.

**The defect.** Conjunct (ii) is unprovable in Case A (where $\exists a \in P.I$ with $B.\mathrm{valuation}(\phi(a)) \ne 0$). For any nonzero such image $u = B.\mathrm{valuation}(\phi(a)) \le u_{\max} < 1$, the convex subgroup $\mathrm{convexGenerated}(u_{\max}^{-1}) = \{ h : \exists n,\ u_{\max}^n \le h \le u_{\max}^{-n} \}$ contains $u$ once $n$ is large enough that $u_{\max}^n \le u$ (which holds for any $u > 0$, since $u_{\max} < 1$ makes the powers $u_{\max}^n$ converge to $0$). So all nonzero $P.I$-image units ARE in $H$, contradicting (ii).

In the Lemma745 proof, $\mathrm{convexGenerated}(u_{\max}^{-1})$ does NOT exclude $P.I$ units — it INCLUDES $u_{\max}$ and ensures $u_{\max}^n$-cofinality at $0$ in the restricted value group, which is what the continuity proof for $v_{\mathrm{ext}}$ actually exploits via `exists_inv_pow_lt_of_mem_convexGenerated`. The "$P.I$ excluded from $H$" framing was a misreading of `restrictToConvex`'s semantics: it sends to $0$ values whose units are outside $H$, BUT the values that need to land at $0$ to keep $v_{\mathrm{ext}}$ continuous are actually the *large* ones (above the cofinal level), not all $P.I$-image values.

**Resolution candidates (asking the reviewer):** see Q1 below.

### 8.2. Defect #2 — Hom-presheaf sheaf condition with discrete-topology placeholder (`T-SP-SHEAF-B`)

The project's structure presheaf $\mathcal{O}_X$ on $X = \operatorname{Spa}(A, A^+)$ is constructed via locally-fraction sections $\mathrm{sectionsSubring}(U)$ equipped with the **discrete uniformity** (`sectionsUniformSpace U := ⊥`). The project docstring acknowledges this is a placeholder: "the correct topology for non-rational opens is the limit topology over rational covers, requires substantial additional infrastructure".

The Round-7 sub-ticket `T-SP-SHEAF-B` proposed proving that for every $E \in$ `CompleteTopCommRingCat`, the Hom-presheaf $U \mapsto \mathrm{Hom}_{\mathrm{cts.\ ring}}(E, \mathrm{sectionsSubring}(U))$ is a sheaf of types over `Opens.grothendieckTopology(SpaTop A)` (i.e. the full topology of $\operatorname{Spa}(A, A^+)$, including arbitrary infinite open covers).

**The defect.** With discrete target, continuous ring homs $E \to \mathrm{sectionsSubring}(U)$ have OPEN kernels. For an arbitrary (possibly infinite) open cover $(U_\alpha)$ in the full topology, gluing a compatible family $(f_\alpha : E \to \mathrm{sectionsSubring}(U_\alpha))$ produces a global $f$ with $\ker(f) = \bigcap_\alpha \ker(f_\alpha)$ — an infinite intersection of open ideals, NOT generally open in a non-discrete $E$. Concrete counterexample: $A$ = Tate ring with non-discrete topology, $E = A$ with its own non-discrete topology, an infinite cover whose kernels intersect down to $\{0\}$; the global hom would have kernel $\{0\}$, open only if $E$ is discrete.

Hence "Hom-presheaf is a sheaf over the full Opens topology" is FALSE under the project's placeholder discrete topology.

The intended correct statement is "Hom-presheaf is a sheaf over the **rational-cover site**" (finitely-indexed covers only); this is Wedhorn 8.28(b) itself. Replacing the discrete topology by the limit topology over rational covers — also acknowledged in the docstring — would repackage the entire goal.

**Resolution candidates:** see Q2 below.

### 8.3. Defect #3 (long-standing) — Noetherian ring of definition from strongly noetherian Tate (`_aux_noeth_A0_generic_of_stronglyNoetherianTate`, path-alpha decision)

The project initially attempted to derive "every ring of definition $P.A_0$ is noetherian" from `[IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]`. This was the natural decomposition for Wedhorn 6.18 (canonical topology / open mapping for fg modules) which needs $P.A_0$ noetherian.

**The defect.** "Strongly noetherian Tate ⇒ every $P.A_0$ noetherian" is NOT in Wedhorn and is false in general: localisation-descent ($A = A_0[1/s]$, $A$ noetherian) does NOT imply $A_0$ noetherian (Nagata-style examples). Wedhorn 6.18 itself is about open-mapping for fg modules over a complete noetherian Tate ring — it says nothing about ring-of-definition noetherianness.

**Current resolution (path alpha).** Take `(P : PairOfDefinition A) [IsNoetherianRing P.A_0]` as an **explicit parameter** at every Wedhorn-clean `IsSheafy` theorem. This propagates through `productRestriction_faithfullyFlat_tate`, the Banach-OMT consumers, the standard-cover reduction, etc.

**Status.** Several B2-SUPERSEDED markers remain in the codebase (`_aux_noeth_A0_generic_of_stronglyNoetherianTate`, `isNoetherianRing_A_0_of_stronglyNoetherianTate_proof`, etc.) — all carrying `sorry` bodies and explicit "RETIRED — false" docstrings. Caller migration to the path-alpha explicit-hypothesis form is incomplete.

**Asking the reviewer:** is path alpha really the right call long-term, or is there a partial recovery (e.g. for the principal pair, under additional Tate hypotheses) we are missing? See Q3 below.

### 8.4. The deep Artin-Rees gap (`locLift_preimage_target_witness_existence_no_noeth`)

The genuine algebraic content of the no-Noeth-source Artin-Rees + denominator-clearing argument. Discharged in the Noeth-source case via the standard Artin-Rees on $A_0$ machinery; the no-Noeth-source version (`T-AR-3`) needs the Artin-Rees on $A[1/D_0.s]$ combined with the radical-relation translation. We have laid the groundwork (`T-AR-1`, `T-AR-2` landed this session), but the per-$(α, k_a)$ depth bookkeeping is genuinely complex (~100–150 LOC).

The crux: given $\mathrm{algebraMap}_A^{A[1/D.s]}(\alpha \cdot e_0^{k_a}) \in \mathrm{locNhd}(D, m)$ in the target localisation, the conclusion requires $\alpha' \in P.I^{n + k_a \cdot D_0.\mathrm{hopen}}$ with $\mathrm{algebraMap}(\alpha) = \mathrm{algebraMap}(\alpha')$ — note the conclusion is about $\alpha$, not $\alpha \cdot e_0^{k_a}$. The "stripping" of the $e_0^{k_a}$ factor and the depth-tracking through the kernel of the localisation are the steps we don't yet have.

---

## 9. Open mathematical questions for the reviewer

**Q1. Resolution route for the Wedhorn 7.45 lift IsContinuous defect (§8.1).** Three candidates:
- **(a) Adapt `Lemma745.exists_spa_point_via_restrictToConvex` directly.** Generalise that lemma's $V_0$-from-Chevalley to an arbitrary dominating $B$, and replace the conclusion "$v \in \operatorname{Spa}$ with $\mathfrak{p} \le v.\mathrm{supp}$" by "$v \in R(T/s)$ with $\mathfrak{p} \le v.\mathrm{supp}$". Single bigger ticket (~200 LOC).
- **(b) Re-decompose with corrected semantics.** Sub-ticket A produces $(H, u_{\max} \in H)$ with the cofinal property `exists_inv_pow_lt_of_mem_convexGenerated`; sub-ticket B builds `restrictToConvexBounded`; sub-ticket C does the continuity discharge.
- **(c) Park; investigate a different route.** Wedhorn 7.45 IsContinuous remains a sub-sorry; we focus on Artin-Rees instead.

Which route would you recommend? Is the Lemma745 generalisation (a) safe — i.e. does the convex-subgroup pattern really transfer cleanly from the Chevalley-produced $V_0$ to an arbitrary dominating $B$, or are there subtleties (e.g. needing additional hypotheses on $B$) we are missing?

**Q2. Resolution route for the Hom-presheaf sheaf-condition defect (§8.2).** Three candidates:
- **(a) Restate over rational-cover site only.** Build a Grothendieck topology on $\operatorname{Spa}(A, A^+)$ whose covers are exactly the rational covers (finite by construction). Show the Hom-presheaf is a sheaf there. Add a site-comparison argument to lift to the full Opens topology.
- **(b) Replace the discrete topology placeholder by the limit topology over rational covers.** This is the project's stated long-term plan but effectively repackages the whole Wedhorn 8.28(b) goal (each $U$'s section ring is defined as a limit over rational covers of $U$; the sheaf-condition is then a tautology).
- **(c) Bypass — extract `IsSheafy` from $(A, A^+)$ directly without going through `Presheaf.IsSheaf`.** The project actually only needs the `IsSheafy` typeclass for downstream consumers; the `Presheaf.IsSheaf` formulation may be vestigial.

Which route is the right architectural call? Is there a fourth option (e.g. a relativised sheaf condition over a known affine site, lifted via Yoneda) we should consider?

**Q3. Path-alpha decision for noetherian $P.A_0$ (§8.3).** Currently every Wedhorn-clean sheafy theorem takes `(P : PairOfDefinition A) [IsNoetherianRing P.A_0]` as an explicit parameter. Is this the right long-term decision? Specifically:
- For the **principal pair** $P_{\mathrm{princ}} = (A^\circ, A^{\circ\circ})$ in a strongly noetherian Tate ring, can we deduce $P.A_0 = A^\circ$ noetherian from the strongly noetherian Tate hypothesis (perhaps with additional structural assumptions like $A^+ = A^\circ$)?
- Are there Wedhorn-clean variants that bypass the noetherian-$A_0$ requirement entirely (e.g. via a different open-mapping route that uses only $A$ being noetherian)?

**Q4. Architecture of the IsSheafy critical path.** With ~70 sorries remaining on the path (Wedhorn 7.45 chain ~10, Artin-Rees chain ~5, structure sheaf ~3, Cor 8.32 leaves ~6, standard-cover reduction ~9, plus assorted), is our current decomposition (Cor 8.32 + flat descent for separation; standard-cover + Hübner 3.8 for gluing; Tate-absorbing OMT + restrictToConvex for inducing) the right one? Is there an alternative architecture (e.g. via Huber's original construction in [Huber 1994] or via a more direct sheafification of the rational presheaf) that would replace several of these sorries with a single deeper theorem?

**Q5. Is the convex-subgroup `restrictToConvex` pattern (Lemma745) really the canonical route?** The Lemma745 proof is ~500 LOC of convex-subgroup gymnastics. Wedhorn 7.45 in the textbook is much shorter (~1 page). Is there an alternative Spa-point construction (e.g. via "Chevalley extension" of the valuation directly, without going through the convex-subgroup restriction) that would be more Lean-friendly?

**Q6. Where does the strongly noetherian Tate hypothesis genuinely bite?** We use it in:
- The `LocalBasisHyp` for the standard-cover reduction (Hübner 3.8 / Wedhorn 8.34).
- The `productRestriction_faithfullyFlat_tate` chain (via locSubring noetherianness).
- The Banach OMT applications (Wedhorn 6.16, but only via the σ-compact / countably-generated machinery).

For each, is the strongly noetherian assumption tight, or could we relax to noetherian + a topological condition (e.g. σ-compact)?

**Q7. References — anything we are missing?** We have integrated Wedhorn 2019, Huber 1994, BGR, Henkel 2014, Hübner, Zavyalov, and Stacks 023N. Are there other treatments of Wedhorn 8.28(b) (e.g. SGA, recent perfectoid-spaces literature, Bhatt–Scholze) that would suggest a different decomposition or fill in a key step?

---

## 10. Auxiliary technical results (appendix)

For completeness, statements of lemmas the reviewer may want to spot-check but need not read in detail:

- **`Valuation.restrictToConvex_lt_one_of_val_lt_one`**: if $v(r) < 1$ in $A$, then $v|_H(r) < 1$ in $\mathrm{WithZero}(H)$ — regardless of whether the unit class of $v(r)$ lies in $H$ (in the "out" case, $v|_H(r) = 0 < 1$; in the "in" case, $v|_H(r) = v(r) < 1$). Used in the Lemma745 continuity argument.
- **`Valuation.supp_le_restrictToConvex_supp`**: $v.\mathrm{supp} \subseteq (v|_H).\mathrm{supp}$. Used to identify the support of the restricted valuation.
- **`exists_inv_pow_lt_of_mem_convexGenerated`**: for $y > 1$, every $h \in \mathrm{convexGenerated}(y)$ admits $n$ with $y^{-n} < h$. The key cofinal property used for continuity.
- **`algebraMap_mul_pow_divByS_eq_one_of_radical_relation`** (project, T092): $\mathrm{algebraMap}(s_0) \cdot (\mathrm{algebraMap}(e) \cdot (1/s)^N) = 1$ in $A[1/s]$ when $e \cdot s_0 = s^N$. The radical-relation denominator identity.
- **`AddMonoidHom.isOpenMap_of_tate_absorbing`** (project, this session): the Tate-absorbing Banach OMT statement; consumer of `_sub_lemma_pettis_lift`.
- **`Lemma745.exists_spa_point_via_restrictToConvex`** (project, sorry-free): Spa-point construction for a non-open prime using the full convex-subgroup + extension chain. ~500 LOC.

---

## 11. Document metadata

- **Project name.** Lean 4 formalisation of adic spaces (Wedhorn 8.28(b) sheafy critical path).
- **Repo location.** Local; not yet publicly hosted.
- **Lean / Mathlib version.** Lean 4 v4.29.0-rc3 + Mathlib v4.29.0-rc3.
- **Build status at brief time.** `lake build` clean (3144 jobs). 125 sorries remaining; ~70 on the IsSheafy critical path.
- **Brief generated.** 2026-05-27.
- **Brief length.** ~14 pages (≈7,500 words).
- **Most recent landings this session.** `T-AR-1` (Artin-Rees in `Localization.Away`), `T-AR-2` (radical-relation denominator lift), `T-SP-SHEAF-A` (Presheaf.IsSheaf unfolding via Hom-presheaves), plus the discovery of the `T-WED-745-CONT-A` and `T-SP-SHEAF-B` signature defects logged here.
- **Self-containment check.** No file paths, no Lean syntax, all notation defined, all citations used.

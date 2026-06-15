# Review brief — Tate acyclicity / IsSheafy (round 5: the Wedhorn 8.34 construction)

*Prepared 2026-05-13 for ChatGPT Pro (continuing series). Self-contained: no repo access required.*

*This is the fifth brief in the series. Round 4 (also 2026-05-13) reframed the IsSheafy topological-inducing route to follow Wedhorn 8.34's refinement-tree induction. We then ran a session that landed the full tree-induction infrastructure axiom-clean, reducing the IsSheafy-for-arbitrary-C topological-inducing requirement to a single named hypothesis: the constructive existence of a Laurent refinement tree refining every rational cover with appropriate inducing + disjointness predicates. This brief reports the executed work and asks for guidance on the **construction step** itself — turning the textbook proof of Wedhorn 8.34 into a Lean term.*

---

## 1. Goal and recap

The end goal is unchanged: **Wedhorn Theorem 8.28(b)** (strongly noetherian Tate rings are sheafy) and its IsSheafy upgrade (the diagonal restriction is a topological embedding).

Round 4 confirmed:
- Stay on Wedhorn's route, not Zavyalov.
- For Lane C arbitrary-cover topological inducing, build a topological refinement induction mirroring Wedhorn 8.34 — Theorem 5.10 (single-Laurent closer) is a *local induction step*, not a global claim.
- The structure is: (i) embed for 2-cover, (ii) refinement transfer, (iii) Laurent tree from standard cover, (iv) propagate inducing up the tree.

We have now completed (i), (ii), and (iv). The remaining piece is (iii): given an arbitrary rational covering C, **construct** the Laurent refinement tree that refines C with the inducing + disjointness predicates needed to feed the tree-induction theorem. This is the constructive content of Wedhorn Lemma 8.34, and it is the entire focus of this brief.

## 2. Background and references

### 2.1. Setting (recap from prior rounds)

- A is a complete topological commutative ring, **Tate** (admits a topologically nilpotent unit), **strongly noetherian** (Wedhorn 6.36: A⟨X₁,…,X_n⟩ is noetherian for all n), Hausdorff, nonarchimedean. A⁺ ⊆ A is an open integrally closed subring of power-bounded elements.
- Spv(A) is the valuation spectrum; Spa(A, A⁺) ⊂ Spv(A) is the set of continuous valuations v with v(a) ≤ 1 for all a ∈ A⁺.
- A **rational subset** is R(T/s) = {v ∈ Spa(A, A⁺) : v(t) ≤ v(s) ≠ 0 for all t ∈ T}, for T a finite subset of A and s ∈ A with (T, s) generating an open ideal.
- The **structure presheaf** 𝒪_X assigns to R(T/s) the completion of A⟨T/s⟩ with the natural Tate topology.
- A **rational covering** of D₀ = R(T₀/s₀) is a finite family C = (R(Tᵢ/sᵢ))_{i ∈ I} of rational subsets of D₀ whose union covers D₀. In the project, a `RationalCovering` is a structure with a base datum and a Finset of "rational locality data" representing the covering pieces.
- For f ∈ A, the **Laurent cover** at f, denoted laurentCovering D₀ f, is the 2-element rational covering whose pieces are:
  - laurentPlusDatum D₀ f = R(D₀.T ∪ {f}, D₀.s) (the "plus piece", where v(f) ≤ v(D₀.s));
  - laurentMinusDatum D₀ f = R("D₀.T · D₀.s ∪ {1}", D₀.s · f) (the "minus piece", where v(f) ≥ v(D₀.s)).

### 2.2. References

- **[Wed19]** Torsten Wedhorn, *Adic Spaces*. Lecture notes (2019, evolving). Theorem 8.28(b) on pp. 81–85; Lemmas 8.29–8.34 and Appendix A on pp. 104–106.
- **[Zav24]** Bogdan Zavyalov, *Sheafiness of Strongly Rigid-Noetherian Huber Pairs* (arXiv:2102.02776v2, 2024). Not the chosen route per round-4 reviewer guidance.
- **[Hub94]** Roland Huber, *A generalization of formal schemes and rigid analytic varieties* (Math. Z. 1994). Background.
- **[Hüb21]** Katharina Hübner, *Adic Tate twists and Iwasawa cohomology*. Source of the project's Nullstellensatz refinement (refines_by_standard_cover).
- **[Stacks]** Tag 023N (flat descent), Tag 00MA (Noetherian completion). Used elsewhere; not directly cited in the Wedhorn 8.34 construction.

## 3. Executed work since round 4

Between round 4 and this brief, we landed the following (all axiom-clean, depending only on propext, Classical.choice, Quot.sound). The unifying point: the **factorisation isolates Wedhorn 8.34's constructive content as the sole remaining residual** for the IsSheafy topological-inducing side.

### 3.1 Tree data structure

**Definition.** A **Laurent refinement tree over A** is an element of the inductive type with constructors `leaf` and `node(f, L, R)` for f ∈ A and L, R further trees. The type is **unindexed** (it does not bake in a root datum): a `LaurentTree` carries only the labelling tree shape, not the bases at each node.

Interpretation: given a root datum D₀, the **leaves of t at D₀** are computed recursively. leaf gives [D₀]; node(f, L, R) gives L.leaves(laurentPlusDatum D₀ f) ++ R.leaves(laurentMinusDatum D₀ f).

(*Why unindexed?* An indexed `LaurentTree : RationalLocData A → Type` with node's recursive children at computed indices laurentPlusDatum D₀ f / laurentMinusDatum D₀ f triggers a kernel strict-positivity rejection because the indices are noncomputable. The unindexed encoding with a separate interpretation function is the workaround.)

The **tree-induced covering** at root D₀ has base D₀ and covers Finset equal to the set of leaf data. The recursive Finset.union construction makes the node-case definitionally equal to `(L.toCovering plus).covers ∪ (R.toCovering minus).covers`, essential for the union-form homeomorphism feeding the NODE inducing step.

### 3.2 Three predicates on a tree

For a tree t at root D₀:

- **t.Refines C** (the refinement predicate): every leaf datum is contained in some piece of C.covers. Equivalent to "the tree-induced covering refines C in the rational-open sense".
- **t.allSplitsInducing D₀** (the inducing predicate): at every internal node node(f, L, R) reached during the recursion (with its own running base), the 2-cover laurentCovering at-that-base f has a topological-inducing diagonal `productRestrictionSub`.
- **t.allNodesDisjoint D₀** (the disjointness predicate): at every internal node, laurentPlusDatum ≠ laurentMinusDatum at the running base AND the two children's leaf-Finsets are disjoint.

### 3.3 Tree induction theorem (axiom-clean)

**Theorem (`productRestrictionSub_isInducing_via_tree`).** *Let t : LaurentTree A and D₀ a rational locality datum. Suppose t has both `allSplitsInducing D₀` and `allNodesDisjoint D₀`. Then `productRestrictionSub A (t.toCovering D₀)` is topological-inducing.*

*Sketch.* Induction on t. **LEAF**: the tree-induced covering at a leaf is the singleton {D₀}; the diagonal collapses (up to a canonical identification by Subsingleton.elim) to the identity on 𝒪_X(D₀), hence inducing by `induced_id`. **NODE(f, L, R)** at base D₀: the tree-induced covering's covers Finset decomposes definitionally as `(L.toCovering plus).covers ∪ (R.toCovering minus).covers`, and this union is disjoint by hypothesis. The topological homeomorphism `Homeomorph.piFinsetUnion` for disjoint Finsets gives `(∏_{D ∈ L.covers} 𝒪_X(D)) × (∏_{D ∈ R.covers} 𝒪_X(D)) ≃ₜ ∏_{D ∈ union} 𝒪_X(D)`. The 2-cover laurentCovering D₀ f is inducing by `allSplitsInducing` at this node. Pair-form composition with the L and R inducing maps (recursive hypothesis) factors through this homeomorphism, yielding inducing for the union-form product restriction at D₀. ∎

### 3.4 Tree → C transfer (axiom-clean)

**Theorem (`productRestrictionSub_isInducing_via_tree_refinement`).** *For C a rational covering and t : LaurentTree A with t.Refines C.base C, allSplitsInducing at C.base, and allNodesDisjoint at C.base, productRestrictionSub A C is topological-inducing.*

*Sketch.* For each leaf datum D, the refinement hypothesis gives some E_D ∈ C.covers with rationalOpen D ⊆ rationalOpen E_D. Pick such an E_D via classical choice (the **refinementTau** map). The natural product map φ : ∏_{E ∈ C.covers} 𝒪_X(E) → ∏_{D ∈ leaves} 𝒪_X(D), defined by φ(x)_D = restrictionMap E_D D _ (x_{E_D}), is continuous and satisfies φ ∘ productRestrictionSub A C = productRestrictionSub A (t.toCovering C.base). The strengthened topological refinement-transfer lemma `productRestrictionSub_isInducing_of_finer_rational_continuous` (Aux 10.7 in the round-4 reviewer's terminology) then transfers inducing from the finer tree-cover to the coarser C-cover. ∎

### 3.5 Factorisation and IsSheafy composition

**Theorem (`productRestrictionSub_isInducing_of_wedhorn_tree_existence`).** *If for every rational covering C there exists a Laurent refinement tree t with t.Refines C.base C, allSplitsInducing at C.base, and allNodesDisjoint at C.base, then for every C, `productRestrictionSub A C` is topological-inducing.*

**Theorem (`isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence`).** *Given the project's strongly-noeth-Tate typeclass bundle, a pair of definition P, the Spa-point existence hypothesis hSpa (separately supplied by Lemma 7.45 / trivial-valuation construction), AND the tree-existence hypothesis above, A satisfies IsSheafy.*

These theorems isolate the named hypothesis `h_wedhorn` as the sole remaining residual for the IsSheafy topological-inducing side. The algebraic side (separation + gluing) is supplied by the Cor 8.32 product injectivity + flat-descent chain, modulo a routing wrapper.

### 3.6 Concrete witnesses for structural endpoints

- **Singleton covers** (covers = {C.base} or covers = {E} for some E): the leaf tree witnesses, with all predicates vacuously satisfied.
- **2-element Laurent covers** (laurentCovering D₀ f for some f): the depth-1 tree node(f, leaf, leaf) witnesses, given (a) topological-inducing for the 2-cover (supplied by Lemma 8.33 = T279/T291) and (b) plus ≠ minus (supplied by `laurentPlus_ne_laurentMinus_of_nonunit`).
- **Right-branching depth-N**: for any List L = [f₁, …, f_r] and per-level inducing + disjointness witnesses, the right-branching tree (each split's plus side is a leaf, minus continues) witnesses, packaged via two convenience predicates `RightBranchInducing D₀ L` and `RightBranchDisjoint D₀ L` and a packager theorem `exists_for_rightBranchList`.

## 4. The construction question (the focus of this brief)

For an arbitrary rational covering C, we need to produce a Laurent refinement tree t with the three predicates. The textbook proof of Wedhorn 8.34 (pp. 81–85 of [Wed19]) provides the algorithm, but the translation to our tree formalism has not crystallised. The textbook proof (as captured in the project's PDF-extracted notes) is:

**Wedhorn Lemma 8.34, 6-step proof.**

1. The 2-element Laurent cover U_f = {R(f/1), R(1/f)} is acyclic — algebraic content of Wedhorn Lemma 8.33.
2. Restriction of U_f to any rational subset remains acyclic, because rational localisations of strongly noetherian Tate rings stay strongly noetherian Tate.
3. By Wedhorn Proposition A.3(3), finite **products** of 2-covers (Laurent covers U_{f₁} × ⋯ × U_{f_n}) are acyclic.
4. For a standard cover generated by T = (f₀, …, f_n) with (T)·A = A, use Wedhorn Corollary 7.32 to choose a dominating unit s such that the Laurent cover generated by s⁻¹f_i has the property: every restriction of this Laurent cover to a piece V_j of an original cover C is generated by units.
5. A rational cover generated by units is trivially refined (each unit gives the whole base).
6. Combine via Proposition A.3(2) (refinement preserves acyclicity).

The tree's role in our Lean formalism is to **enumerate** the simultaneous Laurent intersections U_{f₁} × ⋯ × U_{f_n} as leaves: a **balanced binary tree** at T has, at each internal node `node(f_i, L_i, R_i)`, two children that are *both* the recursive tree on T \ {f_i} interpreted at distinct bases (laurentPlus and laurentMinus of the parent). The 2^|T| leaves correspond to choices of plus or minus at each f_i, giving the simultaneous Laurent intersections.

Three concrete sub-questions for the reviewer:

## 4.1 Sub-question A — handling the "all-minus" leaf

The balanced binary tree at T has 2^|T| leaves indexed by sign-functions σ : T → {+, −}. For the tree to *refine C* in the project's sense (every leaf contained in some single C piece), each leaf σ must have its corresponding rational open contained in some E_σ ∈ C.covers. The plus-heavy leaves are handled by the project's existing predicate **refines_contain**: for σ with σ(f) = + somewhere, the plus piece at that f is contained in some C-piece by refines_contain.

The problematic leaf is **all-minus**: σ ≡ −, the simultaneous intersection ∩_i {v(f_i) ≥ v(D₀.s)}. For T·A = A (= the standard-cover unit-ideal condition), one might hope this leaf is empty, but it isn't always:

In a strongly noetherian Tate ring A with continuous valuation v of dense value group, take T = {f₁, f₂} with 1 = a₁f₁ + a₂f₂ (so T·A = A). The all-minus piece requires v(f₁) ≥ v(D₀.s) AND v(f₂) ≥ v(D₀.s). Setting v(D₀.s) = 1 for normalisation, this is v(f₁) ≥ 1 and v(f₂) ≥ 1. Combined with 1 = a₁f₁ + a₂f₂ and v(a_i) ≤ 1 (integral valuation): v(1) ≤ max v(a_i f_i) ≤ max v(f_i). So max v(f_i) ≥ 1 — consistent with both v(f_i) ≥ 1.

In particular, the all-minus piece can be nonempty.

Wedhorn's Step 4 says: after Cor 7.32 normalisation, *every restriction of the Laurent cover to a piece V_j of the original cover C* becomes generated by units. This is a statement about restricted covers, not about whether individual all-minus leaves are contained in individual C-pieces. The covering condition "the all-minus piece is covered by *some collection* of C-pieces" is automatic (C covers D₀, hence covers the all-minus subset of D₀), but "contained in a single C-piece" is not.

Our current `t.Refines C` predicate demands per-leaf containment in a single piece. Three possible resolutions:

**(a) Relax `Refines`.** Allow each leaf to be covered by a finite *subset* of C-pieces. The refinementTau map (which currently picks one E_D per leaf) becomes a partial choice function, losing the canonical product comparison map used in §3.4. Downstream consequences would need to be re-derived.

**(b) Inflate the cover.** Replace the tree-induced covering with a *fibred* covering whose pieces are (leaf, C-piece) pairs covering rationalOpen(leaf). The fibred covering's product is bigger but every "piece" is contained in a single C-piece. Equivalent to dimension-trick: instead of the tree leaves being the V of "V finer than C", make the V be {leaf ∩ E : leaf, E ∈ C.covers}.

**(c) Abandon per-leaf and follow Wedhorn directly.** Don't try to formalise `t.Refines C` per leaf. Instead, prove a "tree-cover restricted to each C-piece is trivial" theorem and use Wedhorn's Prop A.3(2) at the whole-cover level. This loses the explicit refinementTau but matches the textbook proof.

**Question A.** Which of (a), (b), (c) does the reviewer recommend? Or is there a fourth option — for example, can the textbook's Step 4 normalisation be sharpened to give per-leaf containment after all, exploiting some property of strongly noetherian Tate rings we haven't used yet?

## 4.2 Sub-question B — balanced tree vs abstract A.3(3) combinator

Our infrastructure commits to an **explicit** Laurent refinement tree with the three predicates, then derives inducing-for-arbitrary-C via §3.4. An alternative would be to skip the tree and directly formalise Wedhorn's Proposition A.3(3):

**Abstract Product Cover Lemma (Wedhorn A.3(3)).** *Let U, V be two finite covers of D₀. If every restriction V|_{U_{i₀…i_q}} of V to a U-intersection is acyclic, then U × V is acyclic iff U is acyclic.*

Iterating this combinator on the Laurent factors gives Wedhorn 8.34 with no explicit tree — the "tree" is then *implicit* in the iteration. The bookkeeping moves from "tree leaves" to "intersection multi-indices σ : Fin (q+1) → ι".

Pros of the abstract combinator route:
- Mathlib-idiomatic: matches the way Čech complexes are typically formalised.
- Avoids the strict-positivity workaround in our LaurentTree type.
- The proof goes through Wedhorn's actual Prop A.3(3) directly.

Cons:
- Loses the explicit per-leaf refinementTau structure that makes §3.4's natural-refinement-map approach work cleanly.
- Requires a richer abstract Čech / finite-cover API than we currently have.
- The bookkeeping (handling multi-index σ in proofs) is heavier.

**Question B.** Is one framing clearly preferable from the reviewer's vantage? If so, which? If both work, is there a principled criterion (matching Mathlib idiom, matching Wedhorn's textbook proof, etc.) that should guide the choice?

## 4.3 Sub-question C — discharging `T-LOCLIFT-PRESERVATION`

Wedhorn's Step 2 requires that rational localisations preserve the "strongly noetherian Tate" property. In our class hierarchy we carry two preservation conditions independently:

- **`IsStronglyNoetherian` preservation under Laurent localisation**: presheafValue D is again strongly noetherian. *Done* — sorry-free under `T-STRONG-NOETH-PRESERVATION`.

- **`HasLocLiftPowerBounded` preservation under Laurent localisation**: presheafValue D again has loc-lift power-bounded elements (the analytic-class data needed to define further restriction maps). *Not done* — pending ticket `T-LOCLIFT-PRESERVATION` (#38 in the task tracker).

The `HasLocLiftPowerBounded A` class asserts, for every pair of rational locality data D' ⊂ D in A:
- algebraMap A → A[D'.s⁻¹] sends D.s to a unit;
- the lifted element t/s (for t ∈ D.T, s = D.s) is power-bounded in A[D'.s⁻¹] with its localisation topology.

To preserve this when passing from A to presheafValue D₀ (an iterated rational localisation of A), we need both pieces to lift through the localisation-completion-localisation tower. The "unitness" piece is bookkeeping (transitivity of localisation). The "power-bounded lift" piece requires that "t/s is power-bounded in presheafValue D₀ [(D'.s)⁻¹]^∧" — which in turn requires:
- An identification of the topology on (presheafValue D₀)[D'.s⁻¹]^∧ with the natural topology on the corresponding rational locality datum over A (= an iterated rational locality datum over A);
- Use of strong noetherianness at the appropriate level to control power-boundedness through completion.

**Question C.** Is there a cleaner formulation of `HasLocLiftPowerBounded` (or its replacement) that makes preservation under rational localisation automatic? For instance:

- Would replacing the explicit "power-bounded lift" by a hypothesis at the level of pairs of definition ("A admits a pair of definition (A₀, I) such that t·s⁻¹ ∈ A₀⟨T'/s'⟩ for every rational locality datum and every t ∈ T") work?
- Is there a known Wedhorn / Hübner / Zavyalov formulation of this analytic-class data that is better-behaved under localisation than our ad-hoc class?

The project's analytic-class encoding was set up *before* we knew preservation would be needed; it now feels like an obstacle rather than a convenience.

## 4.4 Sub-question D — is the factorisation the right framing?

We have factorised the IsSheafy topological-inducing requirement into:

> **For every rational covering C, there exists a Laurent refinement tree t with t.Refines C.base C, allSplitsInducing at C.base, and allNodesDisjoint at C.base.**

This is a clean named hypothesis but it commits to encoding Wedhorn's construction through *this specific* tree formalism with *these specific* three predicates.

The reviewer's round-4 guidance was "build a topological refinement induction mirroring Wedhorn 8.34" — which is what we did. But the factorisation may be too rigid: the predicates `allSplitsInducing` and `allNodesDisjoint` are not literally what Wedhorn's textbook proof produces. Wedhorn produces a *Laurent product cover* (all 2^|T| simultaneous intersections), and applies A.3(2)/(3) directly to it; he doesn't explicitly walk a tree.

**Question D.** Is the current factorisation the right framing for the constructive step, or should we relax the named hypothesis to something more abstract (e.g., "for every C, exists a refining V whose product restriction is inducing, where V's pieces are Laurent intersections")? The latter is weaker and more textbook-faithful; it might be easier to discharge from Wedhorn's actual argument. Discharging it from our tree-induction theorem becomes more work (we'd need to recover a tree structure from any Laurent-intersection V), but this might be cheaper overall.

## 5. Ticket board (compact)

| Ticket | Mathematical statement | Status |
|---|---|---|
| `isSheafy_ofStronglyNoetherianTate_flat` | IsSheafy A under strongly-noeth Tate | conditional on h_wedhorn |
| **`T-LAURENT-REFINEMENT-TREE-EXISTENCE`** | **For every C, exists Laurent tree refining C with inducing + disjointness predicates** | **IN PROGRESS — focus of this brief** |
| `T-LOCLIFT-PRESERVATION` | HasLocLiftPowerBounded preserved under Laurent localisation | OPEN (sub-question C) |
| `T-LANE-C-REFINEMENT-INDUCTION` | Tree-induction gives inducing for arbitrary C | DONE (round-4 advice executed) |
| `T-TREE-INDUCING-NODE` | NODE step of tree induction | DONE |
| `T-LAURENT-REFINEMENT-TREE` | LaurentTree type + leaves + Refines | DONE |
| `T-OV-1` (round-4 named blocker) | Bivariate Example 6.38 | DONE (round-4 advice executed) |
| `T-STRONG-NOETH-PRESERVATION` | presheafValue D is noetherian | DONE |
| `T-FLAT-VIA-WEDHORN830` + `T-COR832-VIA-FLAT` | Faithful flatness of product restriction | DONE |
| `tateAcyclicity` routing wrapper | Move Part 1 separation + Part 2 gluing to a downstream wrapper file | OPEN (mathematical content present; routing residual only) |
| `T-MATHLIB-STACKS-00MA` | Adic completion of noetherian is noetherian | OPEN (external — Mathlib contribution) |

## 6. Where we're stuck (a summary)

The infrastructure surrounding Wedhorn 8.34 is complete: we have a clean axiom-clean reduction from "IsSheafy for arbitrary C" to "Wedhorn 8.34 constructive tree existence". The remaining work is the construction itself, and we have three concrete points of friction (the sub-questions of §4) plus the meta-question of framing (§4.4) plus a textbook-walkthrough request:

- (A) The all-minus leaf of the balanced tree has no a-priori per-leaf C-containment.
- (B) Tree formalism vs abstract A.3(3) combinator — neither is clearly preferable on its face.
- (C) HasLocLiftPowerBounded preservation under localisation is open and the class formulation feels wrong-shaped.
- (D) Whether the tree-with-three-predicates hypothesis is the right named residual, or whether a more abstract statement would be cheaper to discharge.
- (E) Wedhorn's Step 4 (the Cor 7.32 normalisation + "cover by units is trivial" argument) is the part of the textbook proof we understand least concretely — we'd like the reviewer to walk through it with quantifier structure made explicit.

If the reviewer can give us a clear preference on (A) — especially if there's a fourth option we haven't surfaced — a recommendation on (B), (C), and a careful explanation of (E), we believe the Wedhorn 8.34 construction is straightforwardly executable in 1–2 sessions of focused work.

## 7. Specific questions for the reviewer

(Numbered to match §4 sub-questions for cross-reference.)

**Q-A.** The balanced binary tree of a standard cover T = (f₀, …, f_n) with T·A = A has an "all-minus" leaf that can be non-empty (Section 4.1 argument). Our `t.Refines C` predicate demands per-leaf containment in a single C-piece. Of the three resolutions (relax to subcover, inflate via fibred cover, abandon per-leaf for whole-cover A.3(2)), which does the reviewer recommend? Is there a fourth option — e.g., does Cor 7.32's dominating-unit normalisation actually produce per-leaf containment in a non-obvious way?

**Q-B.** Tree-formalism vs abstract A.3(3) combinator. Both can support Wedhorn's argument. The tree gives explicit per-leaf witnesses; the combinator avoids the strict-positivity workaround and matches the textbook proof more directly but needs a richer abstract Čech API. Is there a principled criterion (Mathlib idiom, downstream reuse, etc.) that should guide the choice?

**Q-C.** `HasLocLiftPowerBounded` preservation under Laurent localisation (`T-LOCLIFT-PRESERVATION`) is open and the existing class formulation feels obstructive. Is there a cleaner formulation of the analytic-class data (pair-of-definition-level? Tate-algebra-level?) that is better-behaved under localisation?

**Q-D.** Is the current factorisation (`productRestrictionSub_isInducing_of_wedhorn_tree_existence` with the explicit three-predicate tree-existence hypothesis) the right framing for the constructive step? Or should we relax the named hypothesis to a more abstract statement closer to Wedhorn's textbook formulation (Laurent intersection cover + A.3(2)/(3)), even if this makes the existing tree-induction infrastructure less directly applicable?

**Q-E.** *Walking through Wedhorn's Step 4 in detail.* This is the step we understand least well, and it sits at the heart of Sub-question A. Wedhorn's argument (pp. 83–84 of [Wed19]) reads, roughly:

> *Step 4.* Let T = (f₀, …, f_n) with T·A = A. By Cor 7.32, choose a unit s ∈ A such that v(s) ≤ max_i v(f_i) for every v in Spa(A, A⁺) (equivalently, s is "dominated" by the family T in the valuation sense). Replace each f_i by s⁻¹ f_i. Then for every piece V_j of the original cover C, the restriction of the Laurent cover U_T to V_j is generated by elements that are *units* in 𝒪_X(V_j).

The phrase "generated by units" is geometric: each f_i becomes a unit in 𝒪_X(V_j) for the *specific* j that's "active" at that subset. We have three concrete confusions:

- (E.1) *What is the precise statement of "generated by units"?* Is it "each f_i is a unit in 𝒪_X(V_j) for some V_j", or "for every V_j there is some f_i that is a unit in 𝒪_X(V_j)", or something else? The wording is asymmetric between f_i and V_j and we are not sure which way the quantifiers run.

- (E.2) *Why does the all-minus restriction become "generated by units"?* The all-minus restriction of U_T to V_j is the simultaneous condition v(f_i) ≥ v(s) for all i, AND v inside V_j's rational open. If V_j corresponds to a particular f_j₀ in some standard-cover sense, why does the restriction make every other f_i a unit? Our (incomplete) understanding is that the standard-cover refinement assigns each V_j to a specific f_{i(j)} which is a unit on V_j, and then the "all-minus" branches at the *other* f_i's are absorbed by *the* f_{i(j)} being a unit — but we are guessing.

- (E.3) *How does "cover by units is trivial" actually look in Wedhorn's proof?* Concretely: if every f_i is a unit in some piece V_j, then U_T|_{V_j} consists of (a) plus pieces where some f_i is even *smaller*, and (b) minus pieces where 1/f_i is bounded. With f_i a unit, both pieces become V_j itself, so U_T|_{V_j} reduces to the trivial cover {V_j}. Is this the right picture?

If the reviewer could walk through Step 4 with the f_i ↔ V_j quantifier structure made explicit, this would unblock our Sub-question A (the all-minus leaf framing) directly.

## 8. Auxiliary technical results (appendix)

For spot-checking. All sorry-free.

- **`productRestrictionSub_isInducing_via_tree`** — tree induction (LEAF + NODE).
- **`productRestrictionSub_isInducing_via_tree_refinement`** — tree → C transfer via refinementTau.
- **`productRestrictionSub_isInducing_of_wedhorn_tree_existence`** — factorisation.
- **`isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence`** — full IsSheafy composition (modulo hSpa and h_wedhorn).
- **`exists_for_singleton_cover`**, **`exists_for_singleton_cover_of_eq`**, **`exists_for_laurentCovering`**, **`exists_for_rightBranchList`** — concrete witnesses for depth-0, depth-1, and arbitrary right-branching cases.
- **`Homeomorph.piFinsetUnion`** — the topological upgrade of `Equiv.piFinsetUnion`, the key tool for the NODE step's pair-form-to-union-form transport.
- **`productRestrictionSub_isInducing_of_finer_rational_continuous`** (Aux 10.7 in round-4 terminology) — the strengthened refinement transfer used in §3.4.

## 9. Document metadata

- **Project name:** Adic spaces (Wedhorn formalisation in Lean 4 / Mathlib)
- **Brief generated:** 2026-05-13 (round 5, follow-up to round 4)
- **Length:** ~7 pages, ~3,800 words
- **Build status:** compiles cleanly; the tree-induction infrastructure for IsSheafy is fully axiom-clean. Residual project-wide sorries (~46) are either on orthogonal exploratory chains (off-critical-path) or in the routing wrapper sketch.
- **Session context:** 17 axiom-clean commits in the immediately preceding session, executing round-4's advice on the refinement-tree induction.
- **Recent reviewer guidance (round 4, 2026-05-13):** "Stay on Wedhorn; build a topological refinement induction mirroring 8.34; use Aux 10.7 and Aux 10.8 as the core refinement-transfer tools." Executed — this brief reports the result and asks the follow-up construction questions.

# Review brief — Tate acyclicity / IsSheafy (round 8: post-round-7 revisions)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 7). Self-contained: no repo access required.*

*Compact follow-up to round 7. The round-7 reviewer feedback was applied verbatim: (1) the helper definition gained a piecewise-containment clause; (2) W3's output now includes relative `Refines`; (3) W3-transport consumes the relative refinement; (4) W4 was dropped (the prune theorem was identified as not-true-in-this-generality AND unnecessary). This brief shows the post-round-7 statements and asks for verification.*

---

## 1. What changed since round 7

| Object | Round-7 issue | Round-8 fix |
|---|---|---|
| `restricted_standard_cover_generated_by_units` | Only pointwise covering by standard plus-pieces; missing cover-refinement identification | Added clause (d): **piecewise containment** — for each $f \in I_{\mathrm{units}}$, the A-level reading of the relative unit-piece $R(\mathrm{image}_L(s^{-1}f)/1)$ is contained in $L \cap R(\mathrm{insert}(f, C.\mathrm{base}.T)/C.\mathrm{base}.s)$. |
| W3 | Output only `allSplitsInducing L_rel`; no relative refinement | Output now includes `inner_rel.Refines L_rel unitCover` where `unitCover : RationalCovering (𝒪(L))` is the relative unit-generated cover (taken as parameter). |
| W3-transport | Stronger input expected | Now consumes the relative `Refines L_rel unitCover`. Output unchanged: `inner_abs.allSplitsInducing L ∧ inner_abs.Refines L C`. The descent chain: relative-refines → restricted-standard-cover (via clause (d)) → C (via `refines_contain`). |
| W4 (prune) | Identified as false-in-generality AND unnecessary | **Dropped.** Marked the slot in the file as a comment block noting the pending `EmbeddingTopo.lean` NODE-step refactor (use projection `Π(L∪R) → Π(L)×Π(R)` + absorption lemma). After that refactor, the tree-induction theorem needs only `Refines ∧ allSplitsInducing`, and I.1's conclusion drops `allNodesDisjoint`. |
| I.1's conclusion | Still requires `allNodesDisjoint` (backward-compat) | Unchanged for now; pending `EmbeddingTopo.lean` NODE-step refactor. |

## 2. Revised lemma statements (math + Lean)

### 2.1 The helper definition (round-8)

**Mathematical content.** A subfamily $I_{\mathrm{units}} \subseteq S$ generates the restricted standard cover $U \mid L$ by units in $\mathcal{O}(L)$ if (a) inclusion, (b) units, (c) pointwise cover, AND **(d) piecewise containment**: for each $f \in I_{\mathrm{units}}$, the A-level reading of the relative unit-piece at $\mathrm{image}_L(s^{-1}f)$ — which formally is $\{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\}$ — is contained in $L \cap R(\mathrm{insert}(f, C.\mathrm{base}.T)/C.\mathrm{base}.s)$.

Clause (d) is the cover-refinement-identification content the round-7 reviewer flagged was missing.

**Lean.**
```lean
def restricted_standard_cover_generated_by_units
    (L : RationalLocData A) (C : RationalCovering A) (S : Finset A)
    (s : Aˣ) (I_units : Finset A) : Prop :=
  I_units ⊆ S ∧
  (∀ f ∈ I_units, IsUnit (L.canonicalMap (((s⁻¹ : Aˣ) : A) * f))) ∧
  -- (c) pointwise cover
  (∀ v ∈ rationalOpen L.T L.s, ∃ f ∈ I_units,
    v ∈ rationalOpen (insert f C.base.T) C.base.s) ∧
  -- (d) piecewise containment (NEW in round 8)
  (∀ f ∈ I_units,
    {v ∈ rationalOpen L.T L.s | v.vle f C.base.s} ⊆
      rationalOpen (insert f C.base.T) C.base.s ∩ rationalOpen L.T L.s)
```

### 2.2 W2 (unchanged statement; uses revised definition)

**Mathematical content.** *Let $A$, $C$, $S$ be as before. Then there exist $s \in A^{\times}$ and a balanced Laurent tree $t_{\mathrm{outer}}$ on $((S.\mathrm{toList}).\mathrm{map}(f \mapsto s^{-1} \cdot f))$ such that $t_{\mathrm{outer}}.\mathrm{allSplitsInducing}\ C.\mathrm{base}$ and at every leaf $L$ of $t_{\mathrm{outer}}$ there is a sub-family $I_{\mathrm{units}}(L) \subseteq S$ with $\mathrm{restricted\_standard\_cover\_generated\_by\_units}(L, C, S, s, I_{\mathrm{units}}(L))$ (now with the round-8 piecewise containment clause).*

**Lean.** (Same as round 7, with the definition above now including clause (d).)

### 2.3 W3 (revised: relative refinement output)

**Mathematical content.** *Let $L$ be a sub-base of $C.\mathrm{base}$, $I_{\mathrm{units}}$ satisfying $\mathrm{restricted\_standard\_cover\_generated\_by\_units}$, and $\mathrm{unitCover} : \mathrm{RationalCovering}(\mathcal{O}(L))$ the relative unit-generated cover at the relative base $L_{\mathrm{rel}}$. Then there exists a relative Laurent tree $\mathrm{inner\_rel} \in \mathrm{LaurentTree}(\mathcal{O}(L))$ such that:*

- *$\mathrm{inner\_rel}.\mathrm{Refines}\ L_{\mathrm{rel}}\ \mathrm{unitCover}$ — the relative tree refines the relative unit-generated cover (Wedhorn Step (iii) literally);*
- *$\mathrm{inner\_rel}.\mathrm{allSplitsInducing}\ L_{\mathrm{rel}}$ — every internal split is inducing at the relative level.*

**Lean.**
```lean
theorem unitGeneratedCover_has_relative_ratioLaurentRefinement
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (S : Finset A)
    (_hS_contain : refines_contain C S)
    (s : Aˣ)
    (L : RationalLocData A)
    (_hL_subset : rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s)
    (I_units : Finset A)
    (_h_unit_generated : restricted_standard_cover_generated_by_units L C S s I_units)
    [IsTopologicalRing (presheafValue L)] [PlusSubring (presheafValue L)]
    [IsHuberRing (presheafValue L)] [HasLocLiftPowerBounded (presheafValue L)]
    [IsTateRing (presheafValue L)] [IsNoetherianRing (presheafValue L)]
    [IsStronglyNoetherian (presheafValue L)] [T2Space (presheafValue L)]
    [NonarchimedeanRing (presheafValue L)] [IsDomain (presheafValue L)]
    [DecidableEq (presheafValue L)]
    (L_rel : RationalLocData (presheafValue L))
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover_from_I_units : unitCover.base = L_rel) :
    ∃ inner_rel : LaurentTree (presheafValue L),
      inner_rel.Refines L_rel unitCover ∧
      inner_rel.allSplitsInducing L_rel
```

### 2.4 W3-transport (revised: consumes relative refinement)

**Mathematical content.** *Given a relative tree $\mathrm{inner\_rel}$ refining the relative unit-generated cover $\mathrm{unitCover}$ at $L_{\mathrm{rel}}$, and the W2 data with the round-8 piecewise containment, there exists an absolute tree $\mathrm{inner\_abs}$ at $L$ with both $\mathrm{allSplitsInducing}$ and $\mathrm{Refines}\ L\ C$. The descent chain (made explicit per round-7 reviewer):*

> *$\mathrm{inner\_rel}$ refines relative unit-generated cover over $\mathcal{O}(L)$*
> *$\Rightarrow$ unit-generated cover refines restricted standard cover over $L$ (via piecewise containment, clause (d))*
> *$\Rightarrow$ restricted standard cover refines $C$ (via $\mathrm{refines\_contain}$, W1's data).*

**Lean.**
```lean
theorem relative_laurent_tree_to_absolute
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (S : Finset A)
    (_hS_contain : refines_contain C S)
    (s : Aˣ)
    (L : RationalLocData A)
    (_hL_subset : rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s)
    (I_units : Finset A)
    (_h_unit_generated : restricted_standard_cover_generated_by_units L C S s I_units)
    [IsNoetherianRing (locSubring L.P L.T L.s)]
    [IsTopologicalRing (presheafValue L)] [PlusSubring (presheafValue L)]
    [IsHuberRing (presheafValue L)] [HasLocLiftPowerBounded (presheafValue L)]
    (L_rel : RationalLocData (presheafValue L))
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover_from_I_units : unitCover.base = L_rel)
    (inner_rel : LaurentTree (presheafValue L))
    (_h_refines_rel : inner_rel.Refines L_rel unitCover)
    (_h_split_rel : inner_rel.allSplitsInducing L_rel) :
    ∃ inner_abs : LaurentTree A,
      inner_abs.allSplitsInducing L ∧
      inner_abs.Refines L C
```

### 2.5 W4 — dropped

**Round-8 status: removed entirely.** The slot in the residuals file is now a comment block noting:

- the false-in-generality verdict on the round-6 cross-leaf disjointness;
- the not-quite-true verdict on the round-7 prune theorem;
- the pending `EmbeddingTopo.lean` NODE-step refactor as the proper resolution.

After the NODE-step refactor (use projection `Π(L.\mathrm{covers} \cup R.\mathrm{covers}) \to (\Pi\, L.\mathrm{covers}) \times (\Pi\, R.\mathrm{covers})` + the existing absorption principle), the tree-induction theorem needs only `Refines ∧ allSplitsInducing` — no `allNodesDisjoint`, no prune.

## 3. The I.1 chain (post-round-7)

The composition that closes I.1:

1. **W1** — standard cover $S$.
2. **W2** — Cor 7.32 unit $s$ and outer tree $t_{\mathrm{outer}}$ with `allSplitsInducing` and per-leaf `restricted_standard_cover_generated_by_units` (including the new clause (d)).
3. **W3 + W3-transport per outer leaf $L$** — choose an absolute inner tree `inner_of(L)` with `allSplitsInducing L ∧ Refines L C` via:
   - W3 produces a relative tree `inner_rel` refining the relative unit-generated cover;
   - W3-transport descends to absolute, using clause (d) of the W2 output + `refines_contain`.
4. **Graft** — `t_graft := t_outer.graftAt(C.base, inner_of)`. By the existing graft preservation lemmas, `t_graft.Refines C.base C ∧ t_graft.allSplitsInducing C.base`.
5. **(Pending refactor of `EmbeddingTopo.lean`)** — once the NODE step of `productRestrictionSub_isInducing_via_tree` is refactored to not require `allNodesDisjoint`, I.1's conclusion can drop the disjointness clause. Until then, the I.1 conclusion is `Refines ∧ allSplitsInducing ∧ allNodesDisjoint` and the third conjunct is sorry-blocked at the I.1 level pending the refactor.

## 4. Questions

**Q1.** Is the new clause (d) in `restricted_standard_cover_generated_by_units` the right formal expression of "the relative unit-generated cover over $\mathcal{O}(L)$ refines the restriction of the standard plus-cover to $L$"? Concretely, clause (d) reads: for each $f \in I_{\mathrm{units}}$, $\{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\} \subseteq R(\mathrm{insert}(f, C.\mathrm{base}.T)/C.\mathrm{base}.s) \cap R(L.T/L.s)$. Is this the correct A-level reading of the relative unit-piece containment, or does it miss something (e.g., the unit-piece in $\mathcal{O}(L)$ might be strictly smaller than the set $\{v(f) \le v(C.\mathrm{base}.s)\} \cap L$ after transport)?

**Q2.** Is W3's output (`inner_rel.Refines L_rel unitCover ∧ inner_rel.allSplitsInducing L_rel`) now sufficient as input to W3-transport for producing absolute `Refines L C`? The transport chain documented in W3-transport is: relative-refines $\to$ piecewise containment (clause d) $\to$ `refines_contain`. Is this the right chain, or is there an extra step (e.g., the algebraic identification of relative unit-pieces with absolute unit-pieces) that should be made explicit?

**Q3.** For the pending `EmbeddingTopo.lean` NODE-step refactor: does the natural projection `Π(L.covers ∪ R.covers) → Π(L.covers) × Π(R.covers)` (combined with the absorption "if $g \circ f$ inducing and $g$ continuous, then $f$ inducing") give the IsInducing property for non-disjoint Finset unions in the formal sense the project's tree-induction theorem needs? Or are there subtleties (e.g., the projection being not just continuous but also `IsInducing`, or measurability of the projection, etc.) that we should anticipate?

**Q4.** Is the round-8 architecture (W1, W2, W3, W3-transport, no W4, pending NODE refactor) now correct as a target for proof, or are there further structural issues to address before proof work begins?

## 5. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 8 of the series)
- Brief generated: 2026-05-15 (same day as round 7)
- Length: ~5 pages
- Build status: `lake build` clean; 6 sorries (W1, W2, W3, W3-transport, I.1's body, V.1 external)
- Round-7 reply integrated; this brief asks whether the round-7 feedback was correctly applied.

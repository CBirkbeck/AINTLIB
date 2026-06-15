# ChatGPT Pro review packet: Tate acyclicity critical path after latest landings

Date: 2026-04-21

Project: Lean 4 formalization of Wedhorn's *Adic Spaces* in
`/Users/mcu22seu/Documents/GitHub/Adic spaces`.

This packet is self-contained. The reviewer should assume no repository access.

## Goal

We are formalizing the Tate acyclicity result for the presheaf on rational opens,
following Wedhorn Theorem 8.28(b), with the repository ticket system centered on:

- `T-OV-1`: Laurent overlap / Example 6.39 bridge
- `T-OVERLAP-COMPAT`: use the overlap bridge in the presheaf-side gluing theorem
- `T-GEOM-RED`: geometric reduction from arbitrary rational covers to Laurent-style covers
- `T-IDEAL-2` / `T-COMP-FF`: the Corollary 8.32 faithful-flatness lane

The project already received an earlier reviewer recommendation that the best
critical path is:

```text
Lane A (simple Laurent overlap bridge)
  → Lane C (geometric reduction)
  → final tateAcyclicity assembly

while Lane B (Cor 8.32 / faithful flatness) is useful infrastructure but should
not block the final theorem unless truly necessary.
```

That earlier advice has mostly been borne out by the implementation work below.

## Current mathematical picture

There are now three meaningful lanes:

### Lane A: specialized Laurent overlap bridge

This is the Lean formalization of the algebra behind Wedhorn Example 6.39 /
Lemma 8.33 for the simple Laurent overlap. The project is deliberately pursuing
a **specialized** bridge, not a full theorem that Tate algebra commutes with all
closed quotients.

What is already landed:

- A hypothesis bundle
  `BackwardEvalHypotheses` in `LaurentOverlap.lean`.
- The forward specialized quotient map.
- The backward specialized quotient map scaffold.
- Generator action lemmas showing the maps behave correctly on the relevant
  `B`, `X`, and `Y` generators.
- A **parametric forward-backward round trip**
  `TA_B₁_gen_quotient_forward_backward_eq_id`.
- A **parametric RingEquiv bundle**
  `TA_B₁_gen_quotient_specialized_equiv`.

The current shape of the result is:

```lean
noncomputable def TA_B₁_gen_quotient_specialized_equiv
    ...
    (h : BackwardEvalHypotheses (B := B) b)
    (h_bwd_fwd : ...)
    :
    TateAlgebra (LaurentCover.B₁_gen b) ⧸ outerLaurentOverlapIdeal b
      ≃+*
    TateAlgebra₂ B ⧸ bivariateOverlapIdeal b
```

So the forward direction, backward direction, and one round trip are all done.
The remaining open boundary is the **reverse round trip hypothesis**
`h_bwd_fwd`.

Our current understanding is that this missing `h_bwd_fwd` is not a random Lean
plumbing issue. It is the precise place where we still need one of:

1. a Tate-algebra / quotient-density theorem for `LaurentCover.B₁_gen b`, or
2. an equivalent specialized fact showing the backward map is determined by the
   dense polynomial generators in exactly the needed way.

So Lane A is now narrowed to a very specific quotient-Tate/density issue.

### Downstream overlap compatibility (`T-OVERLAP-COMPAT`)

This lane consumes Lane A inside the presheaf-side gluing theorem.

What is already landed:

- In `LaurentRefinement.lean`,
  `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`.
- In `LaurentOverlapCompatReduction.lean`,
  `laurentOverlapBridge_exists_compatible_of_presheaf_bivariate_iso`.

These theorems mean the downstream compatibility theorem has been reduced to the
following ingredients:

1. the algebraic overlap equivalence from Lane A,
2. a presheaf-level bivariate isomorphism, and
3. the required plus/minus intertwining identities.

In other words, the downstream lane is no longer blocked by vague design
uncertainty. It is blocked by the remaining exact mathematical content left in
Lane A.

### Lane C: geometric reduction

This is the Lean formalization of the Wedhorn 8.34 / Huebner-style reduction of
arbitrary rational covers to Laurent-style covers.

What is already landed in `GeometricReduction.lean`:

- `iteratedLaurentPlus_swap_rationalOpen`
- its induced bijective transport infrastructure
- plus-half transport / restriction helper lemmas
- `RationalCovering.standardCover_hV_glue_induction_via_vle`
- `RationalCovering.hBase_vle_plusHalf_of_outer`
- `RationalCovering.step_witness_of_parts`

Interpretation:

- the `h1T`-free reformulation is done,
- the plus-half transfer API is done,
- the packaging layer for the induction step witness is done,
- and much of the cover bookkeeping is no longer a blocker.

What remains is the final **outer induction assembly**:

1. the remaining subtype/index plumbing,
2. symmetric minus-side packaging where genuinely needed,
3. feeding the landed pieces into the final `step_witness`-driven induction.

So Lane C is also no longer in exploration mode. It is in late assembly mode.

## Lane B status: useful infrastructure, but the naive unconditional route is false

This is the main development since the last review.

### What landed

We now have a sorry-free generic Stacks 00MA theorem in a new file
`AdicCompletionFaithfullyFlat.lean`:

```lean
AdicCompletion.faithfullyFlat_of_le_jacobson_bot
```

This is the standard noetherian theorem:

```text
If I ≤ Jacobson(R), then the I-adic completion of R is faithfully flat over R.
```

That theorem has been successfully wired into the project's Corollary 8.32
pipeline in **conditional** form:

- `locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson`
  in `IdealLocalizationCompletion.lean`
- `coeRingHom_preserves_proper_of_locIdeal_le_jacobson`
  in `Cor832.lean`
- `productRestriction_injective_tate_of_locIdeal_le_jacobson`
  in `Cor832.lean`

### What failed mathematically

The open hope had been that for the incomplete rational-localization ring

```text
locSubring = A₀[T/s]
```

one might prove unconditionally:

```lean
locIdeal ≤ Ideal.jacobson (⊥ : Ideal locSubring)
```

That is now known to be **false in general**.

A concrete counterexample packet has already been written separately:

`chatgpt-packet-locIdeal-jacobson-falsity.md`

The counterexample pattern is:

- `A = ℚ_p⟨X⟩`
- `A₀ = ℤ_p⟨X⟩`
- rational datum with `T = {X}`, `s = p`
- then `locSubring = ℤ_p⟨X⟩[X/p]` is an **incomplete** localization ring
- `X ∈ locIdeal` and is topologically nilpotent there
- but `1 + X` is not a unit in `locSubring`
- so `X ∉ Jacobson(0)`

Hence the unconditional Jacobson route for the incomplete `locSubring` cannot be
the right theorem in this generality.

### Consequence

Lane B is now in the following state:

- the generic completion theorem is landed and reusable;
- the project-specific Cor 8.32 wrappers are landed conditionally;
- but the naive unconditional closure of that route is mathematically false.

So the reviewer should assume:

```text
Lane B is no longer the default critical path for finishing Tate acyclicity.
```

It may still be worthwhile as a named theorem under extra hypotheses, or in a
reframed completion-level form, but it should not silently retake the critical
path unless the reviewer believes the final theorem genuinely requires it.

## Current implementation status by file/theorem

### Landed and usable

- `AdicCompletionFaithfullyFlat.lean`
  - `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`
- `IdealLocalizationCompletion.lean`
  - `locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson`
- `Cor832.lean`
  - `coeRingHom_preserves_proper_of_locIdeal_le_jacobson`
  - `productRestriction_injective_tate_of_locIdeal_le_jacobson`
- `LaurentOverlap.lean`
  - `BackwardEvalHypotheses`
  - `TA_B₁_gen_quotient_forward_backward_eq_id`
  - `TA_B₁_gen_quotient_specialized_equiv`
- `LaurentRefinement.lean`
  - `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
- `LaurentOverlapCompatReduction.lean`
  - `laurentOverlapBridge_exists_compatible_of_presheaf_bivariate_iso`
- `GeometricReduction.lean`
  - `iteratedLaurentPlus_swap_rationalOpen`
  - `RationalCovering.standardCover_hV_glue_induction_via_vle`
  - `RationalCovering.hBase_vle_plusHalf_of_outer`
  - `RationalCovering.step_witness_of_parts`

### Still open

1. **Lane A residual**
   - discharge the reverse round-trip hypothesis `h_bwd_fwd` in
     `TA_B₁_gen_quotient_specialized_equiv`
   - likely through a specialized quotient-Tate/density theorem, not through a
     huge general quotient-transport abstraction

2. **Downstream overlap compatibility closure**
   - consume the now-parametric Lane A bridge and close the presheaf-side
     compatible bridge theorem

3. **Geometric outer induction assembly**
   - finish the subtype/index bookkeeping
   - package the remaining minus-side/symmetry hypotheses
   - apply the already-landed `step_witness_of_parts`-style API

4. **Decision about Lane B**
   - either leave it as optional infrastructure,
   - or identify the correct reformulation if the final theorem still needs a
     Cor 8.32-style statement

## Why we are asking for guidance now

The project is no longer broadly stuck, but it is at a point where the next
choice of critical path matters.

The implementation evidence so far suggests:

- Lane A is the most genuine remaining mathematical blocker.
- Lane C is close enough that it should probably be finished once Lane A is
  solid.
- Lane B, in the naive incomplete-localization Jacobson form, is a dead end.

What we need from the reviewer is not another broad survey, but a decision
about the **right final route from here**.

## Questions for the reviewer

### Q1. Should the final Tate acyclicity proof now fully abandon Lane B as a critical dependency?

Given the counterexample above, is the right move now:

```text
finish Lane A
→ finish Lane C
→ assemble tateAcyclicity directly
```

with Lane B kept only as optional side infrastructure?

Or is there still some mathematically correct version of Cor 8.32 that the final
Lean theorem genuinely needs on the critical path?

### Q2. What is the cleanest way to discharge `h_bwd_fwd` in Lane A?

The current open boundary is the reverse round trip in the specialized quotient
equivalence. We would like advice on which of the following is most defensible:

1. prove a specialized quotient-density theorem exactly for
   `LaurentCover.B₁_gen b`,
2. prove a narrowly tailored Tate/polynomial density lemma for the quotient ring
   in this specialized Laurent-overlap setup,
3. refactor the construction so the missing reverse round trip becomes formal
   from universal properties,
4. or retreat further and rebuild this last step by a more direct two-variable
   Example 6.38 argument.

The key point is that we do **not** want to open a giant new abstraction if a
specialized theorem is the mathematically correct finish.

### Q3. Is the current downstream overlap strategy the right one?

We now have reduction theorems showing that the downstream compatibility theorem
is reduced to:

- the algebraic overlap equivalence,
- a presheaf-level bivariate iso,
- and explicit plus/minus intertwining identities.

Is this the right architectural boundary, or should we instead try to fuse the
presheaf-level and algebraic sides into one larger theorem and skip the current
two-stage reduction?

### Q4. Is the geometric lane now formulated correctly?

The current geometric infrastructure is built around:

- `standardCover_hV_glue_induction_via_vle`
- `hBase_vle_plusHalf_of_outer`
- `step_witness_of_parts`

with the minus-side hypothesis kept explicit wherever symmetry has not yet been
abstracted away.

Does this look like the right final Lean architecture for Wedhorn 8.34 / the
Huebner-style reduction, or is there a cleaner mathematical packaging we should
switch to before finishing the outer induction?

### Q5. If Lane B is not fully abandoned, what is the correct reformulation?

Since `locIdeal ≤ Jacobson(0)` is false for the incomplete `locSubring`, the
reviewer should advise only among mathematically sound alternatives, for example:

1. a completion-level faithful-flatness theorem with the correct source/target,
2. a spectrum-surjectivity argument not phrased through Jacobson on
   `locSubring`,
3. an extra hypothesis under which the Jacobson statement actually becomes true,
4. or explicit confirmation that Lane B should be parked completely.

## Bottom line

The project has made real progress:

- the specialized Laurent-overlap bridge is mostly built;
- the downstream compatibility theorem is reduced to a narrow upstream boundary;
- the geometric reduction API is mostly assembled;
- and the naive unconditional Jacobson closure has been correctly identified as
  false, which avoids wasting more time on the wrong route.

What remains is a high-leverage route decision:

```text
Do we now finish Tate acyclicity by pushing Lane A then Lane C,
or is there still a mathematically necessary reformulation of Lane B
that must be on the critical path?
```

The implementation evidence currently points strongly toward:

```text
Lane A first, then Lane C, with Lane B parked unless the reviewer can justify a
different mathematically correct dependency.
```

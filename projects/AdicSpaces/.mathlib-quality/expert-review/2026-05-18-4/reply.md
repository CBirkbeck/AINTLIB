# Round-4 reviewer reply (2026-05-18)

*Saved verbatim from the external reviewer who replied to round 3.*

---

## Overall verdict

The round-4 plan is coherent, with two caveats.

First, **the F12 refactor and the Spa.comap framework are the right next architectural moves**. They remove import-cycle and "silent elaboration blocker" problems rather than adding new mathematics.

Second, **the proposed `cor_8_32_clean_via_laurent` should not be the main Cor. 8.32 theorem for arbitrary covers**. It is fine as a Laurent-shaped special case, but arbitrary rational cover pieces are not generally Laurent-minus pieces. The clean Cor. 8.32 route should consume general rational-restriction flatness, i.e. your C1/Prop. 8.30 theorem, not a per-cover Laurent witness.

I'll answer Q1–Q8 in order.

---

## Q1 — Canonical rank-1 valuation on a complete nonarchimedean Huber field

I would **not** build a general "canonical rank-1 valuation on a complete Huber field" constructor as the next move. It is too broad and likely to become a new foundational project.

For Wedhorn 7.51(2), the cleanest Lean route is to reduce the maximal-ideal case to the already-planned Wedhorn 7.45 / valuation-subring machinery:

```text
Given maximal m:
  if m is open, use the trivial valuation on A/m;
  if m is non-open, apply the non-open-prime valuation construction to p = m.
```

Since `m` is maximal, a valuation support containing `m` is exactly `m`, provided the valuation is not the zero/improper one. This avoids constructing a canonical topology valuation on the quotient field. It also reuses the same Chevalley/valuation-subring infrastructure already needed elsewhere.

So for Q1(a)/(b)/(c):

* I would **not** start with Bourbaki/Engler–Prestel as a standalone valued-field construction.
* The "uniformizer-based" construction works in many Tate-field situations but is not the most robust formal target.
* I would **sidestep** via Wedhorn 7.45 + the open-maximal trivial case.

This also fits the surrounding project: the uploaded round-4 brief already records D9/D12 as valuation/Spa-point API gaps, and this route consolidates those rather than creating a separate valued-field API.

---

## Q2 — F12 file refactor

Yes: move the four declarations as a unit into `TateAcyclicityFinalAssembly.lean`.

The reason is exactly as stated in the brief: `Cor832.lean` imports `LaurentRefinement.lean`, while the gluing proof needs the Cor. 8.32 faithful-flatness theorem. Keeping the final `tateAcyclicity` statements upstream forces either an import cycle or a fake wrapper that merely relabels the `sorry`.

Of the alternatives:

* Splitting `LaurentRefinement.lean` into setup/output files is also valid, but more work.
* Keeping `tateAcyclicity` upstream and trying to route Cor. 8.32 indirectly is likely to recreate the same problem.
* Moving only `tateAcyclicity` but leaving `rationalCovering_hasSeparation/Gluing` upstream risks new re-export/import awkwardness.

So the straight move of all four declarations is the best engineering choice.

---

## Q3 — Spa.comap framework / `Spa_presheafValue_eq_rationalOpen`

Build it in full. Do **not** leave it as a parametric hypothesis on `IsSheafy`.

This theorem is too central: it feeds `HasLocLiftPowerBounded`, rational-open transport, unit/nonvanishing lemmas, and the relative-rational-to-absolute-rational conversions that keep appearing in the refinement-tree work. Treating it as a parameter would only move the main geometric content out of sight.

The right scope is roughly:

```lean
Spa (presheafValue D) ≃ rationalOpen D
```

with:

* forward map by `Spa.comap` along `A → O(D)`;
* inverse map by extending a valuation on `A` satisfying the rational inequalities first to the algebraic rational localization, then continuously to the completion.

This is exactly the rational-localization universal property Zavyalov records: completed rational localizations represent the structure presheaf on rational subsets, and rational localizations have the expected rings of definition and completions.

Mathlib's existing valuation infrastructure may help with equivalence relations and comap, but I would expect project-specific lemmas for:

```lean
valuation_extends_to_localization_of_rationalOpen
valuation_extends_to_completion_of_continuous
Spa_comap_image_eq_rationalOpen
```

This is worth the estimated ~500 LOC.

---

## Q4 — Krull intersection in non-domain Tate / Wedhorn 8.33

The counterexample is directionally correct, though the specific ideal computation should be corrected: in
$$A=\mathbb Q_p \times \mathbb Q_p,\quad f=(p,0),$$
since `p` is a unit in `Q_p`, one has
$$(f)^n = \mathbb Q_p \times 0$$
for all `n`, so the intersection is `Q_p × 0`, not zero. The brief's statement that it contains all `(0,c)` has the coordinates reversed, but the conclusion "not zero" is still right.

Mathematically, Wedhorn's Lemma 8.33 should not require `A` to be a domain. The exactness is a Tate-algebra/Laurent-cover algebraic exactness statement, and the published theorem is for strongly noetherian Tate rings, not domains.

However, **your current proof route** via
$$\bigcap_n (f)^n = 0$$
is domain-like and fails in non-domain rings.

For the current Path α implementation, since the headline theorem intentionally keeps `[IsDomain A]`, it is acceptable to add `[IsDomain A]` to `laurentCover_exact_general` and move on. But document clearly:

```text
This is a domain-restricted proof of Wedhorn 8.33, not Wedhorn's full generality.
```

If you later remove `[IsDomain A]`, the replacement should be the row-exactness / explicit Laurent algebra argument, not Krull intersection.

---

## Q5 — Cluster L completeness

For the current Path α theorem, the three proved parametric replacements for Wedhorn 8.31 are sufficient.

You need:

```lean
TateAlgebra.faithfullyFlat_general
TateAlgebra.flat_quotient_fSubX_general
TateAlgebra.flat_quotient_oneSubfX_general
```

with

```lean
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
```

as explicit input. The brief says these are already axiom-clean, and those are exactly the 8.31 pieces needed for Prop. 8.30 and Cor. 8.32.

Do not reintroduce the deleted wrappers. If future work wants Banach-field or non-parametric versions, those should be separate theorems, not on the current IsSheafy path.

---

## Q6 — Path α discharge / `cor_8_32_clean_via_laurent`

Be careful: a theorem that requires each cover piece to come with a Laurent witness is **not** Cor. 8.32 for arbitrary rational covers.

It is fine to define:

```lean
cor_8_32_clean_via_laurent
```

as a special-purpose theorem for Laurent-shaped covers, but the main Cor. 8.32 theorem should be:

```lean
cor_8_32_clean_via_flat :
  (∀ D ∈ C.covers, Module.Flat (O(C.base)) (O(D))) →
  Spec-surjectivity / Spa-cover condition →
  product restriction faithfully flat
```

Then prove the flatness input from C1 / Prop. 8.30 for arbitrary rational restrictions.

For gluing, the standard-cover/Laurent-refinement route is still the right high-level architecture. But for **separation of an arbitrary rational covering**, do not require each original cover piece to be Laurent. Use general rational restriction flatness.

So my recommendation:

1. Write a general `cor_8_32_clean_via_flat`.
2. Use the Laurent-specific theorem only inside the refinement/Laurent-cover subproofs.
3. Move F12 downstream as planned.
4. Avoid making `cor_8_32_clean_via_laurent` the main clean Cor. 8.32 API.

This aligns with Zavyalov's proof strategy too: standard covers are used after reducing to rational bases, but the sheaf/topological embedding formulation is cover-level.

---

## Q7 — Stacks 0316 routing

Your direct route is reasonable, especially inside the project.

The associated-graded proof is conceptually standard and often elegant, but in Lean it requires a lot of new infrastructure:

```text
associated graded ring,
graded finite generation,
filtration comparison,
lifting homogeneous generators,
adic summability.
```

Your direct route:

```text
choose generators f₁,…,fₙ of I
construct R[[X₁,…,Xₙ]] → R̂
show it is surjective
quotient of noetherian ring is noetherian
```

is more concrete and likely faster, even if the ~150 LOC estimate is optimistic. The direct proof's hard point is the Cauchy lifting/surjectivity, but that is local and easier to control than developing `gr_I`.

So yes: use the direct route.

One caution: if `MvPowerSeries (Fin n) R` noetherian is itself a larger Mathlib gap than expected, consider proving only the finite `n` theorem needed for the chosen number of ideal generators, by induction from the one-variable `PowerSeries` noetherian theorem. That is exactly the route described in the brief, and it is the right one.

---

## Q8 — L5.1.1 ring iso encoding

Use the simpler base-change form if Lean permits it:

```lean
TateAlgebra A ≃+*
  A ⊗[P.A₀] AdicCompletion (P.I extended to P.A₀[X]) (P.A₀[X])
```

or in words:
$$A\langle X\rangle \cong A \otimes_{A_0} \widehat{A_0[X]}.$$

The intermediate factor
$$(P.A_0 \otimes A) \otimes_{P.A_0} \widehat{P.A_0[X]}$$
looks redundant unless it is needed to satisfy Lean's typeclass/algebra-instance inference. Mathematically,
$$P.A_0 \otimes_{P.A_0} A \cong A,$$
so the extra factor should not be part of the conceptual theorem.

Better API:

```lean
tateAlgebra_ringEquiv_baseChange_adicCompletion :
  TateAlgebra A ≃+*
    A ⊗[P.A₀] AdicCompletion ... (Polynomial P.A₀)
```

Then, if the current tensor expression is easier for Lean, prove it as a corollary by associativity/unit isomorphisms.

This is also closer to the rational-localization definitions: a completed rational localization has ring of definition obtained by completing a finitely generated algebra over `A₀`. Zavyalov's Definition 2.1 / Remark 2.3 record the same pattern: start from `A₀[f_i/s]`, then complete it.

---

## Methodological note

The round-4 audit caught the right class of problems: implicit proof-route hypotheses, not just statement errors. The next pre-flight pass should require a small ledger for each high-value lemma:

```text
Statement hypotheses:
Literature theorem hypotheses:
Literature proof actually uses:
Lean proof route uses:
Derived-by lemmas:
```

Then flag anything in "proof uses" that is not either:

* in the statement,
* already proved from the statement hypotheses,
* or explicitly parameterized.

That would catch:

* missing completeness in Wedhorn 7.51;
* hidden compactness in Cor. 7.32 finset form;
* noetherian ring-of-definition assumptions in 8.31;
* Krull-intersection misuse in non-domains.

---

## Recommended execution order

1. **Do the F12 move** into `TateAcyclicityFinalAssembly.lean`.
2. **Build `Spa_presheafValue_eq_rationalOpen`** fully; it is central.
3. **Finish Stacks 0316 direct route**, because it unlocks `presheafValue_pairOfDefinition_isNoetherian`.
4. **Define `cor_8_32_clean_via_flat`**, not only `via_laurent`.
5. **Patch 8.33 with `[IsDomain A]` for the current theorem**, while documenting that this is narrower than Wedhorn's full theorem.
6. **Use the proven parametric 8.31 replacements**; do not resurrect the deleted wrappers.

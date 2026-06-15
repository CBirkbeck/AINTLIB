# Expert reviewer reply — 2026-05-18

*Reviewer: ChatGPT (math model) responding to brief in `.mathlib-quality/expert-review/2026-05-18/brief.md`.*

## Assessment

The audit is valuable and the headline diagnosis is right: the current project still contains several `sorry` lemmas whose statements are not merely hard, but **mathematically false or scoped too broadly**. Those should not remain in the transitive dependency closure of `IsSheafy`.

The most important corrections are:

1. **Do not derive noetherian rings of definition from strong noetherianity.** Strongly noetherian Tate is the right hypothesis for Wedhorn 8.28(b); it does not let you conclude that an arbitrary or canonical ring of definition is noetherian.
2. **Do not use single-map injectivity/surjectivity or `IsLocalization.Away` for completed rational restrictions.** Those claims are false in general and should be removed from the main dependency graph.
3. **Fix the scope of Wedhorn 7.54 / standard-cover refinement.** Wedhorn's standard cover statement is naturally for `Spa A`; for a rational base `C.base`, the clean formulation is over `O(C.base)` or by restricting the cover and transporting back.
4. **Keep the Wedhorn route, but make it parametric where necessary.** The theorem can be proved in the strong-noetherian Tate setting, but the Lean wrappers should not smuggle in false "noetherian ring of definition" consequences.
5. **Your `IsSheafy` target is only the sheaf part of Wedhorn 8.28(b), not the full cohomological acyclicity.** This is fine, but it should be named and documented clearly.

## Responses to the main questions

### Q1. Strongly noetherian Tate ⇒ noetherian ring of definition?

Do **not** use this implication.

Wedhorn explicitly records that completely valued fields of height 1 are strongly noetherian, citing BGR 5.2.6; this includes fields such as `C_p` in the usual rank-one topology. The valuation ring `C_p^∘` has nondiscrete value group, and a valuation ring is noetherian iff it is a DVR or a field. Thus the generic statement `∀ P : PairOfDefinition A, IsNoetherianRing P.A₀` is false.

For the specific theorem `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` the mathematical problem is that strong noetherianity does not supply noetherianity of the chosen ring of definition. If the chosen principal pair is built from something like `A^∘`, `C_p` is a direct obstruction. If it is an arbitrary `Classical.choice`, then the theorem is still not a consequence of the stated hypotheses unless you separately prove existence of a noetherian pair of definition. Do not route Wedhorn 8.28(b) through this lemma.

Wedhorn 8.28(b) is meant to hold for strongly noetherian Tate rings as such. The proof should use strong noetherianity of Tate algebras and rational localizations, not noetherianity of an arbitrary ring of definition.

### Q2. Noetherian Tate ⇒ strongly noetherian Tate?

Do **not** use this as a general theorem. Wedhorn states the strong-noetherian criterion for completely valued height-one fields and their topologically finite type algebras, not a general implication "abstractly noetherian Tate ring ⇒ strongly noetherian." In the Lean development, keep `[IsStronglyNoetherian A]` as an explicit hypothesis rather than trying to derive it from `[IsNoetherianRing A]`. So B4 should be removed from the clean theorem path.

### Q3. Wedhorn 7.54 relative to a rational base

Yes, your scope concern about F2/F3 is correct. The standard-cover refinement in Wedhorn is for covers of `Spa A`. For a cover of a rational base `C.base`, the right formal statement is not the original. The right statement is one of:
- `∃ S : Finset (presheafValue C.base), S generates the unit ideal in O(C.base) and the standard cover over O(C.base) refines C`
- or an equivalent transported version back to `A` using the rational-localization / presheaf-value equivalence.

Your F2 as written is too strong for a nontrivial rational base.

### Q4. Overall strategy: restructure or add hypotheses?

The overall Wedhorn strategy is sound, but the "Wedhorn-clean wrappers" should be split from the parametric theorems more honestly. Structure:
1. Main theorem target: `[IsTateRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]` plus only hypotheses genuinely present in Wedhorn.
2. Parametric internal theorems may take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` only when the theorem is actually about that pair, and only if downstream code later discharges it from a correct source.
3. Do not claim strong noetherianity implies `[IsNoetherianRing P.A₀]`.
4. If some proof path truly needs a noetherian ring of definition, then that proof path proves a strictly narrower theorem.

Do not abandon the Wedhorn architecture. Remove the false wrappers and keep only the parametric versions until the genuine strong-noetherian proof supplies the needed facts by another route.

### Q5. Is full Čech cohomology needed for `IsSheafy`?

For the current `IsSheafy` target, no. The sheaf-of-sets / sheaf-of-topological-rings condition only needs the degree-zero exactness statement `0 → O(U) → ∏ O(U_i) ⇉ ∏ O(U_i ∩ U_j)`. So you can prove:
- separation from Corollary 8.32 / faithful flatness;
- gluing from the degree-zero Laurent exactness plus refinement transfer.

You do not need to formalize all higher Čech cohomology to prove `IsSheafy`. However, do not label this as full "Tate acyclicity" unless you also prove the higher cohomology part.

### Q6. Correct Stacks tag for noetherianity of completion

Use **Stacks tag `0316`**, i.e. Lemma 10.97.6: "Let R be a Noetherian ring and I an ideal of R. The I-adic completion R^∧ is Noetherian." Stacks 00MA is in the "Completion for Noetherian rings" section and concerns exactness/completion of finite modules, not the noetherianity theorem itself.

### Q7. Citation for the power-bounded valuation criterion

Your statement `a ∈ Aᵒ ↔ ∀ continuous valuations v, v(a) ≤ 1` should not be cited as Wedhorn Remark 7.42. The right citation is a combination of the Huber/Wedhorn valuation-theoretic characterization of power-bounded elements. In the project, cite it as something like: "Huber/Wedhorn power-boundedness valuation criterion; one direction from Wedhorn 7.41 for analytic points, plus the non-analytic case via the valuation/generization machinery." Do not label it "Wedhorn 7.42" unless you add a comment explaining that the theorem is assembled from nearby results, not stated there verbatim.

### Q8. False `restrictionMap_isLocalization`

Remove it from the main path. The statement that completed rational restrictions are `IsLocalization.Away` in Mathlib's algebraic sense is false. Completed rational localizations contain convergent denominator tails, so finite denominator clearing fails in general. Keeping this theorem in an imported file with a `sorry` body is dangerous because it lets false statements silently prove downstream results.

The correct route is the one you already identified: restriction maps are flat via Wedhorn 8.30 / 8.31, product restriction is faithfully flat via Cor 8.32, not ordinary algebraic localization.

### Q9. What to do with false G1/G2 scaffolding?

Do not keep false lemmas as load-bearing scaffolding in the main dependency closure. Recommended policy:
- Move false lemmas into a clearly marked scratch/deprecated namespace or file not imported by the main theorem.
- Rename them if they must remain, e.g. `false_restrictionMapHom_surj_counterexample_expected` or document them as problem statements, not theorem dependencies.
- Refactor downstream consumers now if they are in the `IsSheafy` dependency graph.

Gradual migration is fine operationally, but not if the false lemmas remain transitive dependencies of the target theorem. A clean build with false `sorry` theorems in the dependency chain gives a misleading proof state.

### Q10. Ratio tree / refinement-tree encoding

The `RatioLaurentTree` / `RatioTreeRealization` architecture is a reasonable Lean encoding of Wedhorn 8.34. The key correction is that rational subcovers over a rational base must be allowed to live over `O(C.base)` first and then be transported back. Do not force every refinement generator to be an element of the original `A`.

Keep the explicit tree infrastructure, but make sure W1 and the ratio-node construction are **relative over the current affinoid**:
- standard cover over O(base)
- unit-generated cover over O(leaf)
- ratio Laurent cover over O(leaf)
- transport to absolute RationalLocData only through a valid rational-subdomain stability theorem

This is faithful to Wedhorn and more Lean-friendly than a fully abstract Čech-complex formalization.

## Treatment of flagged lemmas

- **B2/B3**: Mark as false or remove from theorem path. Replace with parametric `(P : PairOfDefinition A) [IsNoetherianRing P.A₀] → ...` only when genuinely needed, or use `[IsStronglyNoetherian A]` directly.
- **B4**: Remove. Do not derive strong noetherianity from noetherianity.
- **D15**: Add `[CompleteSpace A]` and the appropriate nonarchimedean/topological-ring hypotheses.
- **E1**: Restate with the correct hypothesis. A finitely generated module need not be complete just because the base is complete. You need the canonical finite-module topology / quotient of a finite free complete module, or a hypothesis that the completion is finite and the module is closed.
- **E2**: Add the missing module-topology constraints: the competing topology must be an `A`-module topology with continuous scalar multiplication and the relevant completeness/countability properties. Uniqueness of arbitrary uniform additive group structures is false.
- **F2/F3**: Relativize over `O(C.base)` or restrict to the case `C.base = Spa A`.
- **G1/G2**: Remove from active imports. Replace consumers with product-level Corollary 8.32 and degree-zero descent.

## Recommended project plan

1. Quarantine all false lemmas. B2, B3, B4, D15 as stated, E1 as stated, E2 as stated, F2/F3 as stated, G1/G2 should not remain in the `IsSheafy` transitive closure.
2. Make the main theorem depend on `[IsStronglyNoetherian A]`, not `[IsNoetherianRing P.A₀]` unless explicitly parametric.
3. Refactor standard-cover existence relative to a base: `exists_standard_cover_refining_relative (C : RationalCovering A) : ∃ S : Finset (presheafValue C.base), standard cover over O(C.base) refining C`, then transport as needed.
4. Continue the ratio-tree architecture, but keep all local cover constructions relative to the current `presheafValue`.
5. Use Corollary 8.32 product faithful flatness for separation. Do not use single-map restriction injectivity/surjectivity.
6. For `IsSheafy`, prove only degree-zero exactness. Save full higher acyclicity for a later Čech-complex project.

## Manager message to worker

Stop using the false scaffolding in the main theorem path. Specifically:
- `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
- `isNoetherianRing_A₀_of_stronglyNoetherianTate`
- `isStronglyNoetherian_of_isNoetherianRing_isTateRing`
- `restrictionMapHom_surj`
- `restrictionMapHom_injective`
- `restrictionMap_isLocalization`

should not be transitive dependencies of `IsSheafy`.

Refactor the clean route as:
```
[IsTateRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]
→ Example 6.38 / rational localization preservation
→ Prop 8.30 flat restriction maps
→ Cor 8.32 product faithful flatness
→ degree-zero Laurent gluing + refinement transfer
→ IsSheafy
```

For standard-cover refinement of a nontrivial rational base, do not use a finite `S ⊆ A` with `Ideal.span S = ⊤` and `R(S/f) ⊆ C-piece`. That is the wrong scope. Work over `O(C.base)` or use a relative standard-cover theorem.

For Stacks citation, use tag `0316` for "completion of a Noetherian ring is Noetherian," not `00MA`.

## References cited by reviewer

- [arXiv 1910.05934] Wedhorn, *Adic Spaces*, BGR 5.2.6 citation for strong noeth of completely valued fields
- [Stacks 00I8] Section 10.50 — Valuation rings (noeth ⇔ DVR or field)
- [math.stanford.edu / Wedhorn PDF] Standard cover refinement statement excerpt
- [Stacks 0316] Lemma 10.97.6 — completion of noeth ring is noeth (CORRECT TAG)
- [Stacks 0BNH] Section 10.97 — Completion for Noetherian rings (sectional context)

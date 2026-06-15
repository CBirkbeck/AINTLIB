# Expert reviewer reply — 2026-05-18 (second brief, Session 22)

*Reviewer: ChatGPT (math model) responding to `brief.md` in this folder.*

## Executive verdict

Your second audit is doing the right thing. Several leaves that were "mathematically true in isolation" are **not cascade-survivable** because their planned proof route passed through deleted false scaffolding. The project should now enforce a stricter separation:

1. **Final Wedhorn-clean theorem path** should use only:

   ```text
   IsTateRing A
   IsStronglyNoetherian A
   T2Space A
   NonarchimedeanRing A
   ```

   plus the actual affinoid/plus-subring data, and should not derive noetherianity of rings of definition.

2. **Parametric noetherian-pair theorems** may remain, but should not be advertised as consequences of strong noetherianity.

3. **False single-map restriction lemmas and algebraic `IsLocalization.Away` claims should stay deleted from the main dependency graph.**

4. **Relative-base issues must be handled over `O(C.base)`, not by forcing all standard-cover elements to live in the original `A`.**

The four most important decisions are:

* **A3:** keep as the final theorem target, but remove any proof route through noetherian rings of definition. Do not delete the statement; delete the bad route.
* **B5:** current statement is too broad / wrong-shaped. Replace by the exact cover-level or rational-data point-existence theorem actually needed for Cor 8.32.
* **F5:** Wedhorn's theorem does not require `IsDomain`; the domain hypothesis is an artifact. Keep a non-domain target, but refactor the proof away from domain-only shortcuts.
* **I2:** the exactness statement is true for all `f`, including units, but the Krull-intersection proof route is wrong for unit `f`. Case-split or use the already-proved algebraic row exactness.

## Meta answers

### Q-META.1 — Strongly noetherian Tate without noetherian ring of definition

Wedhorn 8.28(b) is intended for strongly noetherian Tate rings, not only for Tate rings with a noetherian ring of definition. The `C_p` observation shows only that the **proof route through "strongly noetherian ⇒ noetherian ring of definition" is false**, not that Wedhorn 8.28(b) is false.

So:

* **Do not delete A3 as a theorem target.**
* **Do delete or quarantine every proof route requiring** `IsNoetherianRing P.A₀` **to be derived from** `IsStronglyNoetherian A`.

The right proof should use strong noetherianity of Tate algebras and rational localizations directly. Parametric theorems with explicit noetherian-pair hypotheses are still useful, but they are narrower than Wedhorn 8.28(b).

### Q-META.2 — Cascade audit policy

Yes: every future brief should include a "taint graph" for each false/deleted lemma.

For every false leaf `X`, record:

```text
X false/deleted
→ direct consumers
→ indirect consumers in IsSheafy closure
→ alternate proof route for each consumer, or mark consumer tainted
```

A good internal classification is:

* **statement false**: delete or move to scratch;
* **statement true, route false**: keep statement, replace route;
* **statement true, route blocked by missing infrastructure**: keep, ticket the blocker;
* **statement narrower than final theorem**: keep as parametric only.

This would have caught A3/B5/B1/C2 after B2/B3/B4 were deleted.

### Q-META.3 — IsDomain

Wedhorn 8.28(b) is for strongly noetherian Tate rings, not just domains. The non-domain example `k⟨T,U⟩/(TU)` is a valid stress test for false single-map injectivity, but it is not a counterexample to sheafiness.

So `IsDomain A` is almost certainly a **proof artifact**. It may be convenient for some algebraic sublemmas, but it should not appear in the final Wedhorn-clean theorem.

Where it likely entered:

* to prove injectivity of individual restriction maps, which is false;
* to use Krull intersection in a domain form;
* to avoid nilpotent/zero-divisor cases in Laurent algebra.

The correct fix is not to keep `IsDomain` globally. Use flatness, exact row computations, and cover-level faithful flatness instead.

### Q-META.4 — Cluster E disposition

Cluster E should be moved out of the `IsSheafy` dependency closure.

Keep the genuinely useful parts in a separate support file if wanted:

* E3: noetherianity of adic completion is true and useful.
* E4: Hilbert-basis induction is useful if correctly scoped.
* E2: useful only after its hypotheses are exactly Wedhorn 6.18's module-topology hypotheses.
* E1: false as stated; restate or delete.

But do not let Cluster E block or support the main Wedhorn-clean route.

### Q-META.5 — High-leverage targets

Your proposed priorities are close, but I would slightly reorder:

1. **C1 / rational restriction flatness** — foundational for Cor 8.32 and separation.
2. **C2 / product faithful flatness, with a corrected cover-level Spec/Spa surjectivity theorem** — do not route through B5 as currently stated.
3. **F4 / realised ratio-tree refinement** — closes the topological-inducing/refinement part.
4. **I1 / faithfully flat descent equaliser** — important, but after Cor 8.32 is in shape.
5. **C3 / Spa-presheafValue equivalence** — high value because it also cleans up the unit/nonvanishing and relative-rational transport arguments.

I would not spend main-path time on Cluster E.

### Q-META.6 — Four explicit suspect leaves

**A3**: Keep the statement as the final theorem target. Do not keep a proof path through B2/B3/B4. Retarget proof through strong-noetherian rational localization preservation + Prop 8.30 + Cor 8.32 + Lemma 8.34.

**B5**: Restate. The current "for every finite T, s, prime with s ∉ p" version is too broad / wrong-shaped. Replace by the exact theorem needed: "For a rational cover C of a base D0 and a prime q of O(D0), there exists a cover piece Di and a prime qi of O(Di) lying over q." or by a point-existence theorem with the precise nonemptiness/properness hypotheses required.

**F5**: Do not delete the non-domain target. Wedhorn's theorem should include non-domain strongly noetherian Tate rings. But do not derive F5 directly from a domain-only F4. Instead refactor F4/F5 so the main theorem is non-domain. Domain-only statements can remain as temporary narrower lemmas.

**I2**: Statement true; proof route needs fixing. For unit `f`, the Krull-intersection proof degenerates, but the Laurent exactness statement should still be true. Handle by case-split (unit / non-unit), or better, use row3_exact algebraically for all `f` and transfer to presheaf values. Do not strengthen to `¬ IsUnit f` unless all callers already satisfy that.

### Q-META.7 — Other leaves to be suspicious of

1. **B1**: Statement likely true, but proof route must not depend on the current B5. Prove it through `Spa(O(U)) ≃ rationalOpen(U)` and the power-bounded valuation criterion.

2. **C2**: True, but its Spec-surjectivity proof must be cover-level. Do not use blanket B5.

3. **F1/F4**: Must be relative over `O(C.base)` if `C.base` is not all of `Spa A`.

4. **D9/D10**: Need careful hypothesis audit. Chevalley valuation existence is broad, but continuity / rational-open membership may require exact properness/nondegeneracy conditions. Do not let it become the new overbroad B5.

5. **N2**: Potentially circular if it uses C2 to prove the Spec-surjectivity needed for C2. It should be proved by a direct Spa/prime argument, not by Cor 8.32 itself.

## Cluster-by-cluster pass

### Cluster A

A1 and A2 are fine as parametric / domain-restricted variants. The `IsDomain` hypothesis makes them narrower than Wedhorn, but not false.

A3 is the real target. Keep it, but mark current route invalid.

### Cluster B

B1 is plausible and important, but should be proved from `Spa(O(U)) ≃ rationalOpen(U)` + power-bounded iff valuations ≤ 1; not from the current B5.

B5 should be replaced by a precise cover-level theorem. The blanket statement should not remain in clean dependencies.

B6 is the correct topological-inducing strength. It should be discharged from the realised ratio-tree refinement.

B7/B8 are correct. Their dependencies should be Cor 8.32 and descent/refinement, not retired single-map lemmas.

### Cluster C

C1 is correct and central. Best route: basic rational step flatness via Tate-algebra quotients + decomposition/transitivity of rational localizations → arbitrary rational restriction flatness.

C2 is correct, but its proof needs a cover-level Spec-surjectivity theorem. Do not route through current B5.

C3/C4/C5 are correct and high value. C3 in particular should be prioritised if it unlocks B1, bridge lemmas, and relative-rational transport.

### Cluster D

D1/D2/D5 are fine.

D6/D7 are fine if proved via the Spa/presheaf-value equivalence and power-bounded criterion. Check no hidden B5.

D8 content is correct but mis-cited. Rename/docstring it as "power-bounded valuation criterion," not Wedhorn 7.42.

D9/D10 need hypothesis audit. They should be formulated parametrically with the exact pair/completeness/properness assumptions. Do not use them as global strong-noetherian consequences unless those assumptions are discharged.

D12/D14 are plausible but infrastructure-heavy.

### Cluster E

Delete from the main path. Keep only if someone is actively developing Wedhorn 6.18 as independent infrastructure.

E1 false as stated. E2 only after hypothesis tightening. E3/E4 true but not main-path blockers.

### Cluster F

F1/F2/F3 need relative reformulation. Correct shape: "For a rational cover C of a rational base D, there exists a standard cover over O(D) refining the pullback cover over O(D)." or a transported equivalent.

F4 is the right project encoding, but should ultimately be non-domain.

F5 should be kept as the clean goal, but not proven from domain-only machinery.

F7/F8/F9/F10 are the right conceptual pieces.

F11 is correct.

F12 should be moved into a downstream assembly file to avoid import cycles.

### Cluster G

G3 is fine. The deleted G1/G2 should remain deleted/quarantined.

### Cluster H

H1/H2 are correct. H2's finite form is exactly what Wedhorn uses in Lemma 8.34. The product/finite assembly should be checked, but the statement is fine.

### Cluster I

I1 is correct and worth proving.

I2 is true but proof route must be changed or case-split.

I3 is project scaffolding and likely fine.

### Cluster K

K1/K2 are plausible scaffolding, but ensure they do not depend on the deleted B5/G1/G2-style statements.

### Cluster N

N1 should route through full C1, not Laurent-only flatness unless the cover is Laurent-shaped.

N2 should not be proved via C2 if it is needed for C2. Prove a direct cover-level prime/Spa lifting theorem.

N3/N4 are routing/import-cycle issues, not new mathematics.

## Concrete policy recommendations

1. **Mark false/scoped-wrong lemmas as deprecated and remove from imports.** Do this for: `restrictionMapHom_surj`, `restrictionMapHom_injective`, `restrictionMap_isLocalization`, `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`, `isNoetherianRing_A₀_of_stronglyNoetherianTate`, `isStronglyNoetherian_of_isNoetherianRing_isTateRing`, `exists_ideal_generators_refining_cover` (as currently scoped).

2. **Keep A3, but retarget proof.** A3 is not false; it is the actual theorem. Its current proof route is false.

3. **Restate B5 and F1/F2/F3.** B5 should be cover-level / rational-data-specific. F1/F2/F3 should be relative over `O(C.base)`.

4. **Remove `IsDomain` from the final target.** Keep domain-only lemmas only as intermediate narrow results, not as final wrappers.

5. **Prioritise the following proof work:**
   1. C3: Spa-presheafValue equivalence.
   2. C1: arbitrary rational restriction flatness.
   3. C2: product faithful flatness with corrected Spec-surjectivity.
   4. F4/F5: realised ratio-tree refinement, relative over the base.
   5. I1: faithfully flat descent equaliser.

## Manager message to worker

Use this as the new policy:

1. **A3 stays.** It is the real final theorem. But its proof must not use noetherian rings of definition derived from strong noetherianity.

2. **B5 must be restated.** Do not use the current blanket prime-to-rational-open point theorem. Replace it with the exact cover-level Spec/Spa surjectivity theorem needed for Cor 8.32.

3. **F1/F2/F3 must be relativised.** Standard covers for a rational base live over `O(C.base)`, not as a finite `S ⊆ A` spanning all of `A`.

4. **F5 should be the final refinement-tree target.** Wedhorn does not assume `IsDomain`. Keep domain-only lemmas only temporarily.

5. **I2 is true but needs a new proof route.** Handle the unit case separately or use row exactness for all `f`.

6. **Delete or quarantine every false single-map restriction lemma from the active imports.**

7. **Stop spending main-path time on Cluster E.** It is now orphaned infrastructure.

Highest-leverage next tasks:

```text
C3 Spa(O(D)) ≃ rationalOpen(D)
C1 flatness of arbitrary rational restriction
C2 product faithful flatness with corrected Spec-surjectivity
F4/F5 relative ratio-tree refinement
I1 faithfully flat descent equaliser
```

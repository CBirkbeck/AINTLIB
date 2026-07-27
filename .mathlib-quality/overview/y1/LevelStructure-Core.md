# Phase-1 inventory — LevelStructure core (Y1 spine)

Scope (4 files, 920 lines total, branch `main`, read 2026-07-12):

1. `projects/ModularCurves/ModularCurves/LevelStructure/Basic.lean` (201 lines)
2. `projects/ModularCurves/ModularCurves/LevelStructure/ExactOrder.lean` (341 lines)
3. `projects/ModularCurves/ModularCurves/ForMathlib/GeometricFibreComparison.lean` (147 lines)
4. `projects/ModularCurves/ModularCurves/EllipticCurve/Torsion.lean` (231 lines)

Conventions: paths in "Used by" are relative to `projects/ModularCurves/ModularCurves/`.
Ambient variables `{S : Scheme.{u}} (E : EllipticCurve S)` apply throughout files 1, 2, 4.
CODE-sorry = an actual `sorry` term in the declaration's own proof (producer WIP —
cleanup-untouchable). All four files: no `set_option`, no `private` declarations.

---

## 1. `LevelStructure/Basic.lean` — Γ(N), Γ₁(N), Γ₀(N) level structures (KM Ch. 3)

Imports: `LevelStructure.ExactOrder` (project) + mathlib `Morphisms.Flat`,
`Morphisms.FinitePresentation`. Local instances: `Over.cartesianMonoidalCategory`,
`Over.braidedCategory`. Namespace `ModularCurves.EllipticCurve`.

### `IsNaiveFullLevel`
- **Type**: `def` (Prop)
- **What**: Naive full level-`N` structure (Loeffler Fact 3.8.1): a pair `P Q : E.Section` with `(N:ℤ)•P = 0 ∧ (N:ℤ)•Q = 0`, such that on every geometric point `t : Spec k̄ ⟶ S` every `N`-torsion point lies in `AddSubgroup.closure {pull t P, pull t Q}`.
- **How**: plain definition — conjunction of global killing clause and a ∀-quantified geometric-fibre generation clause.
- **Hypotheses**: `(N : ℕ) [NeZero N] (P Q : E.Section)`.
- **Uses from project**: `E.Section`, `Point.pull` (ExactOrder.lean), `E.Point` (EllipticCurve/GroupLaw.lean).
- **Used by**: in-file `isFullLevel_iff_naive`; externally `ModularCurve/YFullRoute.lean`, `Moduli/GammaH.lean`, `Moduli/GammaHRepresentability.lean`, `Moduli/PullSectionCanonicity.lean`, `Moduli/Groupoid.lean`, `Moduli/NaiveProblems.lean`.
- **Visibility**: public. **Lines**: 41–49.
- **Notes**: sorry-free. Definition of record for the naive register; heavy Moduli-side consumer base.

### `IsNaiveGammaOne`
- **Type**: `def` (Prop)
- **What**: Naive Γ₁(N)-structure: `(N:ℤ)•P = 0` globally, and on every geometric point `pull t P` is killed by `N` and no proper multiple `a•pull t P` (`0 < a < N`) vanishes — the RHS of KM 1.4.4 *with its standing killing hypothesis*.
- **How**: plain definition. Long ADVERSARIAL FIX docstring (2026-07-06) records why the global killing clause is required (`Spec ℚ̄[ε]` tangent-lift counterexample; representability of the unkilled functor was FALSE).
- **Hypotheses**: `(N : ℕ) [NeZero N] (P : E.Section)`.
- **Uses from project**: `E.Section`, `Point.pull` (ExactOrder.lean).
- **Used by**: in-file `isGammaOne_iff_naive`; externally `ModularCurve/YOneAssembly.lean`, `ModularCurve/YOneTatePoint.lean`, `Moduli/PullSectionCanonicity.lean`, `Moduli/NaiveProblems.lean`, `GroupScheme/Subgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 51–66.
- **Notes**: sorry-free. The Y₁(N) moduli problem is built on this — the central definition of the Y1 stream.

### `IsGammaOne`
- **Type**: `def` (Prop)
- **What**: Drinfeld Γ₁(N)-structure (KM 3.2), the definition of record over an arbitrary base: `P` has exact order `N` in KM 1.4.1's sense.
- **How**: delegates outright to `Section.HasExactOrder E N`.
- **Hypotheses**: `(N : ℕ) [NeZero N] (P : E.Section)`.
- **Uses from project**: `Section.HasExactOrder` (ExactOrder.lean).
- **Used by**: in-file `isGammaOne_iff_naive`; externally `Moduli/GammaH.lean`, `LevelStructure/IsoTransport.lean`.
- **Visibility**: public. **Lines**: 68–71.
- **Notes**: sorry-free. Thin alias — dedup/altitude question for consolidation: consumers could use `HasExactOrder` directly, but the name carries the KM 3.2 register.

### `torsionIdeal`
- **Type**: `noncomputable def` (`Scheme.IdealSheafData E.E`)
- **What**: the ideal sheaf of `E[N]` as a closed subscheme of `E` — the kernel ideal of the inclusion `E[N] ⟶ E`.
- **How**: `(E.torsionι N).ker` (mathlib `Scheme.Hom.ker`). Docstring records it became a REAL definition on 2026-07-06 (previously an unregistered data-sorry), pinned by `torsionIdeal_subscheme`.
- **Hypotheses**: `(N : ℕ)` (no `NeZero` needed).
- **Uses from project**: `torsionι` (EllipticCurve/Torsion.lean).
- **Used by**: in-file `torsionIdeal_subscheme`, `IsFullLevel`, `fullLevel_divisor_iff_naive_gen`; externally `LevelStructure/IsoTransport.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 73–80.
- **Notes**: sorry-free.

### `torsionIdeal_subscheme`
- **Type**: `theorem`
- **What**: (T-B3a pinning spec) the closed subscheme cut out by `torsionIdeal N` is `E[N]` itself, compatibly with the inclusions: `∃ e : (torsionIdeal N).subscheme ≅ torsion N, e.hom ≫ torsionι N = subschemeι`.
- **How**: 9-line proof. Named lemmas: `torsionι_isClosedImmersion` (project, T-B3), mathlib `Scheme.IdealSheafData.ker_subschemeι`, `IsClosedImmersion.isIso_lift`, `IsClosedImmersion.lift_fac`; assembles the iso as `asIso (IsClosedImmersion.lift …)`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `torsionIdeal`, `torsion`, `torsionι`, `torsionι_isClosedImmersion` (Torsion.lean).
- **Used by**: `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 82–95.
- **Notes**: sorry-free.

### `IsFullLevel`
- **Type**: `def` (Prop)
- **What**: Drinfeld Γ(N)-structure (KM 3.1): `P, Q` killed by `N` and the degree-`N²` divisor `Σ_{(a,b) ∈ (ℤ/N)²} [aP + bQ]` (indexed by `Fin (N²)` via `i ↦ (i % N)•P + (i / N)•Q`) has ideal equal to `torsionIdeal N` — i.e. the `N²` combinations form a full set of sections of `E[N]/S`.
- **How**: plain definition via `RelEffCartierDiv.sectionsDivisor` and ideal equality.
- **Hypotheses**: `(N : ℕ) [NeZero N] (P Q : E.Section)`.
- **Uses from project**: `RelEffCartierDiv.sectionsDivisor` (LevelStructure/CartierDivisor.lean), `torsionIdeal` (this file), `E.Section`/`E.Point` (ExactOrder/GroupLaw).
- **Used by**: in-file `fullLevel_divisor_iff_naive_gen` (statement mirror), `isFullLevel_iff_naive`; externally `ModularCurve/YFullRoute.lean`, `Moduli/FullLevelTautSection.lean`, `Moduli/GammaH.lean`, `Moduli/LevelSpaces.lean`, `LevelStructure/IsoTransport.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 97–106.
- **Notes**: sorry-free. The `Fin (N²)` / `% N`–`/ N` encoding of the `(ℤ/N)²` index is duplicated verbatim in the statement of `fullLevel_divisor_iff_naive_gen` — an extraction candidate once the register stabilises.

### `fullLevel_divisor_iff_naive_gen` — **CODE-sorry**
- **Type**: `theorem`
- **What**: register box **T-D8-bridge** (KM 3.7 / 1.4.4 for Γ(N)): for `N` invertible and `P, Q` killed by `N`, the divisor `Σ_{(a,b)} [aP+bQ]` equals `E[N]` (ideal equality) iff on every geometric point the pulled-back `P, Q` generate the `N`-torsion.
- **How**: `by sorry` (line 125) — whole proof is the box. Docstring pins the discharge route: reduced-base full-set-of-sections criterion (`isFullSetOfSectionsAlg_iff_fields`, T-D2, proved) glued to the fibre comparison `E[N]_{k̄} ≅ (ℤ/N)²` (T-B6).
- **Hypotheses**: `(N : ℕ) [NeZero N] (hN : NIsInvertible S N) (P Q : E.Section) (hP : (N:ℤ)•P = 0) (hQ : (N:ℤ)•Q = 0)`.
- **Uses from project**: `RelEffCartierDiv.sectionsDivisor`, `torsionIdeal`, `Point.pull`, `NIsInvertible` (Torsion.lean).
- **Used by**: in-file `isFullLevel_iff_naive` (both directions); externally referenced in `ModularCurve/YFullRoute.lean`.
- **Visibility**: public. **Lines**: 108–125.
- **Notes**: **CODE-sorry** — producer WIP, untouchable by cleanup.

### `isFullLevel_iff_naive`
- **Type**: `theorem`
- **What**: **T-D8** (KM 3.7 / KM 1.4.4 upgraded to Γ(N)): for `N` invertible on `S`, `IsFullLevel N P Q ↔ IsNaiveFullLevel N P Q`.
- **How**: 7-line proof: `constructor` + `rintro` unpacking; both directions are one application of `fullLevel_divisor_iff_naive_gen` (the killing clauses are shared structurally).
- **Hypotheses**: `(N : ℕ) [NeZero N] (hN : NIsInvertible S N) (P Q : E.Section)`.
- **Uses from project**: `fullLevel_divisor_iff_naive_gen`, `IsFullLevel`, `IsNaiveFullLevel` (this file).
- **Used by**: `ModularCurve/YFullRoute.lean`, `Moduli/GammaHRepresentability.lean`.
- **Visibility**: public. **Lines**: 127–139.
- **Notes**: itself sorry-free, but inherits `sorryAx` from the T-D8-bridge box.

### `isGammaOne_iff_naive`
- **Type**: `theorem`
- **What**: **T-D9** (KM 1.4.4 (1) ⇔ (3), restated): for `N` invertible, `IsGammaOne N P ↔ IsNaiveGammaOne N P`.
- **How**: 9-line proof. Forward: killing via named lemma `Section.HasExactOrder.smul_eq_zero` (T-D5), then `Section.hasExactOrder_iff_geometric` (T-D6) `.mp`; backward: `.mpr`.
- **Hypotheses**: `(N : ℕ) [NeZero N] (hN : NIsInvertible S N) (P : E.Section)`.
- **Uses from project**: `Section.HasExactOrder.smul_eq_zero`, `Section.hasExactOrder_iff_geometric` (ExactOrder.lean), `IsGammaOne`, `IsNaiveGammaOne` (this file).
- **Used by**: nothing (grep hits only this file) — **unused in project**.
- **Visibility**: public. **Lines**: 141–151.
- **Notes**: sorry-free itself; inherits `sorryAx` via T-D6's boxes. Headline register statement — Y1 consumers currently work with `IsNaiveGammaOne` directly, so this is presently a documentation-of-equivalence theorem.

### `IsGammaZero`
- **Type**: `structure` (Prop-valued, 3 fields: `isSubgroup`, `degree_eq`, `geometricallyCyclic`)
- **What**: Γ₀(N)-structure (KM 3.4): a relative effective Cartier divisor `G ⊆ E` which is a subgroup (KM 1.3.6), of constant degree `N`, and geometrically Drinfeld-cyclic — over every geometric point some section `P₀` of the base-changed curve has `Σ_{a=1}^{N} [a·P₀] = G_t` as divisors (ideal equality).
- **How**: structure declaration. ADVERSARIAL FIX docstring (2026-07-06): the previous naive-exact-order surrogate was wrong in char `p ∣ N` (supersingular `Ker F` has Drinfeld generator `P₀ = 0` but no naive generator); the divisor form is honest in all characteristics.
- **Hypotheses**: `(N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π)`.
- **Uses from project**: `RelEffCartierDiv.IsSubgroup` (ExactOrder.lean), `RelEffCartierDiv.degree`, `RelEffCartierDiv.baseChange` (CartierDivisor.lean), `Section.orderDivisor` (ExactOrder.lean), `E.baseChange` (GroupLaw.lean).
- **Used by**: in-file `isGammaZero_iff_fppf`; externally `GroupScheme/CyclicSubgroup.lean`, `GroupScheme/NIsogeny.lean`, `GroupScheme/Subgroup.lean`.
- **Visibility**: public. **Lines**: 153–173.
- **Notes**: sorry-free.

### `IsGammaZeroFppf`
- **Type**: `def` (Prop)
- **What**: **T-D10** literal fppf-local form of Γ₀(N)-cyclicity (KM 1.4.1 / 3.7.1): `G` a subgroup divisor of constant degree `N` such that some fppf cover `h : T ⟶ S` (surjective + `Flat` + `LocallyOfFinitePresentation`) carries a section `P₀` of `E ×_S T` with `HasExactOrder N` whose order divisor pulls back to `G`.
- **How**: plain definition (∃-statement).
- **Hypotheses**: `(N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π)`.
- **Uses from project**: `RelEffCartierDiv.IsSubgroup`, `Section.HasExactOrder`, `Section.orderDivisor` (ExactOrder.lean), `RelEffCartierDiv.degree`, `.baseChange` (CartierDivisor.lean), `E.baseChange` (GroupLaw.lean); mathlib `Flat`, `LocallyOfFinitePresentation` (the file's two mathlib imports exist for this).
- **Used by**: in-file `isGammaZero_iff_fppf`; externally `GroupScheme/CyclicSubgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 175–189.
- **Notes**: sorry-free. Contains a redundant `haveI : NeZero N := ‹_›` inside the ∃-body (the instance is already in scope) — micro-golf candidate, but the file is producer WIP.

### `isGammaZero_iff_fppf` — **CODE-sorry**
- **Type**: `theorem`
- **What**: **T-D10** (KM 3.7.1): the geometric-fibre Drinfeld cyclicity of record (`IsGammaZero`) agrees with KM's literal fppf-local cyclicity (`IsGammaZeroFppf`).
- **How**: `by sorry` (line 197). Docstring: reverse implication descends a generator from an fppf cover to geometric points; forward is KM 3.7.1's étale-descent representability argument (deferred).
- **Hypotheses**: `(N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π)`.
- **Uses from project**: `IsGammaZero`, `IsGammaZeroFppf` (this file).
- **Used by**: `GroupScheme/CyclicSubgroup.lean`.
- **Visibility**: public. **Lines**: 191–197.
- **Notes**: **CODE-sorry** — producer WIP, untouchable.

---

## 2. `LevelStructure/ExactOrder.lean` — points of exact order N (Drinfeld / KM 1.4)

Imports: `LevelStructure.CartierDivisor`, `EllipticCurve.Torsion` (project) + mathlib
`Morphisms.Etale`, `FieldTheory.IsAlgClosed.Basic`. Local instances:
`Over.cartesianMonoidalCategory`, `Over.braidedCategory`. Namespace
`ModularCurves.EllipticCurve` (two `_root_` escapes).

### `Section`
- **Type**: `abbrev`
- **What**: `E.Section := E.Point (𝟙 S)` — a section of `E/S`, i.e. a point `P ∈ E(S)`.
- **How**: abbreviation.
- **Hypotheses**: none beyond ambient `E`.
- **Uses from project**: `E.Point` (EllipticCurve/GroupLaw.lean).
- **Used by**: pervasive — essentially every LevelStructure/Moduli/ModularCurve/GroupScheme file (the project's notation for `E(S)`).
- **Visibility**: public. **Lines**: 45–46.
- **Notes**: sorry-free. Core vocabulary.

### `Point.pull`
- **Type**: `def`
- **What**: pull a section back along `t : T ⟶ S`: the `T`-point `⟨t ≫ P.1, _⟩` (restriction of a section).
- **How**: subtype constructor; well-formedness by `Category.assoc` + `P.2` + `comp_id`.
- **Hypotheses**: `{T : Scheme.{u}} (t : T ⟶ S) (P : E.Section)`.
- **Uses from project**: `E.Point` (GroupLaw.lean).
- **Used by**: 12+ files: in-file (`pull_zsmul`, `pull_add`, `pull_zero`, all the KM 1.4.4 statements), `LevelStructure/Basic.lean`, `LevelStructure/Incidence.lean`, `ModularCurve/YOneAssembly.lean`, `YOneTatePoint.lean`, `YOneAtlasClassify.lean`, `Moduli/GammaH.lean`, `Moduli/PullSectionCanonicity.lean`, `Moduli/GammaHRepresentability.lean`, `Moduli/NaiveProblems.lean`, `Moduli/PullSectionAdd.lean`, `GroupScheme/DeligneOrder.lean`.
- **Visibility**: public. **Lines**: 48–50.
- **Notes**: sorry-free. Core vocabulary of the naive register.

### `Point.pull_zsmul`
- **Type**: `theorem`
- **What**: `pull t (a • P) = a • pull t P` — pulling back commutes with ℤ-scalars.
- **How**: 6-line proof: `Subtype.ext`, then both sides rewritten to `≫ [a]` by the named lemma `point_smul_eq_comp_mulBy` (GroupLaw.lean), finishing with associativity + `rfl`.
- **Hypotheses**: `{T} (t : T ⟶ S) (a : ℤ) (P : E.Section)`.
- **Uses from project**: `point_smul_eq_comp_mulBy` (GroupLaw.lean), `Point.pull`.
- **Used by**: in-file (`pull_zero`, `orderDivisor_baseChange`, `hasExactOrder_iff_geometric`, `hasExactOrder_iff_etale`); externally `ModularCurve/YOneTatePoint.lean`, `YOneAssembly.lean`, `Moduli/GammaH.lean`, `Moduli/NaiveProblems.lean`, `Moduli/GammaHRepresentability.lean`, `GroupScheme/DeligneOrder.lean`.
- **Visibility**: public. **Lines**: 52–60.
- **Notes**: sorry-free.

### `Point.pull_add`
- **Type**: `theorem`
- **What**: `pull t (P + Q) = pull t P + pull t Q` — `pull` is additive (a group homomorphism); precomposition on the same curve, no canonicity needed (contrast `EllHom.pullSection`).
- **How**: ~15-line proof. Transports through the named equivalence `pointEquivOverHom` (GroupLaw.lean) with `letI` `Hom.commGroup` instances; correspondence lemma `corr` proved by `Over.OverMorphism.ext`; finishes with named lemmas `pointEquivOverHom_add` and `MonObj.comp_mul`.
- **Hypotheses**: `{T} (t : T ⟶ S) (P Q : E.Section)`.
- **Uses from project**: `pointEquivOverHom`, `pointEquivOverHom_add`, `Hom.commGroup`, `E.asOver` (GroupLaw.lean).
- **Used by**: `Moduli/GammaH.lean`, `Moduli/PullSectionCanonicity.lean`, `Moduli/PullSectionAdd.lean`, `Moduli/GammaHRepresentability.lean`, `GroupScheme/DeligneOrder.lean`.
- **Visibility**: public. **Lines**: 62–81.
- **Notes**: sorry-free. Not used in-file (external API only).

### `Point.pull_zero`
- **Type**: `theorem`
- **What**: `pull t 0 = 0`.
- **How**: 3-line proof from `pull_zsmul` with `a = 0` + `zero_smul`.
- **Hypotheses**: `{T} (t : T ⟶ S)`.
- **Uses from project**: `Point.pull_zsmul` (this file).
- **Used by**: in-file (`hasExactOrder_iff_geometric`, `hasExactOrder_iff_etale`); externally `ModularCurve/YOneTatePoint.lean`, `Moduli/GammaH.lean`, `Moduli/GammaHRepresentability.lean`, `Moduli/NaiveProblems.lean`.
- **Visibility**: public. **Lines**: 82–86.
- **Notes**: sorry-free.

### `RelEffCartierDiv.IsSubgroup` (`_root_.ModularCurves.RelEffCartierDiv.IsSubgroup`)
- **Type**: `def` (Prop)
- **What**: **KM 1.3.6** — a relative effective Cartier divisor `D` in `E/S` *is a subgroup* if for every `g : T ⟶ S` there is an `AddSubgroup` of `E.Point g` whose membership is exactly "factors through `D.ideal.subscheme`".
- **How**: plain ∀∃ definition.
- **Hypotheses**: `(D : RelEffCartierDiv E.π)` (takes `E` explicitly: `D.IsSubgroup E`).
- **Uses from project**: `RelEffCartierDiv` (CartierDivisor.lean), `E.Point` (GroupLaw.lean); mathlib `Scheme.IdealSheafData.subscheme`/`subschemeι`.
- **Used by**: in-file (`HasExactOrder`, `smul_eq_zero_of_factors`, `IsSubgroup.baseChange`); externally `LevelStructure/Basic.lean` (`IsGammaZero`, `IsGammaZeroFppf`), `LevelStructure/IsoTransport.lean`, `LevelStructure/Incidence.lean`, `ForMathlib/CartierDual.lean`, `GroupScheme/CyclicSubgroup.lean`, `GroupScheme/DeligneOrder.lean`, `GroupScheme/Subgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 88–94.
- **Notes**: sorry-free. The load-bearing KM 1.3.6 encoding (∃-an-AddSubgroup rather than a subgroup-scheme structure).

### `Section.orderDivisor`
- **Type**: `noncomputable def` (`RelEffCartierDiv E.π`)
- **What**: the KM 1.4.1 divisor `[P] + [2P] + ⋯ + [NP]`, as `sectionsDivisor` over `Fin N` with sections `(a+1) • P`.
- **How**: one application of `RelEffCartierDiv.sectionsDivisor` (DS4a).
- **Hypotheses**: `(P : E.Section) (N : ℕ)`.
- **Uses from project**: `RelEffCartierDiv.sectionsDivisor` (CartierDivisor.lean).
- **Used by**: in-file (`HasExactOrder`, `orderDivisor_baseChange`, `smul_eq_zero`, `orderDivisor_etale_iff_geometric`, `hasExactOrder_iff_etale`); externally `LevelStructure/Basic.lean` (`IsGammaZero.geometricallyCyclic`, `IsGammaZeroFppf`), `LevelStructure/IsoTransport.lean`, `LevelStructure/Incidence.lean`, `GroupScheme/CyclicSubgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 96–99.
- **Notes**: sorry-free.

### `Section.HasExactOrder`
- **Type**: `def` (Prop)
- **What**: **KM 1.4.1** — `P ∈ E(S)` has exact order `N` (Drinfeld) if `[P] + ⋯ + [NP]` is a subgroup divisor of `E/S`. The delicate definition this project exists to get right.
- **How**: `(P.orderDivisor E N).IsSubgroup E`.
- **Hypotheses**: `(P : E.Section) (N : ℕ) [NeZero N]`.
- **Uses from project**: `Section.orderDivisor`, `RelEffCartierDiv.IsSubgroup` (this file).
- **Used by**: in-file (all KM 1.4.2/1.4.4 theorems); externally `LevelStructure/Basic.lean` (`IsGammaOne`, `IsGammaZeroFppf`), `LevelStructure/IsoTransport.lean`, `LevelStructure/Incidence.lean`, `Moduli/LevelSpaces.lean`, `GroupScheme/CyclicSubgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 101–105.
- **Notes**: sorry-free.

### `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (`_root_`) — **CODE-sorry**
- **Type**: `theorem`
- **What**: register box **BB-DELIGNE** (KM 1.4.2, cite [Oort–Tate]) in the project's subgroup-divisor encoding: a subgroup divisor of constant degree `N` is killed by `N` — every point factoring through it satisfies `(N:ℤ) • Q = 0`.
- **How**: `by sorry` (line 115).
- **Hypotheses**: `{D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N] (hdeg : ∀ s, D.degree s = N) {T} (g : T ⟶ S) (Q : E.Point g) (hQ : ∃ h, h ≫ D.ideal.subschemeι = Q.1)`.
- **Uses from project**: `RelEffCartierDiv.degree` (CartierDivisor.lean), `IsSubgroup` (this file).
- **Used by**: in-file `HasExactOrder.smul_eq_zero` (T-D5); externally `GroupScheme/DeligneOrder.lean`, `GroupScheme/Subgroup.lean`, `GroupScheme/NIsogeny.lean`.
- **Visibility**: public. **Lines**: 107–115.
- **Notes**: **CODE-sorry**. Active discharge stream exists: `GroupScheme/DeligneOrder.lean` builds `smul_eq_zero_of_factors'` → `smul_eq_zero_of_factors_section` → `smul_eq_zero_of_factors_affine` (Layer-B leaves themselves still sorried; plan in `.mathlib-quality/plan-deligne.md`). Untouchable.

### `Scheme.IdealSheafData.idealMonoidHom` (`_root_.AlgebraicGeometry`)
- **Type**: `noncomputable def` (`X.IdealSheafData →* (∀ U : X.affineOpens, Ideal Γ(X, U.1))`)
- **What**: `IdealSheafData.ideal` packaged as a monoid homomorphism (products of ideal sheaves are computed pointwise) — exists so `map_prod` can be applied.
- **How**: structure literal; `map_one'` by `simp [one_eq_top, ideal_top, Ideal.one_eq_top]`, `map_mul' := Scheme.IdealSheafData.ideal_mul` (mathlib).
- **Hypotheses**: `(X : Scheme.{u})`.
- **Uses from project**: none (pure mathlib content).
- **Used by**: in-file only — `HasExactOrder.smul_eq_zero` (via `map_prod`). **Unused elsewhere.**
- **Visibility**: public. **Lines**: 117–127.
- **Notes**: sorry-free. Lives in the `AlgebraicGeometry` root namespace but is defined in a LevelStructure file — natural relocation candidate to `ForMathlib/` (or upstream) at consolidation time; genuinely mathlib-shaped.

### `Section.orderDivisor_baseChange`
- **Type**: `theorem`
- **What**: **T-D6a-ii, L3** (KM 1.4.4 (1)⟹(2), divisor side): base-changing `[P] + ⋯ + [NP]` along `t : T ⟶ S` gives the order divisor of the pulled section on the base-changed curve.
- **How**: ~32-line proof (**>30**). `RelEffCartierDiv.ext`; computes both ideals by unfolding `sectionsDivisor` (`dif_pos` on separatedness + smoothness witnesses); pushes `comap` through the finite product via named lemma `Scheme.IdealSheafData.comap_prod` (ForMathlib/IdealSheafComapMul.lean); per-factor identification via named lemmas `Point.asSection_zsmul` (GroupLaw.lean), `Point.pull_zsmul` (this file), and `RelEffCartierDiv.ker_sectionBaseChange` (CartierDivisor.lean); also `RelEffCartierDiv.baseChange_ideal`.
- **Hypotheses**: `(P : E.Section) (N : ℕ) {T} (t : T ⟶ S)` (no `NeZero`, no invertibility).
- **Uses from project**: as named above + `Point.asSection` (GroupLaw.lean), `E.baseChange`, `E.smooth`.
- **Used by**: in-file `HasExactOrder.baseChange`; externally `GroupScheme/NIsogeny.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 129–168.
- **Notes**: sorry-free. Decompose candidate (>30-line proof; the two `hL`/`hR` ideal computations and the per-factor step are extractable) — but downstream of nothing sorried, so eligible for fleet work only once the file has no producer churn.

### `RelEffCartierDiv.IsSubgroup.baseChange` (`_root_`)
- **Type**: `theorem`
- **What**: **T-D6a-ii, L4** (KM 1.3.6 base-change stability): if `D` is a subgroup of `E/S` then `D.baseChange t` is a subgroup of `E ×_S T / T`.
- **How**: 9-line proof: given `g' : T' ⟶ T`, take the subgroup at `g' ≫ t` and `comap` it along the named equivalence `Point.baseChangeEquiv` (GroupLaw.lean); membership transported by named lemma `Scheme.IdealSheafData.exists_factor_comap_iff` (ForMathlib/IdealSheafComapMul.lean) + `RelEffCartierDiv.baseChange_ideal` (CartierDivisor.lean).
- **Hypotheses**: `{D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {T} (t : T ⟶ S)`.
- **Uses from project**: as named + `Point.baseChangeEquiv_apply_coe` (GroupLaw.lean).
- **Used by**: in-file `HasExactOrder.baseChange`; externally `GroupScheme/DeligneOrder.lean`, `GroupScheme/NIsogeny.lean`, `LevelStructure/IsoTransport.lean`.
- **Visibility**: public. **Lines**: 170–183.
- **Notes**: sorry-free.

### `Section.HasExactOrder.baseChange`
- **Type**: `theorem`
- **What**: **T-D6a-ii headline** (KM 1.4.4 (1)⟹(2)): exact order is preserved by base change — `pull t P` (as a section of `E.baseChange t`) has exact order `N`.
- **How**: 4-line proof: rewrite by `orderDivisor_baseChange`, apply `IsSubgroup.baseChange`.
- **Hypotheses**: `{P : E.Section} {N : ℕ} [NeZero N] (h : P.HasExactOrder E N) {T} (t : T ⟶ S)`.
- **Uses from project**: `orderDivisor_baseChange`, `IsSubgroup.baseChange` (this file), `Point.asSection` (GroupLaw.lean).
- **Used by**: `LevelStructure/IsoTransport.lean`.
- **Visibility**: public. **Lines**: 185–195.
- **Notes**: sorry-free. Reduces the T-D6b box to pure field-level (2)⟹(3) per the 2026-07-08 re-assessment.

### `Section.HasExactOrder.smul_eq_zero`
- **Type**: `theorem`
- **What**: **T-D5 = KM 1.4.2**: exact order `N` implies `(N:ℤ) • P = 0`.
- **How**: ~39-line proof (**>30**). Applies the BB-DELIGNE box `IsSubgroup.smul_eq_zero_of_factors` to `P` itself; the factoring obligation is discharged by showing `(orderDivisor P N).ideal ≤ ker P.1` — named lemmas: `RelEffCartierDiv.sectionsDivisor_degree` (CartierDivisor.lean) for the degree hypothesis, `map_prod` of `idealMonoidHom` (this file) + `Ideal.prod_le_inf` + `Finset.inf_le` at index `0`, then closed-immersion factoring via `IsClosedImmersion.of_comp`, `Scheme.Hom.toImage`/`toImage_imageι`, and `Scheme.IdealSheafData.inclusion_subschemeι` (mathlib).
- **Hypotheses**: `{P : E.Section} {N : ℕ} [NeZero N] (h : P.HasExactOrder E N)`.
- **Uses from project**: `smul_eq_zero_of_factors` (sorried box), `idealMonoidHom`, `orderDivisor` (this file), `sectionsDivisor_degree` (CartierDivisor.lean), `E.smooth`.
- **Used by**: `LevelStructure/Basic.lean` (`isGammaOne_iff_naive`).
- **Visibility**: public. **Lines**: 197–240.
- **Notes**: sorry-free itself; inherits `sorryAx` from BB-DELIGNE. Decompose candidate (>30 lines; the `hle`/`hle0` ideal-inequality block is a self-contained helper).

### `Section.HasExactOrder.pull_nsmul_ne_zero` — **CODE-sorry**
- **Type**: `theorem`
- **What**: register box **T-D6b** (KM 1.4.4 (2)⟹(3) at a geometric point): if `P` has exact order `N` (`N` invertible, `P` killed), then over every geometric point no proper multiple `a • pull t P` (`0 < a < N`) vanishes.
- **How**: `by sorry` (line 278). 34-line docstring records the discharge route in detail (RE-ASSESSMENT 2026-07-08: reduce via `HasExactOrder.baseChange` to field-level (2)⟹(3); elementary over `k̄` given `torsionπ_etale`; the bounded missing pieces are the divisor↔closed-subscheme bridge, closed-in-étale-over-`k̄` ⟹ reduced, and length↔point-count).
- **Hypotheses**: `{P} {N} [NeZero N] (hN : NIsInvertible S N) (hkill : (N:ℤ)•P = 0) (h : P.HasExactOrder E N) (k) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S) {a : ℕ} (ha0 : 0 < a) (haN : a < N)`.
- **Uses from project**: `NIsInvertible` (Torsion.lean), `Point.pull`, `HasExactOrder` (this file).
- **Used by**: in-file only — `hasExactOrder_iff_geometric` (forward direction).
- **Visibility**: public. **Lines**: 242–278.
- **Notes**: **CODE-sorry**. Untouchable; the docstring is the live attack plan.

### `Section.hasExactOrder_of_geometric` — **CODE-sorry**
- **Type**: `theorem`
- **What**: register box **T-D6c** (KM 1.4.4 (3)⟹(1) via (4)): if on every geometric point the multiples `aP`, `1 ≤ a ≤ N`, are distinct (no proper multiple of the pull vanishes), then `P` has exact order `N`. Route: `Σ [aP]` finite étale (fibrewise discriminant) ⟹ subgroup.
- **How**: `by sorry` (line 290).
- **Hypotheses**: `{P} {N} [NeZero N] (hN : NIsInvertible S N) (hkill) (h : ∀ geometric point, ∀ 0 < a < N, (a:ℤ) • pull t P ≠ 0)`.
- **Uses from project**: `NIsInvertible`, `Point.pull`, `HasExactOrder`.
- **Used by**: in-file only — `hasExactOrder_iff_geometric` (backward direction).
- **Visibility**: public. **Lines**: 280–290.
- **Notes**: **CODE-sorry**. Untouchable.

### `Section.hasExactOrder_iff_geometric`
- **Type**: `theorem`
- **What**: **T-D6 = KM 1.4.4 (1) ⇔ (3)**: for `P` killed by `N` and `N` invertible, `P` has exact order `N` iff on every geometric point `pull t P` is killed by `N` and no proper multiple vanishes. (The `ℚ̄[ε]` counterexample shows the killing hypothesis is required.)
- **How**: 6-line proof: forward via `pull_nsmul_ne_zero` (T-D6b box) plus killing conjunct from `pull_zsmul` + `hkill` + `pull_zero`; backward via `hasExactOrder_of_geometric` (T-D6c box).
- **Hypotheses**: `{P} {N} [NeZero N] (hN : NIsInvertible S N) (hkill : (N:ℤ)•P = 0)`.
- **Uses from project**: `pull_nsmul_ne_zero`, `hasExactOrder_of_geometric`, `pull_zsmul`, `pull_zero` (this file).
- **Used by**: in-file `hasExactOrder_iff_etale`; externally `LevelStructure/Basic.lean` (`isGammaOne_iff_naive`).
- **Visibility**: public. **Lines**: 292–308.
- **Notes**: sorry-free itself; inherits `sorryAx` from both T-D6 boxes. This is the theorem that makes `IsGammaOne ↔ IsNaiveGammaOne` go.

### `Section.orderDivisor_etale_iff_geometric` — **CODE-sorry**
- **Type**: `theorem`
- **What**: register box **T-D7-bridge** (KM 1.4.4 (3)⟺(4)): `Σ [aP]` is (finite) étale over `S` iff on every geometric point the multiples are distinct. Discharge: trace-form/discriminant theory for the finite locally free `orderDivisor` (T-B4 rank input) + fibre comparison.
- **How**: `by sorry` (line 321).
- **Hypotheses**: `{P} {N} [NeZero N] (hN : NIsInvertible S N) (hkill)`.
- **Uses from project**: `orderDivisor`, `Point.pull`, `NIsInvertible`; mathlib `Etale` (the file's Etale import exists for this statement).
- **Used by**: in-file only — `hasExactOrder_iff_etale`.
- **Visibility**: public. **Lines**: 310–321.
- **Notes**: **CODE-sorry**. Untouchable.

### `Section.hasExactOrder_iff_etale`
- **Type**: `theorem`
- **What**: **T-D7 = KM 1.4.4 (1) ⇔ (4)**: for `P` killed by `N`, `N` invertible: exact order `N` iff `(orderDivisor P N).ideal.subschemeι ≫ E.π` is étale.
- **How**: 8-line proof: rewrite by `hasExactOrder_iff_geometric` and `orderDivisor_etale_iff_geometric`, then bridge the extra killing conjunct with `pull_zsmul` + `pull_zero`.
- **Hypotheses**: `{P} {N} [NeZero N] (hN : NIsInvertible S N) (hkill)`.
- **Uses from project**: `hasExactOrder_iff_geometric`, `orderDivisor_etale_iff_geometric`, `pull_zsmul`, `pull_zero` (this file).
- **Used by**: nothing (grep hits only this file) — **unused in project**.
- **Visibility**: public. **Lines**: 323–337.
- **Notes**: sorry-free itself; inherits `sorryAx` from its two box inputs. Register completeness statement (KM (4)).

---

## 3. `ForMathlib/GeometricFibreComparison.lean` — [T-B6′-IFACE] scheme ↔ affine fibre comparison

Imports: `EllipticCurve.PointsDictionary`, `EllipticCurve.ModelRecord`,
`LevelStructure.ExactOrder` (project). Namespaces `ModularCurves.EllipticCurve` +
one lemma at `ModularCurves` level. Variable block: `{B} [CommRing B] (W : WeierstrassCurve B)
[W.IsElliptic] (E : EllipticCurve (Spec (.of B))) (hE : E.E = projModel W)
(hπ : E.π = eqToHom hE ≫ projModelπ W) (hz : E.zero ≫ eqToHom hE = projModelZero W)
(k) [Field k] [Algebra B k] [DecidableEq k] [(W.baseChange k).IsElliptic]`.

### `geomPoint`
- **Type**: `noncomputable def` (`Spec (.of k) ⟶ Spec (.of B)`)
- **What**: the tautological geometric point — `Spec.map` of the `algebraMap B k`; every geometric point of `Spec B` over a field is of this form.
- **How**: one-liner via `Spec.map`/`CommRingCat.ofHom`.
- **Hypotheses**: `(B) [CommRing B] (k) [Field k] [Algebra B k]`.
- **Uses from project**: none (pure mathlib).
- **Used by**: in-file (`pointSpecPointsEquiv`, `geomFibrePointAddEquiv`); externally `EllipticCurve/MulByHomQuasiFinite.lean`, `ModularCurve/YOneAtlasClassify.lean`, `ModularCurve/YOneAssembly.lean`.
- **Visibility**: public. **Lines**: 42–46.
- **Notes**: sorry-free. Mathlib-shaped utility.

### `pointSpecPointsEquiv`
- **Type**: `noncomputable def` (`E.Point (geomPoint B k) ≃ SpecPoints (projModel W) (projModelπ W) k`)
- **What**: ungated geometry — `E`-points over the tautological geometric point are exactly the `k`-points of the projective model, by transporting the total space along `hE`.
- **How**: explicit `Equiv`: to/inv compose with `eqToHom hE` / `eqToHom hE.symm`; inverse laws by `Subtype.ext` + `simp [Category.assoc]`.
- **Hypotheses**: uses `W E hE hπ k` from the variable block (not `hz`, not `[(W.baseChange k).IsElliptic]`).
- **Uses from project**: `SpecPoints`, `projModel`, `projModelπ` (EllipticCurve/PointsDictionary.lean), `E.Point` (GroupLaw.lean).
- **Used by**: in-file (`geomFibrePointAddEquiv`, `geomFibrePointAddEquiv_apply`); externally `ModularCurve/YOneAssembly.lean`, `ModularCurve/YOneAtlasClassify.lean`.
- **Visibility**: public. **Lines**: 54–70.
- **Notes**: sorry-free, axiom-clean by construction.

### `geomFibrePointAddEquiv`
- **Type**: `noncomputable def` (`E.Point (geomPoint B k) ≃+ (W.baseChange k).toAffine.Point`)
- **What**: **[T-B6′-IFACE, FILLED]** — the geometric-fibre point comparison as a *group* isomorphism: scheme-fibre points `≃+` mathlib affine Weierstrass points. The underlying bijection is `pointSpecPointsEquiv.trans projModelPointsEquiv`.
- **How**: `map_add'` is a ~17-line term/tactic proof (the former [T-B6′] sorry, now filled by the v10.123-CASCADE route). Named lemmas: `EllipticCurveGeom.ext_of_eqToHom` (ModelRecord.lean — the zero pin `hz` makes `E`'s geometry equal the model record's), `point_add_val_of_geom_eq` (ModelRecord.lean — rigidity driver forcing the two additions to agree over the locally noetherian `Spec k`), `mulModelHom_specPoints` (PointsDictionary.lean — C6 dictionary computing model addition as mathlib's affine `Point.add`), `modelEllipticCurve_point_add_val` (ModelRecord.lean).
- **Hypotheses**: full variable block including `hz` and `[(W.baseChange k).IsElliptic]`; `IsLocallyNoetherian (Spec (.of k))` obtained by `inferInstance`.
- **Uses from project**: `pointSpecPointsEquiv` (this file), `projModelPointsEquiv` (PointsDictionary.lean), `modelEllipticCurve` + the three ModelRecord lemmas above.
- **Used by**: in-file `geomFibrePointAddEquiv_apply`; externally `EllipticCurve/MulByHomQuasiFinite.lean`, `EllipticCurve/MulByHomUnramified.lean`, `ModularCurve/YOneAssembly.lean`, `ModularCurve/YOneAtlasClassify.lean` (direct importers of the file: MulByHomQuasiFinite, YOneAssembly). Also mentioned in `EllipticCurve/ModelRecord.lean`'s docstring (upstream pointer, not a use).
- **Visibility**: public. **Lines**: 72–103.
- **Notes**: sorry-free — **the module docstring (lines 8–31) is STALE**: it still says "only `map_add'` carries the `sorry` — the exact [T-B6′] pin" while the declaration is FILLED (grep: no `sorry` term in the file). Docstring refresh is the one safe cleanup this file needs (producer-owned file otherwise).

### `geomFibrePointAddEquiv_apply`
- **Type**: `@[simp] lemma`
- **What**: unfolding lemma — applying `geomFibrePointAddEquiv` is `projModelPointsEquiv ∘ pointSpecPointsEquiv`.
- **How**: `rfl`. Preceded by `omit [(W.baseChange k).IsElliptic] in` (the explicit instance hypothesis is droppable — mathlib's base-change `IsElliptic` instance covers it).
- **Hypotheses**: `(P : E.Point (geomPoint B k))` + variable block minus the omitted instance.
- **Uses from project**: `geomFibrePointAddEquiv`, `pointSpecPointsEquiv` (this file), `projModelPointsEquiv` (PointsDictionary.lean).
- **Used by**: `ModularCurve/YOneAssembly.lean`, `ModularCurve/YOneAtlasClassify.lean`.
- **Visibility**: public. **Lines**: 105–108.
- **Notes**: sorry-free.

### `affine_origin_order_gt_three` (namespace `ModularCurves`, not `EllipticCurve`)
- **Type**: `lemma`
- **What**: on a Tate-normal-form curve over a field (`a₄ = 0`, `a₂`, `a₃` units) the marked affine point `(0,0)` is nowhere of order 1, 2, or 3: `(a:ℤ) • some 0 0 hns ≠ 0` for `1 ≤ a ≤ 3`. The affine core of atlas leaf Y1-vi (`NowhereGeomOrderLEThree (tateMarkedPoint)`), transferred to fibres by consumers through `geomFibrePointAddEquiv`.
- **How**: ~23-line proof by `interval_cases a`. Named lemmas: `WeierstrassCurve.Affine.Point.some_ne_zero` (a = 1), `WeierstrassCurve.Affine.Point.add_some` with the not-2-torsion witness `0 ≠ negY 0 0 = -a₃` (a = 2), and for a = 3 an explicit slope computation (`slope_of_Y_ne`, `ψ`-free: `ℓ = 0`, `addX = -a₂ ≠ 0`) + `WeierstrassCurve.Affine.Point.add_of_X_ne`.
- **Hypotheses**: `{k} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic] (h4 : W.a₄ = 0) (hB2 : IsUnit W.a₂) (hB3 : IsUnit W.a₃) (hns : W.toAffine.Nonsingular 0 0) (a : ℕ) (ha0 : 0 < a) (ha3 : a ≤ 3)`.
- **Uses from project**: none — pure mathlib affine Weierstrass API (self-contained field-level computation).
- **Used by**: `ModularCurve/YOneAssembly.lean`.
- **Visibility**: public. **Lines**: 112–145.
- **Notes**: sorry-free. Genuinely mathlib-adjacent (no project types in the statement); sits slightly oddly in a fibre-comparison file — it is here because its only consumer routes it through `geomFibrePointAddEquiv`.

---

## 4. `EllipticCurve/Torsion.lean` — torsion subgroup schemes `E[N]` (KM 2.3)

Imports: `EllipticCurve.GroupLaw`, `ForMathlib.FinitePresentationCancel` (project) + mathlib
`Morphisms.{Finite,Flat,FlatRank,Etale,QuasiFinite}`, `ZariskisMainTheorem`. Local instances:
`Over.cartesianMonoidalCategory`, `Over.braidedCategory`. Namespace
`ModularCurves.EllipticCurve` (two `_root_` escapes). Trailing block comment (lines 222–227)
records the BB-DIFF relocation: `mulByHom_formallyUnramified` / `mulBy_etale` / `torsionπ_etale`
now live PROVEN in `EllipticCurve/MulByHomUnramified.lean` (statements unchanged).

### `NIsInvertible` (`_root_.ModularCurves`)
- **Type**: `def` (Prop)
- **What**: "`N` is invertible on the scheme `X`": `IsUnit (N : Γ(X, ⊤))`.
- **How**: one-liner.
- **Hypotheses**: `(X : Scheme.{u}) (N : ℕ)`.
- **Uses from project**: none (mathlib `IsUnit`, global sections).
- **Used by**: 14+ files — the project-wide invertibility currency: in-file `isEmpty_of_nIsInvertible_zero`; `EllipticCurve/{MulByHomQuasiFinite, TorsionFibre, TorsionUnramifiedFibre, MulByHomEtale, MulByHomUnramified, KernelDivisibilityGlue, MulByHomSmooth, PointVanishingClopen}.lean`, `ModularCurve/{YOneTatePoint, YFullRoute}.lean`, `Moduli/{Groupoid, FullLevelOpenLocus, GammaHRepresentability}.lean`, `LevelStructure/{ExactOrder, Basic}.lean` (KM 1.4.4 hypotheses).
- **Visibility**: public. **Lines**: 46–48.
- **Notes**: sorry-free.

### `torsion`
- **Type**: `noncomputable def` (`Scheme.{u}`)
- **What**: the `N`-torsion subscheme `E[N]` — kernel of `[N]` as the fibre product `pullback (E.mulByHom N) E.zero` (KM 2.3; Loeffler §3.4).
- **How**: one `pullback`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `mulByHom` (GroupLaw.lean), `E.zero` (GroupLaw.lean core).
- **Used by**: in-file (everything torsion-side); externally `EllipticCurve/{TorsionFibre, TorsionUnramifiedFibre, MulByHomEtale, MulByHomUnramified}.lean`, `ModularCurve/{YRho, YFullRoute}.lean`, `WeilPairing/EtaleDescent.lean`, `Moduli/LevelSpaces.lean`, `LevelStructure/{Basic, Incidence}.lean`, `GroupScheme/Subgroup.lean`.
- **Visibility**: public. **Lines**: 50–54.
- **Notes**: sorry-free. Definitional spine of workstream B.

### `torsionι`
- **Type**: `noncomputable def` (`E.torsion N ⟶ E.E`)
- **What**: the inclusion `E[N] ⟶ E`.
- **How**: `pullback.fst _ _`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `torsion` (this file).
- **Used by**: 14 files incl. in-file (`torsionι_isClosedImmersion`, `torsionι_π`), `LevelStructure/Basic.lean` (`torsionIdeal`), `EllipticCurve/{TorsionFibre, TorsionUnramifiedFibre, EndomorphismDegree, MulByHomUnramified, PointVanishingClopen}.lean`, `ModularCurve/{YFullRoute, YOneTatePoint, YOneAssembly}.lean`, `Moduli/{Groupoid, FullLevelTautSection}.lean`, `LevelStructure/IsoTransport.lean`, `GroupScheme/Subgroup.lean`.
- **Visibility**: public. **Lines**: 56–58.
- **Notes**: sorry-free.

### `torsionπ`
- **Type**: `noncomputable def` (`E.torsion N ⟶ S`)
- **What**: the structure morphism `E[N] ⟶ S`.
- **How**: `pullback.snd _ _`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `torsion` (this file).
- **Used by**: 14+ files: in-file (`pointToTorsion_torsionπ`, `torsionι_π`, `torsionπ_isFinite`, `torsionπ_flat`, `torsion_rank`), `EllipticCurve/{MulByHomQuasiFinite, TorsionFibre, TorsionUnramifiedFibre, MulByHomEtale, MulByHomUnramified, PointVanishingClopen}.lean`, `ModularCurve/{YRho, YOneAssembly, YOneTatePoint, YFullRoute}.lean`, `ForMathlib/{NilpotentKerSpecMap, GeometricFibreComparison, FormallyUnramifiedFibre}.lean`.
- **Visibility**: public. **Lines**: 60–62.
- **Notes**: sorry-free.

### `pointToTorsion`
- **Type**: `noncomputable def` (`T ⟶ E.torsion N`)
- **What**: a `T`-point of `E[N]` from a point `x : E.Point g` raw-killed by `N` (`x.1 ≫ [N] = g ≫ zero`), via the universal property of the kernel pullback.
- **How**: `pullback.lift x.1 g hx`.
- **Hypotheses**: `{N : ℕ} {T} {g : T ⟶ S} (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)`.
- **Uses from project**: `mulByHom`, `E.zero`, `E.Point` (GroupLaw.lean), `torsion` (this file).
- **Used by**: 14 files: in-file (the two simp lemmas), `EllipticCurve/{TorsionFibre, MulByHomUnramified, PointVanishingClopen}.lean`, `ModularCurve/{YFullRoute, YOneTatePoint, YRho}.lean`, `Moduli/{FullLevelOpenLocus, FullLevelTautSection, LevelSpaces}.lean`, `WeilPairing/Basic.lean`, `GroupScheme/{NIsogeny, Subgroup}.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 64–69.
- **Notes**: sorry-free.

### `pointToTorsion_torsionπ`
- **Type**: `@[simp] theorem`
- **What**: `pointToTorsion x hx ≫ torsionπ N = g`.
- **How**: `pullback.lift_snd`.
- **Hypotheses**: as `pointToTorsion`.
- **Uses from project**: `pointToTorsion`, `torsionπ` (this file).
- **Used by**: `EllipticCurve/{TorsionFibre, MulByHomUnramified, PointVanishingClopen}.lean`, `ModularCurve/{YOneTatePoint, YRho, YFullRoute}.lean`, `WeilPairing/Basic.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 71–75.
- **Notes**: sorry-free.

### `pointToTorsion_torsionι`
- **Type**: `@[simp] theorem`
- **What**: `pointToTorsion x hx ≫ torsionι N = x.1`.
- **How**: `pullback.lift_fst`.
- **Hypotheses**: as `pointToTorsion`.
- **Uses from project**: `pointToTorsion`, `torsionι` (this file).
- **Used by**: `EllipticCurve/{TorsionFibre, MulByHomUnramified}.lean`, `ModularCurve/{YOneTatePoint, YFullRoute}.lean`, `Moduli/FullLevelTautSection.lean`, `GroupScheme/Subgroup.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 77–81.
- **Notes**: sorry-free.

### `torsionι_isClosedImmersion`
- **Type**: `theorem`
- **What**: **T-B3** — `E[N] ⟶ E` is a closed immersion (the zero section of a separated morphism is a closed immersion; pull back).
- **How**: 6-line proof. Named lemmas: `IsClosedImmersion.of_comp` (from `zero ≫ π = 𝟙` via `E.zero_π`), `MorphismProperty.pullback_fst`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `torsionι` (this file), `E.zero_π` (GroupLaw.lean).
- **Used by**: `LevelStructure/Basic.lean` (`torsionIdeal_subscheme`), `LevelStructure/Incidence.lean`, `EllipticCurve/PointVanishingClopen.lean`, `ModularCurve/{YOneTatePoint, YOneAssembly}.lean`, `Moduli/FullLevelTautSection.lean`, `GroupScheme/Subgroup.lean`.
- **Visibility**: public. **Lines**: 83–91.
- **Notes**: sorry-free. Every consumer must `haveI := E.torsionι_isClosedImmersion N` — instance-ification is a natural consolidation question (theorem, not instance, today).

### `torsionι_π`
- **Type**: `@[reassoc] theorem`
- **What**: `torsionι N ≫ E.π = torsionπ N`.
- **How**: 11-line calc chain through `[N] ≫ π = π` (named lemma `E.mulByHom_π`, GroupLaw.lean), `pullback.condition`, and `E.zero_π`.
- **Hypotheses**: `(N : ℕ)`.
- **Uses from project**: `mulByHom_π`, `zero_π` (GroupLaw.lean).
- **Used by**: `EllipticCurve/{TorsionFibre, PointVanishingClopen}.lean`, `ModularCurve/YFullRoute.lean`, `Moduli/FullLevelTautSection.lean`, `GroupScheme/Subgroup.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 93–107.
- **Notes**: sorry-free. Golf candidate (the calc spells out associativity steps `simp`/`reassoc` could absorb) — but producer-owned file.

### `mulByHom_isProper`
- **Type**: `instance`
- **What**: `[n]` is proper for every `n : ℤ` — an `S`-endomorphism of the proper `S`-scheme `E` (KM 2.3.1 first reduction).
- **How**: 5-line proof: `IsProper.of_comp` from `IsProper ([n] ≫ π)` obtained by `E.mulByHom_π` + `E.proper`.
- **Hypotheses**: `(n : ℤ)`.
- **Uses from project**: `mulByHom`, `mulByHom_π`, `E.proper` (GroupLaw.lean).
- **Used by**: in-file `mulByHom_isFinite` (via instance search inside `IsFinite.of_isProper_of_locallyQuasiFinite`); as an instance it is consumed invisibly by any downstream `IsProper (mulByHom _)` search (e.g. `MulByHomQuasiFinite.lean`'s `mulByHom_isFinite_of_nIsInvertible`) — grep-based used-by undercounts it.
- **Visibility**: public instance. **Lines**: 109–116.
- **Notes**: sorry-free. The only `instance` in the four files.

### `mulByHom_zero`
- **Type**: `theorem`
- **What**: `[0] = π ≫ zero` — the zero isogeny factors through the base.
- **How**: 12-line proof unfolding `mulBy 0 = toUnit ≫ η`; named lemmas: `Over.w` (to identify `(toUnit E.asOver).left = π`), `E.one_eq_zero` (GroupLaw.lean — group-object unit is the zero section).
- **Hypotheses**: none beyond ambient.
- **Uses from project**: `mulBy`/`mulByHom`, `E.asOver`, `one_eq_zero` (GroupLaw.lean).
- **Used by**: in-file only — `torsionπ_flat` (`N = 0` branch).
- **Visibility**: public. **Lines**: 118–132.
- **Notes**: sorry-free. In-file helper.

### `mulByHom_locallyQuasiFinite` — **CODE-sorry**
- **Type**: `theorem`
- **What**: black box **BB-QF** (fibre input of KM 2.3.1): `[N]` is locally quasi-finite for `N ≥ 1` (all characteristics — fibrewise nonconstancy of `[N]` + finite fibres of nonconstant maps of proper smooth curves).
- **How**: `by sorry` (line 141). Docstring: discharge via fibre-comparison stream (T-B6 + HasseWeil `mulByInt_degree`).
- **Hypotheses**: `(N : ℕ) [NeZero N]`.
- **Uses from project**: `mulByHom` (GroupLaw.lean).
- **Used by**: in-file `mulByHom_isFinite`.
- **Visibility**: public. **Lines**: 134–141.
- **Notes**: **CODE-sorry**. NB: the `N`-invertible special case is already PROVEN downstream as `mulByHom_locallyQuasiFinite_of_nIsInvertible` in `EllipticCurve/MulByHomQuasiFinite.lean` (which imports this file); the general-`N` box stays here. Untouchable.

### `mulByHom_flat` — **CODE-sorry**
- **Type**: `theorem`
- **What**: black box **BB-FLAT** (flatness input of KM 2.3.1): `[N]` is flat for `N ≥ 1` (miracle flatness over the universal regular Weierstrass base; EGA IV 11.3.10 fibrewise criterion).
- **How**: `by sorry` (line 147).
- **Hypotheses**: `(N : ℕ) [NeZero N]`.
- **Uses from project**: `mulByHom` (GroupLaw.lean).
- **Used by**: in-file (`torsionπ_flat` `N ≥ 1` branch, `torsion_rank`); externally `EllipticCurve/{MulByHomEtale, MulByHomSmooth, MulByHomUnramified}.lean`, `ModularCurve/YOneTatePoint.lean`; `EllipticCurve/MulByHomFlat.lean` is the planned discharge site (`mulByHom_flat_of_kernelNDivisible`).
- **Visibility**: public. **Lines**: 143–147.
- **Notes**: **CODE-sorry**. Widest-consumed of the three boxes. Untouchable.

### `mulByHom_finrank` — **CODE-sorry**
- **Type**: `theorem`
- **What**: black box **BB-DEG** (degree input of KM 2.3.1): `[N]` has rank `N²` at every point `x : E.E`.
- **How**: `by sorry` (line 153). Docstring: algebraic anchor is HasseWeil `mulByInt_degree` via T-B6.
- **Hypotheses**: `(N : ℕ) [NeZero N] (x : E.E)`.
- **Uses from project**: `mulByHom` (GroupLaw.lean); mathlib `Scheme.Hom.finrank` (`Morphisms.FlatRank`).
- **Used by**: in-file only — `torsion_rank`.
- **Visibility**: public. **Lines**: 149–153.
- **Notes**: **CODE-sorry**. Untouchable.

### `mulByHom_isFinite`
- **Type**: `theorem`
- **What**: (KM 2.3.1, finiteness of `[N]`) `[N]` is finite: proper + locally quasi-finite via Zariski's Main Theorem.
- **How**: 3-line proof: `haveI` BB-QF, then named lemma `IsFinite.of_isProper_of_locallyQuasiFinite` (mathlib ZMT; `mulByHom_isProper` instance found by search).
- **Hypotheses**: `(N : ℕ) [NeZero N]`.
- **Uses from project**: `mulByHom_locallyQuasiFinite` (sorried box), `mulByHom_isProper` (this file).
- **Used by**: in-file (`torsionπ_isFinite`, `torsion_rank`); mirrored in `EllipticCurve/MulByHomQuasiFinite.lean` (`mulByHom_isFinite_of_nIsInvertible`, the invertible-case analogue).
- **Visibility**: public. **Lines**: 155–159.
- **Notes**: sorry-free itself; inherits `sorryAx` from BB-QF.

### `torsionπ_isFinite`
- **Type**: `theorem`
- **What**: **T-B4** (finite half of KM 2.3.1): `E[N] ⟶ S` is finite.
- **How**: 2-line proof: `MorphismProperty.pullback_snd` of `mulByHom_isFinite`.
- **Hypotheses**: `(N : ℕ) [NeZero N]`.
- **Uses from project**: `mulByHom_isFinite` (this file).
- **Used by**: 11 files: `EllipticCurve/{MulByHomQuasiFinite, TorsionUnramifiedFibre, MulByHomEtale, MulByHomUnramified}.lean`, `ModularCurve/{YFullRoute, YOneTatePoint}.lean`, `Moduli/GammaHRepresentability.lean`, `GroupScheme/Subgroup.lean`, `WeilPairing/EtaleDescent.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 161–167.
- **Notes**: sorry-free itself; inherits `sorryAx` (BB-QF). Headline consumer surface.

### `torsionπ_flat`
- **Type**: `theorem`
- **What**: **T-B4** (flatness half of KM 2.3.1): `E[N] ⟶ S` is flat — for all `N` including `N = 0` (where `E[0] = E` is flat since `π` is smooth).
- **How**: ~17-line proof. `N = 0` branch: named lemmas `IsSplitMono.mk'` (zero section split by `π`), `mulByHom_zero` (this file), `cancel_mono` (to show `pullback.snd = pullback.fst ≫ π`), `SmoothOfRelativeDimension.smooth`; `N ≥ 1` branch: `MorphismProperty.pullback_snd` of BB-FLAT.
- **Hypotheses**: `(N : ℕ)` — deliberately no `NeZero`.
- **Uses from project**: `mulByHom_zero`, `mulByHom_flat` (this file), `E.zero_π`, `E.smooth` (GroupLaw.lean).
- **Used by**: `GroupScheme/Subgroup.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 169–190.
- **Notes**: sorry-free itself; the `N ≥ 1` branch inherits `sorryAx` (BB-FLAT); the `N = 0` branch is unconditional.

### `torsion_rank`
- **Type**: `theorem`
- **What**: **T-B4** (rank part of KM 2.3.1): `(torsionπ N).finrank s = N²` at every `s : S`.
- **How**: 4-line proof: named lemma `Scheme.Hom.finrank_pullback_snd` (mathlib `Morphisms.FlatRank`; needs the `mulByHom_flat`/`mulByHom_isFinite` instances) then `mulByHom_finrank`.
- **Hypotheses**: `(N : ℕ) [NeZero N] (s : S)`.
- **Uses from project**: `mulByHom_flat`, `mulByHom_isFinite`, `mulByHom_finrank` (this file).
- **Used by**: `EllipticCurve/MulByHomUnramified.lean`, `GroupScheme/Subgroup.lean`.
- **Visibility**: public. **Lines**: 192–198.
- **Notes**: sorry-free itself; inherits `sorryAx` from all three boxes (BB-QF, BB-FLAT, BB-DEG).

### `isEmpty_of_nIsInvertible_zero` (`_root_.ModularCurves`)
- **Type**: `theorem`
- **What**: if `0` is invertible on a scheme `X` then `X` is empty (global sections are the zero ring; stalks are nontrivial local rings).
- **How**: 7-line proof: `isUnit_zero_iff` gives `(0:Γ(X,⊤)) = 1`, push through `X.presheaf.germ` to a stalk, contradict `one_ne_zero`.
- **Hypotheses**: `{X : Scheme.{u}} (h : NIsInvertible X 0)`.
- **Uses from project**: `NIsInvertible` (this file).
- **Used by**: `EllipticCurve/{TorsionUnramifiedFibre, MulByHomEtale, MulByHomUnramified}.lean` (degenerate-case dispatch in the étale cascade).
- **Visibility**: public. **Lines**: 200–209.
- **Notes**: sorry-free. Mathlib-shaped scheme lemma parked here next to `NIsInvertible`.

### `mulByHom_locallyOfFinitePresentation`
- **Type**: `theorem`
- **What**: `[N]` is locally of finite presentation — an `S`-endomorphism of the locally-finitely-presented `E/S`, by cancellation (Stacks 01TX).
- **How**: 6-line proof: `Smooth E.π` via `SmoothOfRelativeDimension.smooth`, then named lemma `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType` (project `ForMathlib/FinitePresentationCancel.lean`) applied to `[N] ≫ π = π`.
- **Hypotheses**: `(N : ℕ)` (no `NeZero`).
- **Uses from project**: `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType` (ForMathlib/FinitePresentationCancel.lean), `mulByHom_π`, `E.smooth` (GroupLaw.lean).
- **Used by**: `EllipticCurve/{MulByHomQuasiFinite, MulByHomEtale, MulByHomUnramified, MulByHomSmooth}.lean`, `ModularCurve/YOneTatePoint.lean`, `GroupScheme/Subgroup.lean`, `LevelStructure/Incidence.lean`.
- **Visibility**: public. **Lines**: 211–220.
- **Notes**: sorry-free, unconditional.

---
---

### File Summary — `LevelStructure/Basic.lean` (201 lines)

- **Totals**: 12 declarations — 6 `def` (`IsNaiveFullLevel`, `IsNaiveGammaOne`, `IsGammaOne`, `torsionIdeal` (noncomputable), `IsFullLevel`, `IsGammaZeroFppf`), 1 `structure` (`IsGammaZero`, 3 Prop fields), 5 `theorem`s. All in namespace `ModularCurves.EllipticCurve`.
- **Key API**: the four KM Ch. 3 moduli-problem definitions in both registers — `IsNaiveFullLevel` / `IsFullLevel` (Γ(N)), `IsNaiveGammaOne` / `IsGammaOne` (Γ₁(N)), `IsGammaZero` / `IsGammaZeroFppf` (Γ₀(N)) — plus `torsionIdeal` (+ pin `torsionIdeal_subscheme`) and the register-equivalence theorems `isFullLevel_iff_naive` (T-D8), `isGammaOne_iff_naive` (T-D9), `isGammaZero_iff_fppf` (T-D10). Heaviest external consumers: Moduli/* and ModularCurve/* (Y1 and full-level streams), GroupScheme/*.
- **Unused-in-file / project**: `isGammaOne_iff_naive` — grep finds no consumer outside this file (headline register statement; Y1 consumers use `IsNaiveGammaOne` directly). Everything else has external consumers.
- **CODE-sorry list**: `fullLevel_divisor_iff_naive_gen` (T-D8-bridge, line 125), `isGammaZero_iff_fppf` (T-D10, line 197). Producer WIP — cleanup must not touch these or force them.
- **set_option**: none.
- **Proofs > 30 lines**: none (longest: `torsionIdeal_subscheme` ~9 lines, `isGammaOne_iff_naive` ~9 lines).
- **Private/public**: all public; no `private`, no `instance`. Local `attribute [local instance]` for `Over.cartesianMonoidalCategory` / `Over.braidedCategory`.

### File Summary — `LevelStructure/ExactOrder.lean` (341 lines)

- **Totals**: 19 declarations — 1 `abbrev` (`Section`), 5 `def`s (`Point.pull`, `RelEffCartierDiv.IsSubgroup`, `Section.orderDivisor` (nc), `Section.HasExactOrder`, `Scheme.IdealSheafData.idealMonoidHom` (nc, `_root_.AlgebraicGeometry`)), 13 `theorem`s. Namespace `ModularCurves.EllipticCurve` with two `_root_` escapes (`RelEffCartierDiv.*`, `AlgebraicGeometry.Scheme.IdealSheafData.idealMonoidHom`).
- **Key API**: the project's central KM 1.4 vocabulary — `Section`, `Point.pull` (+ `pull_zsmul`/`pull_add`/`pull_zero` hom-package), `RelEffCartierDiv.IsSubgroup` (KM 1.3.6), `Section.orderDivisor`, `Section.HasExactOrder` (KM 1.4.1), base-change stability (`orderDivisor_baseChange`, `IsSubgroup.baseChange`, `HasExactOrder.baseChange` — T-D6a-ii, all proven), `HasExactOrder.smul_eq_zero` (T-D5), and the KM 1.4.4 equivalences `hasExactOrder_iff_geometric` (T-D6) / `hasExactOrder_iff_etale` (T-D7). Consumed by every Moduli/GroupScheme/LevelStructure downstream file.
- **Unused-in-file / project**: `Scheme.IdealSheafData.idealMonoidHom` — used only by `HasExactOrder.smul_eq_zero` in this file (mathlib-shaped; ForMathlib relocation candidate). `Section.hasExactOrder_iff_etale` (T-D7) — no consumer anywhere (register-completeness statement). `Point.pull_add` — no in-file use (external API only, well-consumed externally). Box theorems `pull_nsmul_ne_zero`, `hasExactOrder_of_geometric`, `orderDivisor_etale_iff_geometric` are in-file-only by design (consumed by the T-D6/T-D7 headlines).
- **CODE-sorry list**: `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (BB-DELIGNE, line 115; discharge stream live in `GroupScheme/DeligneOrder.lean`), `Section.HasExactOrder.pull_nsmul_ne_zero` (T-D6b, line 278), `Section.hasExactOrder_of_geometric` (T-D6c, line 290), `Section.orderDivisor_etale_iff_geometric` (T-D7-bridge, line 321). All producer WIP — untouchable.
- **set_option**: none.
- **Proofs > 30 lines**: `Section.orderDivisor_baseChange` (~32 proof lines, 137–168), `Section.HasExactOrder.smul_eq_zero` (~39 proof lines, 202–240). Both sorry-free — decompose candidates once producer churn stops.
- **Private/public**: all public; no `private`, no `instance`. Local `attribute [local instance]` for the Over monoidal structure.

### File Summary — `ForMathlib/GeometricFibreComparison.lean` (147 lines)

- **Totals**: 5 declarations — 3 noncomputable `def`s (`geomPoint`, `pointSpecPointsEquiv`, `geomFibrePointAddEquiv`), 2 `lemma`s (`geomFibrePointAddEquiv_apply` @[simp], `affine_origin_order_gt_three`). 4 in `ModularCurves.EllipticCurve`, 1 (`affine_origin_order_gt_three`) at `ModularCurves` level.
- **Key API**: `geomFibrePointAddEquiv` — the [T-B6′-IFACE] scheme-fibre ↔ mathlib-affine-Weierstrass group isomorphism `E.Point (geomPoint B k) ≃+ (W.baseChange k).toAffine.Point`, **now FILLED** (map_add' proven via ModelRecord's rigidity route); plus its building blocks `geomPoint`, `pointSpecPointsEquiv` and the Y1-vi affine core `affine_origin_order_gt_three`. Direct importers: `EllipticCurve/MulByHomQuasiFinite.lean`, `ModularCurve/YOneAssembly.lean` (plus transitive users `MulByHomUnramified`, `YOneAtlasClassify`).
- **Unused-in-file / project**: none — all 5 declarations have external consumers.
- **CODE-sorry list**: **none** (zero `sorry` terms in the file). NB the module docstring (lines 8–31) is STALE: it still announces "only `map_add'` carries the `sorry`" — the sole safe cleanup here is a docstring refresh; the declaration docstring already says FILLED.
- **set_option**: none.
- **Proofs > 30 lines**: none (map_add' ~17 lines; `affine_origin_order_gt_three` ~23 lines).
- **Private/public**: all public; no `private`, no `instance`. One `omit [(W.baseChange k).IsElliptic] in` before the simp lemma. File placement note: despite living in `ForMathlib/`, the file is project-specific (imports PointsDictionary/ModelRecord; ModularCurves types in every statement except `affine_origin_order_gt_three`, which alone is genuinely mathlib-adjacent); the `LevelStructure.ExactOrder` import appears vestigial (nothing from it is referenced — verify with a build before removal).

### File Summary — `EllipticCurve/Torsion.lean` (231 lines)

- **Totals**: 20 declarations — 5 `def`s (`NIsInvertible` (`_root_`), and noncomputable `torsion`, `torsionι`, `torsionπ`, `pointToTorsion`), 1 `instance` (`mulByHom_isProper`), 14 `theorem`s (2 @[simp]: `pointToTorsion_torsionπ`, `pointToTorsion_torsionι`; 1 @[reassoc]: `torsionι_π`). Namespace `ModularCurves.EllipticCurve` with two `_root_` escapes (`NIsInvertible`, `isEmpty_of_nIsInvertible_zero`).
- **Key API**: the definitional spine of workstream B — `torsion` (`E[N]` as kernel pullback), `torsionι`/`torsionπ`, `pointToTorsion` (+ simp lemmas), `torsionι_isClosedImmersion` (T-B3), and the KM 2.3.1 headline surface `torsionπ_isFinite` / `torsionπ_flat` / `torsion_rank` (T-B4), plus the project-wide `NIsInvertible` and `mulByHom_locallyOfFinitePresentation`. 14+ downstream files consume the torsion API.
- **Unused-in-file / project**: `mulByHom_zero` and `mulByHom_finrank` are in-file-only (helper for `torsionπ_flat` resp. input to `torsion_rank`) — fine; `mulByHom_isProper` greps in-file-only but is an `instance` consumed invisibly by instance search downstream (undercounted by grep). No genuinely dead declarations.
- **CODE-sorry list**: `mulByHom_locallyQuasiFinite` (BB-QF, line 141), `mulByHom_flat` (BB-FLAT, line 147), `mulByHom_finrank` (BB-DEG, line 153) — the three KM 2.3.1 black-box register items. Producer WIP — untouchable. Context: the `N`-invertible analogues of BB-QF are already proven downstream (`MulByHomQuasiFinite.lean`: `mulByHom_locallyQuasiFinite_of_nIsInvertible`, `mulByHom_isFinite_of_nIsInvertible`); `MulByHomFlat.lean` is the staged BB-FLAT discharge; the former BB-DIFF sorries were relocated and PROVEN in `MulByHomUnramified.lean` (trailing comment, lines 222–227, documents this).
- **set_option**: none.
- **Proofs > 30 lines**: none (longest: `torsionπ_flat` ~17 lines, `mulByHom_zero` ~12, `torsionι_π` ~11 calc lines).
- **Private/public**: all public; no `private`. One public `instance` (`mulByHom_isProper`). Local `attribute [local instance]` for the Over monoidal structure.

# Decomposition: fibrewise versus locally Weierstrass

Date: 2026-07-09. Ticket: `T-W-cmp` / `T-A7-cmp`.

## Correct theorem

The old board shorthand

```lean
FibrewiseElliptic π z hz → LocallyWeierstrass π z hz
```

is not the comparison theorem in Katz--Mazur, Hida, Deligne--Rapoport, or the Stacks
Project. `FibrewiseElliptic` only records pointed models of the residue-field fibres. It
does not contain the global smoothness or properness assumptions. Those are part of the
abstract definition and are mathematically load-bearing, not junk hypotheses.

The exact predicate-level target is:

```lean
theorem locallyWeierstrass_iff_abstractConditions
    {E S : Scheme} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S} :
    LocallyWeierstrass π z hz ↔
      SmoothOfRelativeDimension 1 π ∧ IsProper π ∧ FibrewiseElliptic π z hz
```

The useful converse helper should have no further hypotheses:

```lean
theorem FibrewiseElliptic.locallyWeierstrass
    (hsm : SmoothOfRelativeDimension 1 π) (hproper : IsProper π)
    (h : FibrewiseElliptic π z hz) : LocallyWeierstrass π z hz
```

At record level this says that replacing `EllipticCurveGeom.localModel` by the abstract
smooth/proper/fibrewise field does not change the class of objects.

## Source audit

Sources read from `refs/ModularCurves/`:

- Katz--Mazur, *Arithmetic Moduli of Elliptic Curves*, §§2.2.1--2.2.5, printed
  pp. 67--69. The section supplies the invertible sheaf `ω_{E/S}`, base change, the
  locally-free rank-`n` modules `f_* I(0)^{-n}`, coordinates `x,y`, and the generalized
  Weierstrass equation.
- Hida, *Geometric Modular Forms and Elliptic Curves*, Definition 2.2.1 (p. 107) and
  §§2.2.4--2.2.5 (pp. 111--115). Definition 2.2.1 includes properness, smoothness,
  connected genus-one fibres, and a section. The later sections give the relative
  Riemann--Roch/base-change construction of `x,y` and the cubic embedding.
- Stacks Project, Tag 072J: the abstract definition again includes properness and
  smoothness of relative dimension one. Tag 072T records that every such elliptic curve
  is Zariski-locally Weierstrass. Tag 0A1G, especially Lemma 36.30.4 and Remark 36.30.2,
  gives the arbitrary-base perfect-complex/base-change theorem needed by the proof.

## Dependency correction

This comparison does **not** use `Pic⁰`, a group law, or Abel's theorem. It constructs a
degree-three projective embedding directly from the pole line bundles of the zero
section. Consequently T-A6 (`abelEnrichment`) is not a dependency.

The current Lean predicate `FibrewiseElliptic` is stronger than a bare cohomological
genus-one condition: every fibre already comes with an explicit pointed elliptic
Weierstrass model. Therefore the field-level dimensions and pole bases can be transported
from `EllipticCurve/PoleFiltration.lean`; BB-RR and T-A9 are not needed for this bridge.
They remain necessary only for proving that the eventual cohomological genus-one
predicate is equivalent to `FibrewiseElliptic`.

## Proof decomposition

### 0. Forward implication -- proved

`LocallyWeierstrass.fibrewiseElliptic` is proved in `Basic.lean`. The current development
also proves `isProper_of_locallyWeierstrass` and
`smoothOfRelativeDimension_of_locallyWeierstrass` in `Moduli/EngineDescent.lean`, by
checking both morphism properties on the affine Weierstrass cover and transporting them
across the chart isomorphism. These three axiom-clean declarations give the forward half
of the target equivalence; the integration pass does not duplicate them under new wrapper
names in `Basic.lean`.

### 0b. Globally presented Weierstrass models -- proved

The comparison is complete when the family is already `projModel W`:

```lean
fibrewiseElliptic_iff_locallyWeierstrass_projModel W
```

The proof identifies both sides with `W.IsElliptic`. The reverse fibre argument is
`isElliptic_of_fibrewiseElliptic_projModel`; the forward local-model argument is the
generic top-chart theorem `locallyWeierstrass_projModel`. Thus the remaining general
work is not recognition of an equation but construction of a local equation from the
abstract family. These declarations are axiom-clean, and the generic top-chart theorem
also discharges Y1-B1.

### 1. The zero divisor and its pole sheaves -- `T-W-cmp.DIV`

For a smooth relative curve, the section is a regular closed immersion of codimension
one. Its ideal `I([0])` is therefore invertible. Construct
`O(n[0]) = I([0])^{-n}` together with:

- `O → O([0]) → O(2[0]) → ...`;
- multiplication `O(m[0]) ⊗ O(n[0]) → O((m+n)[0])`;
- compatibility with arbitrary base change;
- identification of the restriction to each fibre with the pole sheaf at its marked
  point.

Current reusable work: `sectionDivisor`, its degree-one theorem, and divisor base-change
in `LevelStructure/CartierDivisor.lean`; `Picard/InvertibleSheaf.lean` has the local
invertibility vocabulary. `Picard/Dual.lean` now constructs the genuine module dual
`Hom_O(M,O)`, including the local-linearity sheaf proof, `O^∨ ≅ O`, and contravariant
functoriality. It also proves that duals preserve local trivializations and invertibility.
The section-specific official Cartier statement is proved as
`RelEffCartierDiv.sectionDivisor_isOfficial`, directly from the axiom-clean local
principal-nonzerodivisor theorem. `EllipticCurve/PoleSheaf.lean` now constructs the
kernel ideal as a bundled module sheaf and proves `sectionIdealModule_isInvertible` by
explicit local generator isomorphisms. It further constructs the invertible simple-pole
sheaf `O([0])`, the coherent tensor powers `O(n[0])`, all filtration maps, and the
multiplication maps. The completed localization argument in
`ForMathlib/SheafOfModulesMonoidal.lean` has been transported to a coherent monoidal
structure on scheme modules. Restriction along an open immersion is now proved to commute
with module sheafification and the sheafified tensor product; this removes the old general
pullback/tensor `sorry` from `IsInvertible.tensorObj`. Consequently
`sectionPoleSheafPower_isInvertible` proves every `O(n[0])` locally trivial and invertible,
axiom-clean. Missing: arbitrary-base-change compatibility and fibrewise identification with
`poleOrderFiltration`. The generic
Cartier-divisor part of base change is now complete:
`RelEffCartierDiv.sectionDivisor_baseChange` identifies the divisor of the base-changed
section for every morphism of bases. At the bundled module level,
`restrictIdealModuleIso` proves that an open restriction of a quasi-compact morphism's
kernel module is the module of the pulled-back kernel ideal; specializing gives
`sectionIdealModuleRestrictIso`. Thus Zariski localization on the base is now compatible
with the zero ideal, without an exactness hypothesis on a general pullback functor.
Both results are axiom-clean. Still missing: arbitrary pullback of the bundled ideal and
pole sheaves, and the residue-fibre identification with `poleOrderFiltration`. The generic
`RelEffCartierDiv.isOfficial` still depends on the registered
`officialAux_exists_finite_chart` `sorry`; it is not needed for the zero section and must
not be treated as an axiom-clean discharge.

### 2. Geometric cohomology and base change -- `T-W-cmp.COH3` (blocking)

Over an affine base `Spec A`, construct a finite complex of finite projective
`A`-modules computing the cohomology of each `O(n[0])` after every affine base change.
For relative curves it may be truncated to amplitude `[0,1]`. This is the geometric
half of the Grothendieck-complex theorem in Stacks 0A1G / Mumford §5.

The module-theoretic half is already formalized and axiom-clean in
`ForMathlib/BaseChangeKerCoker.lean`: cokernel base change, kernel base change under the
flat-cokernel condition, finite projectivity, and the algebra-form base-change
equivalence. What is absent is the comparison from scheme/sheaf cohomology to that
finite complex. Mathlib PR #36345 currently proves only affine vanishing and remains a
draft; it does not provide proper pushforward or arbitrary-base cohomology and base
change.

No theorem in this stream may replace this leaf by a `CohomologyPackage` hypothesis,
an axiom, or an unboarded `sorry`.

### 3. Relative pole modules -- `T-W-cmp.POLE`

Apply Step 2 to `O(n[0])`. Fibrewise, transport along the explicit model supplied by
`FibrewiseElliptic` and use the pole filtration to prove:

```text
H¹(E_s, O(n[0])) = 0,       n >= 1,
rank H⁰(E_s, O(n[0])) = n,  n >= 1.
```

Conclude, after shrinking the base, that `π_*O(n[0])` is locally free of rank `n` and
commutes with base change. A sheaf-level comparison between `O(n[0])` on a projective
model and the existing algebraic `poleOrderFiltration` remains to be added.

### 4. Choose `x` and `y` -- `T-W-cmp.XY`

After a further Zariski shrink, split the inclusions in the pole filtration and choose
bases

```text
P_1 = A·1,
P_2 = A·1 + A·x,
P_3 = A·1 + A·x + A·y,
```

with `x` of exact pole order 2 and `y` of exact pole order 3. The choices are unique up
to the standard changes `x ↦ x+r`, `y ↦ y+s*x+t` (and unit rescaling before fixing a
parameter).

### 5. Derive the cubic -- `T-W-cmp.REL`

The seven elements

```text
1, x, y, x^2, x*y, y^2, x^3
```

lie in the rank-six module `P_6`. Pole orders force the unique dependence to have the
generalized Weierstrass shape

```text
y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6.
```

This step is finite locally-free module algebra once Step 3 is available.

### 6. Identify the family -- `T-W-cmp.EMBED`

Use the basis `1,x,y` of `P_3` to define `E → P^2_S`. Prove `O(3[0])` is relatively
very ample, hence this map is a closed immersion, and identify the image with the cubic
of Step 5. The zero section maps to `(0:1:0)`. This needs a relative very-ampleness /
closed-immersion API; current projective-space and Proj closed-immersion infrastructure
only handles an already-presented graded equation.

### 7. Unit discriminant -- `T-W-cmp.ELL` -- DONE

Landed as `isElliptic_of_fibrewiseElliptic_projModel`. For a hypothetical maximal ideal
containing the discriminant, base-change the model to its residue field and compose the
canonical fibre identification with the pointed elliptic model supplied by
`FibrewiseElliptic`. The existing theorem `pointedIso_exists_variableChange` makes this
pointed isomorphism a variable change, so the base-changed discriminant is a unit. It is
also zero by membership in the chosen maximal ideal, a contradiction. The theorem is
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`). Once Step 6 supplies the cubic
identification, this theorem packages it as the elliptic model required by
`LocallyWeierstrass`.

This route deliberately avoids a second board drift discovered in this audit: the old
T-A3 heading claimed an iff, but the landed `projModel_smooth` proves only unit
discriminant implies smoothness. The reverse theorem is separately ticketed as T-A3rev;
it is not needed here because `FibrewiseElliptic` provides stronger input.

### 8. Assembly -- `T-W-cmp.BACK` and `T-W-cmp.IFF`

Repeat Steps 1--7 near every base point, then combine the converse with
`LocallyWeierstrass.fibrewiseElliptic`, `isProper_of_locallyWeierstrass`, and
`smoothOfRelativeDimension_of_locallyWeierstrass` to prove the exact equivalence. Only
after this predicate theorem should the record equivalence be packaged.

## Drift guards

- Do not state the converse from `FibrewiseElliptic` alone.
- Do not add noetherianity to the final theorem. A noetherian intermediate is acceptable
  only with a separately ticketed approximation step to arbitrary bases.
- Do not assume a prepackaged pole/cohomology/embedding object merely to make assembly
  tautological.
- Do not route through `Pic⁰` or the group law; neither occurs in the source proof of the
  Weierstrass embedding.
- Do not count the existing model-side `PoleFiltration` as the relative pole-sheaf result;
  the sheaf and base-change bridge is substantive.

## Ownership -- `[OWNER-FLW]`

Single-branch rule: all implementation and later monoidal reconciliation for this stream
lands on `codex/fibrewise-weierstrass-comparison`. Other workers review and reuse this
branch; they do not fork parallel implementations of these targets.

Exact theorem targets reserved by this branch:

1. `locallyWeierstrass_iff_abstractConditions`:
   `LocallyWeierstrass π z hz ↔ SmoothOfRelativeDimension 1 π ∧ IsProper π ∧
   FibrewiseElliptic π z hz`.
2. `FibrewiseElliptic.locallyWeierstrass`:
   `SmoothOfRelativeDimension 1 π → IsProper π → FibrewiseElliptic π z hz →
   LocallyWeierstrass π z hz`, with no additional hypotheses.

Integration scope: land `Dual.lean`, `PoleSheaf.lean`, this decomposition artifact, and
the global-model declarations in `Comparison.lean`; consume PIC0's landed
`IsInvertible.tensorObj`. The branch-local pullback-tensor map layer remains preserved on
`codex/fibrewise-weierstrass-comparison-pre-rebase` for PIC0 integration.

Completed dependency claim (2026-07-14): proved
`SpreadData.FunctorModel.baseChangeSpecIso_inv_affineIntersectionOverlapι`,
`affineIntersectionGluedBaseChange`, `affineIntersectionGluedBaseChange_isPullback`, and
`affineIntersectionGluedBaseChangeIso`, with no option, noetherianity, new sorry, or extra
geometric hypothesis; these globalize the spread chart comparisons needed for arbitrary-base
pole-sheaf cohomology.

Completed dependency claim (2026-07-14): proved
`Scheme.Hom.affineIntersectionModelBaseChangeIso`, identifying a proper family's original
scheme with the base change of a spread finite-stage affine-intersection model. This packages
the preceding global comparison for later descent of the pole line bundle, with no option,
noetherianity, new sorry, or additional geometric hypothesis.

Completed dependency claim (2026-07-14): proved
`Scheme.Hom.exists_affineIntersectionModelBaseChangeIso_of_isProper`, producing the finite
affine cover, spread model, finite-stage gluing conditions, and the resulting base-change
isomorphism in one theorem consumable by pole-sheaf descent.

Completed dependency claim (2026-07-14): proved
`Scheme.Hom.isAffineOpen_finiteIntersectionOpen_of_isProper`,
`exists_affineIntersectionModelAtLaterStage_of_isProper_of_cover`, and
`exists_affineIntersectionModelBaseChangeIso_of_isProper_of_cover`. These permit using a
finite affine cover that already trivializes the pole line bundle, rather than introducing
a second cover.

Completed dependency claim (2026-07-14): proved
`Scheme.Modules.IsInvertible.exists_affineIntersectionModelBaseChangeIso_of_isProper`,
packaging a finite affine trivializing cover of an invertible sheaf together with the
finite-stage proper model and its base-change isomorphism.

Completed dependency claim (2026-07-14): proved
`ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv`,
`Scheme.Modules.trivializationTransitionUnit`, and its identity, inverse, and transitivity
laws. Thus changes between two trivializations on one open are represented by genuine units
of its section ring, with the expected cocycle equations and no extra hypotheses.

Completed dependency claim (2026-07-14): moved the generic
`ModularCurves.restrictOverTrivialization_hom_eq_comp_scalar` out of `PoleSheaf.lean` into
the Picard restriction layer, and proved `trivializationTransitionUnit_restrict`. The latter
identifies transition units after restricting trivializations with restriction of the
original unit along the structure-sheaf map.

Completed dependency claim (2026-07-14): defined open-subscheme transition units,
`trivializingCoverTransitionUnitOn` on arbitrary common refinements, and the canonical
`trivializingCoverTransitionUnit` on pairwise overlaps. Proved the common-refinement and
triple-overlap cocycle laws.

Completed dependency claim (2026-07-14): proved
`overTrivializationOfRestrictIso_injective`, `restrictOpenTrivialization_comp`,
`openTrivializationTransitionUnit_restrict`,
`trivializingCoverTransitionUnit_restrict`, and
`trivializingCoverTransitionUnit_cocycle`. The canonical pair-overlap units now form literal
finite Cech descent data on triple overlaps.

Completed dependency claim (2026-07-14): proved
`Algebra.IsFilteredAlgColimit.exists_common_unit_lift`. A finite family of units in a
filtered colimit now lifts to actual units at one common stage, by synchronizing values,
inverses, and their inverse equations without any injectivity hypothesis on transition maps.

Completed dependency claim (2026-07-14): proved
`Algebra.SpreadData.exists_common_unit_lift_atLaterStage`, which lifts those units at a
stage later than any prescribed index and identifies their images under the presented
stage-to-colimit map.

Completed dependency claim (2026-07-14): proved
`Algebra.SpreadData.FunctorModel.exists_common_unit_liftAtLaterStage`. Units belonging to
finitely many varying objects of a spread functor can now be represented simultaneously
at one common later stage, while the entire affine-intersection functor moves with them.

Completed dependency claim (2026-07-14): exposed
`Algebra.SpreadData.exists_common_stage_eq` and proved
`Algebra.SpreadData.FunctorModel.exists_common_eq_atLaterStage`. Finite families of
colimit equalities in varying functor objects can now be made literal at one later stage;
the proof is decomposed through the one-object wrapper and uses no heartbeat override.

Completed dependency claim (2026-07-14): proved
`trivializingCoverTransitionUnitOn_restrict`. Transition units on arbitrary common
refinements are now functorial under further restriction, which connects the local Cech
cocycle to the restriction maps in the affine-intersection algebra functor.

Completed dependency claim (2026-07-14): defined
`affineIntersectionTransitionUnit` and proved
`affineIntersectionTransitionUnit_map` and
`affineIntersectionTransitionUnit_trans`. Thus transition units live directly in every
nonempty object of the affine-intersection coordinate-ring functor, commute with all its
restriction maps, and satisfy the multiplicative transition law there.

Completed dependency claim (2026-07-14): exposed the affine-gluing diagram's canonical
triple index and its left, middle, and right pair-to-triple arrows. The line-bundle Cech
equations can therefore use the same finite-intersection indexing API as the existing scheme
gluing construction.

Completed dependency claim (2026-07-14): defined
`affineIntersectionPairTransitionUnit` and proved
`affineIntersectionTransitionUnit_cocycle`. The finite family indexed by ordered chart pairs
now restricts along the canonical pair-to-triple arrows to a literal multiplicative Cech
equation in every triple object.

Completed dependency claim (2026-07-14): proved
`FunctorModel.mapToStage_map_stageTransition`,
`FunctorModel.mapToStage_map_unitTransition`, and
`FunctorModel.exists_common_unit_eq_atLaterStage`. Functor maps now commute explicitly with
later-stage transport, and finite families of colimit unit equalities can be synchronized as
literal equalities at one common stage.

Completed dependency claim (2026-07-14): proved `FunctorModel.map_unit_colimit`, the unit-level
naturality square between a finite-stage functor map and its target-colimit map. This rewrites
the synchronized finite-stage Cech equations directly to the geometric transition-unit
equations.

Completed dependency claim (2026-07-14): introduced the exact multiplicative descent package
`AffineIntersectionUnitCocycle` and constructed `affineIntersectionUnitCocycle` from an
invertible sheaf's chosen affine trivializations. It records only pair transition units and
their canonical triple equation, with no auxiliary sheaf or cohomology hypothesis.

Completed dependency claim (2026-07-14): proved
`AffineIntersectionUnitCocycle.exists_modelAtLaterStage`. A finite family of pair-overlap
units now lifts to actual units after moving the spread functor to a later stage, every triple
Cech equation holds literally there, and each descended unit maps back to its original
colimit transition unit.

Completed dependency claim (2026-07-14): proved
`AffineIntersectionUnitCocycle.transition_self`, `transition_mul_swap`, and
`transition_swap`. Thus the diagonal transition is one and reversing an ordered overlap
gives the inverse transition after the canonical pair-swap, derived from the triple cocycle
rather than stored as extra descent hypotheses.

Completed dependency claim (2026-07-14): defined
`AffineIntersectionUnitCocycle.overlapTransitionSection` and proved its identity, pair-swap
inverse, and triple-intersection Cech laws. The descended ring units are now genuine invertible
global functions on the finite-stage overlap schemes, compatible with the geometric restriction
maps used by affine gluing.

Completed subdependency (2026-07-14): defined `ModularCurves.unitAutomorphismOfTopUnit`,
which packages multiplication by an invertible top-open section as an automorphism of the
scheme's structure module. Its inverse is multiplication by the inverse unit, using the existing
scalar-composition API and no additional hypotheses.

Completed dependency claim (2026-07-14): defined
`AffineIntersectionUnitCocycle.overlapTransitionIso` and proved its identity, pair-swap inverse,
and triple-intersection Cech laws after canonical pullback. The finite-stage transition functions
therefore give axiom-clean scalar automorphisms of the overlap structure sheaves satisfying the
full line-bundle descent equations.

Completed subdependency (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartTransitionIso`. On the ordered overlap `V i j`, it is the
isomorphism from the pullback of the `i`th chart's unit sheaf to the pullback of the `j`th chart's
unit sheaf along `t i j ≫ f j i`, obtained by conjugating the scalar transition through the two
canonical pullback-unit isomorphisms.

Completed dependency claim (2026-07-14): in a new `InvertibleSheafGlueData` layer, prove
`chartTransitionIso_toUnit` and the diagonal, pair-swap inverse, and triple-overlap coherence
equations for `AffineIntersectionUnitCocycle.chartTransitionIso`, with all type transports supplied
by the existing `pullbackCongr`/`pullbackComp` API. Package exactly these laws as local module
descent data suitable for gluing on the finite-stage proper scheme.

Completed subdependency (2026-07-14): introduced `InvertibleSheafGlueData.lean` and proved
`AffineIntersectionUnitCocycle.chartTransitionIso_toUnit` together with the type-correct diagonal
law `chartTransitionIso_self`. The latter identifies the diagonal transition with canonical
`pullbackCongr` transport along `f i i = t i i ≫ f i i`; both declarations are option-free and
axiom-clean.

Completed subdependency (2026-07-14): proved
`AffineIntersectionUnitCocycle.chartTransitionIso_inv_toUnit` and
`pullback_chartTransitionIso_toUnit`, then isolated the entry and exit normalization halves of the
pair-swap law using the existing `pullbackComp` and `pullbackCongr` coherence. The public coordinate
laws are option-free and depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Completed dependency claim (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartTransitionIsoSwapHom`, the reverse chart transition transported
along the glue-data pair swap in canonical pullback-unit normal form, and proved
`chartTransitionIsoSwapHom_eq_inv`. Thus the chart transitions satisfy the full pair-swap inverse
law without any added hypothesis or proof resource option; both declarations are axiom-clean.

Completed subdependency (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback` for an arbitrary map into an
ordered overlap and proved `chartTransitionIsoCoordinatePullback_eq`. Thus every further pullback of
a chart transition is canonically multiplication by the pulled transition section on the unit
sheaf; the construction is option-free and axiom-clean.

Completed dependency claim (2026-07-14): proved
`AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback_cocycle`. On the canonical
affine triple intersection, the three pulled chart transitions satisfy the Cech equation, by
reducing all three module maps to the existing scalar transition cocycle. This completes the
diagonal, pair-swap inverse, and triple-overlap coherence layer without additional hypotheses or
proof resource options.

Completed subdependency (2026-07-14): defined `Scheme.Modules.pullbackPseudofunctor` by taking
the left-adjoint part of mathlib's existing scheme-module pseudofunctor, and defined
`affineIntersectionChartChosenPullback` from the actual geometric pullback square
`V i j = U i ×_X U j` in the glued scheme. These axiom-clean constructors put the local unit
modules in the exact input format of mathlib's `Pseudofunctor.DescentData'` API.

Completed subdependency (2026-07-14): proved
`affineIntersectionTripleIsPullbackMiddle` and defined
`affineIntersectionChartTripleMiddleChosenPullback` and
`affineIntersectionChartChosenPullback₃`. The canonical affine triple intersection is now the
chosen pullback of adjacent pair overlaps over the middle chart, with all three legs definitionally
given by the existing left, middle, and right restriction maps. The construction is option-free and
all three public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Completed dependency claim (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartDescentData`, packaging the chartwise unit modules and overlap
transition morphisms as mathlib `Pseudofunctor.DescentData'` for the canonical pair and triple
pullbacks. Its diagonal and triple fields are proved from the previously established transition
laws, it introduces no additional hypotheses or proof-resource options, and its axiom audit is
exactly `propext`, `Classical.choice`, and `Quot.sound`. This is the effectivity input for gluing the
finite-stage invertible sheaf before identifying its pullback with the original pole sheaf.

Completed dependency claim (2026-07-14): in `InvertibleSheafGlueEffectivity.lean`, construct
`AffineIntersectionUnitCocycle.gluedModule` as the concrete Cech equalizer attached to
`chartDescentData`, prove `AffineIntersectionUnitCocycle.gluedModuleRestrictIso` on every chart,
and derive `AffineIntersectionUnitCocycle.gluedModule_isInvertible` without adding hypotheses.

Completed subdependency (2026-07-14): proved `Scheme.Modules.restrictFunctor_preservesLimits`.
Restriction along an open immersion therefore carries the chart Cech product and equalizer to
their local counterparts; the proof is option-free and its axiom audit is exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Completed subdependency (2026-07-14): defined
`Scheme.Modules.restrictPushforwardUnitIsoOfIsPullback`. For a pullback square whose vertical
maps are open immersions, restriction of the pushforward of the structure sheaf is canonically
the pushforward of the pullback structure sheaf. This gives the chart-overlap factor
identification needed by the local Cech equalizer; the construction is option-free and its axiom
audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Completed subdependency (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartExtensionRestrictIso`. Restricting the `i`th chart-extension
to `U_k` is now canonically identified with the pushforward of `O_{V(i,k)}` along the right-hand
overlap leg. This is the factorwise local description of the Cech product; it is option-free and
its axiom audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Completed subdependency (2026-07-14): defined
`AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso` and proved its projection formula
`chartGlueSourceRestrictIso_hom_π`. The restricted chart Cech source is therefore identified
with the product of all ordered-overlap pushforwards, compatibly with every product projection.
Both declarations are option-free and their axiom audits are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Completed subdependency (2026-07-14): defined
`AffineIntersectionUnitCocycle.overlapExtensionRestrictIso`,
`chartGlueTargetRestrictIso`, and `chartGlueTargetRestrictIso_hom_π`. Restricting an overlap
extension to `U_k` is the structure sheaf pushed forward from the canonical triple intersection,
and the full restricted Cech target is the product of these factors, compatibly with projection.
The proof pastes the existing chosen-pullback squares and introduces no new geometric hypotheses;
all declarations are option-free and their axiom audits are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Completed subdependency (2026-07-14): constructed the chart-local tuple whose `i`th component is
the adjoint of the inverse transition from `U_k` to `V(i,k)`, transported it into the restricted
Cech source, and proved the inverse triple-overlap identity
`g_ik⁻¹ ∘ g_ij = g_jk⁻¹` from the existing cocycle theorem. Also proved the inverse
projection formula `chartGlueSourceRestrictIso_inv_π`. The construction is option-free, adds no
hypotheses, and the new public projection formula depends only on `propext`, `Classical.choice`,
and `Quot.sound`.

Completed subdependency (2026-07-14): constructed the module-valued open-cartesian base-change
isomorphism natural in the input module and proved that its structure-sheaf specialization agrees
with `Scheme.Modules.restrictPushforwardUnitIsoOfIsPullback`. This supplies the naturality needed
to normalize the two restricted Cech arrows without adding a second public base-change API; the
new comparison layer is private, option-free, and introduces no new hypotheses.

Completed subdependency (2026-07-14): proved
`AffineIntersectionUnitCocycle.gluedModuleRestrictIso` by identifying the restricted Cech
equalizer with the chart unit module and proving both inverse identities from componentwise
overlap compatibility. The chart image opens cover the glued scheme by joint surjectivity, so
these local trivializations yield `AffineIntersectionUnitCocycle.gluedModule_isInvertible`.
Both public declarations are option-free, add no hypotheses, and their axiom audits are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Completed dependency claim (2026-07-15): proved
`AffineIntersectionUnitCocycle.gluedModuleDescentIso`, identifying the descent datum induced by
`gluedModule` with the existing `chartDescentData`. Its component isomorphisms are the proved
`gluedModuleRestrictIso` transported through `restrictFunctorIsoPullback`, and the overlap square
recovers `chartDescentHom` from the Cech equalizer compatibility. The construction is option-free,
adds no hypotheses, and its axiom audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Completed dependency claim (2026-07-15): proved
`AffineIntersectionUnitCocycle.gluedModuleIsoOfDescentIso`. For any module `M` on the
affine-intersection glued scheme, an isomorphism from the pullback descent datum induced by `M`
to `chartDescentData` now induces a global isomorphism
`M ≅ AffineIntersectionUnitCocycle.gluedModule`. The forward map is constructed through the
concrete Cech equalizer; its pullback to each chart is identified with the supplied descent
isomorphism, and Zariski-local detection proves it is globally invertible. The proof adds no
geometric hypotheses or proof-resource options. The focused module build is green, and the
axiom audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Completed dependency claim (2026-07-15): proved
`Scheme.Hom.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso`.
This exposes the chartwise factorization of the canonical glued-to-original morphism as the affine
chart-coordinate isomorphism followed by the original open immersion. This is the geometric
identity needed to transport an original invertible sheaf's chosen trivializations to the glued
model before comparing its descent datum with `AffineIntersectionUnitCocycle.chartDescentData`.
The focused build is green, and the axiom audit is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

Completed dependency claim (2026-07-15): proved
`affineIntersectionOriginalChartTrivialization`. Given chosen trivializations of a module `N`
on opens `U i`, this identifies the restriction to every affine chart of the pullback of `N` along
`affineIntersectionGluedToOriginal` with the unit module. The construction uses the public
chart-factorization equality and the existing pullback composition/unit isomorphisms, without
adding cover, properness, finiteness, or proof-resource hypotheses. The focused module build is
green, and the axiom audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Active dependency claim (2026-07-15): prove
`affineIntersectionOriginalChartTrivialization_transition`. On every chosen pairwise pullback,
show that the chartwise trivializations of the pulled-back original module intertwine its
canonical pullback descent morphism with
`(affineIntersectionUnitCocycle π U e).chartTransitionIso`. This is the sole compatibility
needed to package the local comparisons into an isomorphism of descent data; no extra geometric
hypotheses or proof-resource options may be introduced.

Completed spawned dependency (2026-07-15): exposed the existing proofs
`Scheme.Hom.affineIntersectionGlueData_f_chartIso` and
`Scheme.Hom.affineIntersectionGlueData_t_f_chartIso` as public lemmas. They identify the two
ordered glue-map routes to charts with the affine overlap-coordinate isomorphism followed by the
left and right inclusions of `U i ⊓ U j`. The active transition-square proof consumes these exact
factorizations, with no duplicate comparison construction. The focused build is green, and both
axiom audits are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Completed spawned dependency (2026-07-15): proved
`openTrivializationTransitionUnit_hom`. For two trivializations `e` and `g` of a module on an
open subscheme, identify the change of basis `e.inv ≫ g.hom` with the unit-sheaf endomorphism
defined by the top-section image of `openTrivializationTransitionUnit M U e g`. This is the
scheme-module translation of the existing over-site theorem
`overUnitScalarEnd_transitionUnit`; it adds no hypotheses or proof-resource options. The focused
build is green, and its axiom audit is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Active spawned dependency (2026-07-15): prove
`affineIntersectionUnitCocycle_overlapTransitionSection`. Under
`affineIntersectionOverlapIso`, identify the overlap section of
`affineIntersectionUnitCocycle π U e` with the top-section image of the original transition unit
between the restrictions of `e i` and `e j` to `U i ⊓ U j`. This is the scalar-coordinate bridge
needed by `affineIntersectionOriginalChartTrivialization_transition`; it adds no hypotheses or
proof-resource options.

Completed spawned dependencies (2026-07-15): exposed the existing private proofs as
`Scheme.finiteIntersectionOpen_affineIntersectionPairIndex` and `topIso_inv_naturality`. The
first identifies the geometric open attached to the public pair index with `U i ⊓ U j`; the
second transports the inverse top-section comparison along an inclusion of opens. These remove
duplicate local arguments from `affineIntersectionUnitCocycle_overlapTransitionSection` without
introducing new constructions or hypotheses. The focused build is green, and both axiom audits
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

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

Active dependency claim (2026-07-14): prove restriction compatibility for
`trivializationTransitionUnit`, then package the resulting pairwise units and triple-overlap
cocycle for a finite affine trivializing cover. This is the finite descent datum needed to
spread the pole line bundle together with the proper affine-intersection model.

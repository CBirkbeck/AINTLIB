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
axiom-clean. The generic Cartier-divisor part of base change is complete:
`RelEffCartierDiv.sectionDivisor_baseChange` identifies the divisor of the base-changed
section for every morphism of bases. At the bundled module level,
`restrictIdealModuleIso` proves that an open restriction of a quasi-compact morphism's
kernel module is the module of the pulled-back kernel ideal; specializing gives
`sectionIdealModuleRestrictIso`. Thus Zariski localization on the base is now compatible
with the zero ideal, without an exactness hypothesis on a general pullback functor.
Both results are axiom-clean. The arbitrary-base layer is now also complete:
`dualPullbackIsoOfIsInvertible` proves that the canonical pullback map on duals is an
isomorphism for invertible modules; `sectionPoleSheafBaseChangeIso` and
`sectionPoleSheafPowerBaseChangeIso` apply it to `O([0])` and all `O(n[0])`; and
`sectionPoleSheafFiberIso` specializes the construction to residue fibres. All are
axiom-clean and introduce no noetherianity or flatness hypothesis. The model-side
comparison is now also complete: `sectionPoleSheafPower_projModel_sectionsEquiv`
identifies global sections with the algebraic `poleOrderFiltration`, and
`sectionPoleSheafPower_projModel_basis` transports its explicit pole-monomial basis.
The project-local notion of invertibility is now connected to mathlib's sheaf API:
`Scheme.Modules.IsInvertible.isLocallyFree` builds genuine local rank-one generator
data from the existing trivializing cover, and `IsInvertible.isQuasicoherent` applies
mathlib's locally-free-implies-quasicoherent theorem. Consequently
`sectionPoleSheaf_isQuasicoherent` and `sectionPoleSheafPower_isQuasicoherent` supply
the exact quasicoherence hypotheses required by affine vanishing and coherent
cohomology, without changing the family hypotheses.
Finally, `EllipticCurve/PoleSheafPointedIso.lean` proves that a pointed scheme
isomorphism transports the section ideal module, its dual pole sheaf, and every tensor
power of the pole sheaf. This supplies the sheaf-level bridge from each explicit pointed
model in `FibrewiseElliptic` to the corresponding residue fibre, without using `Pic⁰` or
the group law. `EllipticCurve/PoleSheafFibreSections.lean` evaluates this transport on
global sections over the common residue-field base and proves the resulting linear
equivalence.
The generic
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
equivalence. Its vanishing-cokernel endpoint is now arbitrary-base:
`Module.Projective.ker_of_surjective` and
`Module.Finite.ker_of_surjective_of_projective` identify the kernel of a surjective
differential between finite projectives as finite projective, while
`kerBaseChangeComparison_bijective_of_surjective` proves that this kernel commutes with
every algebra base change. Thus the older noetherian flat-cokernel fallback is not needed
for the pole sheaves. What is absent is the comparison from scheme/sheaf cohomology to
that finite complex. The affine-vanishing part of draft mathlib PR #36345 is now proved
option-free in this project, but that draft does not provide proper pushforward or
arbitrary-base cohomology and base change.

The scheme-module entry point to the existing cohomology API is now complete in
`ForMathlib/SchemeModuleSheaf.lean`: `Scheme.Modules.toSheaf` forgets to an additive
sheaf and is additive, faithful, finite-limit-preserving, and colimit-preserving.
Consequently a short exact sequence of scheme modules maps directly to a short exact
sequence of additive sheaves, so the remaining work can use mathlib's genuine
`Sheaf.H`/`Ext` definitions. This bridge does not assert affine vanishing or the missing
proper cohomology comparison.

The map-level base-change entry is now complete in
`ForMathlib/SchemeModulePushforwardBaseChange.lean`. The transformation
`Scheme.Modules.pullbackPushforwardBaseChange` is the Beck--Chevalley mate obtained from
pullback composition around the cartesian square and the pullback--pushforward counit.
`EllipticCurve/PoleSheafPushforwardBaseChange.lean` composes its component with
`sectionPoleSheafPowerBaseChangeIso`, giving the canonical comparison for
`π_*O(n[0])` under every base change. No invertibility is asserted yet: proving this
specific map invertible is exactly the remaining proper-cohomology input.

The exact-sequence layer for genuine sheaf cohomology is now also complete in
`ForMathlib/SheafCohomologyExact.lean`: `Sheaf.H.δ` constructs the connecting map,
`longSequence_exact` gives a six-term window of the long exact sequence, and the
`longSequence_exact₁/₂/₃` lemmas expose its elementwise lifting consequences.
The terminal-object bridge `longSequence_surjective_of_subsingleton_H` turns an `H¹`
vanishing statement for the kernel sheaf into surjectivity on global sections. This is
the exact formal mechanism needed for the pole-filtration restriction maps. The port is
option-free and axiom-clean; it deliberately omits the option-heavy functoriality layer
of upstream mathlib PR #36218. Proper cohomology/base change remains unresolved.

The first acyclicity dependency is now complete in
`ForMathlib/FlasqueCohomology.lean`. Free abelian sheaves represented by opens detect
restriction maps, injective additive sheaves are flasque, and
`TopCat.Sheaf.IsFlasque.H_isZero` proves that every positive cohomology group of a
flasque sheaf vanishes. The proof is split into the degree-one lifting argument and an
elementwise dimension-shifting step, so it needs none of the transparency options used
by upstream mathlib PR #35790. This result is one input to the local-killing/Kempf
argument for affine vanishing; it does not by itself prove that a quasicoherent sheaf on
an affine scheme is acyclic.

The open-restriction dependency for that argument is now complete in
`ForMathlib/TopCatSheafRestrict.lean`. It supplies restriction along an open embedding,
the restriction--pushforward adjunction and its unit formulas, additive restriction and
pushforward functors, and stability of flasqueness under restriction. Restriction of
additive sheaves preserves finite limits by identifying its underlying presheaf functor
with precomposition and reflecting finite diagrams through the sheaf inclusion. Together
with finite-colimit preservation from the left adjoint, this lets
`ShortComplex.ShortExact.map_of_exact` restrict short exact sequences directly. This
replaces the unproved right-adjoint instance in draft mathlib PR #36345 and uses no
options; it still does not assert affine quasicoherent vanishing.

The degree-one local-killing step is now complete in
`ForMathlib/KempfLocalKilling.lean`. Given a basis of opens, a class in `H¹(X,F)`,
and a point `x`, `TopCat.Sheaf.one_ex_opens_toRestrict_app_zero` produces a basis open
containing `x` on which the class restricts to zero. The proof takes an injective
presentation of `F`, represents the class by a global section of its cokernel, lifts that
section locally using local surjectivity, and compares the restricted cokernel sequence
with the restriction of the presentation. The comparison and section calculation are
separated into an option-free private helper. This is the base case for the higher-degree
induction recorded next; the application to quasicoherent sheaves on affine schemes remains.

The higher-degree induction is now complete as `TopCat.Sheaf.kempfProp1` in
`ForMathlib/KempfInduction.lean`. If a basis is closed under intersections and the
restrictions of `F` have vanishing cohomology in degrees `1` through `n`, every class in
`H^(n+1)(X,F)` restricts to zero on a cover by basis opens. The proof separates dimension
shifting for the cokernel of an injective presentation, short exactness after open
restriction and pushforward, and naturality of the connecting map. It reuses mathlib's
existing `IsOpenCover` API and needs no transparency options.

The affine localization application is now complete in
`ForMathlib/SchemeModuleQuasicoherent.lean` and
`ForMathlib/AffineVanishing.lean`. The first file transports the `tilde` equivalence
from spectra to arbitrary affine schemes, proving closure of quasicoherent modules under
colimits and finite products, quasicoherence of pushforward between affine schemes, and
surjectivity on global sections for epimorphisms. The second constructs the finite
product of open restriction-pushforwards, proves the cover map monic, and applies
`TopCat.Sheaf.kempfProp1` plus the long exact sequence to prove
`Scheme.Modules.affine_subsingleton_H`: every positive `Sheaf.H` of a quasicoherent
module on an affine scheme is subsingleton. All transparency-sensitive calculations are
split into ordinary helpers, so the result uses no options. The remaining Step 2 blocker
is therefore specifically proper cohomology and arbitrary-base change, not affine
acyclicity.

The generic two-chart degree-one calculation is now complete in
`ForMathlib/TwoOpenHOne.lean`. The theorem
`TopCat.Sheaf.subsingleton_H_one_of_two_open_cover` proves global `H¹` vanishing from
vanishing on two covering opens and surjectivity of the section-difference map on their
overlap. It uses an injective presentation, local lifts, exactness to correct their
overlap discrepancy, and ordinary sheaf gluing, avoiding the still-missing comparison
between `H'` and `Sheaf.H`. The result is option-free and axiom-clean. Its next use is the
explicit Laurent-overlap calculation for the section pole sheaves on the two affine
Weierstrass charts; it does not supply proper cohomology or arbitrary-base change.

That explicit model calculation is now complete in
`EllipticCurve/PoleSheafModelHOne.lean`. For every Weierstrass model over a field and
`n >= 1`, `exists_projModelPoleLocalSections_sub_eq` expresses every section of
`O(n[0])` on the chart overlap as a section-neighborhood restriction minus a
`Z`-chart restriction. The proof uses the localization description at the section
parameter, the identities `x*s^2 = v` and `y*s^3 = v` for a cofactor congruent to
one modulo `s`, and denominator induction to remove every principal part. Applying
the two-open criterion and affine quasicoherent vanishing gives
`sectionPoleSheafPower_projModel_subsingleton_H_one`. Local quasicoherence is obtained
from the existing chart trivializations, so this theorem needs neither model
smoothness nor noetherianity and introduces no option. This closes the geometric
model-side `H^1` input; arbitrary-family base change remains separate.

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
commutes with base change. The model-side rank input is proved uniformly over every
nonzero base ring as `sectionPoleSheafPower_projModel_finrank`, and
`sectionPoleSheafPowerPointedIso` supplies the sheaf-level transport from those models
to the residue fibres. The `H⁰` conclusion is now complete as
`FibrewiseElliptic.sectionPoleSheafPower_fiber_finrank`: for every residue fibre and
`n ≥ 1`, the global pole sections have dimension `n`. The model-side geometric
`H¹` vanishing is now also proved by
`sectionPoleSheafPower_projModel_subsingleton_H_one`. The transport is now complete as
`FibrewiseElliptic.sectionPoleSheafPower_fiber_subsingleton_H_one`: the generic theorem
`TopCat.Sheaf.subsingleton_H_of_iso` compares constant sheaves and Ext across a
homeomorphism, while the scheme-level application identifies pullback of the pole module
with pushforward of its additive sheaf along the inverse homeomorphism. Thus every
residue fibre has `H¹(O(n[0])) = 0` for `n ≥ 1`. The remaining work in this step is
the proper cohomology-and-base-change theorem which upgrades these fibrewise dimensions
to local freeness and base change on the family. The definition-level derived-functor seam
is now closed by `CategoryTheory.Abelian.Ext.addEquivRightDerived` and
`TopCat.Sheaf.H.addEquivRightDerivedGlobalSections`: genuine Ext-defined `Sheaf.H` is
identified with `RⁿΓ` through injective resolutions. This makes a future finite-projective
complex for proper pushforward directly applicable to the existing fibrewise vanishing;
constructing that geometric complex and proving its base-change comparison remain open.

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

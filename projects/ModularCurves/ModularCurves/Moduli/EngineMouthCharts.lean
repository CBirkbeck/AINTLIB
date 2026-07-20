/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential
import ModularCurves.ForMathlib.MaximalSpectrumOrbit
import ModularCurves.ForMathlib.SemilocalVariableChangeSplit
import ModularCurves.ForMathlib.SpecGroupAction
import ModularCurves.ForMathlib.WeierstrassInvariantLocal

/-!
# The engine mouth core, Stage 3a–3b: the semilocal chart cover and its split transition
cocycle

**([a5-P-loc] Stage 3 of `exists_localModel_core_at`, `Moduli/EngineDescent.lean` — the
chart-layer bank.)**  Over the semilocalization `L = Localization S` of the affine base
`X` at (the image of) a prime of the invariants, the curve's atlas provides finitely many
basic-open pointed Weierstrass charts covering `Spec L`; their transition variable changes
form a Čech `1`-cocycle over the pairwise overlap localizations of the **semilocal** `L`,
which **splits** by the `VariableChange`-Čech splitting engine
(`SemilocalUnitSplit.exists_variableChange_eq_mul_of_span_eq_top`,
`ForMathlib/SemilocalVariableChangeSplit`).  The split cochain `D i` is exactly the chart
correction datum: rescaling the `i`-th chart by `D i` makes all transitions `1`, so the
corrected charts glue to a global Weierstrass model over `Spec L` — Stage 3c of the mouth
core (the correction, coefficient glue, `Scheme.OpenCover.glueMorphisms` presentation glue
and the invariant-denominator spread to `D(a₁)`) consumes precisely the output packaged
here.

This file is separate from `Moduli/EngineDescent.lean` on purpose: it imports the
`LocalPresentation`/`transVC` chart calculus of `EllipticCurve/InvariantDifferential.lean`
(whose transitive instance set is heavy), keeping the descent file's import surface — and
its elaboration profile — unchanged.

* `finite_maximalSpectrum_localization` — `Finite (MaximalSpectrum L)`: the fixed subring
  `Lᴳ` of the semilocalization is local (`isLocalRing_fixedPoints_of_isLocalization`), and
  maximal ideals of `L` form one finite `G`-orbit over its closed point
  (`MaximalSpectrum.finite_of_isInvariant`).
* `exists_presentation_cover_span_top` — the finite basic-open chart cover of `Spec L`
  extracted from the atlas `C.localModel`.
* `transVC_restrict_trans` — the chart-Čech cocycle law at the section level.
* `sectionsToLoc` / `vc_map_sectionsToLoc_factor` — the comparison ring maps
  `Γ(X, D(g)) →+* Localization S₂` and their factoring squares (the vocabulary bridge into
  the `SemilocalUnitSplit.resLoc` join-localization calculus).
* `exists_cover_transVC_coboundary` ★ — **the Stage 3a–3b package**: a finite chart cover
  of `Spec L` together with a per-chart `VariableChange` cochain `D` whose coboundary is
  the transition cocycle.
-/

universe u

open AlgebraicGeometry CategoryTheory WeierstrassCurve SemilocalUnitSplit

namespace ModularCurves

namespace MouthCharts

variable {X : Scheme.{u}} {C : EllipticCurveGeom X}

/-! ### `Finite (MaximalSpectrum L)` for the semilocalization at a prime of the invariants -/

/-- **(Stage 3a-i, generic form)** A ring with a finite semiring action whose (integral)
fixed subalgebra is local has finitely many maximal ideals: they form one finite `G`-orbit
over the closed point (`MaximalSpectrum.finite_of_isInvariant` at the tautological
invariant extension `Lᴳ ⊆ L`).

Stated at a *variable* ring `L`: at a concrete `Localization`, the term
`FixedPoints.subalgebra ℤ L G` does not elaborate (the `SMul ℤ` instance resolves to the
`OreLocalization` scalar action, for which no `SMulCommClass G ℤ` instance exists — the
`Algebra ℤ (Localization S)` diamond), so consumers must instantiate this generic lemma
and never spell the subalgebra. -/
theorem finite_maximalSpectrum_of_isLocalRing_fixedPoints (G : Type*) [Group G] [Finite G]
    (L : Type*) [CommRing L] [MulSemiringAction G L]
    (h : IsLocalRing (FixedPoints.subalgebra ℤ L G)) :
    Finite (MaximalSpectrum L) := by
  haveI := h
  exact MaximalSpectrum.finite_of_isInvariant (FixedPoints.subalgebra ℤ L G) L G

/-- **(Stage 3a-i)** The semilocalization of `A` at (the image of) a prime `p` of the fixed
subring `Aᴳ` has finitely many maximal ideals: its fixed subring is local
(`isLocalRing_fixedPoints_of_isLocalization`), and the maximal ideals form finitely many
`G`-orbits over the base.  The statement does not mention the localized action, so the
consumer (`exists_localModel_core_at`, Stage 3) can use it under its own `letI`. -/
theorem finite_maximalSpectrum_localization (G : Type*) [Group G] [Finite G]
    {A : Type u} [CommRing A] [MulSemiringAction G A]
    (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    Finite (MaximalSpectrum (Localization
      (p.primeCompl.map (algebraMap (FixedPoints.subring A G) A)))) := by
  letI := MulSemiringAction.localizationInvariant (primeComplImage_fixed p)
  have hcomp : ∀ (g : G) (r : A),
      g • (algebraMap A (Localization
          (p.primeCompl.map (algebraMap (FixedPoints.subring A G) A))) r)
        = algebraMap A (Localization
            (p.primeCompl.map (algebraMap (FixedPoints.subring A G) A))) (g • r) :=
    fun g r => MulSemiringAction.locHom_algebraMap (primeComplImage_fixed p) g r
  haveI : Nontrivial (Localization
      (p.primeCompl.map (algebraMap (FixedPoints.subring A G) A))) :=
    nontrivial_localization_primeComplImage p
  exact finite_maximalSpectrum_of_isLocalRing_fixedPoints G _
    (isLocalRing_fixedPoints_of_isLocalization p hcomp)

/-! ### The finite basic-open chart cover of the semilocalization -/

/-- **([a5-P-loc] Stage 3-cover, chart extraction)** For an affine base `X` and a
localization `Localization S'` of `Γ(X, ⊤)` with finitely many maximal ideals, there are
finitely many `f i ∈ Γ(X, ⊤)` whose basic opens `D(f i) ⊆ X` each carry a pointed
Weierstrass chart of the curve (a `LocalPresentation`, shrunk from the atlas
`C.localModel`), and whose images generate the unit ideal of `Localization S'` — i.e. the
opens `D(f i)` cover `Spec (Localization S')`.

The cover is indexed by the maximal ideals of `Localization S'`: for a maximal `𝔪`, the
corresponding point of `X` is the image of the contraction of `𝔪` under `X ≅ Spec Γ(X, ⊤)`,
the atlas provides a chart there, and `IsAffineOpen.exists_basicOpen_le` shrinks the chart
to a basic open.  The span condition holds because an ideal avoiding the span would lie in
some maximal `𝔪`, whose chart function is invertible at `𝔪` by construction. -/
theorem exists_presentation_cover_span_top [IsAffine X]
    (S' : Submonoid ↑Γ(X, ⊤)) [Finite (MaximalSpectrum (Localization S'))] :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → ↑Γ(X, ⊤))
      (_ : ∀ i, LocalPresentation C
        ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩),
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization S') (f i)) = ⊤ := by
  classical
  -- a basic-open chart of the curve at the point of `X` below each maximal of the
  -- localization
  have hchart : ∀ m : MaximalSpectrum (Localization S'),
      ∃ (g : ↑Γ(X, ⊤)) (_ : LocalPresentation C
        ⟨X.basicOpen g, (isAffineOpen_top X).basicOpen g⟩),
      X.isoSpec.inv (PrimeSpectrum.comap
        (algebraMap ↑Γ(X, ⊤) (Localization S')) m.toPrimeSpectrum) ∈ X.basicOpen g := by
    intro m
    obtain ⟨U, hxU, W, hell, e, hπ, hz⟩ := C.localModel
      (X.isoSpec.inv (PrimeSpectrum.comap
        (algebraMap ↑Γ(X, ⊤) (Localization S')) m.toPrimeSpectrum))
    obtain ⟨g, hgle, hgmem⟩ :=
      (isAffineOpen_top X).exists_basicOpen_le (V := U.1) ⟨_, hxU⟩ trivial
    exact ⟨g, (⟨W, hell, e, hπ, hz⟩ : LocalPresentation C U).restrict hgle, hgmem⟩
  choose g P hmem using hchart
  refine ⟨MaximalSpectrum (Localization S'), Fintype.ofFinite _, g, P, ?_⟩
  -- the span condition: no maximal ideal of `Localization S'` contains all the `g m`
  by_contra hspan
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hspan
  have hin : algebraMap ↑Γ(X, ⊤) (Localization S') (g ⟨M, hMmax⟩) ∈ M :=
    hMle (Ideal.subset_span ⟨⟨M, hMmax⟩, rfl⟩)
  -- translate the membership `x ∈ D(g)` through `X ≅ Spec Γ(X, ⊤)` to `g ∉ 𝔪 ∩ Γ(X, ⊤)`
  have hpt : ∀ pt : Spec Γ(X, ⊤), X.toSpecΓ (X.isoSpec.inv pt) = pt := by
    intro pt
    rw [← Scheme.isoSpec_hom, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hx := hmem ⟨M, hMmax⟩
  rw [← Scheme.toSpecΓ_preimage_basicOpen, Scheme.Hom.mem_preimage, hpt _] at hx
  exact ((PrimeSpectrum.mem_basicOpen _ _).mp hx)
    (by rw [PrimeSpectrum.comap_asIdeal]; exact Ideal.mem_comap.mpr hin)

/-! ### The chart-Čech cocycle law at the section level -/

set_option backward.isDefEq.respectTransparency false in
/-- **([a5-P-loc] Stage 3, the chart-Čech cocycle law at the section level)** The pairwise
comparison variable changes of restricted charts satisfy the triple-overlap cocycle law:
restricting the `(1,2)`-, `(2,3)`- and `(1,3)`-comparisons to a common smaller affine open
`W'`, the first two compose to the third.  Assembled from `transVC_transport` (restriction
is `map` of the sections comparison), `transVC_restrict_restrict` (double restriction is
direct restriction) and the group law `transVC_trans` at `W'`. -/
theorem transVC_restrict_trans {V₁ V₂ V₃ : X.affineOpens}
    (P₁ : LocalPresentation C V₁) (P₂ : LocalPresentation C V₂)
    (P₃ : LocalPresentation C V₃) {V₁₂ V₂₃ V₁₃ W' : X.affineOpens}
    (h₁₂₁ : V₁₂.1 ≤ V₁.1) (h₁₂₂ : V₁₂.1 ≤ V₂.1)
    (h₂₃₂ : V₂₃.1 ≤ V₂.1) (h₂₃₃ : V₂₃.1 ≤ V₃.1)
    (h₁₃₁ : V₁₃.1 ≤ V₁.1) (h₁₃₃ : V₁₃.1 ≤ V₃.1)
    (hW₁₂ : W'.1 ≤ V₁₂.1) (hW₂₃ : W'.1 ≤ V₂₃.1) (hW₁₃ : W'.1 ≤ V₁₃.1) :
    ((P₁.restrict h₁₂₁).transVC (P₂.restrict h₁₂₂)).map (Scheme.resLE hW₁₂)
      * ((P₂.restrict h₂₃₂).transVC (P₃.restrict h₂₃₃)).map (Scheme.resLE hW₂₃)
    = ((P₁.restrict h₁₃₁).transVC (P₃.restrict h₁₃₃)).map (Scheme.resLE hW₁₃) := by
  -- fold each mapped comparison into the comparison of direct restrictions to `W'`
  have hfold : ∀ {VA VB : X.affineOpens} (PA : LocalPresentation C VA)
      (PB : LocalPresentation C VB) {VAB : X.affineOpens} (hA : VAB.1 ≤ VA.1)
      (hB : VAB.1 ≤ VB.1) (hW : W'.1 ≤ VAB.1),
      ((PA.restrict hA).transVC (PB.restrict hB)).map (Scheme.resLE hW)
        = (PA.restrict (hW.trans hA)).transVC (PB.restrict (hW.trans hB)) := by
    intro VA VB PA PB VAB hA hB hW
    have htr : ((PA.restrict hA).restrict hW).transVC ((PB.restrict hB).restrict hW)
        = ((PA.restrict hA).transVC (PB.restrict hB)).map
          (sectionsMapLE (𝟙 X) (show W'.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ VAB.1 by simpa using hW)) :=
      LocalPresentation.transVC_transport (𝟙 X) (𝟙 C.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp) (PA.restrict hA) (PB.restrict hB)
        (show W'.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ VAB.1 by simpa using hW)
    rw [← LocalPresentation.transVC_restrict_restrict PA PB hA hB hW, htr,
      LocalPresentation.sectionsMapLE_id]
  rw [hfold P₁ P₂ h₁₂₁ h₁₂₂ hW₁₂, hfold P₂ P₃ h₂₃₂ h₂₃₃ hW₂₃, hfold P₁ P₃ h₁₃₁ h₁₃₃ hW₁₃]
  exact LocalPresentation.transVC_trans _ _ _

/-! ### The comparison maps into the join-localization vocabulary -/

/-- `D(a · b) ⊆ D(a)`, at the level of section-ring basic opens. -/
theorem basicOpen_mul_le_left {U : X.Opens} (a b : Γ(X, U)) :
    X.basicOpen (a * b) ≤ X.basicOpen a := by
  rw [Scheme.basicOpen_mul]
  exact inf_le_left

/-- `D(a · b) ⊆ D(b)`. -/
theorem basicOpen_mul_le_right {U : X.Opens} (a b : Γ(X, U)) :
    X.basicOpen (a * b) ≤ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]
  exact inf_le_right

/-- `D(a · b · c) ⊆ D(b · c)`. -/
theorem basicOpen_mul_mul_le_right {U : X.Opens} (a b c : Γ(X, U)) :
    X.basicOpen (a * b * c) ≤ X.basicOpen (b * c) := by
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, Scheme.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_right

/-- `D(a · b · c) ⊆ D(a · c)`. -/
theorem basicOpen_mul_mul_le_outer {U : X.Opens} (a b c : Γ(X, U)) :
    X.basicOpen (a * b * c) ≤ X.basicOpen (a * c) := by
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, Scheme.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

/-- The comparison ring map from the sections of a basic open of `X` to a localization of
`Localization S'` inverting (the image of) the basic-open function: the `Away`-universal
property of the affine sections `Γ(X, D(g))` (`isLocalization_basicOpen`). -/
noncomputable def sectionsToLoc [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g : ↑Γ(X, ⊤)) (S₂ : Submonoid (Localization S'))
    (hg : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g))) :
    ↑Γ(X, X.basicOpen g) →+* Localization S₂ :=
  IsLocalization.Away.lift
    (g := (algebraMap (Localization S') (Localization S₂)).comp
      (algebraMap ↑Γ(X, ⊤) (Localization S'))) g hg

/-- The comparison map extends the canonical composite on global sections. -/
theorem sectionsToLoc_algebraMap [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g : ↑Γ(X, ⊤)) (S₂ : Submonoid (Localization S'))
    (hg : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g))) (a : ↑Γ(X, ⊤)) :
    sectionsToLoc S' g S₂ hg (algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g) a)
      = algebraMap (Localization S') (Localization S₂)
          (algebraMap ↑Γ(X, ⊤) (Localization S') a) :=
  IsLocalization.Away.lift_eq g hg a

/-- **(the factoring square)** Post-restricting the comparison map along `resLoc` agrees
with pre-restricting the sections along `D(g₂) ⊆ D(g₁)` — the two ways from `Γ(X, D(g₁))`
into the larger localization coincide on mapped variable changes.  This is the vocabulary
bridge from the pairwise-overlap cocycle to the triple-overlap localization. -/
theorem vc_map_sectionsToLoc_factor [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g₁ g₂ : ↑Γ(X, ⊤)) (hle : X.basicOpen g₂ ≤ X.basicOpen g₁)
    (S₂ S₃ : Submonoid (Localization S')) (hS : S₂ ≤ S₃)
    (hg₁ : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₁)))
    (hg₂ : IsUnit (algebraMap (Localization S') (Localization S₃)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₂)))
    (T : VariableChange ↑Γ(X, X.basicOpen g₁)) :
    (T.map (sectionsToLoc S' g₁ S₂ hg₁)).map (resLoc S₂ S₃ hS)
      = (T.map (Scheme.resLE hle)).map (sectionsToLoc S' g₂ S₃ hg₂) := by
  rw [VariableChange.map_map, VariableChange.map_map]
  refine congrArg T.map ?_
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [show Scheme.resLE hle (algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₁) a)
      = algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₂) a from
      Scheme.resLE_resLE hle (X.basicOpen_le g₁) a,
    sectionsToLoc_algebraMap, sectionsToLoc_algebraMap, resLoc_algebraMap]

/-- `map` along a ring hom is multiplicative, in composition-friendly orientation. -/
private theorem vc_map_mul' {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (φ : A →+* B) (T₁ T₂ : VariableChange A) :
    T₁.map φ * T₂.map φ = (T₁ * T₂).map φ :=
  (map_mul (VariableChange.mapHom φ) T₁ T₂).symm

/-! ### The Stage 3a–3b package: cover + split transition cocycle -/

/-- **([a5-P-loc] Stage 3a–3b, the chart-cover coboundary package ★)** Over an affine `X`
with a semilocal localization `L = Localization S'` of its global sections, there is a
finite basic-open chart cover `{D(f i)}` of `Spec L` (pointed Weierstrass charts `P i` from
the atlas, images of the `f i` generating the unit ideal of `L`), together with a
per-chart variable-change cochain `D i` over `L[1/f i]` whose coboundary is the chart
transition cocycle: for all `i, j`,

`(transVC of the restricted charts, pushed into `L[1/fᵢ, 1/fⱼ]`) = (D i) * (D j)⁻¹.`

Rescaling the `i`-th chart by `D i` therefore makes all transitions `1` — the corrected
chart curves and chart isomorphisms agree on overlaps and glue over `Spec L`; this output
is exactly what Stage 3c of `exists_localModel_core_at` (correction, coefficient glue,
`glueMorphisms` presentation glue, invariant-denominator spread) consumes.

The unit-side conditions `hU` are packaged so consumers can form the comparison maps
`sectionsToLoc` verbatim. -/
theorem exists_cover_transVC_coboundary [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    [Finite (MaximalSpectrum (Localization S'))] :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → ↑Γ(X, ⊤))
      (P : ∀ i, LocalPresentation C
        ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
      (hU : ∀ i j, IsUnit (algebraMap (Localization S')
        (Localization
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
            ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
        (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))))
      (D : ∀ i, VariableChange (Localization
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))),
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization S') (f i)) = ⊤ ∧
      ∀ i j,
        (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
              (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (basicOpen_mul_le_left (f i) (f j))).transVC
          ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
            (sectionsToLoc S' (f i * f j) _ (hU i j))
        = (D i).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_left)
          * ((D j).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_right))⁻¹ := by
  classical
  obtain ⟨ι, hfin, f, P, hspan⟩ := exists_presentation_cover_span_top (C := C) S'
  haveI := hfin
  set f' : ι → Localization S' := fun i => algebraMap ↑Γ(X, ⊤) (Localization S') (f i)
    with hf'
  -- the unit-side conditions for the comparison maps
  have hUmem : ∀ (i : ι) (S₂ : Submonoid (Localization S')) (h : f' i ∈ S₂),
      IsUnit (algebraMap (Localization S') (Localization S₂) (f' i)) :=
    fun i S₂ h => IsLocalization.map_units _ ⟨f' i, h⟩
  have hU : ∀ i j, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))) := by
    intro i j
    rw [map_mul, map_mul]
    exact (hUmem i _ (SetLike.le_def.mp le_sup_left (Submonoid.mem_powers _))).mul
      (hUmem j _ (SetLike.le_def.mp le_sup_right (Submonoid.mem_powers _)))
  have hU₃ : ∀ i j k, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)
        ⊔ Submonoid.powers (f' k)))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j * f k))) := by
    intro i j k
    rw [map_mul, map_mul, map_mul, map_mul]
    exact ((hUmem i _ (SetLike.le_def.mp (le_sup_left.trans le_sup_left)
        (Submonoid.mem_powers _))).mul
      (hUmem j _ (SetLike.le_def.mp (le_sup_right.trans le_sup_left)
        (Submonoid.mem_powers _)))).mul
      (hUmem k _ (SetLike.le_def.mp le_sup_right (Submonoid.mem_powers _)))
  -- the transition cocycle over the pairwise join-localizations
  set T : ∀ i j, VariableChange
      (Localization (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j))) := fun i j =>
    (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
          (isAffineOpen_top X).basicOpen (f i * f j)⟩)
        (basicOpen_mul_le_left (f i) (f j))).transVC
      ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
        (sectionsToLoc S' (f i * f j) _ (hU i j)) with hT
  -- the diagonal normalization
  have hdiag : ∀ i, T i i = 1 := by
    intro i
    show (((P i).restrict (V' := ⟨X.basicOpen (f i * f i),
          (isAffineOpen_top X).basicOpen (f i * f i)⟩)
        (basicOpen_mul_le_left (f i) (f i))).transVC
      ((P i).restrict (basicOpen_mul_le_left (f i) (f i)))).map
        (sectionsToLoc S' (f i * f i) _ (hU i i)) = 1
    rw [LocalPresentation.transVC_self]
    exact map_one (VariableChange.mapHom _)
  -- split the cocycle over the semilocal base
  obtain ⟨D, hD⟩ := SemilocalUnitSplit.exists_variableChange_eq_mul_of_span_eq_top f'
    hspan T hdiag (by
      intro i j k
      simp only [hT]
      have h₁ := vc_map_sectionsToLoc_factor S' (f i * f j) (f i * f j * f k)
        (basicOpen_mul_le_left (f i * f j) (f k)) _ _ le_sup_left (hU i j) (hU₃ i j k)
        (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
              (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (basicOpen_mul_le_left (f i) (f j))).transVC
          ((P j).restrict (basicOpen_mul_le_right (f i) (f j))))
      have h₂ := vc_map_sectionsToLoc_factor S' (f j * f k) (f i * f j * f k)
        (basicOpen_mul_mul_le_right (f i) (f j) (f k)) _ _
        (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (hU j k) (hU₃ i j k)
        (((P j).restrict (V' := ⟨X.basicOpen (f j * f k),
              (isAffineOpen_top X).basicOpen (f j * f k)⟩)
            (basicOpen_mul_le_left (f j) (f k))).transVC
          ((P k).restrict (basicOpen_mul_le_right (f j) (f k))))
      have h₃ := vc_map_sectionsToLoc_factor S' (f i * f k) (f i * f j * f k)
        (basicOpen_mul_mul_le_outer (f i) (f j) (f k)) _ _
        (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (hU i k) (hU₃ i j k)
        (((P i).restrict (V' := ⟨X.basicOpen (f i * f k),
              (isAffineOpen_top X).basicOpen (f i * f k)⟩)
            (basicOpen_mul_le_left (f i) (f k))).transVC
          ((P k).restrict (basicOpen_mul_le_right (f i) (f k))))
      exact (congrArg₂ (· * ·) h₁ h₂).trans ((vc_map_mul' _ _ _).trans
        ((congrArg (fun Z : VariableChange ↑Γ(X, X.basicOpen (f i * f j * f k)) =>
            Z.map (sectionsToLoc S' (f i * f j * f k) _ (hU₃ i j k)))
          (transVC_restrict_trans
            (V₁₂ := ⟨X.basicOpen (f i * f j), (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (V₂₃ := ⟨X.basicOpen (f j * f k), (isAffineOpen_top X).basicOpen (f j * f k)⟩)
            (V₁₃ := ⟨X.basicOpen (f i * f k), (isAffineOpen_top X).basicOpen (f i * f k)⟩)
            (W' := ⟨X.basicOpen (f i * f j * f k),
              (isAffineOpen_top X).basicOpen (f i * f j * f k)⟩)
            (P i) (P j) (P k)
            (basicOpen_mul_le_left (f i) (f j)) (basicOpen_mul_le_right (f i) (f j))
            (basicOpen_mul_le_left (f j) (f k)) (basicOpen_mul_le_right (f j) (f k))
            (basicOpen_mul_le_left (f i) (f k)) (basicOpen_mul_le_right (f i) (f k))
            (basicOpen_mul_le_left (f i * f j) (f k))
            (basicOpen_mul_mul_le_right (f i) (f j) (f k))
            (basicOpen_mul_mul_le_outer (f i) (f j) (f k)))).trans h₃.symm)))
  exact ⟨ι, hfin, f, P, hU, D, hspan, fun i j => hD i j⟩

end MouthCharts

end ModularCurves

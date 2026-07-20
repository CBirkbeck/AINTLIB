/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential
import ModularCurves.ForMathlib.AffineCechH0
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

/-! ### Stage 3c-α: the corrected charts glue to a global Weierstrass model over `L` -/

/-- An element is invertible in the localization at its own powers. -/
theorem isUnit_algebraMap_powers_self {L : Type*} [CommRing L] (x : L) :
    IsUnit (algebraMap L (Localization (Submonoid.powers x)) x) :=
  IsLocalization.map_units _ ⟨x, Submonoid.mem_powers x⟩

/-- **(the factoring square, ring-hom form)** Post-restricting the comparison map along
`resLoc` agrees with pre-restricting the sections along `D(g₂) ⊆ D(g₁)` — as ring
homomorphisms `Γ(X, D(g₁)) →+* Localization S₃`. -/
theorem sectionsToLoc_factor [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g₁ g₂ : ↑Γ(X, ⊤)) (hle : X.basicOpen g₂ ≤ X.basicOpen g₁)
    (S₂ S₃ : Submonoid (Localization S')) (hS : S₂ ≤ S₃)
    (hg₁ : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₁)))
    (hg₂ : IsUnit (algebraMap (Localization S') (Localization S₃)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₂))) :
    (resLoc S₂ S₃ hS).comp (sectionsToLoc S' g₁ S₂ hg₁)
      = (sectionsToLoc S' g₂ S₃ hg₂).comp (Scheme.resLE hle) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [show Scheme.resLE hle (algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₁) a)
      = algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₂) a from
      Scheme.resLE_resLE hle (X.basicOpen_le g₁) a,
    sectionsToLoc_algebraMap, sectionsToLoc_algebraMap, resLoc_algebraMap]

/-- The factoring square applied to a Weierstrass curve over the chart sections. -/
theorem wc_map_sectionsToLoc_factor [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g₁ g₂ : ↑Γ(X, ⊤)) (hle : X.basicOpen g₂ ≤ X.basicOpen g₁)
    (S₂ S₃ : Submonoid (Localization S')) (hS : S₂ ≤ S₃)
    (hg₁ : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₁)))
    (hg₂ : IsUnit (algebraMap (Localization S') (Localization S₃)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₂)))
    (W : WeierstrassCurve ↑Γ(X, X.basicOpen g₁)) :
    (W.map (sectionsToLoc S' g₁ S₂ hg₁)).map (resLoc S₂ S₃ hS)
      = (W.map (Scheme.resLE hle)).map (sectionsToLoc S' g₂ S₃ hg₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    sectionsToLoc_factor S' g₁ g₂ hle S₂ S₃ hS hg₁ hg₂]

/-- The chart curve of a restriction to a smaller basic open is the `resLE`-image of the
chart curve. -/
theorem restrict_W_eq [IsAffine X] {g₁ g₂ : ↑Γ(X, ⊤)} (h : X.basicOpen g₂ ≤ X.basicOpen g₁)
    (P₁ : LocalPresentation C ⟨X.basicOpen g₁, (isAffineOpen_top X).basicOpen g₁⟩) :
    (P₁.restrict (V' := ⟨X.basicOpen g₂, (isAffineOpen_top X).basicOpen g₂⟩) h).W
      = P₁.W.map (Scheme.resLE h) := by
  show P₁.W.map (sectionsMapLE (𝟙 X) _) = P₁.W.map (Scheme.resLE h)
  exact congrArg P₁.W.map (LocalPresentation.sectionsMapLE_id _)

/-- **(the corrected-chart agreement, generic barrier form)** Over *variable* rings: two
chart curves `W₁ / A₁`, `W₂ / A₂` mapping to a common overlap ring `B`, whose images are
compared by a transition `T` that is a coboundary `T = D₁ * D₂⁻¹`, have agreeing corrected
images: `(D₁⁻¹ • W₁) = (D₂⁻¹ • W₂)` over `B`.  Stated over variable rings on purpose: at the
concrete localization towers of the mouth core, rewriting under the scheme-typed sections
functor blows the `whnf` budget; as a general lemma it is applied, never unfolded. -/
private theorem corrected_map_eq {A₁ A₂ B : Type*} [CommRing A₁] [CommRing A₂] [CommRing B]
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (D₁ : VariableChange A₁) (D₂ : VariableChange A₂)
    (W₁ : WeierstrassCurve A₁) (W₂ : WeierstrassCurve A₂)
    (T : VariableChange B) (W₁' W₂' : WeierstrassCurve B)
    (h₁ : W₁.map ρ₁ = W₁') (h₂ : W₂.map ρ₂ = W₂')
    (hT : T • W₂' = W₁') (hcob : T = D₁.map ρ₁ * (D₂.map ρ₂)⁻¹) :
    (D₁⁻¹ • W₁).map ρ₁ = (D₂⁻¹ • W₂).map ρ₂ := by
  subst h₁
  subst h₂
  subst hcob
  have hinv₁ : (D₁⁻¹).map ρ₁ = (D₁.map ρ₁)⁻¹ := map_inv (VariableChange.mapHom ρ₁) D₁
  have hinv₂ : (D₂⁻¹).map ρ₂ = (D₂.map ρ₂)⁻¹ := map_inv (VariableChange.mapHom ρ₂) D₂
  rw [← WeierstrassCurve.map_variableChange, ← WeierstrassCurve.map_variableChange, ← hT,
    hinv₁, hinv₂, ← mul_smul, inv_mul_cancel_left]

/-- **(the coboundary reshaped for the inverse cochain, generic barrier form)**
`T = D₁ * D₂⁻¹` rewrites as `T = (D₁⁻¹)⁻¹ * (D₂⁻¹)` — the coboundary identity for the
corrected cochain `i ↦ Dᵢ⁻¹`. -/
private theorem cob_inv_reshape {A₁ A₂ B : Type*} [CommRing A₁] [CommRing A₂] [CommRing B]
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (D₁ : VariableChange A₁) (D₂ : VariableChange A₂)
    (T : VariableChange B) (h : T = D₁.map ρ₁ * (D₂.map ρ₂)⁻¹) :
    T = (((D₁⁻¹).map ρ₁))⁻¹ * (D₂⁻¹).map ρ₂ := by
  have hinv₁ : (D₁⁻¹).map ρ₁ = (D₁.map ρ₁)⁻¹ := map_inv (VariableChange.mapHom ρ₁) D₁
  have hinv₂ : (D₂⁻¹).map ρ₂ = (D₂.map ρ₂)⁻¹ := map_inv (VariableChange.mapHom ρ₂) D₂
  rw [h, hinv₁, hinv₂, inv_inv]

/-- **(the mapped cocycle action, generic barrier form)** The comparison acts on the mapped
chart curves: from `T • W₂ = W₁` over the sections, `(T.map ψ) • (W₂.map ψ) = W₁.map ψ`. -/
private theorem smul_map_of_smul {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (T : VariableChange A) (W₁ W₂ : WeierstrassCurve A) (h : T • W₂ = W₁) :
    (T.map ψ) • (W₂.map ψ) = W₁.map ψ :=
  (WeierstrassCurve.map_variableChange (W := W₂) (C := T) (φ := ψ)).trans
    (congrArg (fun W => W.map ψ) h)

set_option backward.isDefEq.respectTransparency false in
/-- **([a5-P-loc] Stage 3c-α, the glued model over the semilocalization ★)** Over an affine
`X` with a semilocal localization `L = Localization S'` of its global sections, the corrected
charts of the Stage 3a–3b package glue to a **global Weierstrass model over `L`**: a finite
basic-open chart cover `{D(f i)}` with pointed charts `P i`, a per-chart correction cochain
`D i` over `L[1/fᵢ]`, and a Weierstrass curve `W₀L / L` with invertible discriminant, such
that over each `L[1/fᵢ]`

`W₀L = (D i) • ((P i).W)`  (coefficientwise, through the comparison `sectionsToLoc`),

while the chart-transition comparisons satisfy the *corrected* coboundary identity
`transVC = (D i)⁻¹ * (D j)` on overlaps — so rescaling the `i`-th chart by `D i` makes all
transitions `1`.  Stage 3c-β (the invariant-denominator spread) consumes exactly this data.

Under the hood: the corrected chart curves `(D i) • (P i).W` agree on the pairwise overlap
localizations (from the coboundary identity and the cocycle action `transVC_smul`), so their
five coefficients glue by the affine Čech `H⁰` sheaf condition
(`SemilocalUnitSplit.exists_algebraMap_eq_of_span_eq_top`); the discriminant is a unit
because it is chartwise (`SemilocalUnitSplit.isUnit_of_span_eq_top`). -/
theorem exists_cover_glued_model [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
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
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
      (W₀L : WeierstrassCurve (Localization S')),
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization S') (f i)) = ⊤ ∧
      IsUnit W₀L.Δ ∧
      (∀ i, W₀L.map (algebraMap (Localization S')
          (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
        = D i • ((P i).W.map (sectionsToLoc S' (f i)
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
            (isUnit_algebraMap_powers_self
              (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))) ∧
      ∀ i j,
        (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
              (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (basicOpen_mul_le_left (f i) (f j))).transVC
          ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
            (sectionsToLoc S' (f i * f j) _ (hU i j))
        = ((D i).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_left))⁻¹
          * (D j).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_right) := by
  classical
  obtain ⟨ι, hfin, f, P, hU, D₀, hspan, hcob⟩ := exists_cover_transVC_coboundary (C := C) S'
  haveI := hfin
  -- notation: the images of the cover functions
  set f' : ι → Localization S' := fun i => algebraMap ↑Γ(X, ⊤) (Localization S') (f i)
    with hf'
  -- ### factoring the per-chart comparison maps through the overlap chart
  have hfac₁ : ∀ i j, (((P i).W.map (sectionsToLoc S' (f i) (Submonoid.powers (f' i))
        (isUnit_algebraMap_powers_self (f' i)))).map
          (resLoc (Submonoid.powers (f' i))
            (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)) le_sup_left))
      = (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
            (isAffineOpen_top X).basicOpen (f i * f j)⟩)
          (basicOpen_mul_le_left (f i) (f j))).W).map
          (sectionsToLoc S' (f i * f j) _ (hU i j)) := fun i j => by
    rw [wc_map_sectionsToLoc_factor S' (f i) (f i * f j)
      (basicOpen_mul_le_left (f i) (f j)) _ _ le_sup_left
      (isUnit_algebraMap_powers_self (f' i)) (hU i j) (P i).W,
      restrict_W_eq (basicOpen_mul_le_left (f i) (f j)) (P i)]
  have hfac₂ : ∀ i j, (((P j).W.map (sectionsToLoc S' (f j) (Submonoid.powers (f' j))
        (isUnit_algebraMap_powers_self (f' j)))).map
          (resLoc (Submonoid.powers (f' j))
            (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)) le_sup_right))
      = (((P j).restrict (V' := ⟨X.basicOpen (f i * f j),
            (isAffineOpen_top X).basicOpen (f i * f j)⟩)
          (basicOpen_mul_le_right (f i) (f j))).W).map
          (sectionsToLoc S' (f i * f j) _ (hU i j)) := fun i j => by
    rw [wc_map_sectionsToLoc_factor S' (f j) (f i * f j)
      (basicOpen_mul_le_right (f i) (f j)) _ _ le_sup_right
      (isUnit_algebraMap_powers_self (f' j)) (hU i j) (P j).W,
      restrict_W_eq (basicOpen_mul_le_right (f i) (f j)) (P j)]
  -- ### the corrected chart curves agree on pairwise overlaps (generic barrier lemma)
  have hagreeW : ∀ i j,
      ((D₀ i)⁻¹ • ((P i).W.map (sectionsToLoc S' (f i) (Submonoid.powers (f' i))
          (isUnit_algebraMap_powers_self (f' i))))).map
        (resLoc (Submonoid.powers (f' i))
          (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)) le_sup_left)
      = ((D₀ j)⁻¹ • ((P j).W.map (sectionsToLoc S' (f j) (Submonoid.powers (f' j))
          (isUnit_algebraMap_powers_self (f' j))))).map
        (resLoc (Submonoid.powers (f' j))
          (Submonoid.powers (f' i) ⊔ Submonoid.powers (f' j)) le_sup_right) := fun i j =>
    corrected_map_eq _ _ (D₀ i) (D₀ j) _ _ _ _ _ (hfac₁ i j) (hfac₂ i j)
      (smul_map_of_smul (sectionsToLoc S' (f i * f j) _ (hU i j)) _ _ _
        (LocalPresentation.transVC_smul
          ((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
            (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (basicOpen_mul_le_left (f i) (f j)))
          ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))))
      (hcob i j)
  -- ### per-chart ellipticity of the corrected curves
  have hVell : ∀ i, ((D₀ i)⁻¹ • ((P i).W.map (sectionsToLoc S' (f i)
      (Submonoid.powers (f' i))
      (isUnit_algebraMap_powers_self (f' i))))).IsElliptic := fun i => by
    letI := (P i).elliptic
    letI : (((P i).W.map (sectionsToLoc S' (f i) (Submonoid.powers (f' i))
        (isUnit_algebraMap_powers_self (f' i))))).IsElliptic :=
      ⟨by rw [WeierstrassCurve.map_Δ]; exact (P i).W.isUnit_Δ.map _⟩
    infer_instance
  -- ### glue the corrected curves by the Weierstrass Čech `H⁰` sheaf condition
  obtain ⟨W₀L, hglue, hΔ'⟩ := exists_weierstrassCurve_map_eq_of_span_eq_top f' hspan
    (fun i => (D₀ i)⁻¹ • ((P i).W.map (sectionsToLoc S' (f i) (Submonoid.powers (f' i))
      (isUnit_algebraMap_powers_self (f' i))))) hagreeW
  have hΔ : IsUnit W₀L.Δ := hΔ' (fun i => by
    letI := hVell i
    exact WeierstrassCurve.isUnit_Δ _)
  -- ### assemble, with the corrected coboundary identity `transVC = (D i)⁻¹ * (D j)`
  exact ⟨ι, hfin, f, P, hU, fun i => (D₀ i)⁻¹, W₀L, hspan, hΔ, hglue,
    fun i j => cob_inv_reshape _ _ (D₀ i) (D₀ j) _ (hcob i j)⟩

/-! ### Stage 3c-β/γ: the residual — invariant-denominator spread and the native glue -/

/-- **(Stage 3c-β ingredient — the span witness spreads to an invariant basic open)** If the
images of a finite family `f : ι → A` generate the unit ideal of the semilocalization
`L = Localization S` at (the image of) a prime `p` of the invariants, then some invariant
`k ∉ p` works as a universal denominator: over every invariant away-localization `A[1/a]`
with `k ∣ a`, the images of the `f i` still generate the unit ideal.  (Clear the
denominators of one partition of unity; the cleared witness `t·b ∈ S` has an invariant
preimage.) -/
theorem exists_invariant_span_away (G : Type*) [Group G]
    {A : Type u} [CommRing A] [MulSemiringAction G A]
    (p : Ideal (FixedPoints.subring A G)) [p.IsPrime]
    {ι : Type*} [Fintype ι] (f : ι → A)
    (hspan : Ideal.span (Set.range fun i => algebraMap A
      (Localization (p.primeCompl.map (algebraMap (FixedPoints.subring A G) A))) (f i))
      = ⊤) :
    ∃ (k : FixedPoints.subring A G) (_ : k ∉ p),
      ∀ a : FixedPoints.subring A G, k ∣ a →
        Ideal.span (Set.range fun i =>
          algebraMap A (Localization.Away ((a : A))) (f i)) = ⊤ := by
  classical
  set S : Submonoid A := p.primeCompl.map (algebraMap (FixedPoints.subring A G) A)
    with hSdef
  -- a partition of unity over `L`
  have h1 : (1 : Localization S) ∈ Ideal.span (Set.range fun i =>
      algebraMap A (Localization S) (f i)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  -- a common `S`-denominator for the coefficients
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (M := S) Finset.univ c
  have hb' : ∀ i, ∃ y : A, algebraMap A (Localization S) y = ((b : A)) • c i := fun i =>
    hb i (Finset.mem_univ i)
  choose d hd using hb'
  -- the cleared partition of unity: `t·b` is an `A`-combination of the `f i`
  have hbc : algebraMap A (Localization S) (∑ i, d i * f i)
      = algebraMap A (Localization S) ((b : A)) := by
    rw [map_sum]
    calc (∑ i, algebraMap A (Localization S) (d i * f i))
        = ∑ i, (b : A) • (c i * algebraMap A (Localization S) (f i)) :=
          Finset.sum_congr rfl (fun i _ => by rw [map_mul, hd i, smul_mul_assoc])
      _ = (b : A) • (∑ i, c i * algebraMap A (Localization S) (f i)) :=
          (Finset.smul_sum).symm
      _ = (b : A) • (1 : Localization S) := by rw [hc]
      _ = algebraMap A (Localization S) ((b : A)) := by rw [Algebra.smul_def, mul_one]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp hbc
  -- the invariant preimage of the cleared denominator
  obtain ⟨k, hk, hke⟩ := Submonoid.mem_map.mp
    (mul_mem t.2 b.2 : ((t : A)) * ((b : A)) ∈ S)
  refine ⟨k, hk, fun a hka => ?_⟩
  -- over `A[1/a]` the image of `k` is a unit lying in the span
  have hkunit : IsUnit (algebraMap A (Localization.Away ((a : A)))
      (algebraMap (FixedPoints.subring A G) A k)) :=
    isUnit_algebraMap_away (map_dvd (algebraMap (FixedPoints.subring A G) A) hka)
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hkunit
  rw [hke, ← ht, map_mul, map_sum, Finset.mul_sum]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [map_mul, ← mul_assoc]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **(Stage 3c-γ ingredient — the chart basic opens cover `D(a)`)** If the images of the
`f i` generate the unit ideal of `Localization.Away a`, the basic opens `D(a * f i)` cover
`D(a)` in `X` (prime avoidance through `X ≅ Spec Γ(X, ⊤)`). -/
theorem basicOpen_le_iSup_basicOpen_mul [IsAffine X] (a : ↑Γ(X, ⊤)) {κ : Type*}
    (f : κ → ↑Γ(X, ⊤))
    (hspan : Ideal.span (Set.range fun i =>
      algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)) = ⊤) :
    X.basicOpen a ≤ ⨆ i, X.basicOpen (a * f i) := by
  intro x hx
  rw [← Scheme.toSpecΓ_preimage_basicOpen, Scheme.Hom.mem_preimage] at hx
  have hanot : a ∉ (X.toSpecΓ x).asIdeal := (PrimeSpectrum.mem_basicOpen _ _).mp hx
  -- the point lifts to the away-localization
  have hmem : X.toSpecΓ x ∈ Set.range
      (PrimeSpectrum.comap (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
    exact hx
  obtain ⟨q, hq⟩ := hmem
  -- some cover function avoids the lifted prime, hence avoids the point downstairs
  have hex : ∃ i, algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i) ∉ q.asIdeal := by
    by_contra hall
    refine q.isPrime.ne_top (top_le_iff.mp ?_)
    rw [← hspan]
    refine Ideal.span_le.mpr fun z hz => ?_
    obtain ⟨i, rfl⟩ := hz
    exact of_not_not fun hzm => hall ⟨i, hzm⟩
  obtain ⟨i, hi⟩ := hex
  have hfnot : f i ∉ (X.toSpecΓ x).asIdeal := fun hmemf => by
    rw [← hq, PrimeSpectrum.comap_asIdeal] at hmemf
    exact hi (Ideal.mem_comap.mp hmemf)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
  rw [← Scheme.toSpecΓ_preimage_basicOpen, Scheme.Hom.mem_preimage]
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr (fun hmul =>
    ((X.toSpecΓ x).isPrime.mem_or_mem hmul).elim hanot hfnot)

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage 3c-γ ingredient — the corrected-chart transition factors through the
corrections)** For chart presentations `P₁ / V₁`, `P₂ / V₂` twisted by variable changes
`C₁`, `C₂` and restricted to a common affine open `V'`, the transition comparison of the
twisted charts is the conjugate of the original transition by the restricted corrections:

`transVC (Q₁|, Q₂|) = C₁| * transVC (P₁|, P₂|) * (C₂|)⁻¹`.

With `Cᵢ` the spread correction cochain (so that the right side is `1` by the corrected
coboundary identity), this is exactly the transVC-triviality of the corrected charts that
`pointedIso_hom_of_transVC_eq_one` consumes in the Stage 3c-γ glue. -/
theorem transVC_ofVC_restrict_pair {V₁ V₂ V' : X.affineOpens}
    (P₁ : LocalPresentation C V₁) (P₂ : LocalPresentation C V₂)
    (C₁ : VariableChange ↑Γ(X, V₁.1)) (C₂ : VariableChange ↑Γ(X, V₂.1))
    (h₁ : V'.1 ≤ V₁.1) (h₂ : V'.1 ≤ V₂.1) :
    ((P₁.ofVC C₁).restrict h₁).transVC ((P₂.ofVC C₂).restrict h₂)
      = (C₁.map (sectionsMapLE (𝟙 X) h₁))
        * ((P₁.restrict h₁).transVC (P₂.restrict h₂))
        * ((C₂.map (sectionsMapLE (𝟙 X) h₂)))⁻¹ := by
  have hinv : (P₂.restrict h₂).transVC ((P₂.ofVC C₂).restrict h₂)
      = (((P₂.ofVC C₂).restrict h₂).transVC (P₂.restrict h₂))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by
      rw [LocalPresentation.transVC_trans, LocalPresentation.transVC_self])
  rw [← LocalPresentation.transVC_trans ((P₁.ofVC C₁).restrict h₁) (P₁.restrict h₁)
      ((P₂.ofVC C₂).restrict h₂),
    ← LocalPresentation.transVC_trans (P₁.restrict h₁) (P₂.restrict h₂)
      ((P₂.ofVC C₂).restrict h₂),
    hinv, LocalPresentation.transVC_restrict_ofVC, LocalPresentation.transVC_restrict_ofVC,
    mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **([a5-P-loc] Stage 3c, the mouth-core presentation at an invariant prime — THE
FRONTIER)** At every prime `p` of the invariants `Aᴳ = Γ(X, ⊤)ᴳ` there is an invariant
`a₁ ∉ p` and an elliptic Weierstrass model `W₀R₁ / A_{a₁}` presenting the curve over the
basic open `D(a₁)`: a morphism `ρR₁ : projModel W₀R₁ ⟶ E` with the base-change square
against `Spec A_{a₁} ⟶ Spec A ≅ X` and the zero-leg.

This statement is EXACTLY the `hpres` residual of `exists_localModel_core_at`
(`Moduli/EngineDescent.lean`, [a5-P-loc] Stage 3); closing the `sorry` below and consuming
the theorem there completes the KM 4.7.0 engine.  (Wiring note: adding the import
`EngineDescent ← EngineMouthCharts` pulls the heavy `InvariantDifferential` instance set —
decompose the two slow `EngineDescent` proofs first, per the measured v10.343 finding.)

Stages 1–2 (the semilocalization at `p`) and Stages 3a–3c-α (the chart cover, the split
transition cocycle, and the glued model `W₀L / L`, all AXIOM-CLEAN) are consumed in the
body; the `sorry` is the pure Stage 3c-β/γ residual (invariant-denominator spread + native
glue over `D(a₁)`), with the full recipe in the continuation comment at the frontier. -/
theorem exists_invariant_away_presentation (G : Type*) [Group G] [Finite G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)]
    (p : Ideal (FixedPoints.subring ↑Γ(X, ⊤) G)) [p.IsPrime] :
    ∃ (a₁ : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a₁ ∉ p)
      (W₀R₁ : WeierstrassCurve (Localization.Away ((a₁ : ↑Γ(X, ⊤))))),
      W₀R₁.IsElliptic ∧
      ∃ ρR₁ : projModel W₀R₁ ⟶ C.E,
        IsPullback (projModelπ W₀R₁) ρR₁
          (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
            (Localization.Away ((a₁ : ↑Γ(X, ⊤))))))) (C.π ≫ X.isoSpec.hom) ∧
        projModelZero W₀R₁ ≫ ρR₁
          = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
              (Localization.Away ((a₁ : ↑Γ(X, ⊤)))))) ≫ X.isoSpec.inv ≫ C.zero := by
  classical
  -- ### Stages 1–2: the semilocalization at `p` (`a`-independent ring data)
  set S : Submonoid ↑Γ(X, ⊤) :=
    p.primeCompl.map (algebraMap (FixedPoints.subring ↑Γ(X, ⊤) G) ↑Γ(X, ⊤)) with hSdef
  -- every denominator has an invariant preimage avoiding `p` (the spread's fuel)
  have hpre : ∀ s : S, ∃ k : FixedPoints.subring ↑Γ(X, ⊤) G,
      k ∉ p ∧ algebraMap (FixedPoints.subring ↑Γ(X, ⊤) G) ↑Γ(X, ⊤) k = (s : ↑Γ(X, ⊤)) :=
    fun s => by
      obtain ⟨k, hk, hke⟩ := Submonoid.mem_map.mp s.2
      exact ⟨k, hk, hke⟩
  -- the semilocalization is semilocal
  haveI : Finite (MaximalSpectrum (Localization S)) :=
    finite_maximalSpectrum_localization G p
  -- ### Stages 3a–3c-α: cover + split transition cocycle + the glued model `W₀L / L`
  obtain ⟨ι, hfin, f, P, hU, D, W₀L, hspan, hΔ, hglue, hcobInv⟩ :=
    exists_cover_glued_model (C := C) S
  haveI := hfin
  -- ### Stage 3c-β first step (BANKED): the span witness spreads to an invariant level —
  -- for every invariant `a` with `k₀ ∣ a`, the `f i`-images generate the unit ideal of
  -- `A[1/a]`, so the opens `D(a·fᵢ)` cover `D(a)` (`basicOpen_le_iSup_basicOpen_mul`).
  obtain ⟨k₀, hk₀, hspanA⟩ := exists_invariant_span_away G p f hspan
  -- ### Stage 3c-β/γ (THE RESIDUAL — spread + native glue).  In context: the invariant
  -- multiplicative set `S` with invariant preimages `hpre`, the spread span witness
  -- `k₀`/`hspanA`, and the α-package: the finite chart cover `f`/`P` with span witness
  -- `hspan` over `L = Localization S`, the pairwise units `hU`, the correction cochain
  -- `D i / L[1/fᵢ]`, the glued model `W₀L / L` with `IsUnit W₀L.Δ` (`hΔ`), the per-chart
  -- identity `hglue` (`W₀L = D i • (P i).W` over `L[1/fᵢ]` through `sectionsToLoc`), and
  -- the corrected coboundary `hcobInv` (`transVC = (D i)⁻¹ * (D j)` on pairwise overlaps).
  --
  -- **β (the invariant-denominator spread — the Part-2 pattern of
  -- `exists_away_invariant_descent`, `ForMathlib/WeierstrassInvariantLocal.lean:444–806`):**
  -- (β1) register the clearing calculus: `L[1/fᵢ]` is a localization of `A = Γ(X, ⊤)` at
  --      `IsLocalization.localizationLocalizationSubmodule S (Submonoid.powers fᵢ')`
  --      (mathlib `IsLocalization.localization_localization_isLocalization`); against the
  --      chart ring `Γ(X, D(a·fᵢ))` (`IsLocalization.Away (a·fᵢ)` via
  --      `isLocalization_basicOpen`) use `IsLocalization.isLocalization_of_submonoid_le`
  --      to clear equalities: two chart sections with equal `sectionsToLoc`-images differ
  --      by a multiplier `c` whose `L`-image factors as `fᵢᵏ · (image of S)`
  --      (`mem_localizationLocalizationSubmodule`), and a second clearing
  --      (`IsLocalization.eq_iff_exists S L`) converts `c`-multiplication into
  --      `s'·fᵢᵏ`-multiplication with `s' ∈ S`; the `fᵢ`-power is already invertible on
  --      the chart, and `s'` has an invariant preimage (`hpre`) folded into `a₁`.
  -- (β2) spread: the five coefficients of `W₀L` (fractions `mk' b s` with invariant
  --      denominators — the `W₁ₗ` construction), the `Δ`-inverse witness
  --      (⟹ `W₀R₁.IsElliptic`), the components of each `D i` (`u`/`u⁻¹`/`r`/`s`/`t` —
  --      the `Dₗ` construction with the `hUpu` unit trick), the per-chart glue
  --      identities, the pairwise transVC-triviality at chart level (reshape via
  --      `transVC_restrict_ofVC` + `transVC_trans`/`transVC_self`:
  --      `transVC (Qᵢ|, Qⱼ|) = Dᵢᴬ| * transVC (Pᵢ|, Pⱼ|) * (Dⱼᴬ|)⁻¹`, trivial after
  --      clearing `hcobInv`), and the span witness (one `S`-clearing of `1 = Σ cᵢ fᵢ'`,
  --      giving `Ideal.span (range (algebraMap A A_{a₁} ∘ f)) = ⊤`); fold the finitely
  --      many invariant preimages into a single `a₁ ∉ p` and shrink along the canonical
  --      `fK`/`fR` transport maps (`IsLocalization.lift` on powers).
  -- **γ (the native glue over `D(a₁)` — no geometric spread):**
  -- (γ1) corrected charts `Q i := ((P i).restrict h).ofVC Dᵢᴬ` over `D(a₁·fᵢ)` with
  --      `(Q i).W = W₀R₁.map (toChartᵢ)` and pairwise `transVC = 1` — the transition
  --      factorization `transVC (Q₁|, Q₂|) = C₁| * transVC (P₁|, P₂|) * (C₂|)⁻¹` is
  --      BANKED (`transVC_ofVC_restrict_pair`, above);
  -- (γ2) the cover `D(a₁) = ⋃ D(a₁·fᵢ)`: `basicOpen_le_iSup_basicOpen_mul` (above) with
  --      the spread span witness `hspanA` (in context, from
  --      `exists_invariant_span_away` — BANKED);
  -- (γ3) `ρR₁` by `Scheme.OpenCover.glueMorphisms` on the `projModelπ W₀R₁`-preimages of
  --      the basic opens `D(fᵢ) ⊆ Spec A_{a₁}` — each piece is the projective model of
  --      the chart base change (`isPullback_projModelBaseChange` + open-immersion range
  --      transport), mapped to `E` by `(Q i).e.inv ≫ pullback.fst`; overlap agreement
  --      from `pointedIso_hom_of_transVC_eq_one` (`Moduli/AdaptedModel.lean:755`) on the
  --      transVC-triviality + `restrict_e_baseChange` (the `glueMorphisms_hf_of_agree`
  --      pattern, `ForMathlib/SpecBasicOpenAway.lean`);
  -- (γ4) the pullback square by `isPullback_of_iSup_eq_top`
  --      (`ForMathlib/PullbackLocalAtTarget.lean`) on the same cover of `Spec A_{a₁}`,
  --      per piece from `(Q i).compat_π` + `isPullback_projModelBaseChange` pasting; the
  --      zero-leg checked on the cover from `(Q i).compat_zero` +
  --      `projModelZero_baseChange`.
  sorry

end MouthCharts

end ModularCurves

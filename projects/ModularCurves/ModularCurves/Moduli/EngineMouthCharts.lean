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
import ModularCurves.ForMathlib.PullbackLocalAtTarget

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

/-! ### Stage 3c-β1: the invariant-denominator clearing calculus (generic barrier lemmas)

Everything in this section is stated over *variable* rings — `A` any commutative ring, `S` a
submonoid, `L := Localization S` the semilocalization, `T := L[1/f']` the per-chart tower
localization (`f' := algebraMap A L f`), and the chart ring `B` any
`IsLocalization.Away (g·f)`-algebra with `g ∈ S` (concretely `Γ(X, D(a·fᵢ))` at an invariant
level `a`).  At the concrete chart sections these lemmas are *applied*, never unfolded
(v10.343 barrier-lemma discipline). -/

section ClearingCalculus

variable {A : Type u} [CommRing A]

/-- **(β1, two-step clearing at `A`-level)** Two elements of `A` with equal images in the
tower localization `L[1/f']` differ by an `S`-multiplier after an `f`-power: one
`eq_iff_exists` at the `f'`-powers over `L`, one at `S` over `A`. -/
theorem exists_mem_pow_mul_eq_of_map_eq (S : Submonoid A) (f : A) {x y : A}
    (h : algebraMap (Localization S)
        (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
        (algebraMap A (Localization S) x)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
          (algebraMap A (Localization S) y)) :
    ∃ (s : S) (k : ℕ), (s : A) * (f ^ k * x) = (s : A) * (f ^ k * y) := by
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap A (Localization S) f))
    (Localization (Submonoid.powers (algebraMap A (Localization S) f)))).mp h
  obtain ⟨k, hk⟩ := c.2
  have hk' : algebraMap A (Localization S) f ^ k = (c : Localization S) := hk
  have hL : algebraMap A (Localization S) (f ^ k * x)
      = algebraMap A (Localization S) (f ^ k * y) := by
    rw [map_mul, map_mul, map_pow, hk']
    exact hc
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp hL
  exact ⟨s, k, hs⟩

/-- **(β1, tower fractions)** Every element of the tower localization `L[1/f']` clears to an
element of `A` after multiplying by an `S`-denominator and an `f`-power. -/
theorem exists_mem_pow_mul_map_eq (S : Submonoid A) (f : A)
    (x : Localization (Submonoid.powers (algebraMap A (Localization S) f))) :
    ∃ (b : A) (s : S) (k : ℕ),
      algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
          (algebraMap A (Localization S) ((s : A) * f ^ k)) * x
        = algebraMap (Localization S)
            (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
            (algebraMap A (Localization S) b) := by
  obtain ⟨⟨xL, c⟩, hc⟩ := IsLocalization.surj
    (Submonoid.powers (algebraMap A (Localization S) f)) x
  obtain ⟨k, hk⟩ := c.2
  have hk' : algebraMap A (Localization S) f ^ k = (c : Localization S) := hk
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj S xL
  refine ⟨b, s, k, ?_⟩
  have hfc : algebraMap A (Localization S) ((s : A) * f ^ k)
      = algebraMap A (Localization S) ((s : A)) * (c : Localization S) := by
    rw [map_mul, map_pow, hk']
  rw [hfc, map_mul, mul_assoc,
    mul_comm (algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f))) (c : Localization S)) x,
    hc, ← map_mul, mul_comm (algebraMap A (Localization S) ((s : A))) xL, hs]

/-- **(β1, chart-level clearing into the tower)** Two chart sections with equal images in the
tower localization `L[1/f']` differ by an invertible-after-`S` multiplier: the `f`-power is
already invertible on the chart, so a *pure* `S`-multiplier suffices. -/
theorem exists_mem_mul_eq_of_sections_map_eq (S : Submonoid A) {g f : A} (hg : g ∈ S)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (g * f) B]
    (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f)))
    (hψ : ∀ a : A, ψ (algebraMap A B a)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
          (algebraMap A (Localization S) a))
    {x y : B} (h : ψ x = ψ y) :
    ∃ s : S, algebraMap A B ((s : A)) * x = algebraMap A B ((s : A)) * y := by
  obtain ⟨⟨bx, cx⟩, hbx⟩ := IsLocalization.surj (Submonoid.powers (g * f)) x
  obtain ⟨n, hn⟩ := cx.2
  have hn' : (g * f) ^ n = (cx : A) := hn
  obtain ⟨⟨by', cy⟩, hby⟩ := IsLocalization.surj (Submonoid.powers (g * f)) y
  obtain ⟨m, hm⟩ := cy.2
  have hm' : (g * f) ^ m = (cy : A) := hm
  -- the `T`-level identity between the `A`-numerators
  have hx' : ψ x * algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
      (algebraMap A (Localization S) ((g * f) ^ n))
      = algebraMap (Localization S) _ (algebraMap A (Localization S) bx) := by
    have h0 := congrArg ψ hbx
    rw [map_mul, hψ, hψ] at h0
    rw [← hn'] at h0
    exact h0
  have hy' : ψ y * algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
      (algebraMap A (Localization S) ((g * f) ^ m))
      = algebraMap (Localization S) _ (algebraMap A (Localization S) by') := by
    have h0 := congrArg ψ hby
    rw [map_mul, hψ, hψ] at h0
    rw [← hm'] at h0
    exact h0
  have hT : algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
      (algebraMap A (Localization S) (bx * (g * f) ^ m))
      = algebraMap (Localization S) _ (algebraMap A (Localization S) (by' * (g * f) ^ n)) := by
    rw [map_mul, map_mul, map_mul, map_mul]
    calc algebraMap (Localization S) _ (algebraMap A (Localization S) bx)
          * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ m))
        = (ψ x * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ n)))
            * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ m)) := by
          rw [hx']
      _ = (ψ y * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ m)))
            * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ n)) := by
          rw [h]; ring
      _ = algebraMap (Localization S) _ (algebraMap A (Localization S) by')
            * algebraMap (Localization S) _ (algebraMap A (Localization S) ((g * f) ^ n)) := by
          rw [hy']
  obtain ⟨s, k, hs⟩ := exists_mem_pow_mul_eq_of_map_eq S f hT
  have hBid := congrArg (algebraMap A B) hs
  simp only [map_mul, map_pow] at hBid
  -- units on the chart
  have hgfB : IsUnit (algebraMap A B (g * f)) := IsLocalization.Away.algebraMap_isUnit _
  have hgB : IsUnit (algebraMap A B g) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B) (dvd_mul_right g f)) hgfB
  have hfB : IsUnit (algebraMap A B f) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B) (dvd_mul_left f g)) hgfB
  -- substitute the numerators back
  have hbxB : algebraMap A B bx = x * (algebraMap A B g * algebraMap A B f) ^ n := by
    rw [← hbx, ← hn', map_pow, map_mul]
  have hbyB : algebraMap A B by' = y * (algebraMap A B g * algebraMap A B f) ^ m := by
    rw [← hby, ← hm', map_pow, map_mul]
  rw [hbxB, hbyB] at hBid
  refine ⟨s, ((hfB.pow k).mul ((hgB.mul hfB).pow (n + m))).mul_left_cancel ?_⟩
  linear_combination hBid

/-- **(β1, chart-level clearing into the semilocalization)** Two `Away`-chart sections with
equal images in `L = Localization S` differ by an `S`-multiplier. -/
theorem exists_mem_mul_eq_of_away_map_eq (S : Submonoid A) {g : A}
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away g B]
    (j : B →+* Localization S)
    (hj : ∀ a : A, j (algebraMap A B a) = algebraMap A (Localization S) a)
    {x y : B} (h : j x = j y) :
    ∃ s : S, algebraMap A B ((s : A)) * x = algebraMap A B ((s : A)) * y := by
  obtain ⟨⟨bx, cx⟩, hbx⟩ := IsLocalization.surj (Submonoid.powers g) x
  obtain ⟨n, hn⟩ := cx.2
  have hn' : g ^ n = (cx : A) := hn
  obtain ⟨⟨by', cy⟩, hby⟩ := IsLocalization.surj (Submonoid.powers g) y
  obtain ⟨m, hm⟩ := cy.2
  have hm' : g ^ m = (cy : A) := hm
  have hx' : j x * algebraMap A (Localization S) (g ^ n)
      = algebraMap A (Localization S) bx := by
    have h0 := congrArg j hbx
    rw [map_mul, hj, hj] at h0
    rw [← hn'] at h0
    exact h0
  have hy' : j y * algebraMap A (Localization S) (g ^ m)
      = algebraMap A (Localization S) by' := by
    have h0 := congrArg j hby
    rw [map_mul, hj, hj] at h0
    rw [← hm'] at h0
    exact h0
  have hL : algebraMap A (Localization S) (bx * g ^ m)
      = algebraMap A (Localization S) (by' * g ^ n) := by
    rw [map_mul, map_mul]
    calc algebraMap A (Localization S) bx * algebraMap A (Localization S) (g ^ m)
        = (j x * algebraMap A (Localization S) (g ^ n))
            * algebraMap A (Localization S) (g ^ m) := by rw [hx']
      _ = (j y * algebraMap A (Localization S) (g ^ m))
            * algebraMap A (Localization S) (g ^ n) := by rw [h]; ring
      _ = algebraMap A (Localization S) by' * algebraMap A (Localization S) (g ^ n) := by
          rw [hy']
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp hL
  have hBid := congrArg (algebraMap A B) hs
  simp only [map_mul, map_pow] at hBid
  have hgB : IsUnit (algebraMap A B g) := IsLocalization.Away.algebraMap_isUnit _
  have hbxB : algebraMap A B bx = x * algebraMap A B g ^ n := by
    rw [← hbx, ← hn', map_pow]
  have hbyB : algebraMap A B by' = y * algebraMap A B g ^ m := by
    rw [← hby, ← hm', map_pow]
  rw [hbxB, hbyB] at hBid
  refine ⟨s, (hgB.pow (n + m)).mul_left_cancel ?_⟩
  linear_combination hBid

/-- **(β1, fraction preimages)** Mapping the chart fraction `b·d⁻¹` recovers any element `x`
with `x · φ(d) = φ(b)`. -/
theorem map_num_mul_inv_eq {B : Type u} [CommRing B] [Algebra A B] {L' : Type u} [CommRing L']
    (φ : B →+* L') {x : L'} {b d : A}
    (hx : x * φ (algebraMap A B d) = φ (algebraMap A B b))
    (hd : IsUnit (algebraMap A B d)) :
    φ (algebraMap A B b * ↑hd.unit⁻¹) = x := by
  refine (hd.map φ).mul_left_cancel ?_
  rw [← map_mul,
    show algebraMap A B d * (algebraMap A B b * ↑hd.unit⁻¹)
      = algebraMap A B b * (↑hd.unit * ↑hd.unit⁻¹) from by rw [IsUnit.unit_spec]; ring,
    Units.mul_inv, mul_one, ← hx, mul_comm]

/-- Clearing multipliers upgrade along divisibility. -/
theorem mul_eq_mul_of_dvd {B : Type*} [CommRing B] {u v x y : B} (hd : u ∣ v)
    (h : u * x = u * y) : v * x = v * y := by
  obtain ⟨e, rfl⟩ := hd
  linear_combination e * h

/-- Cleared equalities descend along any ring hom that makes the multiplier invertible. -/
theorem map_eq_of_isUnit_mul_eq {B B' : Type*} [CommRing B] [CommRing B'] (ρ : B →+* B')
    {u x y : B} (hu : IsUnit (ρ u)) (h : u * x = u * y) : ρ x = ρ y :=
  hu.mul_left_cancel (by rw [← map_mul, ← map_mul, h])

/-- **(β1, `VariableChange`-level clearing)** Two variable changes over the chart with equal
`ψ`-images have componentwise-`S`-cleared equal components. -/
theorem exists_mem_clear_variableChange (S : Submonoid A) {g f : A} (hg : g ∈ S)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (g * f) B]
    (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f)))
    (hψ : ∀ a : A, ψ (algebraMap A B a)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
          (algebraMap A (Localization S) a))
    {T₁ T₂ : VariableChange B} (h : T₁.map ψ = T₂.map ψ) :
    ∃ s : S, algebraMap A B ((s : A)) * (T₁.u : B) = algebraMap A B ((s : A)) * (T₂.u : B)
      ∧ algebraMap A B ((s : A)) * T₁.r = algebraMap A B ((s : A)) * T₂.r
      ∧ algebraMap A B ((s : A)) * T₁.s = algebraMap A B ((s : A)) * T₂.s
      ∧ algebraMap A B ((s : A)) * T₁.t = algebraMap A B ((s : A)) * T₂.t := by
  have hu : ψ ((T₁.u : B)) = ψ ((T₂.u : B)) := by
    have h0 := congrArg (fun z : VariableChange
      (Localization (Submonoid.powers (algebraMap A (Localization S) f))) => ((z.u :
        Localization (Submonoid.powers (algebraMap A (Localization S) f)))) ) h
    simpa using h0
  have hr : ψ T₁.r = ψ T₂.r := by
    have h0 := congrArg VariableChange.r h
    simpa using h0
  have hs : ψ T₁.s = ψ T₂.s := by
    have h0 := congrArg VariableChange.s h
    simpa using h0
  have ht : ψ T₁.t = ψ T₂.t := by
    have h0 := congrArg VariableChange.t h
    simpa using h0
  obtain ⟨s₁, hc₁⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ hu
  obtain ⟨s₂, hc₂⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ hr
  obtain ⟨s₃, hc₃⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ hs
  obtain ⟨s₄, hc₄⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ ht
  refine ⟨((s₁ * s₂) * s₃) * s₄, ?_, ?_, ?_, ?_⟩
  · exact mul_eq_mul_of_dvd (map_dvd _
      (((dvd_mul_right (s₁ : A) (s₂ : A)).mul_right (s₃ : A)).mul_right (s₄ : A))) hc₁
  · exact mul_eq_mul_of_dvd (map_dvd _
      (((dvd_mul_left (s₂ : A) (s₁ : A)).mul_right (s₃ : A)).mul_right (s₄ : A))) hc₂
  · exact mul_eq_mul_of_dvd (map_dvd _
      ((dvd_mul_left (s₃ : A) ((s₁ : A) * (s₂ : A))).mul_right (s₄ : A))) hc₃
  · exact mul_eq_mul_of_dvd (map_dvd _
      (dvd_mul_left (s₄ : A) (((s₁ : A) * (s₂ : A)) * (s₃ : A)))) hc₄

/-- **(β1, `WeierstrassCurve`-level clearing)** Two chart curves with equal `ψ`-images have
componentwise-`S`-cleared equal coefficients. -/
theorem exists_mem_clear_weierstrassCurve (S : Submonoid A) {g f : A} (hg : g ∈ S)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (g * f) B]
    (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f)))
    (hψ : ∀ a : A, ψ (algebraMap A B a)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
          (algebraMap A (Localization S) a))
    {W₁ W₂ : WeierstrassCurve B} (h : W₁.map ψ = W₂.map ψ) :
    ∃ s : S, algebraMap A B ((s : A)) * W₁.a₁ = algebraMap A B ((s : A)) * W₂.a₁
      ∧ algebraMap A B ((s : A)) * W₁.a₂ = algebraMap A B ((s : A)) * W₂.a₂
      ∧ algebraMap A B ((s : A)) * W₁.a₃ = algebraMap A B ((s : A)) * W₂.a₃
      ∧ algebraMap A B ((s : A)) * W₁.a₄ = algebraMap A B ((s : A)) * W₂.a₄
      ∧ algebraMap A B ((s : A)) * W₁.a₆ = algebraMap A B ((s : A)) * W₂.a₆ := by
  obtain ⟨s₁, hc₁⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ
    (congrArg WeierstrassCurve.a₁ h)
  obtain ⟨s₂, hc₂⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ
    (congrArg WeierstrassCurve.a₂ h)
  obtain ⟨s₃, hc₃⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ
    (congrArg WeierstrassCurve.a₃ h)
  obtain ⟨s₄, hc₄⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ
    (congrArg WeierstrassCurve.a₄ h)
  obtain ⟨s₆, hc₆⟩ := exists_mem_mul_eq_of_sections_map_eq S hg B ψ hψ
    (congrArg WeierstrassCurve.a₆ h)
  refine ⟨(((s₁ * s₂) * s₃) * s₄) * s₆, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_eq_mul_of_dvd (map_dvd _
      ((((dvd_mul_right (s₁ : A) (s₂ : A)).mul_right (s₃ : A)).mul_right
        (s₄ : A)).mul_right (s₆ : A))) hc₁
  · exact mul_eq_mul_of_dvd (map_dvd _
      ((((dvd_mul_left (s₂ : A) (s₁ : A)).mul_right (s₃ : A)).mul_right
        (s₄ : A)).mul_right (s₆ : A))) hc₂
  · exact mul_eq_mul_of_dvd (map_dvd _
      (((dvd_mul_left (s₃ : A) ((s₁ : A) * (s₂ : A))).mul_right (s₄ : A)).mul_right
        (s₆ : A))) hc₃
  · exact mul_eq_mul_of_dvd (map_dvd _
      ((dvd_mul_left (s₄ : A) (((s₁ : A) * (s₂ : A)) * (s₃ : A))).mul_right (s₆ : A))) hc₄
  · exact mul_eq_mul_of_dvd (map_dvd _
      (dvd_mul_left (s₆ : A) ((((s₁ : A) * (s₂ : A)) * (s₃ : A)) * (s₄ : A)))) hc₆

/-- **(β1, two-step clearing at `A`-level, join form)** As
`exists_mem_pow_mul_eq_of_map_eq`, over the pairwise-overlap localization
`L[1/f'₁, 1/f'₂]`. -/
theorem exists_mem_pow_mul_eq_of_map_eq₂ (S : Submonoid A) (f₁ f₂ : A) {x y : A}
    (h : algebraMap (Localization S)
        (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
          ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
        (algebraMap A (Localization S) x)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
            ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
          (algebraMap A (Localization S) y)) :
    ∃ (s : S) (k l : ℕ), (s : A) * (f₁ ^ k * (f₂ ^ l * x))
      = (s : A) * (f₁ ^ k * (f₂ ^ l * y)) := by
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap A (Localization S) f₁)
      ⊔ Submonoid.powers (algebraMap A (Localization S) f₂))
    (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
      ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))).mp h
  obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := Submonoid.mem_sup.mp c.2
  obtain ⟨k, hk⟩ := hc₁
  obtain ⟨l, hl⟩ := hc₂
  have hk' : algebraMap A (Localization S) f₁ ^ k = c₁ := hk
  have hl' : algebraMap A (Localization S) f₂ ^ l = c₂ := hl
  have hL : algebraMap A (Localization S) (f₁ ^ k * (f₂ ^ l * x))
      = algebraMap A (Localization S) (f₁ ^ k * (f₂ ^ l * y)) := by
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, hk', hl', ← mul_assoc,
      ← mul_assoc, hcc]
    exact hc
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp hL
  exact ⟨s, k, l, hs⟩

/-- **(β1, chart-level clearing into the join tower)** As
`exists_mem_mul_eq_of_sections_map_eq`, for the pairwise-overlap chart
`B = A[1/(g·(f₁·f₂))]` and the join localization. -/
theorem exists_mem_mul_eq_of_sections_map_eq₂ (S : Submonoid A) {g f₁ f₂ : A} (hg : g ∈ S)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (g * (f₁ * f₂)) B]
    (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
      ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
    (hψ : ∀ a : A, ψ (algebraMap A B a)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
            ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
          (algebraMap A (Localization S) a))
    {x y : B} (h : ψ x = ψ y) :
    ∃ s : S, algebraMap A B ((s : A)) * x = algebraMap A B ((s : A)) * y := by
  obtain ⟨⟨bx, cx⟩, hbx⟩ := IsLocalization.surj (Submonoid.powers (g * (f₁ * f₂))) x
  obtain ⟨n, hn⟩ := cx.2
  have hn' : (g * (f₁ * f₂)) ^ n = (cx : A) := hn
  obtain ⟨⟨by', cy⟩, hby⟩ := IsLocalization.surj (Submonoid.powers (g * (f₁ * f₂))) y
  obtain ⟨m, hm⟩ := cy.2
  have hm' : (g * (f₁ * f₂)) ^ m = (cy : A) := hm
  have hx' : ψ x * algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
        ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
      (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ n))
      = algebraMap (Localization S) _ (algebraMap A (Localization S) bx) := by
    have h0 := congrArg ψ hbx
    rw [map_mul, hψ, hψ] at h0
    rw [← hn'] at h0
    exact h0
  have hy' : ψ y * algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
        ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
      (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ m))
      = algebraMap (Localization S) _ (algebraMap A (Localization S) by') := by
    have h0 := congrArg ψ hby
    rw [map_mul, hψ, hψ] at h0
    rw [← hm'] at h0
    exact h0
  have hT : algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
        ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
      (algebraMap A (Localization S) (bx * (g * (f₁ * f₂)) ^ m))
      = algebraMap (Localization S) _
          (algebraMap A (Localization S) (by' * (g * (f₁ * f₂)) ^ n)) := by
    rw [map_mul, map_mul, map_mul, map_mul]
    calc algebraMap (Localization S) _ (algebraMap A (Localization S) bx)
          * algebraMap (Localization S) _
            (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ m))
        = (ψ x * algebraMap (Localization S) _
              (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ n)))
            * algebraMap (Localization S) _
              (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ m)) := by
          rw [hx']
      _ = (ψ y * algebraMap (Localization S) _
              (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ m)))
            * algebraMap (Localization S) _
              (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ n)) := by
          rw [h]; ring
      _ = algebraMap (Localization S) _ (algebraMap A (Localization S) by')
            * algebraMap (Localization S) _
              (algebraMap A (Localization S) ((g * (f₁ * f₂)) ^ n)) := by
          rw [hy']
  obtain ⟨s, k, l, hs⟩ := exists_mem_pow_mul_eq_of_map_eq₂ S f₁ f₂ hT
  have hBid := congrArg (algebraMap A B) hs
  simp only [map_mul, map_pow] at hBid
  have hgfB : IsUnit (algebraMap A B (g * (f₁ * f₂))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hgB : IsUnit (algebraMap A B g) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B) (dvd_mul_right g (f₁ * f₂))) hgfB
  have hf₁B : IsUnit (algebraMap A B f₁) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B)
      ((dvd_mul_right f₁ f₂).mul_left g)) hgfB
  have hf₂B : IsUnit (algebraMap A B f₂) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B)
      ((dvd_mul_left f₂ f₁).mul_left g)) hgfB
  have hbxB : algebraMap A B bx
      = x * (algebraMap A B g * (algebraMap A B f₁ * algebraMap A B f₂)) ^ n := by
    rw [← hbx, ← hn', map_pow, map_mul, map_mul]
  have hbyB : algebraMap A B by'
      = y * (algebraMap A B g * (algebraMap A B f₁ * algebraMap A B f₂)) ^ m := by
    rw [← hby, ← hm', map_pow, map_mul, map_mul]
  rw [hbxB, hbyB] at hBid
  refine ⟨s, (((hf₁B.pow k).mul (hf₂B.pow l)).mul
    ((hgB.mul (hf₁B.mul hf₂B)).pow (n + m))).mul_left_cancel ?_⟩
  linear_combination hBid

/-- **(β1, `VariableChange`-level clearing, join form)** -/
theorem exists_mem_clear_variableChange₂ (S : Submonoid A) {g f₁ f₂ : A} (hg : g ∈ S)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (g * (f₁ * f₂)) B]
    (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
      ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
    (hψ : ∀ a : A, ψ (algebraMap A B a)
      = algebraMap (Localization S)
          (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
            ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))
          (algebraMap A (Localization S) a))
    {T₁ T₂ : VariableChange B} (h : T₁.map ψ = T₂.map ψ) :
    ∃ s : S, algebraMap A B ((s : A)) * (T₁.u : B) = algebraMap A B ((s : A)) * (T₂.u : B)
      ∧ algebraMap A B ((s : A)) * T₁.r = algebraMap A B ((s : A)) * T₂.r
      ∧ algebraMap A B ((s : A)) * T₁.s = algebraMap A B ((s : A)) * T₂.s
      ∧ algebraMap A B ((s : A)) * T₁.t = algebraMap A B ((s : A)) * T₂.t := by
  have hu : ψ ((T₁.u : B)) = ψ ((T₂.u : B)) := by
    have h0 := congrArg (fun z : VariableChange
      (Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
        ⊔ Submonoid.powers (algebraMap A (Localization S) f₂))) => ((z.u :
        Localization (Submonoid.powers (algebraMap A (Localization S) f₁)
          ⊔ Submonoid.powers (algebraMap A (Localization S) f₂)))) ) h
    simpa using h0
  have hr : ψ T₁.r = ψ T₂.r := by
    have h0 := congrArg VariableChange.r h
    simpa using h0
  have hs : ψ T₁.s = ψ T₂.s := by
    have h0 := congrArg VariableChange.s h
    simpa using h0
  have ht : ψ T₁.t = ψ T₂.t := by
    have h0 := congrArg VariableChange.t h
    simpa using h0
  obtain ⟨s₁, hc₁⟩ := exists_mem_mul_eq_of_sections_map_eq₂ S hg B ψ hψ hu
  obtain ⟨s₂, hc₂⟩ := exists_mem_mul_eq_of_sections_map_eq₂ S hg B ψ hψ hr
  obtain ⟨s₃, hc₃⟩ := exists_mem_mul_eq_of_sections_map_eq₂ S hg B ψ hψ hs
  obtain ⟨s₄, hc₄⟩ := exists_mem_mul_eq_of_sections_map_eq₂ S hg B ψ hψ ht
  refine ⟨((s₁ * s₂) * s₃) * s₄, ?_, ?_, ?_, ?_⟩
  · exact mul_eq_mul_of_dvd (map_dvd _
      (((dvd_mul_right (s₁ : A) (s₂ : A)).mul_right (s₃ : A)).mul_right (s₄ : A))) hc₁
  · exact mul_eq_mul_of_dvd (map_dvd _
      (((dvd_mul_left (s₂ : A) (s₁ : A)).mul_right (s₃ : A)).mul_right (s₄ : A))) hc₂
  · exact mul_eq_mul_of_dvd (map_dvd _
      ((dvd_mul_left (s₃ : A) ((s₁ : A) * (s₂ : A))).mul_right (s₄ : A))) hc₃
  · exact mul_eq_mul_of_dvd (map_dvd _
      (dvd_mul_left (s₄ : A) (((s₁ : A) * (s₂ : A)) * (s₃ : A)))) hc₄

/-- `map` along a ring hom is compatible with `⁻¹ * ·` (composition-friendly shape). -/
theorem vc_map_inv_mul {B B' : Type*} [CommRing B] [CommRing B'] (φ : B →+* B')
    (Z₁ Z₂ : VariableChange B) : (Z₁⁻¹ * Z₂).map φ = (Z₁.map φ)⁻¹ * Z₂.map φ := by
  rw [show (Z₁⁻¹ * Z₂).map φ = (Z₁⁻¹).map φ * Z₂.map φ from
      map_mul (VariableChange.mapHom φ) _ _,
    show (Z₁⁻¹).map φ = (Z₁.map φ)⁻¹ from map_inv (VariableChange.mapHom φ) _]

/-- **(β1, descend a cleared `VariableChange` equality)** -/
theorem variableChange_map_eq_of_mul_eq {B B' : Type u} [CommRing B] [CommRing B']
    (ρ : B →+* B') {u : B} (hu : IsUnit (ρ u)) {T₁ T₂ : VariableChange B}
    (h1 : u * (T₁.u : B) = u * (T₂.u : B)) (h2 : u * T₁.r = u * T₂.r)
    (h3 : u * T₁.s = u * T₂.s) (h4 : u * T₁.t = u * T₂.t) :
    T₁.map ρ = T₂.map ρ := by
  refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
  · exact map_eq_of_isUnit_mul_eq ρ hu h1
  · exact map_eq_of_isUnit_mul_eq ρ hu h2
  · exact map_eq_of_isUnit_mul_eq ρ hu h3
  · exact map_eq_of_isUnit_mul_eq ρ hu h4

/-- **(β1, descend a cleared `WeierstrassCurve` equality)** -/
theorem weierstrassCurve_map_eq_of_mul_eq {B B' : Type u} [CommRing B] [CommRing B']
    (ρ : B →+* B') {u : B} (hu : IsUnit (ρ u)) {W₁ W₂ : WeierstrassCurve B}
    (h1 : u * W₁.a₁ = u * W₂.a₁) (h2 : u * W₁.a₂ = u * W₂.a₂)
    (h3 : u * W₁.a₃ = u * W₂.a₃) (h4 : u * W₁.a₄ = u * W₂.a₄)
    (h6 : u * W₁.a₆ = u * W₂.a₆) :
    W₁.map ρ = W₂.map ρ := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · exact map_eq_of_isUnit_mul_eq ρ hu h1
  · exact map_eq_of_isUnit_mul_eq ρ hu h2
  · exact map_eq_of_isUnit_mul_eq ρ hu h3
  · exact map_eq_of_isUnit_mul_eq ρ hu h4
  · exact map_eq_of_isUnit_mul_eq ρ hu h6

/-- **(β2, the `VariableChange` spread)** A variable change `D` over the tower localization
`T = L[1/f']` spreads, after ONE invariant multiplier `s`, to a preimage over EVERY chart
ring `B = A[1/(g·f)]` (`g ∈ S`) in which `s` is invertible, compatibly with the comparison
`ψ` (`DB.map ψ = D`).  The unit component uses the `bu·bv`-relation trick: the numerator of
`D.u` is invertible on the chart because `bu·bv` equals the (invertible) product of
denominators after one more clearing. -/
theorem exists_variableChange_sections_preimage (S : Submonoid A) (f : A)
    (D : VariableChange (Localization (Submonoid.powers (algebraMap A (Localization S) f)))) :
    ∃ s : S, ∀ {g : A}, g ∈ S → ∀ (B : Type u) [CommRing B] [Algebra A B]
      [IsLocalization.Away (g * f) B]
      (ψ : B →+* Localization (Submonoid.powers (algebraMap A (Localization S) f))),
      (∀ a : A, ψ (algebraMap A B a)
        = algebraMap (Localization S)
            (Localization (Submonoid.powers (algebraMap A (Localization S) f)))
            (algebraMap A (Localization S) a)) →
      IsUnit (algebraMap A B ((s : A))) →
      ∃ DB : VariableChange B, DB.map ψ = D := by
  obtain ⟨bu, su, ku, hu⟩ := exists_mem_pow_mul_map_eq S f ((D.u :
    Localization (Submonoid.powers (algebraMap A (Localization S) f))))
  obtain ⟨bv, sv, kv, hv⟩ := exists_mem_pow_mul_map_eq S f ((↑D.u⁻¹ :
    Localization (Submonoid.powers (algebraMap A (Localization S) f))))
  obtain ⟨br, sr, kr, hr⟩ := exists_mem_pow_mul_map_eq S f D.r
  obtain ⟨bs, ss, ks, hs⟩ := exists_mem_pow_mul_map_eq S f D.s
  obtain ⟨bt, st, kt, ht⟩ := exists_mem_pow_mul_map_eq S f D.t
  -- the unit relation over `T`, cleared to `A` (through the composite comparison `φ`)
  set φ : A →+* Localization (Submonoid.powers (algebraMap A (Localization S) f)) :=
    (algebraMap (Localization S)
      (Localization (Submonoid.powers (algebraMap A (Localization S) f)))).comp
      (algebraMap A (Localization S)) with hφ
  have huφ : φ ((su : A) * f ^ ku) * ((D.u :
      Localization (Submonoid.powers (algebraMap A (Localization S) f)))) = φ bu := hu
  have hvφ : φ ((sv : A) * f ^ kv) * ((↑D.u⁻¹ :
      Localization (Submonoid.powers (algebraMap A (Localization S) f)))) = φ bv := hv
  have h1 : ((D.u : Localization (Submonoid.powers (algebraMap A (Localization S) f))))
      * ((↑D.u⁻¹ : Localization (Submonoid.powers (algebraMap A (Localization S) f))))
      = 1 := D.u.mul_inv
  have huv : φ (bu * bv) = φ (((su : A) * f ^ ku) * ((sv : A) * f ^ kv)) := by
    rw [map_mul, map_mul]
    calc φ bu * φ bv
        = (φ ((su : A) * f ^ ku) * ((D.u :
              Localization (Submonoid.powers (algebraMap A (Localization S) f)))))
          * (φ ((sv : A) * f ^ kv) * ((↑D.u⁻¹ :
              Localization (Submonoid.powers (algebraMap A (Localization S) f))))) := by
          rw [huφ, hvφ]
      _ = (φ ((su : A) * f ^ ku) * φ ((sv : A) * f ^ kv))
          * (((D.u : Localization (Submonoid.powers (algebraMap A (Localization S) f))))
            * ((↑D.u⁻¹ :
              Localization (Submonoid.powers (algebraMap A (Localization S) f))))) := by
          ring
      _ = φ ((su : A) * f ^ ku) * φ ((sv : A) * f ^ kv) := by rw [h1, mul_one]
  obtain ⟨s₀, k₀, h₀⟩ := exists_mem_pow_mul_eq_of_map_eq S f huv
  refine ⟨((((su * sv) * s₀) * sr) * ss) * st, ?_⟩
  intro g hg B _ _ _ ψ hψ hsU
  -- the divisibility chain into the folded multiplier
  have hdvd_su : (su : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (su : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact ((((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _).mul_right _
  have hdvd_sv : (sv : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (sv : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact ((((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _).mul_right _
  have hdvd_s₀ : (s₀ : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (s₀ : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact (((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _
  have hdvd_sr : (sr : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (sr : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact ((dvd_mul_left _ _).mul_right _).mul_right _
  have hdvd_ss : (ss : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (ss : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact (dvd_mul_left _ _).mul_right _
  have hdvd_st : (st : A) ∣ (((((((su * sv) * s₀) * sr) * ss) * st : S)) : A) := by
    show (st : A) ∣ (((((su : A) * (sv : A)) * (s₀ : A)) * (sr : A)) * (ss : A)) * (st : A)
    exact dvd_mul_left _ _
  have hsuB : IsUnit (algebraMap A B ((su : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_su) hsU
  have hsvB : IsUnit (algebraMap A B ((sv : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_sv) hsU
  have hs₀B : IsUnit (algebraMap A B ((s₀ : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_s₀) hsU
  have hsrB : IsUnit (algebraMap A B ((sr : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_sr) hsU
  have hssB : IsUnit (algebraMap A B ((ss : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_ss) hsU
  have hstB : IsUnit (algebraMap A B ((st : A))) :=
    isUnit_of_dvd_unit (map_dvd _ hdvd_st) hsU
  have hgfB : IsUnit (algebraMap A B (g * f)) := IsLocalization.Away.algebraMap_isUnit _
  have hfB : IsUnit (algebraMap A B f) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A B) (dvd_mul_left f g)) hgfB
  -- the denominator units
  have hdu : IsUnit (algebraMap A B ((su : A) * f ^ ku)) := by
    rw [map_mul, map_pow]; exact hsuB.mul (hfB.pow ku)
  have hdv : IsUnit (algebraMap A B ((sv : A) * f ^ kv)) := by
    rw [map_mul, map_pow]; exact hsvB.mul (hfB.pow kv)
  have hdr : IsUnit (algebraMap A B ((sr : A) * f ^ kr)) := by
    rw [map_mul, map_pow]; exact hsrB.mul (hfB.pow kr)
  have hds : IsUnit (algebraMap A B ((ss : A) * f ^ ks)) := by
    rw [map_mul, map_pow]; exact hssB.mul (hfB.pow ks)
  have hdt : IsUnit (algebraMap A B ((st : A) * f ^ kt)) := by
    rw [map_mul, map_pow]; exact hstB.mul (hfB.pow kt)
  -- the numerator of the unit component is invertible on the chart
  have hbb : algebraMap A B bu * algebraMap A B bv
      = (algebraMap A B ((su : A)) * algebraMap A B f ^ ku)
        * (algebraMap A B ((sv : A)) * algebraMap A B f ^ kv) := by
    have h0 := congrArg (algebraMap A B) h₀
    simp only [map_mul, map_pow] at h0
    exact (hs₀B.mul (hfB.pow k₀)).mul_left_cancel (by linear_combination h0)
  have hbuU : IsUnit (algebraMap A B bu) :=
    isUnit_of_mul_isUnit_left (show IsUnit (algebraMap A B bu * algebraMap A B bv) from by
      rw [hbb]; exact (hsuB.mul (hfB.pow ku)).mul ((hsvB.mul (hfB.pow kv))))
  refine ⟨⟨hbuU.unit * hdu.unit⁻¹,
    algebraMap A B br * ↑hdr.unit⁻¹,
    algebraMap A B bs * ↑hds.unit⁻¹,
    algebraMap A B bt * ↑hdt.unit⁻¹⟩, ?_⟩
  refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
  · show ψ ((hbuU.unit * hdu.unit⁻¹ : Bˣ) : B)
      = ((D.u : Localization (Submonoid.powers (algebraMap A (Localization S) f))))
    rw [show ((hbuU.unit * hdu.unit⁻¹ : Bˣ) : B) = algebraMap A B bu * ↑hdu.unit⁻¹ from by
      rw [Units.val_mul, IsUnit.unit_spec]]
    exact map_num_mul_inv_eq ψ (by rw [hψ, hψ, mul_comm]; exact hu) hdu
  · exact map_num_mul_inv_eq ψ (by rw [hψ, hψ, mul_comm]; exact hr) hdr
  · exact map_num_mul_inv_eq ψ (by rw [hψ, hψ, mul_comm]; exact hs) hds
  · exact map_num_mul_inv_eq ψ (by rw [hψ, hψ, mul_comm]; exact ht) hdt

/-- **(β2, element spread into an `Away`-ring)** An element `x` of the semilocalization `L`
with fraction data `x·s = b` has a preimage in every `Away`-chart in which the denominator
`s` is invertible. -/
theorem awayPreimage_map_eq {S : Submonoid A}
    (B : Type u) [CommRing B] [Algebra A B]
    (j : B →+* Localization S)
    (hj : ∀ a : A, j (algebraMap A B a) = algebraMap A (Localization S) a)
    {x : Localization S} {b : A} {s : S}
    (hx : x * algebraMap A (Localization S) ((s : A)) = algebraMap A (Localization S) b)
    (hs : IsUnit (algebraMap A B ((s : A)))) :
    j (algebraMap A B b * ↑hs.unit⁻¹) = x :=
  map_num_mul_inv_eq j (by rw [hj, hj]; exact hx) hs

end ClearingCalculus

/-! ### Stage 3c-β2: the level maps and the restriction vocabulary -/

/-- `resLoc` at equal submonoids is the identity. -/
theorem resLoc_self {R : Type*} [CommRing R] (S₂ : Submonoid R) :
    resLoc S₂ S₂ le_rfl = RingHom.id (Localization S₂) := by
  apply IsLocalization.ringHom_ext S₂
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, resLoc_algebraMap]

/-- The comparison maps at nested basic opens into the SAME localization agree along
restriction (the `S₂ = S₃` degeneration of `sectionsToLoc_factor`). -/
theorem sectionsToLoc_comp_resLE [IsAffine X] (S' : Submonoid ↑Γ(X, ⊤))
    (g₁ g₂ : ↑Γ(X, ⊤)) (hle : X.basicOpen g₂ ≤ X.basicOpen g₁)
    (S₂ : Submonoid (Localization S'))
    (hg₁ : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₁)))
    (hg₂ : IsUnit (algebraMap (Localization S') (Localization S₂)
      (algebraMap ↑Γ(X, ⊤) (Localization S') g₂))) :
    (sectionsToLoc S' g₂ S₂ hg₂).comp (Scheme.resLE hle) = sectionsToLoc S' g₁ S₂ hg₁ := by
  have h := sectionsToLoc_factor S' g₁ g₂ hle S₂ S₂ le_rfl hg₁ hg₂
  rw [resLoc_self, RingHom.id_comp] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **(the restricted-comparison fold)** The comparison variable change of a restricted chart
pair, restricted further, is the `resLE`-image (the standalone form of the `hfold` step of
`transVC_restrict_trans`). -/
theorem transVC_restrict_map_resLE {VA VB : X.affineOpens} (PA : LocalPresentation C VA)
    (PB : LocalPresentation C VB) {VAB W' : X.affineOpens} (hA : VAB.1 ≤ VA.1)
    (hB : VAB.1 ≤ VB.1) (hW : W'.1 ≤ VAB.1) :
    ((PA.restrict hA).transVC (PB.restrict hB)).map (Scheme.resLE hW)
      = (PA.restrict (hW.trans hA)).transVC (PB.restrict (hW.trans hB)) := by
  have htr : ((PA.restrict hA).restrict hW).transVC ((PB.restrict hB).restrict hW)
      = ((PA.restrict hA).transVC (PB.restrict hB)).map
        (sectionsMapLE (𝟙 X) (show W'.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ VAB.1 by simpa using hW)) :=
    LocalPresentation.transVC_transport (𝟙 X) (𝟙 C.E)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp) (PA.restrict hA) (PB.restrict hB)
      (show W'.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ VAB.1 by simpa using hW)
  rw [← LocalPresentation.transVC_restrict_restrict PA PB hA hB hW, htr,
    LocalPresentation.sectionsMapLE_id]

/-- The comparison variable change is antisymmetric under inversion. -/
theorem transVC_inv_eq {V : X.affineOpens} (P Q : LocalPresentation C V) :
    (P.transVC Q)⁻¹ = Q.transVC P :=
  inv_eq_of_mul_eq_one_left (by
    rw [LocalPresentation.transVC_trans, LocalPresentation.transVC_self])

/-- Right-argument collapse of a double restriction in a comparison. -/
theorem transVC_restrict_restrict_right {VQ V V'' : X.affineOpens}
    (R : LocalPresentation C V'') (Q : LocalPresentation C VQ)
    (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    R.transVC ((Q.restrict q).restrict h) = R.transVC (Q.restrict (h.trans q)) := by
  rw [← transVC_inv_eq, LocalPresentation.transVC_restrict_restrict_left, transVC_inv_eq]

/-- Basic opens are antitone in divisibility. -/
theorem basicOpen_le_basicOpen_of_dvd {U : X.Opens} {a b : Γ(X, U)} (h : a ∣ b) :
    X.basicOpen b ≤ X.basicOpen a := by
  obtain ⟨c, rfl⟩ := h
  exact basicOpen_mul_le_left a c

/-- A divisor of the localized element is a unit in any `Away`-localization. -/
theorem isUnit_algebraMap_of_isLocalizationAway_dvd {A : Type u} [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B] (w : A) [IsLocalization.Away w B]
    {x : A} (h : x ∣ w) : IsUnit (algebraMap A B x) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit _)

/-- The canonical map `A[1/a] →+* Γ(X, D(a·g))` (the chart-sections incarnation of the
level inclusion; `a` is invertible on `D(a·g)` because `a ∣ a·g`). -/
noncomputable def awayToSections [IsAffine X] (a g : ↑Γ(X, ⊤)) :
    Localization.Away a →+* ↑Γ(X, X.basicOpen (a * g)) :=
  haveI := (isAffineOpen_top X).isLocalization_basicOpen (a * g)
  IsLocalization.Away.lift (g := algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen (a * g))) a
    (isUnit_algebraMap_of_isLocalizationAway_dvd _ (a * g) (dvd_mul_right a g))

@[simp] theorem awayToSections_algebraMap [IsAffine X] (a g x : ↑Γ(X, ⊤)) :
    awayToSections (X := X) a g (algebraMap ↑Γ(X, ⊤) (Localization.Away a) x)
      = algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen (a * g)) x := by
  haveI := (isAffineOpen_top X).isLocalization_basicOpen (a * g)
  exact IsLocalization.Away.lift_eq a _ x

/-- **(ForMathlib, localization-away tower)** Localizing the localization of `A` away from `a`
further at the image of `g` gives the localization of `A` away from `a * g`.  Tower form:
if `R₁` is `A` away from `a` and `Γ` is `A` away from `a * g`, and `Γ` is a compatible
`R₁`-algebra (scalar tower), then `Γ` is `R₁` away from the image of `g`. -/
theorem isLocalizationAway_of_tower {A R₁ Γ : Type*} [CommRing A] [CommRing R₁] [CommRing Γ]
    [Algebra A R₁] [Algebra A Γ] [Algebra R₁ Γ] [IsScalarTower A R₁ Γ]
    (a g : A) [IsLocalization.Away a R₁] [IsLocalization.Away (a * g) Γ] :
    IsLocalization.Away (algebraMap A R₁ g) Γ := by
  have hau : IsUnit (algebraMap A R₁ a) := IsLocalization.Away.algebraMap_isUnit a
  have htower : ∀ x : A, algebraMap R₁ Γ (algebraMap A R₁ x) = algebraMap A Γ x :=
    fun x => (IsScalarTower.algebraMap_apply A R₁ Γ x).symm
  have hunit_val : algebraMap R₁ Γ (↑hau.unit) = algebraMap A Γ a := by
    rw [hau.unit_spec, htower]
  set v : Γ := algebraMap R₁ Γ (↑hau.unit⁻¹) with hv
  have hav : algebraMap A Γ a * v = 1 := by
    rw [hv, ← hunit_val, ← map_mul, Units.mul_inv, map_one]
  apply IsLocalization.Away.mk
  · rw [htower]
    exact isUnit_of_dvd_unit (map_dvd (algebraMap A Γ) (dvd_mul_left g a))
      (IsLocalization.Away.algebraMap_isUnit (a * g))
  · intro s
    obtain ⟨m, b, hmb⟩ := IsLocalization.Away.surj (a * g) s
    rw [map_mul, mul_pow] at hmb
    refine ⟨m, algebraMap A R₁ b * (↑hau.unit⁻¹) ^ m, ?_⟩
    rw [htower, map_mul, map_pow, htower, ← hv]
    have hav1 : (algebraMap A Γ a) ^ m * v ^ m = 1 := by rw [← mul_pow, hav, one_pow]
    calc s * (algebraMap A Γ g) ^ m
        = s * (algebraMap A Γ g) ^ m * ((algebraMap A Γ a) ^ m * v ^ m) := by rw [hav1, mul_one]
      _ = s * ((algebraMap A Γ a) ^ m * (algebraMap A Γ g) ^ m) * v ^ m := by ring
      _ = algebraMap A Γ b * v ^ m := by rw [hmb]
  · intro b c hbc
    obtain ⟨j, b₀, hb₀⟩ := IsLocalization.Away.surj a b
    obtain ⟨k, c₀, hc₀⟩ := IsLocalization.Away.surj a c
    have hθ : algebraMap A Γ (b₀ * a ^ k) = algebraMap A Γ (c₀ * a ^ j) := by
      have hψb : algebraMap R₁ Γ b * algebraMap A Γ a ^ j = algebraMap A Γ b₀ := by
        have := congrArg (algebraMap R₁ Γ) hb₀
        rwa [map_mul, map_pow, htower, htower] at this
      have hψc : algebraMap R₁ Γ c * algebraMap A Γ a ^ k = algebraMap A Γ c₀ := by
        have := congrArg (algebraMap R₁ Γ) hc₀
        rwa [map_mul, map_pow, htower, htower] at this
      rw [map_mul, map_mul, map_pow, map_pow, ← hψb, ← hψc, hbc]
      ring
    obtain ⟨p, hp⟩ := IsLocalization.Away.exists_of_eq (a * g) hθ
    refine ⟨p, ?_⟩
    have hφp : algebraMap A R₁ ((a * g) ^ p * (b₀ * a ^ k))
        = algebraMap A R₁ ((a * g) ^ p * (c₀ * a ^ j)) := congrArg (algebraMap A R₁) hp
    simp only [map_mul, map_pow] at hφp
    rw [← hb₀, ← hc₀, mul_pow] at hφp
    have hunit : IsUnit (algebraMap A R₁ a ^ (p + j + k)) := hau.pow _
    apply hunit.mul_right_cancel
    rw [pow_add, pow_add]
    linear_combination hφp

/-- **(Stage 3c-γ, THE missing barrier — open immersion)** `Spec.map (awayToSections a g)` is an
open immersion: `Γ(X, D(a·g))` is the localization of `A[1/a]` away from the image of `g`
(`isLocalizationAway_of_tower`), so this is `Spec` of a localization-away map.  An `instance` so
`(Spec.map (awayToSections a g)).opensRange` elaborates downstream. -/
instance isOpenImmersion_specMap_awayToSections [IsAffine X] (a g : ↑Γ(X, ⊤)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayToSections a g))) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  letI : IsScalarTower ↑Γ(X, ⊤) (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    IsScalarTower.of_algebraMap_eq (fun x => (awayToSections_algebraMap a g x).symm)
  haveI := isLocalizationAway_of_tower (A := ↑Γ(X, ⊤)) (R₁ := Localization.Away a)
    (Γ := ↑Γ(X, X.basicOpen (a * g))) a g
  exact IsOpenImmersion.of_isLocalization (R := Localization.Away a)
    (S := ↑Γ(X, X.basicOpen (a * g)))
    (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)

/-- **(Stage 3c-γ, THE missing barrier — range)** The open range of `Spec.map (awayToSections a g)`
is the basic open `D(g')` of `Spec A[1/a]`, where `g'` is the image of `g`
(`localization_away_comap_range` at the tower localization). -/
theorem opensRange_specMap_awayToSections [IsAffine X] (a g : ↑Γ(X, ⊤)) :
    (Spec.map (CommRingCat.ofHom (awayToSections a g))).opensRange =
      specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  letI : IsScalarTower ↑Γ(X, ⊤) (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    IsScalarTower.of_algebraMap_eq (fun x => (awayToSections_algebraMap a g x).symm)
  haveI := isLocalizationAway_of_tower (A := ↑Γ(X, ⊤)) (R₁ := Localization.Away a)
    (Γ := ↑Γ(X, X.basicOpen (a * g))) a g
  apply TopologicalSpace.Opens.ext
  show Set.range ⇑(Spec.map (CommRingCat.ofHom (awayToSections a g))) = _
  exact PrimeSpectrum.localization_away_comap_range ↑Γ(X, X.basicOpen (a * g))
    (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)

/-- **(Stage 3c-γ helper, banked)** The base-change model map `projModelBaseChange σ W` is an open
immersion when the base `Spec σ` is: it is the base change of `Spec σ` along `projModelπ W`.  An
`instance` so `(projModelBaseChange σ W).opensRange` elaborates downstream. -/
instance isOpenImmersion_projModelBaseChange {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    [Algebra R R'] (W : WeierstrassCurve R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R R')))] :
    IsOpenImmersion (projModelBaseChange (algebraMap R R') W) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_projModelBaseChange W).flip inferInstance

-- NOTE (banked, γ3): the *range* of `projModelBaseChange σ W` equals
-- `projModelπ W ⁻¹ᵁ (Spec σ).opensRange`.  As a standalone `= ...opensRange` lemma this hits an
-- `opensRange` dependent-motive snag (rewriting the morphism under `.opensRange`, whose type
-- carries the `IsOpenImmersion` instance); derive it inline where needed, at the `Set`-level:
-- `apply Opens.ext; show Set.range ⇑(projModelBaseChange σ W) = _;`
-- `rw [← (isPullback_projModelBaseChange W).isoPullback_hom_fst]` (motive OK at `Set.range ⇑·`),
-- then `Scheme.Hom.comp_apply` + `Set.range_comp` + iso-surjectivity + `Scheme.Pullback.range_fst`.

/-- The canonical map `A[1/a] →+* Localization S` for `a ∈ S`. -/
noncomputable def awayToLocalization {A : Type u} [CommRing A] (S : Submonoid A)
    {a : A} (ha : a ∈ S) : Localization.Away a →+* Localization S :=
  IsLocalization.Away.lift (g := algebraMap A (Localization S)) a
    (IsLocalization.map_units (Localization S) ⟨a, ha⟩)

@[simp] theorem awayToLocalization_algebraMap {A : Type u} [CommRing A] (S : Submonoid A)
    {a : A} (ha : a ∈ S) (x : A) :
    awayToLocalization S ha (algebraMap A (Localization.Away a) x)
      = algebraMap A (Localization S) x :=
  IsLocalization.Away.lift_eq a _ x

/-- The canonical map `A[1/a] →+* A[1/b]` for `a ∣ b`. -/
noncomputable def awayMapDvd {A : Type u} [CommRing A] {a b : A} (h : a ∣ b) :
    Localization.Away a →+* Localization.Away b :=
  IsLocalization.lift (M := Submonoid.powers a)
    (g := algebraMap A (Localization.Away b)) (by
      rintro ⟨y, n, rfl⟩
      show IsUnit (algebraMap A (Localization.Away b) (a ^ n))
      rw [map_pow]
      exact (isUnit_algebraMap_away h).pow n)

@[simp] theorem awayMapDvd_algebraMap {A : Type u} [CommRing A] {a b : A} (h : a ∣ b)
    (x : A) :
    awayMapDvd h (algebraMap A (Localization.Away a) x)
      = algebraMap A (Localization.Away b) x :=
  IsLocalization.lift_eq _ x

/-- Restriction of a global section to a smaller basic open is the smaller algebra map. -/
theorem resLE_algebraMap [IsAffine X] {g₁ g₂ : ↑Γ(X, ⊤)}
    (hle : X.basicOpen g₂ ≤ X.basicOpen g₁) (x : ↑Γ(X, ⊤)) :
    Scheme.resLE hle (algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₁) x)
      = algebraMap ↑Γ(X, ⊤) ↑Γ(X, X.basicOpen g₂) x :=
  Scheme.resLE_resLE hle (X.basicOpen_le g₁) x

/-! ### Stage 3c-β decomposition helpers (heartbeat-scoped) -/

theorem resLE_comp_resLE [IsAffine X] {g₁ g₂ g₃ : ↑Γ(X, ⊤)}
    (h12 : X.basicOpen g₂ ≤ X.basicOpen g₁) (h23 : X.basicOpen g₃ ≤ X.basicOpen g₂) :
    (Scheme.resLE h23).comp (Scheme.resLE h12) = Scheme.resLE (h23.trans h12) := by
  haveI := (isAffineOpen_top X).isLocalization_basicOpen g₁
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [resLE_algebraMap, resLE_algebraMap, resLE_algebraMap]

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 glue clearing)** Per chart, `DA₀ i • (P i).W|` and `W₀R₀ ⊗ Γ(X, D(a₀·fᵢ))`
agree after one invariant `S'`-multiplier. -/
theorem spread_glue_clear (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (W₀L : WeierstrassCurve (Localization S'))
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G) (ha₀S : ((a₀ : ↑Γ(X, ⊤))) ∈ S')
    (W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))))
    (hW₀R₀ : W₀R₀.map (awayToLocalization S' ha₀S) = W₀L)
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))))
    (hDA₀eq : ∀ i, (DA₀ i).map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i)
    (hglue : ∀ i, W₀L.map (algebraMap (Localization S')
        (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
      = D i • ((P i).W.map (sectionsToLoc S' (f i)
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
          (isUnit_algebraMap_powers_self
            (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))) :
    ∀ i, ∃ s : S',
      algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₁
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₁
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₂
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₂
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₃
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₃
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₄
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₄
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₆
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₆ := by
  intro i
  set j₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤))) →+* Localization S' :=
    awayToLocalization S' ha₀S with hj₀def
  have hj₀alg : ∀ x : ↑Γ(X, ⊤),
      j₀ (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) x)
        = algebraMap ↑Γ(X, ⊤) (Localization S') x :=
    fun x => awayToLocalization_algebraMap S' ha₀S x
  haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)
  have hcompᵢ : (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)).comp
        (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))
      = (algebraMap (Localization S')
          (Localization (Submonoid.powers
            (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))).comp j₀ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (a₀ : ↑Γ(X, ⊤)))
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, awayToSections_algebraMap,
      sectionsToLoc_algebraMap, hj₀alg]
  have hLHS : ((DA₀ i) • ((P i).W.map (Scheme.resLE
          (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).map
        (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      = D i • ((P i).W.map (sectionsToLoc S' (f i) _
          (isUnit_algebraMap_powers_self (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))) := by
    rw [← WeierstrassCurve.map_variableChange, hDA₀eq i, WeierstrassCurve.map_map,
      sectionsToLoc_comp_resLE S' (f i) ((a₀ : ↑Γ(X, ⊤)) * f i)
        (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i)) _
        (isUnit_algebraMap_powers_self _) (hψunit i)]
  have hRHS : (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).map
        (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      = W₀L.map (algebraMap (Localization S')
          (Localization (Submonoid.powers
            (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))) := by
    rw [WeierstrassCurve.map_map, hcompᵢ, ← WeierstrassCurve.map_map, hW₀R₀]
  have hWeq : ((DA₀ i) • ((P i).W.map (Scheme.resLE
        (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).map
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      = (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).map
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) := by
    rw [hLHS, hRHS]; exact (hglue i).symm
  exact exists_mem_clear_weierstrassCurve S' (g := (a₀ : ↑Γ(X, ⊤))) (f := f i) ha₀S _
    (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
    (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i) a) hWeq

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 transVC LHS-image)** The `ψ₂`-image of the corrected transition equals the
pairwise transition over the join tower. -/
theorem spread_transVC_T1 (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (hU : ∀ i j, IsUnit (algebraMap (Localization S')
      (Localization
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
          ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))))
    (i j : ι)
    (hWij : X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) ≤ X.basicOpen (f i * f j))
    (hJ2 : IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
        ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))) :
    (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
          (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
          ((hWij).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
        ((P j).restrict ((hWij).trans (basicOpen_mul_le_right (f i) (f j))))).map
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2)
      = (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
            (isAffineOpen_top X).basicOpen (f i * f j)⟩)
            (basicOpen_mul_le_left (f i) (f j))).transVC
          ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
            (sectionsToLoc S' (f i * f j) _ (hU i j)) := by
  set ψ₂ := sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2 with hψ₂def
  have hcomp2 : ψ₂.comp (Scheme.resLE hWij)
      = sectionsToLoc S' (f i * f j) _ (hU i j) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f i * f j))
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, resLE_algebraMap,
      sectionsToLoc_algebraMap, hψ₂def]
  rw [← transVC_restrict_map_resLE (P i) (P j)
    (VAB := ⟨X.basicOpen (f i * f j), (isAffineOpen_top X).basicOpen (f i * f j)⟩)
    (W' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
      (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
    (basicOpen_mul_le_left (f i) (f j))
    (basicOpen_mul_le_right (f i) (f j)) (hWij), VariableChange.map_map, hcomp2]

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 transVC single-chart image)** For one chart `k` of the pair `(i,j)`, the
`ψ₂`-image of the restricted correction `DA₀ k|` is the tower-restriction of `D k`. -/
theorem spread_transVC_DAmap (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))))
    (hDA₀eq : ∀ i, (DA₀ i).map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i)
    (i j k : ι)
    (hleAk : X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f k))
    (hsub : Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f k))
      ≤ (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
        ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
    (hJ2 : IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
        ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))) :
    ((DA₀ k).map (Scheme.resLE hleAk)).map
        (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2)
      = (D k).map (resLoc (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f k)))
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
            ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))) hsub) := by
  have hcompDA : (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2).comp
        (Scheme.resLE hleAk)
      = (resLoc (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f k)))
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
            ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))) hsub).comp
        (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f k) _ (hψunit k)) := by
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f k)
    apply IsLocalization.ringHom_ext (Submonoid.powers ((a₀ : ↑Γ(X, ⊤)) * f k))
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, resLE_algebraMap,
      sectionsToLoc_algebraMap, resLoc_algebraMap]
  rw [VariableChange.map_map, hcompDA, ← VariableChange.map_map, hDA₀eq k]

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 transVC RHS-image)** The `ψ₂`-image of `(DA₀|)⁻¹·(DA₀|)` equals the correction
coboundary over the join tower. -/
theorem spread_transVC_T2 (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))))
    (hDA₀eq : ∀ i, (DA₀ i).map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i)
    (i j : ι)
    (hleAi : X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))
    (hleAj : X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j))
    (hJ2 : IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
        ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))) :
    ((((DA₀ i).map (Scheme.resLE hleAi))⁻¹
        * (DA₀ j).map (Scheme.resLE hleAj)).map
        (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2))
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
  rw [vc_map_inv_mul,
    spread_transVC_DAmap G S' f D a₀ DA₀ hψunit hDA₀eq i j i hleAi le_sup_left hJ2,
    spread_transVC_DAmap G S' f D a₀ DA₀ hψunit hDA₀eq i j j hleAj le_sup_right hJ2]

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 transVC clearing)** Per overlap, the corrected transition and `(DA₀|)⁻¹·(DA₀|)`
agree after one invariant `S'`-multiplier. -/
theorem spread_transVC_clear (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G) (ha₀S : ((a₀ : ↑Γ(X, ⊤))) ∈ S')
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))))
    (hDA₀eq : ∀ i, (DA₀ i).map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i)
    (hU : ∀ i j, IsUnit (algebraMap (Localization S')
      (Localization
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
          ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))))
    (hcobInv : ∀ i j,
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
            le_sup_right))
    (hWij : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) ≤ X.basicOpen (f i * f j))
    (hleAi : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))
    (hleAj : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j)) :
    ∀ i j, ∃ c : S',
      algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * ((((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).u
            : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * ((((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).u
            : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).r
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).r
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).s
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).s
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).t
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).t := by
  intro i j
  haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
  have hJ2 : IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
        ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)))) := by
    rw [map_mul, map_mul]
    exact ((IsLocalization.map_units (Localization S')
        (⟨(a₀ : ↑Γ(X, ⊤)), ha₀S⟩ : S')).map (algebraMap (Localization S') _)).mul (hU i j)
  exact exists_mem_clear_variableChange₂ S' (g := (a₀ : ↑Γ(X, ⊤))) (f₁ := f i) (f₂ := f j)
    ha₀S _ (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2)
    (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2 a)
    ((spread_transVC_T1 G S' f P a₀ hU i j (hWij i j) hJ2).trans
      ((hcobInv i j).trans
        (spread_transVC_T2 G S' f D a₀ DA₀ hψunit hDA₀eq i j (hleAi i j) (hleAj i j) hJ2).symm))

set_option backward.isDefEq.respectTransparency false in
/-- **(β2 model curve)** Realize `W₀L`'s coefficients and `Δ`-inverse over `A_{a₀}`. -/
theorem spread_build_curve (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    (W₀L : WeierstrassCurve (Localization S'))
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G) (ha₀S : ((a₀ : ↑Γ(X, ⊤))) ∈ S')
    (b₁ b₂ b₃ b₄ b₆ bΔ : ↑Γ(X, ⊤)) (s₁ s₂ s₃ s₄ s₆ sΔ : S') (v : Localization S')
    (hb₁ : W₀L.a₁ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₁ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') b₁)
    (hb₂ : W₀L.a₂ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₂ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') b₂)
    (hb₃ : W₀L.a₃ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₃ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') b₃)
    (hb₄ : W₀L.a₄ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₄ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') b₄)
    (hb₆ : W₀L.a₆ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₆ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') b₆)
    (hv : W₀L.Δ * v = 1)
    (hbΔ : v * algebraMap ↑Γ(X, ⊤) (Localization S') (sΔ : ↑Γ(X, ⊤))
      = algebraMap ↑Γ(X, ⊤) (Localization S') bΔ)
    (hdvd₁ : ((s₁ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤)))) (hdvd₂ : ((s₂ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))))
    (hdvd₃ : ((s₃ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤)))) (hdvd₄ : ((s₄ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))))
    (hdvd₆ : ((s₆ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤)))) (hdvdΔ : ((sΔ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤)))) :
    ∃ (W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))))
      (vR₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ : S'),
      W₀R₀.map (awayToLocalization S' ha₀S) = W₀L ∧
      algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ : ↑Γ(X, ⊤))
          * (W₀R₀.Δ * vR₀)
        = algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ : ↑Γ(X, ⊤)) * 1 := by
  set j₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤))) →+* Localization S' :=
    awayToLocalization S' ha₀S with hj₀def
  have hj₀alg : ∀ x : ↑Γ(X, ⊤),
      j₀ (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) x)
        = algebraMap ↑Γ(X, ⊤) (Localization S') x :=
    fun x => awayToLocalization_algebraMap S' ha₀S x
  have hu₁ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₁ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₁
  have hu₂ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₂ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₂
  have hu₃ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₃ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₃
  have hu₄ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₄ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₄
  have hu₆ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₆ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₆
  have huΔ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (sΔ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvdΔ
  set W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) :=
    ⟨algebraMap _ _ b₁ * ↑hu₁.unit⁻¹, algebraMap _ _ b₂ * ↑hu₂.unit⁻¹,
     algebraMap _ _ b₃ * ↑hu₃.unit⁻¹, algebraMap _ _ b₄ * ↑hu₄.unit⁻¹,
     algebraMap _ _ b₆ * ↑hu₆.unit⁻¹⟩ with hW₀R₀def
  set vR₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤))) :=
    algebraMap _ _ bΔ * ↑huΔ.unit⁻¹ with hvR₀def
  have hW₀R₀ : W₀R₀.map j₀ = W₀L := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show j₀ (algebraMap _ _ b₁ * ↑hu₁.unit⁻¹) = W₀L.a₁
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₁ (hj₀alg b₁) (hj₀alg (s₁ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₁).symm
    · show j₀ (algebraMap _ _ b₂ * ↑hu₂.unit⁻¹) = W₀L.a₂
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₂ (hj₀alg b₂) (hj₀alg (s₂ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₂).symm
    · show j₀ (algebraMap _ _ b₃ * ↑hu₃.unit⁻¹) = W₀L.a₃
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₃ (hj₀alg b₃) (hj₀alg (s₃ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₃).symm
    · show j₀ (algebraMap _ _ b₄ * ↑hu₄.unit⁻¹) = W₀L.a₄
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₄ (hj₀alg b₄) (hj₀alg (s₄ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₄).symm
    · show j₀ (algebraMap _ _ b₆ * ↑hu₆.unit⁻¹) = W₀L.a₆
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₆ (hj₀alg b₆) (hj₀alg (s₆ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₆).symm
  have hvR₀ : j₀ vR₀ = v := by
    rw [hvR₀def, map_mul_isUnit_inv_eq_mk' j₀ huΔ (hj₀alg bΔ) (hj₀alg (sΔ : ↑Γ(X, ⊤)))]
    exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hbΔ).symm
  have hΔ01 : j₀ W₀R₀.Δ = W₀L.Δ := by
    have h := congrArg WeierstrassCurve.Δ hW₀R₀
    rwa [WeierstrassCurve.map_Δ] at h
  have hunitΔ : j₀ (W₀R₀.Δ * vR₀) = j₀ 1 := by
    rw [map_mul, hΔ01, hvR₀, map_one]; exact hv
  obtain ⟨cΔ, hcΔ⟩ := exists_mem_mul_eq_of_away_map_eq S' (g := (a₀ : ↑Γ(X, ⊤)))
    (B := Localization.Away ((a₀ : ↑Γ(X, ⊤)))) j₀ hj₀alg hunitΔ
  exact ⟨W₀R₀, vR₀, cΔ, hW₀R₀, hcΔ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **(β assembly, transVC-triviality goal at `a₁`)** -/
theorem spread_assemble_transVC (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (a₀ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (a₁ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (hDAle : ∀ i, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i) ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))
    (cAll : S') (pc : ↑Γ(X, ⊤))
    (ha₁coe : (a₁ : ↑Γ(X, ⊤)) = (a₀ : ↑Γ(X, ⊤)) * pc)
    (hcAlldvda₁ : (cAll : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)))
    (cT : ι → ι → S')
    (hWij : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) ≤ X.basicOpen (f i * f j))
    (hleAi : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))
    (hleAj : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j))
    (hcTdvd : ∀ i j, (cT i j : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)))
    (hcTu : ∀ i j, algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * ((((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
            (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
            ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
            ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).u
          : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))
      = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * ((((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
            * (DA₀ j).map (Scheme.resLE (hleAj i j))).u
          : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)))))
    (hcTr : ∀ i j, algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
            (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
            ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
            ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).r
      = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
            * (DA₀ j).map (Scheme.resLE (hleAj i j))).r)
    (hcTs : ∀ i j, algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
            (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
            ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
            ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).s
      = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
            * (DA₀ j).map (Scheme.resLE (hleAj i j))).s)
    (hcTt : ∀ i j, algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
            (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
            ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
            ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).t
      = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤))
        * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
            * (DA₀ j).map (Scheme.resLE (hleAj i j))).t)
    (i j : ι) :
    ((P i).restrict (V' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
        (isAffineOpen_top X).basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))⟩)
        ((basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j)).trans
          (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i)))).transVC
      ((P j).restrict
        ((basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j)).trans
          (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f j))))
      = (((DA₀ i).map (Scheme.resLE (hDAle i))).map (Scheme.resLE
          (basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))))⁻¹
        * ((DA₀ j).map (Scheme.resLE (hDAle j))).map (Scheme.resLE
          (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))) := by
  have hle₂ : X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) :=
    basicOpen_le_basicOpen_of_dvd
      ⟨(a₀ : ↑Γ(X, ⊤)) * (pc * pc), by rw [ha₁coe]; ring⟩
  have hUcAll_ij : IsUnit (algebraMap ↑Γ(X, ⊤)
      ↑Γ(X, X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)))
      (cAll : ↑Γ(X, ⊤))) := by
    haveI := (isAffineOpen_top X).isLocalization_basicOpen
      (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
    exact isUnit_algebraMap_of_isLocalizationAway_dvd _
      (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
      (hcAlldvda₁.trans ((dvd_mul_right (a₁ : ↑Γ(X, ⊤)) (f i)).mul_right _))
  have hup : ∀ (w₁ w₂ : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)))),
      algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤)) * w₁
        = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤)) * w₂ →
      algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₁
        = algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₂ :=
    fun w₁ w₂ h => mul_eq_mul_of_dvd (map_dvd _ (hcTdvd i j)) h
  have hmapeq := variableChange_map_eq_of_mul_eq (Scheme.resLE hle₂)
    (u := algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))
    (show IsUnit (Scheme.resLE hle₂
      (algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))) by rw [resLE_algebraMap]; exact hUcAll_ij)
    (hup _ _ (hcTu i j)) (hup _ _ (hcTr i j)) (hup _ _ (hcTs i j)) (hup _ _ (hcTt i j))
  rw [← transVC_restrict_map_resLE (P i) (P j)
    (VAB := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
      (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
    (W' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
      (isAffineOpen_top X).basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))⟩)
    ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))
    ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))) hle₂,
    VariableChange.map_map, VariableChange.map_map,
    resLE_comp_resLE (hDAle i) (basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i)
      ((a₁ : ↑Γ(X, ⊤)) * f j)),
    resLE_comp_resLE (hDAle j) (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i)
      ((a₁ : ↑Γ(X, ⊤)) * f j))]
  rw [vc_map_inv_mul, VariableChange.map_map, VariableChange.map_map,
    resLE_comp_resLE (hleAi i j) hle₂, resLE_comp_resLE (hleAj i j) hle₂] at hmapeq
  exact hmapeq

set_option backward.isDefEq.respectTransparency false in
/-- **(β assembly, ellipticity goal at `a₁`)** -/
theorem spread_assemble_ell (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    (a₀ a₁ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))))
    (vR₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ cAll : S')
    (hcΔ : algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ : ↑Γ(X, ⊤))
        * (W₀R₀.Δ * vR₀)
      = algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cΔ : ↑Γ(X, ⊤)) * 1)
    (hcΔdvd : (cΔ : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)))
    (ha₀dvda₁ : (a₀ : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)))
    (hcAlldvda₁ : (cAll : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤))) :
    IsUnit (W₀R₀.map (awayMapDvd ha₀dvda₁)).Δ := by
  refine IsUnit.of_mul_eq_one (awayMapDvd ha₀dvda₁ vR₀) ?_
  have hcΔcAll : algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤))
        * (W₀R₀.Δ * vR₀)
      = algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤)) * 1 :=
    mul_eq_mul_of_dvd (map_dvd _ hcΔdvd) hcΔ
  have hUcAllAway : IsUnit (awayMapDvd ha₀dvda₁ (algebraMap ↑Γ(X, ⊤)
      (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤)))) := by
    rw [awayMapDvd_algebraMap]
    exact isUnit_algebraMap_away hcAlldvda₁
  have h := map_eq_of_isUnit_mul_eq (awayMapDvd ha₀dvda₁) hUcAllAway hcΔcAll
  rw [map_mul, map_one] at h
  rw [WeierstrassCurve.map_Δ]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **(β assembly, glue goal at `a₁`)** -/
theorem spread_assemble_glue (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    {ι : Type u} (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (a₀ a₁ : FixedPoints.subring ↑Γ(X, ⊤) G)
    (W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))))
    (DA₀ : ∀ i, VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)))
    (hDAle : ∀ i, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i) ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))
    (ha₀dvda₁ : (a₀ : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)))
    (cAll : S') (sGlue : ι → S')
    (hsGdvd : ∀ i, (sGlue i : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)))
    (hcAlldvda₁ : (cAll : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)))
    (hsG1 : ∀ i, algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₁
      = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₁)
    (hsG2 : ∀ i, algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₂
      = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₂)
    (hsG3 : ∀ i, algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₃
      = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₃)
    (hsG4 : ∀ i, algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₄
      = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₄)
    (hsG6 : ∀ i, algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₆
      = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤))
        * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₆)
    (i : ι) :
    (DA₀ i).map (Scheme.resLE (hDAle i)) • ((P i).W.map (Scheme.resLE
        (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i))))
      = (W₀R₀.map (awayMapDvd ha₀dvda₁)).map (awayToSections (a₁ : ↑Γ(X, ⊤)) (f i)) := by
  have hUcAll_i : IsUnit (algebraMap ↑Γ(X, ⊤)
      ↑Γ(X, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)) (cAll : ↑Γ(X, ⊤))) := by
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)
    exact isUnit_algebraMap_of_isLocalizationAway_dvd _ ((a₁ : ↑Γ(X, ⊤)) * f i)
      (hcAlldvda₁.trans (dvd_mul_right _ _))
  have hup : ∀ (w₁ w₂ : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))),
      algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤)) * w₁
        = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤)) * w₂ →
      algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₁
        = algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₂ :=
    fun w₁ w₂ h => mul_eq_mul_of_dvd (map_dvd _ (hsGdvd i)) h
  have hmapeq := weierstrassCurve_map_eq_of_mul_eq (Scheme.resLE (hDAle i))
    (u := algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))
    (show IsUnit (Scheme.resLE (hDAle i)
      (algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))) by rw [resLE_algebraMap]; exact hUcAll_i)
    (hup _ _ (hsG1 i)) (hup _ _ (hsG2 i)) (hup _ _ (hsG3 i)) (hup _ _ (hsG4 i)) (hup _ _ (hsG6 i))
  have hcompRHS : (Scheme.resLE (hDAle i)).comp (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))
      = (awayToSections (a₁ : ↑Γ(X, ⊤)) (f i)).comp (awayMapDvd ha₀dvda₁) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (a₀ : ↑Γ(X, ⊤)))
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, awayToSections_algebraMap,
      resLE_algebraMap, awayMapDvd_algebraMap]
  rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map,
    resLE_comp_resLE (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i)) (hDAle i),
    WeierstrassCurve.map_map, hcompRHS, ← WeierstrassCurve.map_map] at hmapeq
  exact hmapeq



/-- **(β2 fractions)** Realize the five coefficients of the glued model `W₀L / L` and the
`Δ`-inverse witness as fractions with denominators in `S'` (a single `IsLocalization.surj`
sweep, extracted so the main spread body stays under the per-declaration heartbeat budget). -/
theorem spread_fractions (S' : Submonoid ↑Γ(X, ⊤))
    (W₀L : WeierstrassCurve (Localization S')) (hΔ : IsUnit W₀L.Δ) :
    ∃ (b₁ b₂ b₃ b₄ b₆ bΔ : ↑Γ(X, ⊤)) (s₁ s₂ s₃ s₄ s₆ sΔ : S') (v : Localization S'),
      W₀L.a₁ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₁ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') b₁ ∧
      W₀L.a₂ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₂ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') b₂ ∧
      W₀L.a₃ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₃ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') b₃ ∧
      W₀L.a₄ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₄ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') b₄ ∧
      W₀L.a₆ * algebraMap ↑Γ(X, ⊤) (Localization S') (s₆ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') b₆ ∧
      W₀L.Δ * v = 1 ∧
      v * algebraMap ↑Γ(X, ⊤) (Localization S') (sΔ : ↑Γ(X, ⊤))
          = algebraMap ↑Γ(X, ⊤) (Localization S') bΔ := by
  obtain ⟨⟨b₁, s₁⟩, hb₁⟩ := IsLocalization.surj S' W₀L.a₁
  obtain ⟨⟨b₂, s₂⟩, hb₂⟩ := IsLocalization.surj S' W₀L.a₂
  obtain ⟨⟨b₃, s₃⟩, hb₃⟩ := IsLocalization.surj S' W₀L.a₃
  obtain ⟨⟨b₄, s₄⟩, hb₄⟩ := IsLocalization.surj S' W₀L.a₄
  obtain ⟨⟨b₆, s₆⟩, hb₆⟩ := IsLocalization.surj S' W₀L.a₆
  obtain ⟨v, hv⟩ := hΔ.exists_right_inv
  obtain ⟨⟨bΔ, sΔ⟩, hbΔ⟩ := IsLocalization.surj S' v
  exact ⟨b₁, b₂, b₃, b₄, b₆, bΔ, s₁, s₂, s₃, s₄, s₆, sΔ, v,
    hb₁, hb₂, hb₃, hb₄, hb₆, hv, hbΔ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **([a5-P-loc] Stage 3c-β, the invariant-denominator spread ★)** The α-package data over
the semilocalization `L = Localization S'` — the glued model `W₀L`, the correction cochain
`D i / L[1/fᵢ]`, the per-chart glue identities and the corrected coboundary — spreads to a
single invariant level `a₁ ∉ p`: an elliptic model `W₀R₁ / A[1/a₁]`, per-chart corrections
`DA i` over the chart sections `Γ(X, D(a₁·fᵢ))` with

* `DA i • (P i).W|_{D(a₁fᵢ)} = W₀R₁ ⊗ Γ(X, D(a₁·fᵢ))` (through `awayToSections`), and
* the corrected chart coboundary
  `transVC ((P i)|, (P j)|) = (DA i|)⁻¹ * (DA j|)` on the chart overlaps `D((a₁fᵢ)(a₁fⱼ))`,

together with the span condition over `A[1/a₁]`.  This is the Part-2 pattern of
`exists_away_invariant_descent` run through the chart-clearing calculus above: choose
fraction data over `L`/`L[1/fᵢ]`, fold the denominators into a preliminary invariant `a₀`,
build the data at level `a₀`, clear the finitely many identities (each `ψ`-image holds on
the nose), fold the clearing multipliers into `a₁` and descend along the canonical
restriction maps. -/
theorem exists_invariant_chart_spread (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    (p : Ideal (FixedPoints.subring ↑Γ(X, ⊤) G)) [p.IsPrime]
    (hpreS : ∀ s : S', ∃ k : FixedPoints.subring ↑Γ(X, ⊤) G,
      k ∉ p ∧ algebraMap (FixedPoints.subring ↑Γ(X, ⊤) G) ↑Γ(X, ⊤) k = (s : ↑Γ(X, ⊤)))
    (hmemS : ∀ k : FixedPoints.subring ↑Γ(X, ⊤) G, k ∉ p → ((k : ↑Γ(X, ⊤))) ∈ S')
    {ι : Type u} [Fintype ι] (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (k₀ : FixedPoints.subring ↑Γ(X, ⊤) G) (hk₀ : k₀ ∉ p)
    (hspanA : ∀ a : FixedPoints.subring ↑Γ(X, ⊤) G, k₀ ∣ a →
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization.Away ((a : ↑Γ(X, ⊤)))) (f i)) = ⊤)
    (hU : ∀ i j, IsUnit (algebraMap (Localization S')
      (Localization
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
          ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))))
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (W₀L : WeierstrassCurve (Localization S'))
    (hΔ : IsUnit W₀L.Δ)
    (hglue : ∀ i, W₀L.map (algebraMap (Localization S')
        (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
      = D i • ((P i).W.map (sectionsToLoc S' (f i)
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
          (isUnit_algebraMap_powers_self
            (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))))
    (hcobInv : ∀ i j,
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
            le_sup_right)) :
    ∃ (a₁ : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a₁ ∉ p)
      (W₀R₁ : WeierstrassCurve (Localization.Away ((a₁ : ↑Γ(X, ⊤)))))
      (DA : ∀ i, VariableChange ↑Γ(X, X.basicOpen (((a₁ : ↑Γ(X, ⊤))) * f i))),
      IsUnit W₀R₁.Δ ∧
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₁ : ↑Γ(X, ⊤)))) (f i)) = ⊤ ∧
      (∀ i, DA i • ((P i).W.map (Scheme.resLE
          (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f i))))
        = W₀R₁.map (awayToSections ((a₁ : ↑Γ(X, ⊤))) (f i))) ∧
      (∀ i j,
        ((P i).restrict (V' := ⟨X.basicOpen ((((a₁ : ↑Γ(X, ⊤))) * f i)
              * (((a₁ : ↑Γ(X, ⊤))) * f j)),
            (isAffineOpen_top X).basicOpen ((((a₁ : ↑Γ(X, ⊤))) * f i)
              * (((a₁ : ↑Γ(X, ⊤))) * f j))⟩)
          ((basicOpen_mul_le_left (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j)).trans
            (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f i)))).transVC
        ((P j).restrict
          ((basicOpen_mul_le_right (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j)).trans
            (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f j))))
        = ((DA i).map (Scheme.resLE
            (basicOpen_mul_le_left (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j))))⁻¹
          * (DA j).map (Scheme.resLE
            (basicOpen_mul_le_right (((a₁ : ↑Γ(X, ⊤))) * f i)
              (((a₁ : ↑Γ(X, ⊤))) * f j)))) := by
  classical
  choose pre hpre_mem hpre_eq using hpreS
  have hmulmem : ∀ {x y : FixedPoints.subring ↑Γ(X, ⊤) G}, x ∉ p → y ∉ p → x * y ∉ p :=
    fun hx hy => p.primeCompl.mul_mem hx hy
  -- ### the per-chart `VariableChange`-spread multipliers (level-independent)
  have hDsp : ∀ i, ∃ s : S', ∀ {g : ↑Γ(X, ⊤)}, g ∈ S' →
      ∀ (B : Type u) [CommRing B] [Algebra ↑Γ(X, ⊤) B]
        [IsLocalization.Away (g * f i) B]
        (ψ : B →+* Localization
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))),
        (∀ a : ↑Γ(X, ⊤), ψ (algebraMap ↑Γ(X, ⊤) B a)
          = algebraMap (Localization S')
              (Localization
                (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
              (algebraMap ↑Γ(X, ⊤) (Localization S') a)) →
        IsUnit (algebraMap ↑Γ(X, ⊤) B ((s : ↑Γ(X, ⊤)))) →
        ∃ DB : VariableChange B, DB.map ψ = D i :=
    fun i => exists_variableChange_sections_preimage S' (f i) (D i)
  choose sVC hsVC using hDsp
  -- ### fraction data for the five coefficients of `W₀L` and the `Δ`-witness
  obtain ⟨b₁, b₂, b₃, b₄, b₆, bΔ, s₁, s₂, s₃, s₄, s₆, sΔ, v,
    hb₁, hb₂, hb₃, hb₄, hb₆, hv, hbΔ⟩ := spread_fractions S' W₀L hΔ
  -- ### the preliminary invariant level `a₀`, introduced OPAQUELY via the `⟨_, rfl⟩`
  -- existential (never `set`, whose `kabstract` over the huge `hglue`/`hcobInv`/clearing
  -- hypotheses is what breaks the 200k budget — see the heartbeat-split note above).
  obtain ⟨sPre, hsPre⟩ :
      ∃ s : S', s = ((((((s₁ * s₂) * s₃) * s₄) * s₆) * sΔ) * ∏ i, sVC i) := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀def⟩ :
      ∃ a : FixedPoints.subring ↑Γ(X, ⊤) G, a = k₀ * pre sPre := ⟨_, rfl⟩
  have ha₀ : a₀ ∉ p := by rw [ha₀def]; exact hmulmem hk₀ (hpre_mem sPre)
  have ha₀S : ((a₀ : ↑Γ(X, ⊤))) ∈ S' := hmemS a₀ ha₀
  have hpre_dvd_a₀ : ((pre sPre : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := by
    rw [ha₀def]; push_cast; exact dvd_mul_left _ _
  have hsPre_dvd : ((sPre : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := by
    rw [← hpre_eq sPre]; exact hpre_dvd_a₀
  -- coefficient-denominator divisibilities into `a₀` (via the submonoid inclusion)
  have hdvdS : ∀ t : S', t ∣ ((((((s₁ * s₂) * s₃) * s₄) * s₆) * sΔ) * ∏ i, sVC i) →
      ((t : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := fun t ht =>
    dvd_trans (map_dvd S'.subtype ht) (hsPre ▸ hsPre_dvd)
  have hdvd₁ : ((s₁ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₁
    ((((((dvd_mul_right s₁ s₂).mul_right s₃).mul_right s₄).mul_right s₆).mul_right
      sΔ).mul_right _)
  have hdvd₂ : ((s₂ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₂
    ((((((dvd_mul_left s₂ s₁).mul_right s₃).mul_right s₄).mul_right s₆).mul_right
      sΔ).mul_right _)
  have hdvd₃ : ((s₃ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₃
    (((((dvd_mul_left s₃ (s₁ * s₂)).mul_right s₄).mul_right s₆).mul_right sΔ).mul_right _)
  have hdvd₄ : ((s₄ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₄
    ((((dvd_mul_left s₄ ((s₁ * s₂) * s₃)).mul_right s₆).mul_right sΔ).mul_right _)
  have hdvd₆ : ((s₆ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₆
    (((dvd_mul_left s₆ (((s₁ * s₂) * s₃) * s₄)).mul_right sΔ).mul_right _)
  have hdvdΔ : ((sΔ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS sΔ
    ((dvd_mul_left sΔ ((((s₁ * s₂) * s₃) * s₄) * s₆)).mul_right _)
  have hdvdVC : ∀ i, ((sVC i : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := fun i => hdvdS (sVC i)
    ((Finset.dvd_prod_of_mem sVC (Finset.mem_univ i)).mul_left _)
  have hk₀dvda₀ : k₀ ∣ a₀ := ⟨pre sPre, ha₀def⟩
  clear hsPre_dvd hpre_dvd_a₀ hdvdS
  -- ### (β2 build) the model curve `W₀R₀ / A_{a₀}` realizing `W₀L`'s coefficients + `Δ`-inv
  obtain ⟨W₀R₀, vR₀, cΔ, hW₀R₀, hcΔ⟩ := spread_build_curve G S' W₀L a₀ ha₀S
    b₁ b₂ b₃ b₄ b₆ bΔ s₁ s₂ s₃ s₄ s₆ sΔ v hb₁ hb₂ hb₃ hb₄ hb₆ hv hbΔ
    hdvd₁ hdvd₂ hdvd₃ hdvd₄ hdvd₆ hdvdΔ
  -- the `A_{a₀·fᵢ}`-unit of `a₀·fᵢ` and the per-chart correction `DA₀ i` over `D(a₀·fᵢ)`
  have hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))) := by
    intro i
    rw [map_mul, map_mul]
    exact ((IsLocalization.map_units (Localization S')
        (⟨(a₀ : ↑Γ(X, ⊤)), ha₀S⟩ : S')).map
        (algebraMap (Localization S') _)).mul (isUnit_algebraMap_powers_self _)
  have hDA₀ : ∀ i, ∃ DB : VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)),
      DB.map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i := by
    intro i
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)
    refine hsVC i ha₀S _ (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i) a) ?_
    exact isUnit_algebraMap_of_isLocalizationAway_dvd _ ((a₀ : ↑Γ(X, ⊤)) * f i)
      ((hdvdVC i).trans (dvd_mul_right _ _))
  choose DA₀ hDA₀eq using hDA₀
  -- ### (β2 clear) per-chart glue and pairwise transVC identities hold after one `S'`-mult
  have hglue₀ := spread_glue_clear G S' f P D W₀L a₀ ha₀S W₀R₀ hW₀R₀ DA₀ hψunit hDA₀eq hglue
  choose sGlue hsG1 hsG2 hsG3 hsG4 hsG6 using hglue₀
  have hWij : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) ≤ X.basicOpen (f i * f j) :=
    fun i j => basicOpen_le_basicOpen_of_dvd (dvd_mul_left (f i * f j) (a₀ : ↑Γ(X, ⊤)))
  have hleAi : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i) :=
    fun i j => basicOpen_le_basicOpen_of_dvd ⟨f j, by ring⟩
  have hleAj : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j) :=
    fun i j => basicOpen_le_basicOpen_of_dvd ⟨f i, by ring⟩
  have htriv₀ := spread_transVC_clear G S' f P D a₀ ha₀S DA₀ hψunit hDA₀eq hU hcobInv
    hWij hleAi hleAj
  choose cT hcTu hcTr hcTs hcTt using htriv₀
  -- ### (β assembly) fold every clearing multiplier into a single invariant `a₁ ∉ p`
  -- (`cAll`/`a₁` also introduced opaquely — same `kabstract`-avoidance as `sPre`/`a₀`)
  obtain ⟨cAll, hcAlldef⟩ :
      ∃ c : S', c = (cΔ * ∏ i, sGlue i) * ∏ q : ι × ι, cT q.1 q.2 := ⟨_, rfl⟩
  have hcΔdvd : (cΔ : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) := by
    rw [hcAlldef]; exact map_dvd S'.subtype ((dvd_mul_right cΔ _).mul_right _)
  have hsGdvd : ∀ i, (sGlue i : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) := by
    intro i; rw [hcAlldef]
    exact map_dvd S'.subtype
      (((Finset.dvd_prod_of_mem sGlue (Finset.mem_univ i)).mul_left cΔ).mul_right _)
  have hcTdvd : ∀ i j, (cT i j : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) := by
    intro i j; rw [hcAlldef]
    exact map_dvd S'.subtype
      ((Finset.dvd_prod_of_mem (fun q : ι × ι => cT q.1 q.2) (Finset.mem_univ (i, j))).mul_left _)
  obtain ⟨a₁, ha₁def⟩ :
      ∃ a : FixedPoints.subring ↑Γ(X, ⊤) G, a = a₀ * pre cAll := ⟨_, rfl⟩
  have ha₁ : a₁ ∉ p := by rw [ha₁def]; exact hmulmem ha₀ (hpre_mem cAll)
  have ha₁coe : (a₁ : ↑Γ(X, ⊤)) = (a₀ : ↑Γ(X, ⊤)) * (pre cAll : ↑Γ(X, ⊤)) := by
    rw [ha₁def]; push_cast; ring
  have hcAllcoe : (pre cAll : ↑Γ(X, ⊤)) = (cAll : ↑Γ(X, ⊤)) := hpre_eq cAll
  have ha₀dvda₁ : (a₀ : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)) := ⟨(pre cAll : ↑Γ(X, ⊤)), ha₁coe⟩
  have hcAlldvda₁ : (cAll : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)) :=
    ⟨(a₀ : ↑Γ(X, ⊤)), by rw [ha₁coe, hcAllcoe]; ring⟩
  have hk₀dvda₁ : k₀ ∣ a₁ := by rw [ha₁def]; exact hk₀dvda₀.trans ⟨pre cAll, rfl⟩
  have hDAle : ∀ i, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i) ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i) :=
    fun i => basicOpen_le_basicOpen_of_dvd ⟨(pre cAll : ↑Γ(X, ⊤)), by rw [ha₁coe]; ring⟩
  refine ⟨a₁, ha₁, W₀R₀.map (awayMapDvd ha₀dvda₁),
    fun i => (DA₀ i).map (Scheme.resLE (hDAle i)), ?_, ?_, ?_, ?_⟩
  · exact spread_assemble_ell G S' a₀ a₁ W₀R₀ vR₀ cΔ cAll hcΔ hcΔdvd ha₀dvda₁ hcAlldvda₁
  · exact hspanA a₁ hk₀dvda₁
  · intro i
    exact spread_assemble_glue G S' f P a₀ a₁ W₀R₀ DA₀ hDAle ha₀dvda₁ cAll sGlue hsGdvd
      hcAlldvda₁ hsG1 hsG2 hsG3 hsG4 hsG6 i
  · intro i j
    exact spread_assemble_transVC G S' f P a₀ DA₀ a₁ hDAle cAll (pre cAll : ↑Γ(X, ⊤))
      ha₁coe hcAlldvda₁ cT hWij hleAi hleAj hcTdvd hcTu hcTr hcTs hcTt i j

/-- **(Stage 3c-γ barrier — the corrected-cochain conjugate collapses)** In any
variable-change group, `a * (a⁻¹ * b) * b⁻¹ = 1`; used to collapse the corrected chart
transition `transVC (Qᵢ|, Qⱼ|) = DAᵢ| * (DAᵢ|⁻¹ * DAⱼ|) * DAⱼ|⁻¹` to `1`.  Stated at a
variable ring so the concrete `Γ(X, D(a₁·fᵢ))` cochains are never unfolded. -/
private theorem vc_conj_cancel {R : Type*} [CommRing R]
    (a b : WeierstrassCurve.VariableChange R) : a * (a⁻¹ * b) * b⁻¹ = 1 := by
  group

section NativeGlueAssembly
open CategoryTheory.Limits

/-- Range of the base-change piece. -/
lemma gluePieceRange [IsAffine X] (a g : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a)) :
    Set.range ⇑(projModelBaseChange (awayToSections a g) W) =
      Set.range ⇑(projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  haveI hoi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayToSections a g))) :=
    isOpenImmersion_specMap_awayToSections a g
  haveI hoi2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) ↑Γ(X, X.basicOpen (a * g))))) := hoi1
  haveI : IsOpenImmersion (projModelBaseChange (awayToSections a g) W) :=
    isOpenImmersion_projModelBaseChange W
  have hpb := isPullback_projModelBaseChange (R := Localization.Away a)
    (R' := ↑Γ(X, X.basicOpen (a * g))) W
  have hsurj : Function.Surjective ⇑(hpb.isoPullback.hom) :=
    (Scheme.homeoOfIso hpb.isoPullback).surjective
  rw [Scheme.Opens.range_ι]
  show Set.range ⇑(projModelBaseChange (awayToSections a g) W) = _
  rw [show (projModelBaseChange (awayToSections a g) W)
        = hpb.isoPullback.hom ≫ pullback.fst (projModelπ W)
            (Spec.map (CommRingCat.ofHom (awayToSections a g)))
      from hpb.isoPullback_hom_fst.symm]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ,
    Scheme.Pullback.range_fst]
  rw [show Set.range ⇑(Spec.map (CommRingCat.ofHom (awayToSections a g)))
      = ↑(specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)) from by
    rw [← opensRange_specMap_awayToSections a g]; rfl]
  rfl

/-- The `i`-th native-glue piece `Uᵢ ⟶ C.E`. -/
noncomputable def gluePiece [IsAffine X] (a g : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a))
    (Q : LocalPresentation C ⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩)
    (hQW : Q.W = W.map (awayToSections a g)) :
    (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).toScheme ⟶ C.E :=
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) ↑Γ(X, X.basicOpen (a * g))))) :=
    isOpenImmersion_specMap_awayToSections a g
  haveI : IsOpenImmersion (projModelBaseChange (awayToSections a g) W) :=
    isOpenImmersion_projModelBaseChange W
  (IsOpenImmersion.isoOfRangeEq (projModelBaseChange (awayToSections a g) W)
      (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι
      (gluePieceRange a g W)).inv ≫
    eqToHom (congrArg projModel hQW).symm ≫ Q.e.inv ≫
      pullback.fst C.π
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι

/-- Range of `Spec.map (awayToSections a g)` equals that of the basic-open inclusion. -/
lemma specMap_awayToSections_range [IsAffine X] (a g : ↑Γ(X, ⊤)) :
    Set.range ⇑(Spec.map (CommRingCat.ofHom (awayToSections a g))) =
      Set.range ⇑(specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι := by
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, opensRange_specMap_awayToSections]


/-- **(γ4 per-piece)** Over `U'ᵢ = D(fᵢ')` the model restriction is the base change of `C.E`. -/
lemma gluePiece_isPullback [IsAffine X] (a g : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a))
    (Q : LocalPresentation C ⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩)
    (hQW : Q.W = W.map (awayToSections a g)) :
    IsPullback
      (projModelπ W ∣_ specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g))
      (gluePiece a g W Q hQW)
      ((specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))))
      (C.π ≫ X.isoSpec.hom) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  haveI hoi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayToSections a g))) :=
    isOpenImmersion_specMap_awayToSections a g
  haveI hoi2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) ↑Γ(X, X.basicOpen (a * g))))) := hoi1
  haveI : IsOpenImmersion (projModelBaseChange (awayToSections a g) W) :=
    isOpenImmersion_projModelBaseChange W
  -- the chart square
  have S_chart : IsPullback (Q.e.inv ≫ pullback.fst C.π
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι)
      (projModelπ Q.W) C.π
      ((⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
          X.affineOpens).2.isoSpec.inv ≫
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι) := by
    refine (IsPullback.of_hasPullback C.π
      (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι).of_iso
      Q.e (Iso.refl _) (⟨X.basicOpen (a * g),
        (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · exact Q.compat_π.symm
    · simp
    · simp
  -- the two iso comparisons
  have hSbc : IsPullback (projModelBaseChange (awayToSections a g) W)
      (projModelπ (W.map (awayToSections a g))) (projModelπ W)
      (Spec.map (CommRingCat.ofHom (awayToSections a g))) :=
    isPullback_projModelBaseChange (R := Localization.Away a)
      (R' := ↑Γ(X, X.basicOpen (a * g))) W
  set ζ := IsOpenImmersion.isoOfRangeEq (projModelBaseChange (awayToSections a g) W)
    (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (gluePieceRange a g W) with hζ
  set κ := ζ.symm ≪≫ eqToIso (congrArg projModel hQW).symm with hκ
  set ξ := IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (awayToSections a g)))
    (specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (specMap_awayToSections_range a g) with hξ
  -- the top square `s`: iso on two edges
  have hs_w : (projModelπ W ∣_ specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)) ≫ ξ.inv = κ.hom ≫ projModelπ Q.W := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (awayToSections a g))), Category.assoc,
      Category.assoc, hξ,
      IsOpenImmersion.isoOfRangeEq_inv_fac (Spec.map (CommRingCat.ofHom (awayToSections a g)))
        (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (specMap_awayToSections_range a g),
      morphismRestrict_ι, hκ]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    have hpc : eqToHom (congrArg projModel hQW).symm ≫ projModelπ Q.W =
        projModelπ (W.map (awayToSections a g)) := LocalPresentation.projModelπ_congr hQW.symm
    rw [reassoc_of% hpc, ← hSbc.w, ← Category.assoc, hζ,
      IsOpenImmersion.isoOfRangeEq_inv_fac]
  have s : IsPullback (projModelπ W ∣_ specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)) κ.hom ξ.inv (projModelπ Q.W) :=
    IsPullback.of_vert_isIso ⟨hs_w⟩
  -- paste `s` with `S_chart.flip`
  have hpaste := s.paste_vert S_chart.flip
  -- identify the resulting maps
  have hFi : κ.hom ≫ Q.e.inv ≫ pullback.fst C.π
      (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι
      = gluePiece a g W Q hQW := by
    rw [hκ, hζ, gluePiece]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  -- the restriction `Γ(X,⊤) → Γ(X, D(a·g))` factors as `awayToSections ∘ algebraMap`
  have hrestr : Spec.map (X.presheaf.map
        (homOfLE (le_top : X.basicOpen (a * g) ≤ ⊤)).op) =
      Spec.map (CommRingCat.ofHom (awayToSections a g)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine CommRingCat.hom_ext ?_
    refine RingHom.ext fun x => ?_
    rw [CommRingCat.hom_ofHom, RingHom.comp_apply, awayToSections_algebraMap]
    rfl
  have hbot : ξ.inv ≫ (⟨X.basicOpen (a * g),
        (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.inv ≫
      (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι =
      (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a)))
        ≫ X.isoSpec.inv := by
    have hmid : (⟨X.basicOpen (a * g),
          (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.inv ≫
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι ≫
          X.isoSpec.hom =
        Spec.map (X.presheaf.map (homOfLE (le_top : X.basicOpen (a * g) ≤ ⊤)).op) := by
      rw [show X.isoSpec.hom = X.toSpecΓ from rfl,
        ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, ← Category.assoc,
        show (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩
            : X.affineOpens).2.isoSpec.inv ≫ (X.basicOpen (a * g)).toSpecΓ = 𝟙 _ from by
          rw [show (X.basicOpen (a * g)).toSpecΓ = (⟨X.basicOpen (a * g),
              (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.hom from rfl,
            Iso.inv_hom_id],
        Category.id_comp]
    rw [← cancel_mono X.isoSpec.hom, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, hmid, hrestr, ← Category.assoc, hξ,
      IsOpenImmersion.isoOfRangeEq_inv_fac]
  -- transport the pasted square through `isoSpec` on the bottom-right corner
  rw [hFi] at hpaste
  refine hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) X.isoSpec ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.id_comp, hbot, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp


/-- **(zero-leg per-piece)** The point at infinity of the model over `Uᵢ` is `C.zero`. -/
lemma gluePiece_zero [IsAffine X] (a g : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a))
    (Q : LocalPresentation C ⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩)
    (hQW : Q.W = W.map (awayToSections a g)) :
    ∃ z : (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).toScheme ⟶
        (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).toScheme,
      z ≫ (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι =
        (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι ≫ projModelZero W ∧
      z ≫ gluePiece a g W Q hQW =
        (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) ≫
            X.isoSpec.inv ≫ C.zero := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen (a * g)) :=
    (awayToSections a g).toAlgebra
  haveI hoi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayToSections a g))) :=
    isOpenImmersion_specMap_awayToSections a g
  haveI hoi2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) ↑Γ(X, X.basicOpen (a * g))))) := hoi1
  haveI : IsOpenImmersion (projModelBaseChange (awayToSections a g) W) :=
    isOpenImmersion_projModelBaseChange W
  set ζ := IsOpenImmersion.isoOfRangeEq (projModelBaseChange (awayToSections a g) W)
    (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (gluePieceRange a g W) with hζ
  set ξ := IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (awayToSections a g)))
    (specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (specMap_awayToSections_range a g) with hξ
  -- bottom-edge identity (as in `gluePiece_isPullback`)
  have hrestr : Spec.map (X.presheaf.map
        (homOfLE (le_top : X.basicOpen (a * g) ≤ ⊤)).op) =
      Spec.map (CommRingCat.ofHom (awayToSections a g)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rw [CommRingCat.hom_ofHom, RingHom.comp_apply, awayToSections_algebraMap]
    rfl
  have hbot : ξ.inv ≫ (⟨X.basicOpen (a * g),
        (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.inv ≫
      (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι =
      (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a)))
        ≫ X.isoSpec.inv := by
    have hmid : (⟨X.basicOpen (a * g),
          (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.inv ≫
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι ≫
          X.isoSpec.hom =
        Spec.map (X.presheaf.map (homOfLE (le_top : X.basicOpen (a * g) ≤ ⊤)).op) := by
      rw [show X.isoSpec.hom = X.toSpecΓ from rfl,
        ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, ← Category.assoc,
        show (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩
            : X.affineOpens).2.isoSpec.inv ≫ (X.basicOpen (a * g)).toSpecΓ = 𝟙 _ from by
          rw [show (X.basicOpen (a * g)).toSpecΓ = (⟨X.basicOpen (a * g),
              (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).2.isoSpec.hom from rfl,
            Iso.inv_hom_id],
        Category.id_comp]
    rw [← cancel_mono X.isoSpec.hom, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, hmid, hrestr, ← Category.assoc, hξ,
      IsOpenImmersion.isoOfRangeEq_inv_fac]
  -- the zero point over the piece
  refine ⟨ξ.inv ≫ projModelZero (W.map (awayToSections a g)) ≫ ζ.hom, ?_, ?_⟩
  · -- lifts the model zero section
    have hzbc : projModelZero (W.map (awayToSections a g)) ≫
          projModelBaseChange (awayToSections a g) W =
        Spec.map (CommRingCat.ofHom (awayToSections a g)) ≫ projModelZero W :=
      projModelZero_baseChange (R' := ↑Γ(X, X.basicOpen (a * g))) W
    rw [Category.assoc, Category.assoc, hζ, IsOpenImmersion.isoOfRangeEq_hom_fac, hzbc,
      ← Category.assoc, hξ, IsOpenImmersion.isoOfRangeEq_inv_fac]
  · -- realises `C.zero` through the chart
    rw [gluePiece]
    have hZ1 : projModelZero Q.W ≫ Q.e.inv ≫ pullback.fst C.π
          (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι =
        (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
            X.affineOpens).2.isoSpec.inv ≫
          (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι ≫
            C.zero := by
      rw [← Q.compat_zero, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
        pullback.lift_fst]
    have hZzero : projModelZero (W.map (awayToSections a g)) ≫
          eqToHom (congrArg projModel hQW).symm = projModelZero Q.W := by
      rw [LocalPresentation.projModelZero_congr hQW]
    calc (ξ.inv ≫ projModelZero (W.map (awayToSections a g)) ≫ ζ.hom) ≫
            (IsOpenImmersion.isoOfRangeEq (projModelBaseChange (awayToSections a g) W)
              (projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
                (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g)).ι (gluePieceRange a g W)).inv ≫
            eqToHom (congrArg projModel hQW).symm ≫ Q.e.inv ≫ pullback.fst C.π
              (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ : X.affineOpens).1.ι
        = ξ.inv ≫ projModelZero (W.map (awayToSections a g)) ≫
            eqToHom (congrArg projModel hQW).symm ≫ Q.e.inv ≫ pullback.fst C.π
              (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
                X.affineOpens).1.ι := by
          rw [← hζ]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = ξ.inv ≫ projModelZero Q.W ≫ Q.e.inv ≫ pullback.fst C.π
              (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
                X.affineOpens).1.ι := by rw [← Category.assoc _ (eqToHom _), hZzero]
      _ = ξ.inv ≫ (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
              X.affineOpens).2.isoSpec.inv ≫
            (⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩ :
                X.affineOpens).1.ι ≫ C.zero := by rw [hZ1]
      _ = _ := by rw [reassoc_of% hbot]

/-! ### γ3 agreement infrastructure (banked — the reversed-template toolkit for `hagree`)

These are the reusable pieces the γ3 native-glue agreement (`hagree`, inside `nativeGlue`) is
built from — the reversed analogues of `chartPiece_restrict` / `chartPiece_index_congr`
(`Moduli/UniversalAdapted.lean`) together with the overlap base-change range.  All AXIOM-CLEAN.
* `chart_baseChange_fst` — the `‡` identity: over `V' ≤ V` the base-changed big-chart projection
  IS the restricted-chart projection (`restrict_e_baseChange` + `restrictTheta_fst`).
* `gluePiece_chart_congr` — reversed index congruence: two charts over the same affine with
  `transVC = 1` give the same `gluePiece` (via `pointedIso_hom_of_transVC_eq_one_loc`).
* `overlapMap` / `overlapMap_range` / `overlapRange` — the composite localization map
  `A[1/a] → Γ(X, D((a·g₁)(a·g₂)))` and the identification of the base-change range with the
  overlap `Uₖ ⊓ Uₗ` (localization tower + `localization_away_comap_range`; the `a`-unit cancels the
  `a²`-vs-`a` discrepancy between `D(a²·g₁g₂)` and `D(a·g₁g₂)`). -/

open LocalPresentation in
/-- Local reproof of `pointedIso_hom_of_transVC_eq_one` (which lives in `Moduli/AdaptedModel.lean`,
not imported here): presentations with trivial comparison have `eqToHom` as their pointed iso. -/
private theorem pointedIso_hom_of_transVC_eq_one_loc {V : X.affineOpens}
    {P Q : LocalPresentation C V} (h : P.transVC Q = 1) :
    (P.pointedIso Q).hom =
      eqToHom (show projModel P.W = projModel Q.W by
        rw [show Q.W = P.W from by
          have := P.transVC_smul Q; rwa [h, one_smul] at this]) := by
  have congr_vc : ∀ {D₁ D₂ : VariableChange ↑Γ(X, V.1)} (hh : D₁ = D₂),
      (projModelVCIso D₁ Q.W).hom
        = eqToHom (congrArg (fun t => projModel (t • Q.W)) hh)
          ≫ (projModelVCIso D₂ Q.W).hom := by
    intro D₁ D₂ hh; subst hh; rw [eqToHom_refl, Category.id_comp]
  rw [P.transVC_spec Q, congr_vc h, projModelVCIso_one, eqToHom_trans, eqToHom_trans]

open Scheme LocalPresentation in
/-- **(reversed `chartPiece_restrict`, the `‡` identity)** Over a smaller affine `V' ≤ V`, the
base change of `Q.W` post-composed with the big chart projection equals the restricted chart
projection. -/
lemma chart_baseChange_fst {V : X.affineOpens} (Q : LocalPresentation C V)
    {V' : X.affineOpens} (h : V'.1 ≤ V.1) :
    projModelBaseChange (sectionsMapLE (𝟙 X) h) Q.W ≫ Q.e.inv ≫ pullback.fst C.π V.1.ι
      = (Q.restrict h).e.inv ≫ pullback.fst C.π V'.1.ι := by
  have goal2 : (Q.restrict h).e.hom ≫ projModelBaseChange (sectionsMapLE (𝟙 X) h) Q.W
        ≫ Q.e.inv ≫ pullback.fst C.π V.1.ι
      = (Q.restrict h).e.hom ≫ (Q.restrict h).e.inv ≫ pullback.fst C.π V'.1.ι := by
    rw [Iso.hom_inv_id_assoc, reassoc_of% (LocalPresentation.restrict_e_baseChange Q h),
      Iso.hom_inv_id_assoc, restrictTheta_fst]
  exact (cancel_epi (Q.restrict h).e.hom).mp goal2

open Scheme LocalPresentation in
/-- **(reversed `chartPiece_index_congr`)** Two presentations of `C` over the same away-affine,
both with chart curve `W₀.map (awayToSections a g)` and trivial comparison, give the same
native-glue piece. -/
lemma gluePiece_chart_congr [IsAffine X] (a g : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a))
    (Q Q' : LocalPresentation C ⟨X.basicOpen (a * g), (isAffineOpen_top X).basicOpen (a * g)⟩)
    (hQW : Q.W = W.map (awayToSections a g)) (hQW' : Q'.W = W.map (awayToSections a g))
    (hVC : Q.transVC Q' = 1) :
    gluePiece a g W Q hQW = gluePiece a g W Q' hQW' := by
  rw [gluePiece, gluePiece]
  have hIso := pointedIso_hom_of_transVC_eq_one_loc hVC
  rw [show (Q.pointedIso Q').hom = Q.e.inv ≫ Q'.e.hom from rfl] at hIso
  have key : eqToHom (congrArg projModel hQW).symm ≫ Q.e.inv
      = eqToHom (congrArg projModel hQW').symm ≫ Q'.e.inv := by
    calc eqToHom (congrArg projModel hQW).symm ≫ Q.e.inv
        = eqToHom (congrArg projModel hQW).symm ≫ (Q.e.inv ≫ Q'.e.hom) ≫ Q'.e.inv := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = eqToHom (congrArg projModel hQW).symm ≫ eqToHom (by rw [hQW, hQW']) ≫ Q'.e.inv := by
          rw [hIso]
      _ = eqToHom (congrArg projModel hQW').symm ≫ Q'.e.inv := by
          rw [← Category.assoc, eqToHom_trans]
  rw [reassoc_of% key]

/-- The composite localization map `A[1/a] → Γ(X, D((a·g₁)·(a·g₂)))` — restriction of
`awayToSections a g₁` to the common away-affine. -/
noncomputable def overlapMap [IsAffine X] (a g₁ g₂ : ↑Γ(X, ⊤)) :
    Localization.Away a →+* ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
  (Scheme.resLE (basicOpen_mul_le_left (a * g₁) (a * g₂))).comp (awayToSections a g₁)

/-- `Spec.map (overlapMap …)` is an open immersion: `Γ(X, D((a·g₁)(a·g₂)))` is `A[1/a]` localized
away from the image of `a·g₁·g₂` (localization tower). -/
instance isOpenImmersion_specMap_overlapMap [IsAffine X] (a g₁ g₂ : ↑Γ(X, ⊤)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (overlapMap a g₁ g₂))) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    (overlapMap a g₁ g₂).toAlgebra
  letI : IsScalarTower ↑Γ(X, ⊤) (Localization.Away a)
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap _ _ x = overlapMap a g₁ g₂ (algebraMap _ _ x)
      rw [overlapMap, RingHom.comp_apply, awayToSections_algebraMap, resLE_algebraMap])
  haveI hbo : IsLocalization.Away ((a * g₁) * (a * g₂))
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    (isAffineOpen_top X).isLocalization_basicOpen ((a * g₁) * (a * g₂))
  haveI : IsLocalization.Away (a * (a * g₁ * g₂))
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) := by
    rw [show a * (a * g₁ * g₂) = (a * g₁) * (a * g₂) from by ring]; exact hbo
  haveI := isLocalizationAway_of_tower (A := ↑Γ(X, ⊤)) (R₁ := Localization.Away a)
    (Γ := ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))) a (a * g₁ * g₂)
  exact IsOpenImmersion.of_isLocalization (R := Localization.Away a)
    (S := ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))))
    (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (a * g₁ * g₂))

/-- The range of `Spec.map (overlapMap …)` is `D(g₁') ⊓ D(g₂')` in `Spec A[1/a]` — the `a`-power
inside `a·g₁·g₂` is a unit, so `D(a·g₁·g₂) = D(g₁') ⊓ D(g₂')`. -/
theorem overlapMap_range [IsAffine X] (a g₁ g₂ : ↑Γ(X, ⊤)) :
    Set.range ⇑(Spec.map (CommRingCat.ofHom (overlapMap a g₁ g₂)))
      = ↑(specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₁) ⊓
          specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₂)) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    (overlapMap a g₁ g₂).toAlgebra
  letI : IsScalarTower ↑Γ(X, ⊤) (Localization.Away a)
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap _ _ x = overlapMap a g₁ g₂ (algebraMap _ _ x)
      rw [overlapMap, RingHom.comp_apply, awayToSections_algebraMap, resLE_algebraMap])
  haveI hbo : IsLocalization.Away ((a * g₁) * (a * g₂))
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    (isAffineOpen_top X).isLocalization_basicOpen ((a * g₁) * (a * g₂))
  haveI : IsLocalization.Away (a * (a * g₁ * g₂))
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) := by
    rw [show a * (a * g₁ * g₂) = (a * g₁) * (a * g₂) from by ring]; exact hbo
  haveI := isLocalizationAway_of_tower (A := ↑Γ(X, ⊤)) (R₁ := Localization.Away a)
    (Γ := ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))) a (a * g₁ * g₂)
  have hopen : PrimeSpectrum.basicOpen (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (a * g₁ * g₂))
      = specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₁) ⊓
        specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₂) := by
    have hunit : PrimeSpectrum.basicOpen (algebraMap ↑Γ(X, ⊤) (Localization.Away a) a) = ⊤ := by
      obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a
      have h1 : PrimeSpectrum.basicOpen
          ((u : Localization.Away a) * (↑u⁻¹ : Localization.Away a)) = ⊤ := by
        rw [Units.mul_inv, PrimeSpectrum.basicOpen_one]
      rw [PrimeSpectrum.basicOpen_mul, hu] at h1
      exact top_le_iff.mp (h1 ▸ inf_le_left)
    rw [map_mul, map_mul, PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_mul, hunit,
      top_inf_eq]; rfl
  rw [← hopen]
  show Set.range ⇑(Spec.map (CommRingCat.ofHom (overlapMap a g₁ g₂))) = _
  exact PrimeSpectrum.localization_away_comap_range
    ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))
    (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (a * g₁ * g₂))

/-- **(the overlap range)** The base-change model map over `overlapMap` has range exactly the
overlap `Uₖ ⊓ Uₗ = projModelπ ⁻¹ᵁ (D(g₁') ⊓ D(g₂'))` of the two native-glue domains. -/
theorem overlapRange [IsAffine X] (a g₁ g₂ : ↑Γ(X, ⊤))
    (W : WeierstrassCurve (Localization.Away a)) :
    Set.range ⇑(projModelBaseChange (overlapMap a g₁ g₂) W)
      = Set.range ⇑((projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₁) ⊓
          projModelπ W ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₂)).ι) := by
  letI : Algebra (Localization.Away a) ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂))) :=
    (overlapMap a g₁ g₂).toAlgebra
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))))) :=
    isOpenImmersion_specMap_overlapMap a g₁ g₂
  haveI : IsOpenImmersion (projModelBaseChange (algebraMap (Localization.Away a)
      ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))) W) :=
    isOpenImmersion_projModelBaseChange W
  have hpb := isPullback_projModelBaseChange (R := Localization.Away a)
    (R' := ↑Γ(X, X.basicOpen ((a * g₁) * (a * g₂)))) W
  have hsurj : Function.Surjective ⇑(hpb.isoPullback.hom) :=
    (Scheme.homeoOfIso hpb.isoPullback).surjective
  rw [Scheme.Opens.range_ι]
  show Set.range ⇑(projModelBaseChange (overlapMap a g₁ g₂) W) = _
  rw [show (projModelBaseChange (overlapMap a g₁ g₂) W)
        = hpb.isoPullback.hom ≫ pullback.fst (projModelπ W)
            (Spec.map (CommRingCat.ofHom (overlapMap a g₁ g₂)))
      from hpb.isoPullback_hom_fst.symm]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]
  rw [show Set.range ⇑(Spec.map (CommRingCat.ofHom (overlapMap a g₁ g₂)))
      = ↑(specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₁) ⊓
          specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) g₂))
      from overlapMap_range a g₁ g₂]
  rfl

/-- The native glue over `D(a)` (γ3 + γ4). -/
theorem nativeGlue [IsAffine X] (a : ↑Γ(X, ⊤)) {ι : Type u}
    (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (W₀R₁ : WeierstrassCurve (Localization.Away a))
    (DA : ∀ i, VariableChange ↑Γ(X, X.basicOpen (a * f i)))
    (hQW : ∀ i, (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
          (isAffineOpen_top X).basicOpen (a * f i)⟩)
        (basicOpen_mul_le_right a (f i))).ofVC (DA i)).W
        = W₀R₁.map (awayToSections a (f i)))
    (hspan₁ : Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)) = ⊤)
    (hVC1 : ∀ i j,
        ((((P i).restrict (V' := ⟨X.basicOpen (a * f i),
              (isAffineOpen_top X).basicOpen (a * f i)⟩)
            (basicOpen_mul_le_right a (f i))).ofVC (DA i)).restrict
            (V' := ⟨X.basicOpen ((a * f i) * (a * f j)),
              (isAffineOpen_top X).basicOpen _⟩)
            (basicOpen_mul_le_left (a * f i) (a * f j))).transVC
          ((((P j).restrict (V' := ⟨X.basicOpen (a * f j),
              (isAffineOpen_top X).basicOpen (a * f j)⟩)
            (basicOpen_mul_le_right a (f j))).ofVC (DA j)).restrict
            (V' := ⟨X.basicOpen ((a * f i) * (a * f j)),
              (isAffineOpen_top X).basicOpen _⟩)
            (basicOpen_mul_le_right (a * f i) (a * f j))) = 1) :
    ∃ ρR₁ : projModel W₀R₁ ⟶ C.E,
      IsPullback (projModelπ W₀R₁) ρR₁
        (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))))
        (C.π ≫ X.isoSpec.hom) ∧
      projModelZero W₀R₁ ≫ ρR₁
        = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a)))
          ≫ X.isoSpec.inv ≫ C.zero := by
  classical
  -- the cover of `projModel W₀R₁` by preimages of the basic opens `D(fᵢ')`
  set U : ι → (projModel W₀R₁).Opens := fun i =>
    projModelπ W₀R₁ ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
      (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)) with hUdef
  -- the pieces
  set F : ∀ i, (U i).toScheme ⟶ C.E := fun i =>
    gluePiece a (f i) W₀R₁
      (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
          (isAffineOpen_top X).basicOpen (a * f i)⟩)
        (basicOpen_mul_le_right a (f i))).ofVC (DA i)) (hQW i) with hFdef
  -- γ3 cover: `⨆ᵢ Uᵢ = ⊤`
  have hcov3 : ⨆ i, U i = ⊤ := by
    have hspanTop : ⨆ i, specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan₁
    exact (projModelπ W₀R₁).iSup_preimage_eq_top hspanTop
  -- ### γ3 AGREEMENT — THE SINGLE REMAINING FRONTIER (the genuine descent glue).
  -- Everything else of the KM 4.7.0 mouth core is now AXIOM-CLEAN: the five barrier lemmas
  -- (`gluePieceRange`, `gluePiece`, `specMap_awayToSections_range`, `gluePiece_isPullback`,
  -- `gluePiece_zero`), the cover `hcov3`, `ρR₁` (built below), the per-piece `hpiece`, the γ4
  -- pullback square, and the zero-leg are ALL proved sorry-free.  What remains is exactly the
  -- pairwise agreement of the native-glue pieces on the overlaps `Uₖ ⊓ Uₗ`:  the two corrected
  -- charts `Q k`, `Q l` restrict to the common affine `D((a·fₖ)·(a·fₗ))` where their comparison
  -- variable change is trivial (`hVC1 k l : … .transVC … = 1`), so the two chart maps into `C.E`
  -- coincide there.  Formally: feed `hVC1 k l` through `pointedIso_hom_of_transVC_eq_one`
  -- (`Moduli/AdaptedModel.lean`) to identify the restricted chart isos, and connect `F k`/`F l`
  -- to those restricted charts by `restrict_e_baseChange` + `restrictTheta_fst`
  -- (`EllipticCurve/InvariantDifferential.lean`), transporting across the base-change comparison
  -- over the overlap (`projModelBaseChange_comp'`).  Mirror `chartPiece_index_congr` +
  -- `chartPiece_restrict` (`Moduli/UniversalAdapted.lean`), reversed (proj-model → E).
  -- NOTE the one friction point: `hVC1`'s overlap is `D(a²·fₖfₗ)` whereas the away-charts live
  -- over `D(a·fₖfₗ)` — the SAME open, different terms (transport with an `eqToHom`/`≤`-restrict).
  --
  -- BANKED TOOLKIT (all AXIOM-CLEAN, above `nativeGlue`): the reversed template is now assembled —
  -- `pointedIso_hom_of_transVC_eq_one_loc` (B0, a local reproof since AdaptedModel isn't imported),
  -- `chart_baseChange_fst` (B1 = the `‡` identity), `gluePiece_chart_congr` (B2 = reversed index
  -- congruence), and the overlap range `overlapMap` / `overlapMap_range` / `overlapRange` (the
  -- localization-tower identification `range(projModelBaseChange (overlapMap a fₖ fₗ) W) = Uₖ ⊓ Uₗ`,
  -- with the `a`-unit collapsing the `a²`-vs-`a` friction).  REMAINING (a `reduceSide` per-side
  -- lemma, developed + green in scratch but split-blocked): with the shared iso
  -- `ζτ := isoOfRangeEq (projModelBaseChange (overlapMap a fₖ fₗ) W₀R₁) (Uₖ⊓Uₗ).ι overlapRange`,
  --   (∗∗)  `homOfLE hincl ≫ ζ_g.inv = ζτ.inv ≫ projModelBaseChange (sectionsMapLE hgV) (W.map σ_g)`
  --         (cancel the mono `projModelBaseChange σ_g W`; both sides `≫ it = (Uₖ⊓Uₗ).ι`, using
  --         `projModelBaseChange_comp'` + `(sectionsMapLE hgV).comp σ_g = overlapMap` [`rfl` on the
  --         `fₖ`-side, `IsLocalization.ringHom_ext` on the `fₗ`-side]);
  --   then `gluePiece`-unfold + (∗∗) + `projModelBaseChange_congr''` + B1 reduces each side to
  --         `ζτ.inv ≫ eqToHom qᵢ ≫ (Qᵢ.restrict hᵢ).e.inv ≫ pullback.fst C.π V.ι`;
  --   finish: `cancel_epi ζτ.inv`, then `pointedIso_hom_of_transVC_eq_one_loc (hVC1 k l)` gives
  --         `(Qₖ.restrict hk).e.inv ≫ fst = eqToHom hW ≫ (Qₗ.restrict hl).e.inv ≫ fst`, and
  --         `eqToHom_trans` (proof-irrelevance) closes.  The `reduceSide` proof over-runs the 200k
  --         heartbeat ceiling on the concrete chart/base-change terms; it needs splitting (opaque
  --         `set` of `(∗∗)`, the `projModelBaseChange_congr''` step, and the B1 step into separate
  --         barrier lemmas) — no `maxHeartbeats` bump.
  have hagree : ∀ k l, (projModel W₀R₁).homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ F k =
      (projModel W₀R₁).homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ F l := by
    sorry
  -- the glued native model map
  set ρR₁ : projModel W₀R₁ ⟶ C.E :=
    (projModel W₀R₁).topIso.inv ≫ (projModel W₀R₁).homOfLE hcov3.ge ≫
      (Scheme.Opens.iSupOpenCover U).glueMorphisms F
        (glueMorphisms_hf_of_agree U F hagree) with hρdef
  -- per-piece: `Uᵢ.ι ≫ ρR₁ = Fᵢ`
  have hpiece : ∀ i, (U i).ι ≫ ρR₁ = F i := by
    intro i
    have hstep : (U i).ι ≫ (projModel W₀R₁).topIso.inv ≫
        (projModel W₀R₁).homOfLE hcov3.ge = (projModel W₀R₁).homOfLE (le_iSup U i) := by
      rw [← cancel_mono (⨆ i, U i).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.toIso_inv_ι, Category.comp_id, Scheme.homOfLE_ι]
    rw [hρdef, reassoc_of% hstep]
    exact (Scheme.Opens.iSupOpenCover U).ι_glueMorphisms F _ i
  -- the `Uᵢ` cover `projModel W₀R₁` (for hom-extensionality)
  have hcov_pt : ∀ x : ↥(projModel W₀R₁), ∃ i, x ∈ (U i).1 := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (hcov3 ▸ (show x ∈ (⊤ : (projModel W₀R₁).Opens) from
      trivial))
  set cover : (projModel W₀R₁).OpenCover :=
    Scheme.Cover.mkOfCovers ι (fun i => (U i).toScheme) (fun i => (U i).ι)
      (fun x => by obtain ⟨i, hi⟩ := hcov_pt x; exact ⟨i, ⟨x, hi⟩, rfl⟩) with hcover
  refine ⟨ρR₁, ?_, ?_⟩
  · -- γ4 square, via `isPullback_of_iSup_eq_top` on the basic-open cover of `Spec A[1/a]`
    refine isPullback_of_iSup_eq_top ?_
      (fun i => specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)))
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan₁) (fun i => ?_)
    · -- the square commutes (checked on the `Uᵢ` cover)
      refine cover.hom_ext _ _ (fun i => ?_)
      have keyw : (U i).ι ≫ projModelπ W₀R₁ ≫
            Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) =
          (U i).ι ≫ ρR₁ ≫ C.π ≫ X.isoSpec.hom := by
        have hw := (gluePiece_isPullback a (f i) W₀R₁
          (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
              (isAffineOpen_top X).basicOpen (a * f i)⟩)
            (basicOpen_mul_le_right a (f i))).ofVC (DA i)) (hQW i)).w
        rw [← Category.assoc,
          morphismRestrict_ι (projModelπ W₀R₁)
            (specBasicOpen (CommRingCat.of (Localization.Away a))
              (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i)))] at hw
        rw [show (U i).ι ≫ ρR₁ ≫ C.π ≫ X.isoSpec.hom = F i ≫ C.π ≫ X.isoSpec.hom from by
            rw [← Category.assoc, hpiece i], ← Category.assoc]
        exact hw
      rw [show cover.f i = (U i).ι from rfl]
      exact keyw
    · -- the per-piece square is `gluePiece_isPullback` (snd leg rewritten via `hpiece`)
      rw [show (projModelπ W₀R₁ ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι ≫ ρR₁ = F i from hpiece i]
      exact gluePiece_isPullback a (f i) W₀R₁
        (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
            (isAffineOpen_top X).basicOpen (a * f i)⟩)
          (basicOpen_mul_le_right a (f i))).ofVC (DA i)) (hQW i)
  · -- zero-leg, via the basic-open cover of `Spec A[1/a]` + `gluePiece_zero`
    have hcov_pt' : ∀ x : ↥(Spec (CommRingCat.of (Localization.Away a))),
        ∃ i, x ∈ (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).1 := fun x =>
      TopologicalSpace.Opens.mem_iSup.mp
        ((PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan₁) ▸
          (show x ∈ (⊤ : (Spec (CommRingCat.of (Localization.Away a))).Opens) from trivial))
    refine (Scheme.Cover.mkOfCovers ι
      (fun i => (specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).toScheme)
      (fun i => (specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι)
      (fun x => by obtain ⟨i, hi⟩ := hcov_pt' x; exact ⟨i, ⟨x, hi⟩, rfl⟩)).hom_ext _ _ (fun i => ?_)
    obtain ⟨z, hz1, hz2⟩ := gluePiece_zero a (f i) W₀R₁
      (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
          (isAffineOpen_top X).basicOpen (a * f i)⟩)
        (basicOpen_mul_le_right a (f i))).ofVC (DA i)) (hQW i)
    have keyz : (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι ≫ projModelZero W₀R₁ ≫ ρR₁ =
        (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away a))) ≫
            X.isoSpec.inv ≫ C.zero := by
      have hpi : (projModelπ W₀R₁ ⁻¹ᵁ specBasicOpen (CommRingCat.of (Localization.Away a))
            (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι ≫ ρR₁ =
          gluePiece a (f i) W₀R₁
            (((P i).restrict (V' := ⟨X.basicOpen (a * f i),
                (isAffineOpen_top X).basicOpen (a * f i)⟩)
              (basicOpen_mul_le_right a (f i))).ofVC (DA i)) (hQW i) := hpiece i
      rw [← Category.assoc, ← hz1, Category.assoc, hpi, hz2]
    rw [show (Scheme.Cover.mkOfCovers ι
        (fun i => (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).toScheme)
        (fun i => (specBasicOpen (CommRingCat.of (Localization.Away a))
          (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι)
        (fun x => by obtain ⟨i, hi⟩ := hcov_pt' x; exact ⟨i, ⟨x, hi⟩, rfl⟩)).f i =
      (specBasicOpen (CommRingCat.of (Localization.Away a))
        (algebraMap ↑Γ(X, ⊤) (Localization.Away a) (f i))).ι from rfl]
    exact keyz

end NativeGlueAssembly

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
  -- ### Stage 3c-β (invariant-denominator spread) — CLOSED, AXIOM-CLEAN, via the mouth-core
  -- theorem `exists_invariant_chart_spread` (the β2 clearing calculus + β-assembly, all
  -- decomposed into the `spread_*` helpers above).  It consumes the whole α-package and the
  -- spread span witness, delivering the invariant level `a₁ ∉ p`, an elliptic model
  -- `W₀R₁ / A[1/a₁]`, per-chart corrections `DA i` over `Γ(X, D(a₁·fᵢ))`, the span over
  -- `A[1/a₁]`, the per-chart glue `DA i • (P i).W| = W₀R₁ ⊗ Γ(X, D(a₁·fᵢ))`, and the
  -- corrected chart coboundary `transVC ((P i)|, (P j)|) = (DA i|)⁻¹ * (DA j|)`.
  have hmemS : ∀ k : FixedPoints.subring ↑Γ(X, ⊤) G, k ∉ p → ((k : ↑Γ(X, ⊤))) ∈ S :=
    fun k hk => Submonoid.mem_map.mpr ⟨k, hk, rfl⟩
  obtain ⟨a₁, ha₁, W₀R₁, DA, hΔ₁, hspan₁, hglue₁, hcob₁⟩ :=
    exists_invariant_chart_spread G S p hpre hmemS f P k₀ hk₀ hspanA hU D W₀L hΔ hglue hcobInv
  refine ⟨a₁, ha₁, W₀R₁, ⟨hΔ₁⟩, ?_⟩
  -- ### Stage 3c-γ (THE NATIVE GLUE over `D(a₁)`).  γ1 (corrected charts + transVC = 1) and
  -- γ2 (the cover) are proved GREEN below; the residual `sorry` is exactly γ3+γ4.
  -- (γ1) corrected charts `Q i := ((P i).restrict (D(a₁·fᵢ) ≤ D(fᵢ))).ofVC (DA i)` over
  --      `D(a₁·fᵢ)`, with `(Q i).W = W₀R₁.map (awayToSections a₁ fᵢ)` (`hQW`).
  have hQW : ∀ i, (((P i).restrict (V' := ⟨X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i),
        (isAffineOpen_top X).basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)⟩)
      (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i))).ofVC (DA i)).W
      = W₀R₁.map (awayToSections (a₁ : ↑Γ(X, ⊤)) (f i)) := fun i => by
    rw [LocalPresentation.ofVC_W,
      restrict_W_eq (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i)) (P i)]
    exact hglue₁ i
  -- (γ2) the cover `D(a₁) ≤ ⋃ᵢ D(a₁·fᵢ)` (`basicOpen_le_iSup_basicOpen_mul` + `hspan₁`).
  have hcover : X.basicOpen (a₁ : ↑Γ(X, ⊤)) ≤ ⨆ i, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i) :=
    basicOpen_le_iSup_basicOpen_mul (a₁ : ↑Γ(X, ⊤)) f hspan₁
  -- (γ1) the pairwise transition-triviality `transVC (Qᵢ|, Qⱼ|) = 1`
  --      (`transVC_ofVC_restrict_pair` + `transVC_restrict_restrict_left/right` + `hcob₁`);
  --      note the two charts restrict to DIFFERENT opens `D(a₁·fᵢ)`/`D(a₁·fⱼ)`, so the
  --      asymmetric `_left`/`_right` restriction laws are required (not the symmetric one).
  have hVC1 : ∀ i j,
      ((((P i).restrict (V' := ⟨X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i),
            (isAffineOpen_top X).basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)⟩)
          (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i))).ofVC (DA i)).restrict
          (V' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
            (isAffineOpen_top X).basicOpen _⟩)
          (basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))).transVC
        ((((P j).restrict (V' := ⟨X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f j),
            (isAffineOpen_top X).basicOpen ((a₁ : ↑Γ(X, ⊤)) * f j)⟩)
          (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f j))).ofVC (DA j)).restrict
          (V' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
            (isAffineOpen_top X).basicOpen _⟩)
          (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))) = 1 :=
    fun i j => by
    have key := transVC_ofVC_restrict_pair
      ((P i).restrict (V' := ⟨X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i),
          (isAffineOpen_top X).basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)⟩)
        (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f i)))
      ((P j).restrict (V' := ⟨X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f j),
          (isAffineOpen_top X).basicOpen ((a₁ : ↑Γ(X, ⊤)) * f j)⟩)
        (basicOpen_mul_le_right (a₁ : ↑Γ(X, ⊤)) (f j)))
      (DA i) (DA j)
      (V' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
          (isAffineOpen_top X).basicOpen _⟩)
      (basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))
      (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i) ((a₁ : ↑Γ(X, ⊤)) * f j))
    rw [LocalPresentation.transVC_restrict_restrict_left,
      LocalPresentation.transVC_restrict_restrict_right, hcob₁ i j] at key
    rw [key]
    simp only [LocalPresentation.sectionsMapLE_id]
    exact vc_conj_cancel _ _
  -- ### Stage 3c-γ RESIDUAL (γ3 + γ4 only).  γ1 (`hQW`, `hVC1`) and γ2 (`hcover`/`hspan₁`) are
  -- green, and THE localization barrier the prior session flagged as "the one missing lemma" is
  -- now DISCHARGED, axiom-clean, above (banked, reusable):
  --   • `isLocalizationAway_of_tower` (KEY, ForMathlib): `A[1/(a·g)]` IS `A[1/a]` localized at
  --     the image `g'` of `g` — so `Γ(X, D(a₁·fᵢ)) = A[1/a₁]`-away-at-`fᵢ'` via `awayToSections`.
  --   • `isOpenImmersion_specMap_awayToSections` : `Spec.map (awayToSections a₁ fᵢ)` is an OPEN
  --     IMMERSION (via `IsOpenImmersion.of_isLocalization` at the tower localization).
  --   • `opensRange_specMap_awayToSections` : its range is `specBasicOpen (Away a₁) fᵢ'` (via
  --     `PrimeSpectrum.localization_away_comap_range`).
  --   • `isOpenImmersion_projModelBaseChange` (instance) : `bcᵢ := projModelBaseChange
  --     (awayToSections a₁ fᵢ) W₀R₁` is an OPEN IMMERSION (OI is stable under base change).  Its
  --     range `bcᵢ.opensRange = Uᵢ := projModelπ W₀R₁ ⁻¹ᵁ specBasicOpen (Away a₁) fᵢ'` is derived
  --     inline at the `Set`-level from `isPullback_projModelBaseChange` + `Scheme.Pullback.range_fst`
  --     (see the NOTE above `awayToLocalization` — a standalone `.opensRange` lemma hits a motive snag).
  -- Note: `isOpenImmersion_specMap_awayToSections` and `isOpenImmersion_projModelBaseChange` are
  -- `instance`s, so `(Spec.map (awayToSections a₁ fᵢ)).opensRange` and `bcᵢ.opensRange` elaborate;
  -- set `letI : Algebra (Away a₁) Γ(X, D(a₁·fᵢ)) := (awayToSections a₁ (f i)).toAlgebra` so
  -- `projModelBaseChange (awayToSections a₁ fᵢ) W₀R₁` matches `isPullback_projModelBaseChange`.
  --
  -- REMAINING (pure scheme-gluing, mechanical, mirrors `negHomOf`/`mulModelHom`):
  --   γ3 cover:  `⨆ᵢ Uᵢ = ⊤` from `iSup_basicOpen_eq_top_iff.mpr hspan₁` (rewriting each
  --     `opensRange` by `opensRange_specMap_awayToSections`) + `Scheme.Hom.iSup_preimage_eq_top`.
  --   γ3 pieces:  `Fᵢ := (IsOpenImmersion.isoOfRangeEq bcᵢ (Uᵢ).ι …).inv ≫
  --     eqToHom (congrArg projModel (hQW i)).symm ≫ (Q i).e.inv ≫ pullback.fst C.π (D(a₁·fᵢ)).ι`.
  --   γ3 agreement (the true remaining math): pairwise on `Uₓ ⊓ Uᵧ` from `hVC1` via
  --     `pointedIso_hom_of_transVC_eq_one` + `restrict_e_baseChange`, fed to
  --     `glueMorphisms_hf_of_agree`; then
  --     `ρR₁ := (topIso).inv ≫ (Scheme.Opens.iSupOpenCover U).glueMorphisms F …`.
  --   γ4: `isPullback_of_iSup_eq_top` on `{specBasicOpen (Away a₁) fᵢ'}` (cover of Spec A[1/a₁]),
  --     per-piece from `(Q i).compat_π` pasted on `isPullback_projModelBaseChange`; zero-leg from
  --     `(Q i).compat_zero` + `projModelZero_baseChange`, both checked on the cover per piece.
  -- γ1/γ2 are the `hQW`/`hVC1`/`hspan₁` in scope; γ3+γ4 are assembled by `nativeGlue`
  -- (ρR₁ built, γ4 pullback square + zero-leg PROVEN; residual `sorry` = the γ3 native-glue
  -- agreement `hagree`, the descent glue from `hVC1` inside `nativeGlue`).
  exact nativeGlue (C := C) ((a₁ : ↑Γ(X, ⊤))) f P W₀R₁ DA hQW hspan₁ hVC1

end MouthCharts

end ModularCurves

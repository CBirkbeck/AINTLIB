/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q3.
-/
import ModularCurves.ForMathlib.SpecGroupAction
import ModularCurves.ForMathlib.InvariantLocalization

/-!
# The affine quotient by a finite group action: universal property

For a finite group `G` acting on a commutative ring `B` (over a base `R`), the
invariants morphism `invariantsπ : Spec B ⟶ Spec Bᴳ` is the **categorical quotient**
of `Spec B` by `G` in the category of schemes:

* `existsUnique_factor_fixedPoints_away` — the algebra engine: a ring hom into `B_a`
  (`a` an invariant) with `G`-fixed image factors uniquely through `(Bᴳ)_a`.
* `invariantsπ_hom_ext_of_isOpenImmersion` — uniqueness of descent, in a form stable
  under restriction: two morphisms out of an open `W ⊆ Spec Bᴳ` agreeing after
  precomposition with (the pullback of) `invariantsπ` are equal. `W = Spec Bᴳ`
  (`j = 𝟙`) is `invariantsπ_hom_ext`.
* `exists_invariantsπ_lift` — existence of descent: every `G`-invariant morphism
  `Spec B ⟶ Y` factors through `invariantsπ`.
* `existsUnique_invariantsπ_lift` — the universal property ([Loeffler, *Modular
  curves*, Prop 3.6.1], affine case: "for X = Spec(A) affine, Spec(A^G) works").

The proof is the standard one (SGA I V.1.1; Stacks 07S5/07S7): `invariantsπ` is
integral, surjective, with fibres the `G`-orbits (`SpecGroupAction.lean`); an
invariant morphism `f : Spec B ⟶ Y` is descended affine-locally on the target —
around each `p : Spec Bᴳ` one finds an invariant basic open `D(a) ∋ p` with
`π ⁻¹(D(a)) ⊆ f ⁻¹(V)` for an affine chart `V ∋ f(π⁻¹ p)` (integrality makes `π`
closed), and there the factorization is the algebra statement "invariants of the
localization = localization of the invariants" (`InvariantLocalization.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {G : Type*} [Group G]
variable {B : Type u} [CommRing B] [MulSemiringAction G B]
variable (R : Type u) [CommRing R] [Algebra R B] [SMulCommClass G R B]

section Algebra

variable [Finite G]

/-- **Factorization through the localized invariants** (the algebra engine of the
affine quotient): a ring hom `φ : C →+* B_a`, `a` an invariant, whose image is fixed
by the localized `G`-action factors uniquely through the localized inclusion
`(Bᴳ)_a →+* B_a`. -/
theorem existsUnique_factor_fixedPoints_away {C : Type u} [CommRing C]
    (a : FixedPoints.subalgebra R B G)
    (φ : C →+* Localization.Away ((a : B)))
    (hφ : ∀ (g : G) (c : C), MulSemiringAction.awayHom (fun g => a.2 g) g (φ c) = φ c) :
    ∃! ψ : C →+* Localization.Away a,
      (IsLocalization.map (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a)).comp ψ = φ := by
  set inclMap : Localization.Away a →+* Localization.Away ((a : B)) :=
    IsLocalization.map (Localization.Away ((a : B)))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R a) with hinclMap
  have hinj : Function.Injective inclMap := fixedPoints_awayMap_injective R a
  have hrange : ∀ c : C, φ c ∈ inclMap.range := by
    intro c
    rw [RingHom.mem_range]
    obtain ⟨y, hy⟩ := (mem_range_fixedPoints_awayMap_iff R a (φ c)).mpr
      (fun g => hφ g c)
    exact ⟨y, hy⟩
  have hinv : Function.LeftInverse (Function.invFun inclMap) inclMap :=
    Function.leftInverse_invFun hinj
  set e := RingEquiv.ofLeftInverse hinv with he
  have hfac : ∀ c : C,
      inclMap (e.symm.toRingHom.comp (φ.codRestrict inclMap.range hrange) c) = φ c := by
    intro c
    show inclMap (e.symm (φ.codRestrict inclMap.range hrange c)) = φ c
    rw [he, RingEquiv.ofLeftInverse_symm_apply]
    exact Function.invFun_eq (RingHom.mem_range.mp (hrange c))
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict inclMap.range hrange), ?_, ?_⟩
  · ext c
    exact hfac c
  · intro ψ' hψ'
    ext c
    refine hinj ?_
    have h2 : inclMap (ψ' c) = φ c := by
      rw [← RingHom.comp_apply, hψ']
    rw [h2, hfac c]

end Algebra

section UniversalProperty

variable (G B) in
/-- Uniqueness of descent along the invariants morphism, in restriction-stable form:
for an open immersion `j : W ⟶ Spec Bᴳ`, two morphisms out of `W` agreeing after
precomposition with the pullback of `invariantsπ` along `j` are equal.

(`invariantsπ` is surjective with `Γ`-injectivity on basic opens — it is an effective
epimorphism; this is the epimorphism half, in the generality needed to glue local
descents at overlaps.) -/
theorem invariantsπ_hom_ext_of_isOpenImmersion [Finite G] {W Y : Scheme.{u}}
    (j : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j] (h₁ h₂ : W ⟶ Y)
    (H : pullback.snd (invariantsπ G B R) j ≫ h₁ =
      pullback.snd (invariantsπ G B R) j ≫ h₂) :
    h₁ = h₂ := by
  -- `pullback.snd π j` is surjective (`Surjective` is stable under base change),
  -- so `h₁` and `h₂` agree on points.
  have hπ : Surjective (invariantsπ G B R) := ⟨invariantsπ_surjective G B R⟩
  have hsnd : Surjective (pullback.snd (invariantsπ G B R) j) :=
    MorphismProperty.pullback_snd _ _ hπ
  have hbase : ∀ w : W, h₁ w = h₂ w := by
    intro w
    obtain ⟨z, hz⟩ := hsnd.surj w
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H]
  -- Around every point of `W` there is an open chart on which `h₁` and `h₂` agree.
  have key : ∀ w : W, ∃ (Z : Scheme.{u}) (ℓ : Z ⟶ W),
      IsOpenImmersion ℓ ∧ (∃ z, ℓ z = w) ∧ ℓ ≫ h₁ = ℓ ≫ h₂ := by
    intro w
    -- an affine chart `ι` of `Y` around `h₁ w`
    obtain ⟨i₀, y₀, hy₀⟩ := Y.affineCover.exists_eq (h₁ w)
    set ι := Y.affineCover.f i₀ with hι
    -- `T`: the locus where `h₁` (equivalently `h₂`) lands in the chart
    set T : Set W := h₁.base ⁻¹' Set.range ι with hT
    have hTopen : IsOpen T := ι.isOpenEmbedding.isOpen_range.preimage h₁.continuous
    have hwT : w ∈ T := ⟨y₀, hy₀⟩
    -- push into `Spec Bᴳ` along `j` and find an invariant basic open inside
    have hOopen : IsOpen (j.base '' T) := j.isOpenEmbedding.isOpenMap _ hTopen
    obtain ⟨s, ⟨a, rfl⟩, hjws, hsO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (⟨w, hwT, rfl⟩ : j w ∈ j.base '' T) hOopen
    -- the localization chart over `D(a)` and its lift `ℓ` to `W`
    set κ : Spec (CommRingCat.of (Localization.Away a)) ⟶
        Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a))) with hκ
    have hκrange : Set.range ⇑κ = (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G))) :=
      PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    have hκj : Set.range ⇑κ ⊆ Set.range ⇑j := by
      rw [hκrange]
      exact hsO.trans (Set.image_subset_range _ _)
    set ℓ := IsOpenImmersion.lift j κ hκj with hℓ
    have hℓj : ℓ ≫ j = κ := IsOpenImmersion.lift_fac j κ hκj
    have hℓimm : IsOpenImmersion ℓ := by
      have : IsOpenImmersion (ℓ ≫ j) := hℓj ▸ inferInstance
      exact IsOpenImmersion.of_comp ℓ j
    -- the range of `ℓ` lies in `T` and contains `w`
    have hrangeT : ∀ v, ℓ v ∈ T := by
      intro v
      have h5 : j (ℓ v) ∈ j.base '' T := by
        refine hsO ?_
        show j (ℓ v) ∈ (↑(PrimeSpectrum.basicOpen a) :
          Set (PrimeSpectrum (FixedPoints.subalgebra R B G)))
        rw [← hκrange]
        exact ⟨v, by rw [← hℓj, Scheme.Hom.comp_apply]⟩
      obtain ⟨t, htT, ht⟩ := h5
      rwa [← j.isOpenEmbedding.injective ht]
    have hwℓ : ∃ z, ℓ z = w := by
      have h6 : j w ∈ Set.range ⇑κ := by
        rw [hκrange]
        exact hjws
      obtain ⟨v, hv⟩ := h6
      refine ⟨v, j.isOpenEmbedding.injective ?_⟩
      rw [← hℓj, Scheme.Hom.comp_apply] at hv
      exact hv
    -- lift `ℓ ≫ hᵢ` into the affine chart
    have hrange₁ : Set.range ⇑(ℓ ≫ h₁) ⊆ Set.range ⇑ι := by
      rintro _ ⟨v, rfl⟩
      exact hrangeT v
    have hrange₂ : Set.range ⇑(ℓ ≫ h₂) ⊆ Set.range ⇑ι := by
      rintro _ ⟨v, rfl⟩
      have h7 : (ℓ ≫ h₂) v = h₁ (ℓ v) := by
        rw [Scheme.Hom.comp_apply, hbase (ℓ v)]
      rw [Scheme.Hom.comp_apply] at h7 ⊢
      rw [h7]
      exact hrangeT v
    set t₁ := IsOpenImmersion.lift ι (ℓ ≫ h₁) hrange₁ with ht₁def
    set t₂ := IsOpenImmersion.lift ι (ℓ ≫ h₂) hrange₂ with ht₂def
    have ht₁ : t₁ ≫ ι = ℓ ≫ h₁ := IsOpenImmersion.lift_fac ι (ℓ ≫ h₁) hrange₁
    have ht₂ : t₂ ≫ ι = ℓ ≫ h₂ := IsOpenImmersion.lift_fac ι (ℓ ≫ h₂) hrange₂
    -- the B-side chart and the comparison map into the pullback
    set κB : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
        Spec (CommRingCat.of B) :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away ((a : B))))) with hκB
    set πa : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
        Spec (CommRingCat.of (Localization.Away a)) :=
      Spec.map (CommRingCat.ofHom (IsLocalization.map
        (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a))) with hπa
    have hsquare : κB ≫ invariantsπ G B R = πa ≫ κ := by
      rw [hκB, hπa, hκ, invariantsπ, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact (IsLocalization.map_comp _).symm
    set ρ := pullback.lift κB (πa ≫ ℓ)
      (by rw [hsquare, Category.assoc, hℓj]) with hρ
    have hρsnd : ρ ≫ pullback.snd (invariantsπ G B R) j = πa ≫ ℓ :=
      pullback.lift_snd _ _ _
    -- the localized invariants morphism coequalizes `h₁, h₂` after `ℓ`
    have hπaℓ : πa ≫ ℓ ≫ h₁ = πa ≫ ℓ ≫ h₂ := by
      rw [← Category.assoc, ← hρsnd, Category.assoc, H, ← Category.assoc, hρsnd,
        Category.assoc]
    have hπat : πa ≫ t₁ = πa ≫ t₂ := by
      rw [← cancel_mono ι, Category.assoc, Category.assoc, ht₁, ht₂]
      exact hπaℓ
    -- cancel `πa` on `Γ`-level: the localized inclusion is injective
    have ht : t₁ = t₂ := by
      rw [← cancel_mono (Y.affineCover.X i₀).isoSpec.hom]
      obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (t₁ ≫ (Y.affineCover.X i₀).isoSpec.hom)
      obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective (t₂ ≫ (Y.affineCover.X i₀).isoSpec.hom)
      rw [← hφ₁, ← hφ₂]
      congr 1
      have h8 : πa ≫ Spec.map φ₁ = πa ≫ Spec.map φ₂ := by
        rw [hφ₁, hφ₂, ← Category.assoc, ← Category.assoc, hπat]
      rw [hπa, ← Spec.map_comp, ← Spec.map_comp] at h8
      have h9 := Spec.map_injective h8
      ext c
      have h10 := congrArg (fun ψ => ψ.hom c) h9
      exact fixedPoints_awayMap_injective R a h10
    refine ⟨_, ℓ, hℓimm, hwℓ, ?_⟩
    rw [← ht₁, ← ht₂, ht]
  -- glue: the charts form an open cover of `W`
  choose Z ℓ himm hcov heq using key
  have := himm
  exact Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers W Z ℓ
      (fun x => ⟨x, (hcov x).choose, (hcov x).choose_spec⟩)
      (fun w => himm w))
    h₁ h₂ heq

variable (G B) in
/-- Uniqueness of descent along the invariants morphism: `invariantsπ` is an
epimorphism of schemes. -/
theorem invariantsπ_hom_ext [Finite G] {Y : Scheme.{u}}
    (h₁ h₂ : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y)
    (H : invariantsπ G B R ≫ h₁ = invariantsπ G B R ≫ h₂) :
    h₁ = h₂ := by
  refine invariantsπ_hom_ext_of_isOpenImmersion G B R (𝟙 _) h₁ h₂ ?_
  have hc := pullback.condition (f := invariantsπ G B R)
    (g := 𝟙 (Spec (CommRingCat.of (FixedPoints.subalgebra R B G))))
  rw [Category.comp_id] at hc
  rw [← hc, Category.assoc, Category.assoc, H]

/-- The basic-open chart of `Spec Bᴳ` at an invariant `a`. -/
private noncomputable def chartA (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away a)) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a)))

/-- The basic-open chart of `Spec B` at (the image of) an invariant `a`. -/
private noncomputable def chartB (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away ((a : B)))))

/-- The localized invariants morphism over the chart at `a`. -/
private noncomputable def chartπ (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
      Spec (CommRingCat.of (Localization.Away a)) :=
  Spec.map (CommRingCat.ofHom (IsLocalization.map
    (Localization.Away ((a : B)))
    (algebraMap (FixedPoints.subalgebra R B G) B)
    (Submonoid.powers_le_comap_algebraMap R a)))

private theorem chartπ_def (a : FixedPoints.subalgebra R B G) :
    chartπ R a = Spec.map (CommRingCat.ofHom (IsLocalization.map
      (Localization.Away ((a : B)))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R a))) := rfl

private theorem chartA_def (a : FixedPoints.subalgebra R B G) :
    chartA R a = Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a))) := rfl

private theorem chartB_def (a : FixedPoints.subalgebra R B G) :
    chartB R a = Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away ((a : B))))) := rfl

private instance (a : FixedPoints.subalgebra R B G) : IsOpenImmersion (chartA R a) :=
  inferInstanceAs (IsOpenImmersion (Spec.map _))

private instance (a : FixedPoints.subalgebra R B G) : IsOpenImmersion (chartB R a) :=
  inferInstanceAs (IsOpenImmersion (Spec.map _))

private theorem chartA_opensRange (a : FixedPoints.subalgebra R B G) :
    (chartA R a).opensRange = PrimeSpectrum.basicOpen a :=
  Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (FixedPoints.subalgebra R B G)) a

private theorem chartB_opensRange (a : FixedPoints.subalgebra R B G) :
    (chartB R a).opensRange = PrimeSpectrum.basicOpen ((a : B)) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) ((a : B))

variable (G B) in
private theorem chart_square (a : FixedPoints.subalgebra R B G) :
    chartB R a ≫ invariantsπ G B R = chartπ R a ≫ chartA R a := by
  rw [chartB_def, chartπ_def, chartA_def, invariantsπ, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (IsLocalization.map_comp _).symm

variable (G B) in
/-- The chart square is cartesian: `D(a) ×_{Spec Bᴳ} Spec B = D((a : B))`. -/
private theorem isPullback_chart (a : FixedPoints.subalgebra R B G) :
    IsPullback (chartπ R a) (chartB R a) (chartA R a) (invariantsπ G B R) := by
  refine IsOpenImmersion.isPullback (chartπ R a) (chartB R a) (chartA R a)
    (invariantsπ G B R) (chart_square G B R a) ?_
  rw [chartA_opensRange, chartB_opensRange]
  exact TopologicalSpace.Opens.ext rfl

variable (G B) in
/-- One leg of the gluing compatibility: over any morphism `j'` into `Spec Bᴳ` that
factors through the chart at an invariant `r`, a local descent `qr` of `f` pulls back
to `pullback.fst π j' ≫ f`. -/
private theorem chart_descent_side [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y)
    {P : Scheme.{u}} (j' : P ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (r : FixedPoints.subalgebra R B G)
    (qr : Spec (CommRingCat.of (Localization.Away r)) ⟶ Y)
    (hqr : chartπ R r ≫ qr = chartB R r ≫ f)
    (pr : P ⟶ Spec (CommRingCat.of (Localization.Away r)))
    (hpr : pr ≫ chartA R r = j') :
    pullback.snd (invariantsπ G B R) j' ≫ (pr ≫ qr) =
      pullback.fst (invariantsπ G B R) j' ≫ f := by
  have hcone : (pullback.snd (invariantsπ G B R) j' ≫ pr) ≫ chartA R r =
      pullback.fst (invariantsπ G B R) j' ≫ invariantsπ G B R := by
    rw [Category.assoc, hpr]
    exact pullback.condition.symm
  have hu₁ := (isPullback_chart G B R r).lift_fst
    (pullback.snd (invariantsπ G B R) j' ≫ pr)
    (pullback.fst (invariantsπ G B R) j') hcone
  have hu₂ := (isPullback_chart G B R r).lift_snd
    (pullback.snd (invariantsπ G B R) j' ≫ pr)
    (pullback.fst (invariantsπ G B R) j') hcone
  rw [← Category.assoc, ← hu₁, Category.assoc, hqr, ← Category.assoc, hu₂]

variable (G B) in
/-- Around every point of `Spec Bᴳ` there is an invariant basic open over which a
`G`-invariant morphism out of `Spec B` descends. -/
private theorem exists_chart_descent [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f)
    (p : Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) :
    ∃ a : FixedPoints.subalgebra R B G,
      p ∈ PrimeSpectrum.basicOpen a ∧
      ∃ qa : Spec (CommRingCat.of (Localization.Away a)) ⟶ Y,
        chartπ R a ≫ qa = chartB R a ≫ f := by
  -- `f` is constant on the fibres of `invariantsπ` (they are orbits)
  have hconst : ∀ x y : Spec (CommRingCat.of B),
      invariantsπ G B R x = invariantsπ G B R y → f x = f y := by
    intro x y hxy
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G B R x y).mp hxy
    rw [← hg, ← Scheme.Hom.comp_apply, hf g]
  -- `invariantsπ` is a closed map (it is integral)
  have hclosed : IsClosedMap ⇑(invariantsπ G B R) := by
    have hint : (algebraMap (FixedPoints.subalgebra R B G) B).IsIntegral :=
      Algebra.isIntegral_def.mp
        (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)
    exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint
  -- a point of the fibre and an affine chart of `Y` around its image
  obtain ⟨x, hx⟩ := invariantsπ_surjective G B R p
  obtain ⟨i₀, y₀, hy₀⟩ := Y.affineCover.exists_eq (f x)
  set ι := Y.affineCover.f i₀ with hι
  -- the saturated open `U` and the separating invariant basic open
  set U : Set (Spec (CommRingCat.of B)) := f.base ⁻¹' Set.range ι with hU
  have hUopen : IsOpen U := ι.isOpenEmbedding.isOpen_range.preimage f.continuous
  have hfibU : ∀ x', invariantsπ G B R x' = p → x' ∈ U := by
    intro x' hx'
    have h4 : f x' = f x := hconst x' x (by rw [hx', hx])
    show f x' ∈ Set.range ⇑ι
    rw [h4]
    exact ⟨y₀, hy₀⟩
  have hpZ : p ∉ (invariantsπ G B R).base '' Uᶜ := by
    rintro ⟨x', hx'U, hx'⟩
    exact hx'U (hfibU x' hx')
  have hZclosed : IsClosed ((invariantsπ G B R).base '' Uᶜ) :=
    hclosed _ hUopen.isClosed_compl
  obtain ⟨s, ⟨a, rfl⟩, hps, hsZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ ((invariantsπ G B R).base '' Uᶜ)ᶜ from hpZ) hZclosed.isOpen_compl
  refine ⟨a, hps, ?_⟩
  -- the `B`-side chart lands in `U`
  have hchartU : ∀ v, chartB R a v ∈ U := by
    intro v
    by_contra hvU
    have hmemA : ∀ z, chartA R a z ∈ PrimeSpectrum.basicOpen a := by
      intro z
      have h9 : chartA R a z ∈ Set.range ⇑(chartA R a) := ⟨z, rfl⟩
      exact chartA_opensRange R a ▸ h9
    refine hsZ ?_ ⟨chartB R a v, hvU, rfl⟩
    show invariantsπ G B R (chartB R a v) ∈
      (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G)))
    rw [← Scheme.Hom.comp_apply, chart_square G B R a, Scheme.Hom.comp_apply]
    exact hmemA _
  -- lift `chartB ≫ f` into the affine chart of `Y`
  have hrange : Set.range ⇑(chartB R a ≫ f) ⊆ Set.range ⇑ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hchartU v
  set t := IsOpenImmersion.lift ι (chartB R a ≫ f) hrange with htdef
  have ht : t ≫ ι = chartB R a ≫ f := IsOpenImmersion.lift_fac ι _ hrange
  -- the Γ-level ring hom of the lifted restriction
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ (Y.affineCover.X i₀).isoSpec.hom)
  -- `φ` has `G`-fixed image: transport the invariance of `f` through the chart
  have hspec : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫
        chartB R a = chartB R a ≫ specSMul g := by
    intro g
    rw [chartB_def, specSMul, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.map_comp _
  have hφfix : ∀ (g : G) (c), MulSemiringAction.awayHom (fun g => a.2 g) g
      (φ.hom c) = φ.hom c := by
    intro g
    have h11 : Spec.map (CommRingCat.ofHom
        (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ t = t := by
      rw [← cancel_mono ι, Category.assoc, ht, ← Category.assoc, hspec g,
        Category.assoc, hf g]
    have h12 : Spec.map (CommRingCat.ofHom
          (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ Spec.map φ =
        Spec.map φ := by
      rw [hφ, ← Category.assoc, h11]
    rw [← Spec.map_comp] at h12
    have h13 := Spec.map_injective h12
    intro c
    exact congrArg (fun ψ => ψ.hom c) h13
  -- factor through the invariants (the algebra engine)
  obtain ⟨ψ, hψ, -⟩ := existsUnique_factor_fixedPoints_away R a φ.hom hφfix
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (Y.affineCover.X i₀).isoSpec.inv ≫ ι, ?_⟩
  have h14 : chartπ R a ≫ Spec.map (CommRingCat.ofHom ψ) = Spec.map φ := by
    rw [chartπ_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h14' : CommRingCat.ofHom ((IsLocalization.map
        (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a)).comp ψ) = φ := by
      rw [hψ]
      exact CommRingCat.ofHom_hom φ
    rw [h14']
  rw [← Category.assoc, h14, hφ, Category.assoc, Iso.hom_inv_id_assoc, ht]

variable (G B) in
/-- Existence of descent: every `G`-invariant morphism out of `Spec B` factors
through the invariants morphism. -/
theorem exists_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃ q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f := by
  choose a hmem qa hqa using exists_chart_descent G B R f hf
  have hcoverA : ∀ p : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)),
      ∃ v, chartA R (a p) v = p := by
    intro p
    have h15' : p ∈ (chartA R (a p)).opensRange := by
      rw [chartA_opensRange]
      exact hmem p
    exact h15'
  set 𝒰 : (Spec (CommRingCat.of (FixedPoints.subalgebra R B G))).OpenCover :=
    Scheme.Cover.mkOfCovers
    (J := ↥(Spec (CommRingCat.of (FixedPoints.subalgebra R B G))))
    (fun p => Spec (CommRingCat.of (Localization.Away (a p))))
    (fun p => chartA R (a p))
    (fun p => ⟨p, hcoverA p⟩)
    (fun p => inferInstance) with h𝒰
  -- compatibility on overlaps, via the restriction-stable uniqueness
  have hcompat : ∀ p q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)),
      pullback.fst (chartA R (a p)) (chartA R (a q)) ≫ qa p =
        pullback.snd (chartA R (a p)) (chartA R (a q)) ≫ qa q := by
    intro p q
    refine invariantsπ_hom_ext_of_isOpenImmersion G B R
      (pullback.fst (chartA R (a p)) (chartA R (a q)) ≫ chartA R (a p)) _ _ ?_
    rw [chart_descent_side G B R f _ (a p) (qa p) (hqa p)
        (pullback.fst (chartA R (a p)) (chartA R (a q))) rfl,
      chart_descent_side G B R f _ (a q) (qa q) (hqa q)
        (pullback.snd (chartA R (a p)) (chartA R (a q))) pullback.condition.symm]
  refine ⟨𝒰.glueMorphisms (fun p => qa p) hcompat, ?_⟩
  -- verify the factorization on the `B`-side cover
  have hcoverB : ∀ x : Spec (CommRingCat.of B),
      ∃ v, chartB R (a (invariantsπ G B R x)) v = x := by
    intro x
    have h17 : x ∈ (chartB R (a (invariantsπ G B R x))).opensRange := by
      rw [chartB_opensRange]
      exact hmem (invariantsπ G B R x)
    exact h17
  refine Scheme.Cover.hom_ext
    ((Scheme.Cover.mkOfCovers
      (J := ↥(Spec (CommRingCat.of B)))
      (fun x => Spec (CommRingCat.of
        (Localization.Away ((a (invariantsπ G B R x) : B)))))
      (fun x => chartB R (a (invariantsπ G B R x)))
      (fun x => ⟨x, hcoverB x⟩)
      (fun x => inferInstance) : (Spec (CommRingCat.of B)).OpenCover))
    _ _ (fun x => ?_)
  show chartB R (a (invariantsπ G B R x)) ≫ invariantsπ G B R ≫
      𝒰.glueMorphisms (fun p => qa p) hcompat =
    chartB R (a (invariantsπ G B R x)) ≫ f
  rw [← Category.assoc, chart_square G B R, Category.assoc]
  have h18 : chartA R (a (invariantsπ G B R x)) ≫
      𝒰.glueMorphisms (fun p => qa p) hcompat = qa (invariantsπ G B R x) :=
    𝒰.ι_glueMorphisms _ hcompat (invariantsπ G B R x)
  rw [h18]
  exact hqa (invariantsπ G B R x)

variable (G B) in
/-- **The affine quotient by a finite group** ([Loeffler, *Modular curves*,
Prop 3.6.1], affine case; SGA I V.1.1; Stacks 07S7): `Spec Bᴳ` together with the
invariants morphism represents the functor `Y ↦ {G-invariant morphisms Spec B ⟶ Y}`
— every `G`-invariant morphism out of `Spec B` factors uniquely through
`invariantsπ : Spec B ⟶ Spec Bᴳ`. In particular `Spec Bᴳ` is the categorical
quotient of `Spec B` by `G` in the category of all schemes. -/
theorem existsUnique_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃! q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f := by
  obtain ⟨q, hq⟩ := exists_invariantsπ_lift G B R f hf
  exact ⟨q, hq, fun q' hq' => invariantsπ_hom_ext G B R q' q (hq'.trans hq.symm)⟩

end UniversalProperty

end AlgebraicGeometry

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
    have hκrange : Set.range κ.base = (PrimeSpectrum.basicOpen a : Set _) :=
      PrimeSpectrum.localization_away_comap_range _ a
    have hκj : Set.range κ.base ⊆ Set.range j.base := by
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
        rw [← hκrange]
        exact ⟨v, by rw [← hℓj, Scheme.Hom.comp_apply]⟩
      obtain ⟨t, htT, ht⟩ := h5
      rwa [← j.isOpenEmbedding.injective ht]
    have hwℓ : ∃ z, ℓ z = w := by
      have h6 : j w ∈ Set.range κ.base := hκrange ▸ hjws
      obtain ⟨v, hv⟩ := h6
      refine ⟨v, j.isOpenEmbedding.injective ?_⟩
      rw [← hℓj, Scheme.Hom.comp_apply] at hv
      exact hv
    -- lift `ℓ ≫ hᵢ` into the affine chart
    have hrange₁ : Set.range (ℓ ≫ h₁).base ⊆ Set.range ι.base := by
      rintro _ ⟨v, rfl⟩
      exact hrangeT v
    have hrange₂ : Set.range (ℓ ≫ h₂).base ⊆ Set.range ι.base := by
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
      rw [← Category.assoc, ← hρsnd, Category.assoc, Category.assoc, H]
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
  exact Scheme.OpenCover.hom_ext
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

variable (G B) in
/-- Existence of descent: every `G`-invariant morphism out of `Spec B` factors
through the invariants morphism. -/
theorem exists_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃ q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f := by
  sorry

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

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
  sorry

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

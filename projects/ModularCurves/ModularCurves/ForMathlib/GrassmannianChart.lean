/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Affine charts of the Grassmannian functor ([NISOG-GRASS], wave 1)

The chart algebra for representing `Module.Grassmannian.functor` by a scheme, following
mathlib's own TODO ladder in `RingTheory/Grassmannian.lean` (*"Define `chart x` indexed
by `x : Fin k → M` … the composition `R^k → M → M⧸N` is an isomorphism"*) and Stacks
089T (Lemma 27.22.1, the chart-subfunctor route):

* `Module.Grassmannian.IsChartAt x N` — the chart predicate at a tuple `x : Fin k → M`;
* `chartEquivRetraction` — chart members are exactly the retractions `φ` of `x`
  (`N = ker φ`), the coordinate-free form of Stacks' "F_i ≅ S ↦ Γ(S, O_S^{k(n−k)})";
* `isChartAt_map` — base change (mathlib's `Grassmannian.map`) preserves charts;
* `retractionEquivMatrix` — over `M = Fin n → R` with `x` a coordinate sub-basis, the
  retraction space is the matrix space of the complementary block.

Consumer: KM 6.5.1's ambient space for `[N-Isog]` (`exists_nIsogSpace`,
`GroupScheme/NIsogeny.lean`, gate [NISOG-GRASS]).
-/

universe u v

namespace Module.Grassmannian

open Module

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

/-- The linear map `(Fin k → R) →ₗ[R] M` sending coordinates to their combination along
a tuple `x` — the "matrix whose columns are `x`". Private-ish seam isolating the
`Fintype.linearCombination` spelling ([GR-A0] attack 3). -/
noncomputable def coordMap (x : Fin k → M) : (Fin k → R) →ₗ[R] M :=
  Fintype.linearCombination R x

@[simp] lemma coordMap_single (x : Fin k → M) (i : Fin k) :
    coordMap x (Pi.single i (1 : R)) = x i := by
  simp [coordMap]

/-- **[GR-A0]** The chart predicate: `N` lies in the chart at `x : Fin k → M` when the
composite `(Fin k → R) → M → M ⧸ N` is bijective — the images of `x` form a basis of the
quotient (mathlib TODO: *"the composition `R^k → M → M⧸N` is an isomorphism"*). -/
def IsChartAt (x : Fin k → M) (N : G(k, M; R)) : Prop :=
  Function.Bijective (N.toSubmodule.mkQ ∘ₗ coordMap x)

/-- A retraction of `x` is a left inverse of `coordMap x` — the workhorse computation
shared by [GR-A1]'s directions. -/
lemma retraction_comp_coordMap (x : Fin k → M) {φ : M →ₗ[R] (Fin k → R)}
    (hφ : ∀ i, φ (x i) = Pi.single i 1) (c : Fin k → R) :
    φ (coordMap x c) = c := by
  rw [coordMap, Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, hφ, ← Pi.single_smul, smul_eq_mul, mul_one]
  exact Finset.univ_sum_single c

set_option backward.isDefEq.respectTransparency false in
/-- Forward direction of [GR-A1]: the retraction attached to a chart member,
`φ = (chart iso)⁻¹ ∘ mkQ`. -/
noncomputable def chartToRetraction (x : Fin k → M) (N : {N : G(k, M; R) // IsChartAt x N}) :
    {φ : M →ₗ[R] (Fin k → R) // ∀ i, φ (x i) = Pi.single i 1} :=
  ⟨(LinearEquiv.ofBijective _ N.2).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ, fun i => by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq,
      LinearEquiv.ofBijective_apply, LinearMap.comp_apply, coordMap_single]⟩

/-- The kernel of a retraction of `x` is a chart member: the composite
`(Fin k → R) → M → M ⧸ ker φ` is bijective. -/
lemma bijective_mkQ_comp_coordMap (x : Fin k → M) {φ : M →ₗ[R] (Fin k → R)}
    (hφ : ∀ i, φ (x i) = Pi.single i 1) :
    Function.Bijective ((LinearMap.ker φ).mkQ ∘ₗ coordMap x) := by
  constructor
  · intro c c' h
    have hmem : coordMap x (c - c') ∈ LinearMap.ker φ := by
      rw [map_sub]
      exact (Submodule.Quotient.eq _).mp h
    have hc := retraction_comp_coordMap x hφ (c - c')
    rw [LinearMap.mem_ker.mp hmem] at hc
    exact sub_eq_zero.mp hc.symm
  · intro m
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨φ m, (Submodule.Quotient.eq _).mpr ?_⟩
    rw [LinearMap.mem_ker, map_sub, retraction_comp_coordMap x hφ, sub_self]

/-- Backward direction of [GR-A1]: the chart member attached to a retraction,
`N = ker φ`. -/
noncomputable def retractionToChart (x : Fin k → M)
    (φ : {φ : M →ₗ[R] (Fin k → R) // ∀ i, φ (x i) = Pi.single i 1}) :
    {N : G(k, M; R) // IsChartAt x N} :=
  have hsurj : Function.Surjective φ.1 := fun c =>
    ⟨coordMap x c, retraction_comp_coordMap x φ.2 c⟩
  let e : (M ⧸ LinearMap.ker φ.1) ≃ₗ[R] (Fin k → R) :=
    φ.1.quotKerEquivOfSurjective hsurj
  ⟨{ toSubmodule := LinearMap.ker φ.1
     finite_quotient := Module.Finite.equiv e.symm
     projective_quotient := Module.Projective.of_equiv e.symm
     rankAtStalk_eq := fun p => by
       haveI : Nontrivial R :=
         ⟨0, 1, fun h01 => p.isPrime.ne_top
           ((Ideal.eq_top_iff_one _).mpr (h01 ▸ p.asIdeal.zero_mem))⟩
       rw [rankAtStalk_eq_of_equiv e]
       simp [rankAtStalk_eq_finrank_of_free] },
   bijective_mkQ_comp_coordMap x φ.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- **[GR-A1]** A chart member at `x` is the same data as a retraction of `x`: a linear
`φ : M → (Fin k → R)` with `φ (x i) = eᵢ`, via `N = ker φ` (Stacks 089T step (3), the
coordinate-free form). -/
noncomputable def chartEquivRetraction (x : Fin k → M) :
    {N : G(k, M; R) // IsChartAt x N} ≃
      {φ : M →ₗ[R] (Fin k → R) // ∀ i, φ (x i) = Pi.single i 1} where
  toFun := chartToRetraction x
  invFun := retractionToChart x
  left_inv N := by
    refine Subtype.ext (Module.Grassmannian.ext ?_)
    show LinearMap.ker ((LinearEquiv.ofBijective _ N.2).symm.toLinearMap ∘ₗ
      N.1.toSubmodule.mkQ) = N.1.toSubmodule
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  right_inv φ := by
    refine Subtype.ext (LinearMap.ext fun m => ?_)
    show (LinearEquiv.ofBijective _ (retractionToChart x φ).2).symm
      ((retractionToChart x φ).1.toSubmodule.mkQ m) = φ.1 m
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, LinearMap.comp_apply]
    refine ((Submodule.Quotient.eq _).mpr ?_).symm
    show coordMap x (φ.1 m) - m ∈ LinearMap.ker φ.1
    rw [LinearMap.mem_ker, map_sub, retraction_comp_coordMap x φ.2, sub_self]

/-- **[GR-B]** Over `M = Fin n → R` with chart tuple a coordinate sub-basis (an
embedding `ι : Fin k ↪ Fin n`), a retraction is freely determined by its values on the
complementary coordinates — the chart is a matrix space (Stacks 089T step (3)). -/
noncomputable def retractionEquivMatrix (n : ℕ) (ι : Fin k ↪ Fin n) :
    {φ : (Fin n → R) →ₗ[R] (Fin k → R) //
        ∀ i, φ (Pi.single (ι i) 1) = Pi.single i 1} ≃
      ({j : Fin n // j ∉ Set.range ι} → (Fin k → R)) := by
  classical
  exact
  { toFun := fun φ j => φ.1 (Pi.single j.1 1)
    invFun := fun v =>
      ⟨(Pi.basisFun R (Fin n)).constr ℕ (fun j =>
        if h : j ∈ Set.range ι then
          Pi.single ((Equiv.ofInjective ι ι.injective).symm ⟨j, h⟩) 1
        else v ⟨j, h⟩), fun i => by
        rw [← Pi.basisFun_apply, Basis.constr_basis, dif_pos ⟨i, rfl⟩]
        congr 1
        exact Equiv.ofInjective_symm_apply ι.injective i⟩
    left_inv := fun φ => by
      refine Subtype.ext ((Pi.basisFun R (Fin n)).ext fun j => ?_)
      rw [Basis.constr_basis, Pi.basisFun_apply]
      by_cases h : j ∈ Set.range ι
      · rw [dif_pos h]
        obtain ⟨i, rfl⟩ := h
        rw [φ.2]
        congr 1
        exact Equiv.ofInjective_symm_apply ι.injective i
      · rw [dif_neg h]
    right_inv := fun v => by
      funext j
      show ((Pi.basisFun R (Fin n)).constr ℕ _) (Pi.single j.1 1) = v j
      rw [← Pi.basisFun_apply, Basis.constr_basis, dif_neg j.2] }

section Congr

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- **[GR-T1]** Transport of a Grassmannian element along a module equivalence — the
quotient instances ride the induced quotient equivalence. Mathlib's Grassmannian file has
no `congr`; upstream-shaped. -/
noncomputable def congr (e : M ≃ₗ[R] M') (N : G(k, M; R)) : G(k, M'; R) where
  toSubmodule := N.toSubmodule.map (e : M →ₗ[R] M')
  finite_quotient := Module.Finite.equiv
    (Submodule.Quotient.equiv N.toSubmodule (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl)
  projective_quotient := Module.Projective.of_equiv
    (Submodule.Quotient.equiv N.toSubmodule (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl)
  rankAtStalk_eq := fun p => by
    rw [← rankAtStalk_eq_of_equiv
      (Submodule.Quotient.equiv N.toSubmodule (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl)]
    exact N.rankAtStalk_eq p

@[simp] lemma congr_toSubmodule (e : M ≃ₗ[R] M') (N : G(k, M; R)) :
    (congr e N).toSubmodule = N.toSubmodule.map (e : M →ₗ[R] M') := rfl

/-- The chart tuple transports contravariantly under `congr`: `N` is in the chart at `x`
iff `congr e N` is in the chart at `e ∘ x`. -/
lemma isChartAt_congr (e : M ≃ₗ[R] M') (x : Fin k → M) (N : G(k, M; R)) :
    IsChartAt (⇑e ∘ x) (congr e N) ↔ IsChartAt x N := by
  have hsquare : ⇑((congr e N).toSubmodule.mkQ ∘ₗ coordMap (⇑e ∘ x))
      = ⇑(Submodule.Quotient.equiv N.toSubmodule
            (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl) ∘
          ⇑(N.toSubmodule.mkQ ∘ₗ coordMap x) := by
    funext c
    show (N.toSubmodule.map (e : M →ₗ[R] M')).mkQ
        (Fintype.linearCombination R (⇑e ∘ x) c) = _
    simp [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, coordMap,
      Fintype.linearCombination_apply, map_sum, map_smul]
  simp only [IsChartAt]
  rw [hsquare]
  exact Function.Bijective.of_comp_iff'
    (Submodule.Quotient.equiv N.toSubmodule
      (N.toSubmodule.map (e : M →ₗ[R] M')) e rfl).bijective _

end Congr

section BaseChange

open TensorProduct

universe w

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **[GR-C2]** A surjection from a rank-`k` free module onto a finite projective module
of constant `rankAtStalk` `k` is bijective — the kernel is a finitely generated projective
direct summand of stalkwise rank `0`, hence zero (Stacks 089T step (4)'s dimension
argument, module form). -/
theorem bijective_of_surjective_of_rankAtStalk {Q : Type v} [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (hrank : ∀ p, rankAtStalk (R := R) Q p = k)
    (ψ : (Fin k → R) →ₗ[R] Q) (hsurj : Function.Surjective ψ) :
    Function.Bijective ψ := by
  -- `Q` is projective, so the surjection `ψ` splits: pick a section `s`.
  obtain ⟨s, hs⟩ := ψ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hsx : ∀ q, ψ (s q) = q := fun q => by simpa using LinearMap.congr_fun hs q
  -- the complementary projection `id - s ∘ ψ` lands in `ker ψ`; corestrict it to `r`.
  have hmem : ∀ x, (LinearMap.id (R := R) (M := (Fin k → R)) - s ∘ₗ ψ) x ∈ LinearMap.ker ψ :=
    fun x => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        map_sub, hsx, sub_self]
  set r : (Fin k → R) →ₗ[R] ↥(LinearMap.ker ψ) :=
    (LinearMap.id (R := R) (M := (Fin k → R)) - s ∘ₗ ψ).codRestrict (LinearMap.ker ψ) hmem with hr
  have hrval : ∀ x, (r x : Fin k → R) = x - s (ψ x) := fun x => by
    rw [hr, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
  -- `r` is a retraction of the inclusion `ker ψ ↪ (Fin k → R)`.
  have hr_section : ∀ y : ↥(LinearMap.ker ψ), r (y : Fin k → R) = y := fun y => by
    apply Subtype.ext
    rw [hrval, LinearMap.mem_ker.mp y.2, map_zero, sub_zero]
  have hr_surj : Function.Surjective r := fun y => ⟨(y : Fin k → R), hr_section y⟩
  -- hence `ker ψ` is a finite projective (thus flat) direct summand.
  haveI : Module.Finite R ↥(LinearMap.ker ψ) := Module.Finite.of_surjective r hr_surj
  haveI : Module.Projective R ↥(LinearMap.ker ψ) :=
    Module.Projective.of_split (LinearMap.ker ψ).subtype r (LinearMap.ext fun y => hr_section y)
  -- the splitting isomorphism `(Fin k → R) ≃ₗ Q × ker ψ`.
  set g : Q × ↥(LinearMap.ker ψ) →ₗ[R] (Fin k → R) :=
    s ∘ₗ LinearMap.fst R Q ↥(LinearMap.ker ψ) +
      (LinearMap.ker ψ).subtype ∘ₗ LinearMap.snd R Q ↥(LinearMap.ker ψ) with hg
  have hgval : ∀ (q : Q) (n : ↥(LinearMap.ker ψ)), g (q, n) = s q + (n : Fin k → R) :=
    fun q n => by simp [hg]
  let e : (Fin k → R) ≃ₗ[R] Q × ↥(LinearMap.ker ψ) :=
    LinearEquiv.ofLinear (ψ.prod r) g
      (by
        refine LinearMap.ext fun x => ?_
        obtain ⟨q, n⟩ := x
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [hgval]
        have h1 : ψ (s q + (n : Fin k → R)) = q := by
          rw [map_add, hsx, LinearMap.mem_ker.mp n.2, add_zero]
        have h2 : (r (s q + (n : Fin k → R)) : Fin k → R) = (n : Fin k → R) := by
          rw [hrval, h1]; abel
        show (ψ (s q + (n : Fin k → R)), r (s q + (n : Fin k → R))) = (q, n)
        rw [h1, Subtype.ext h2])
      (by
        refine LinearMap.ext fun x => ?_
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        show g (ψ x, r x) = x
        rw [hgval, hrval]; abel)
  -- rank bookkeeping: `ker ψ` has stalkwise rank `0`, hence is trivial.
  have hker0 : rankAtStalk (R := R) ↥(LinearMap.ker ψ) = 0 := by
    funext p
    haveI : Nontrivial R :=
      ⟨0, 1, fun h01 => p.isPrime.ne_top
        ((Ideal.eq_top_iff_one _).mpr (h01 ▸ p.asIdeal.zero_mem))⟩
    have htotal : rankAtStalk (R := R) (Fin k → R) p = k := by
      simp [rankAtStalk_eq_finrank_of_free]
    have key : rankAtStalk (R := R) (Fin k → R) p
        = rankAtStalk (R := R) Q p + rankAtStalk (R := R) ↥(LinearMap.ker ψ) p := by
      have hEq := rankAtStalk_eq_of_equiv (R := R) e
      rw [rankAtStalk_prod] at hEq
      exact congr_fun hEq p
    rw [htotal, hrank p] at key
    have hz : rankAtStalk (R := R) ↥(LinearMap.ker ψ) p = 0 := by omega
    simpa using hz
  -- conclude injectivity from triviality of the kernel.
  refine ⟨?_, hsurj⟩
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (Module.rankAtStalk_eq_zero_iff_subsingleton).mp hker0

section Covering

open TensorProduct

universe w'

variable {A : Type w'} [CommRing A] [Algebra R A]

/-- Base change of a quotient is right exact: for an `A₀`-algebra `B`, an `A₀`-module `Q` and a
submodule `S`, the base change `B ⊗ (Q ⧸ S)` is trivial iff `S.baseChange B = ⊤` (i.e. the images
`1 ⊗ s` generate `B ⊗ Q` over `B`). Used both for the residue-field selection and the final
`Localization.Away` surjectivity in [GR-C1]. -/
private lemma subsingleton_baseChange_quotient_iff {A₀ B Q : Type*} [CommRing A₀] [CommRing B]
    [Algebra A₀ B] [AddCommGroup Q] [Module A₀ Q] (S : Submodule A₀ Q) :
    S.baseChange B = ⊤ ↔ Subsingleton (B ⊗[A₀] (Q ⧸ S)) := by
  have hexact : Function.Exact (S.subtype.baseChange B) (S.mkQ.baseChange B) :=
    lTensor_exact B (LinearMap.exact_subtype_mkQ S) (Submodule.mkQ_surjective S)
  have hsurj : Function.Surjective (S.mkQ.baseChange B) :=
    LinearMap.baseChange_surjective B (Submodule.mkQ_surjective S)
  have hker : LinearMap.ker (S.mkQ.baseChange B) = S.baseChange B := hexact.linearMap_ker_eq
  rw [← hker, ← Submodule.Quotient.subsingleton_iff]
  exact ((S.mkQ.baseChange B).quotKerEquivOfSurjective hsurj).toEquiv.subsingleton_congr

/-- The standard tensor generators `1 ⊗ Pi.single j 1` of `A ⊗[R] (Fin n → R)` span it over `A`;
they are the base change of the coordinate basis of `Fin n → R`. -/
private lemma span_tmul_single_eq_top (n : ℕ) :
    Submodule.span A (Set.range (fun j : Fin n => (1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R)))
      = ⊤ := by
  have hb : (fun j : Fin n => (1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R))
      = ⇑((Pi.basisFun R (Fin n)).baseChange A) := by
    funext j
    rw [Basis.baseChange_apply, Pi.basisFun_apply]
  rw [hb]
  exact Basis.span_eq _

/-- A spanning family `v : Fin n → V` of a `k`-dimensional vector space contains a `k`-element
spanning sub-family, indexed by an embedding `Fin k ↪ Fin n`. Used to pick the coordinate subset
at the residue field in [GR-C1]. -/
private lemma exists_emb_span_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (v : Fin n → V)
    (hspan : Submodule.span K (Set.range v) = ⊤) (hdim : Module.finrank K V = k) :
    ∃ ι : Fin k ↪ Fin n, Submodule.span K (Set.range (v ∘ ι)) = ⊤ := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K v
  rw [hspan] at hsp
  let b : Basis κ K V := Basis.mk hli hsp.ge
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by rw [← Module.finrank_eq_card_basis b]; exact hdim
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
  have hrange : Set.range (v ∘ (a ∘ e)) = Set.range (v ∘ a) := by
    rw [← Function.comp_assoc, Set.range_comp, e.surjective.range_eq, Set.image_univ]
  show Submodule.span K (Set.range (v ∘ (a ∘ e))) = ⊤
  rw [hrange]; exact hsp

/-- The range of `coordMap x` is the span of the tuple `x`. -/
private lemma range_coordMap {R' : Type*} [CommRing R'] {W : Type v} [AddCommGroup W]
    [Module R' W] {m : ℕ} (x : Fin m → W) :
    LinearMap.range (coordMap (R := R') x) = Submodule.span R' (Set.range x) := by
  unfold coordMap
  exact Fintype.range_linearCombination R' x

/-- The kernel of `baseChangeMkQ` depends on the `A`-algebra structure on `B` only through its
equality class — so `Grassmannian.map`'s quotient (built with `f.toAlgebra`) has the same
`toSubmodule` as the ambient `baseChangeMkQ`, once the two `Algebra A B` instances are identified.
Resolves the `OreLocalization` scalar-instance diamond in the assembly of [GR-C1]. -/
private lemma ker_baseChangeMkQ_congr {B : Type w'} [CommRing B] [Algebra R B]
    (N : Submodule A (A ⊗[R] M)) (i₁ i₂ : Algebra A B)
    (j₁ : @IsScalarTower R A B _ i₁.toSMul _) (j₂ : @IsScalarTower R A B _ i₂.toSMul _)
    (h : i₁ = i₂) :
    (letI := i₁; letI := j₁; LinearMap.ker (baseChangeMkQ B N))
    = (letI := i₂; letI := j₂; LinearMap.ker (baseChangeMkQ B N)) := by
  subst h; congr!

/-- **[GR-C1]** Nakayama covering, surjectivity half (Stacks 089T step (5)): every
Grassmannian element over `A` admits, near any prime `p`, a coordinate `k`-subset whose
chart composite becomes surjective after inverting some `f ∉ p` — the images of the
standard basis generate the quotient, a rank-`k` sub-selection spans at the residue
field, and the finitely generated cokernel of that selection dies on a basic open. -/
theorem exists_localizationAway_surjective (n : ℕ)
    (N : G(k, A ⊗[R] (Fin n → R); A)) (p : Ideal A) [p.IsPrime] :
    ∃ (ι : Fin k ↪ Fin n) (f : A), f ∉ p ∧
      Function.Surjective
        ((N.map (IsScalarTower.toAlgHom R A (Localization.Away f))).toSubmodule.mkQ ∘ₗ
          coordMap (fun i =>
            (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))) := by
  classical
  -- The quotient `Q` and its standard generators `q j = mkQ (1 ⊗ eⱼ)`, which span it over `A`.
  set q : Fin n → ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) :=
    fun j => N.toSubmodule.mkQ (1 ⊗ₜ[R] (Pi.single j 1 : Fin n → R)) with hq
  have hq_span : Submodule.span A (Set.range q) = ⊤ := by
    rw [hq, show (fun j : Fin n => N.toSubmodule.mkQ (1 ⊗ₜ[R] (Pi.single j 1 : Fin n → R)))
          = ⇑N.toSubmodule.mkQ ∘ (fun j : Fin n => (1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R))
        from rfl, Set.range_comp, ← Submodule.map_span, span_tmul_single_eq_top,
      Submodule.map_top, Submodule.range_mkQ]
  -- Over the residue field `κ(p)`, the fibre `κ(p) ⊗ Q` is `k`-dimensional and spanned by the
  -- `1 ⊗ qⱼ`; pick a `k`-element sub-family forming a basis, indexed by `ι : Fin k ↪ Fin n`.
  have hVdim : Module.finrank p.ResidueField
      (p.ResidueField ⊗[A] ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule)) = k :=
    (Ideal.finrank_fiber_eq_rankAtStalk p).trans (N.rankAtStalk_eq ⟨p, inferInstance⟩)
  have hVspan : Submodule.span p.ResidueField
      (Set.range (fun j => (1 : p.ResidueField) ⊗ₜ[A] q j)) = ⊤ := by
    rw [show (fun j => (1 : p.ResidueField) ⊗ₜ[A] q j)
          = ⇑(TensorProduct.mk A p.ResidueField _ 1) ∘ q from rfl,
      Set.range_comp, ← Submodule.baseChange_span, hq_span, Submodule.baseChange_top]
  obtain ⟨ι, hι⟩ := exists_emb_span_eq_top (K := p.ResidueField)
    (fun j => (1 : p.ResidueField) ⊗ₜ[A] q j) hVspan hVdim
  -- The cokernel `Q ⧸ S` of the selected generators is `A`-finite and vanishes at `p`, so by
  -- Nakayama (residue-field base change) plus spreading out it also vanishes on some `D(f)`.
  set S : Submodule A ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) :=
    Submodule.span A (Set.range (fun i => q (ι i))) with hS
  haveI : Module.Finite A (((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S) :=
    Module.Finite.of_surjective S.mkQ (Submodule.mkQ_surjective S)
  have hκC : Subsingleton (p.ResidueField ⊗[A]
      (((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S)) := by
    rw [← subsingleton_baseChange_quotient_iff, hS, Submodule.baseChange_span, ← Set.range_comp]
    exact hι
  haveI : Subsingleton (LocalizedModule p.primeCompl
      (((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S)) := by
    have hns : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A
        (((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S) := by
      rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
      exact not_nontrivial_iff_subsingleton.mpr hκC
    exact Module.notMem_support_iff.mp hns
  obtain ⟨f, hf, hfsub⟩ := LocalizedModule.exists_subsingleton_away
    (M := ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S) p
  refine ⟨ι, f, hf, ?_⟩
  -- On `D(f)` the selected generators span, so the chart composite is surjective.  We transport
  -- through the identification `baseChangeMkQEquiv : (chart quotient) ≃ A_f ⊗ Q`.
  have hsub_loc : Subsingleton (Localization.Away f ⊗[A]
      (((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) ⧸ S)) :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) _).toEquiv.subsingleton_congr.mp hfsub
  have hSbcf : S.baseChange (Localization.Away f) = ⊤ :=
    (subsingleton_baseChange_quotient_iff S).mpr hsub_loc
  set Ψ := baseChangeMkQEquiv (B := Localization.Away f) N.toSubmodule with hΨdef
  have hΨ : Ψ.toLinearMap ∘ₗ (baseChangeMkQ (Localization.Away f) N.toSubmodule).ker.mkQ
      = baseChangeMkQ (Localization.Away f) N.toSubmodule := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply, hΨdef]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ (baseChangeMkQ_surjective N.toSubmodule) y
  have hbc : ⇑(baseChangeMkQ (Localization.Away f) N.toSubmodule) ∘
      (fun i => (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))
      = (fun i => (1 : Localization.Away f) ⊗ₜ[A] q (ι i)) := by
    funext i
    simp only [Function.comp_apply, hq]
    simp [baseChangeMkQ]
  have hspan_eq : Submodule.span (Localization.Away f)
      (Set.range (fun i => (1 : Localization.Away f) ⊗ₜ[A] q (ι i)))
      = S.baseChange (Localization.Away f) := by
    rw [hS, Submodule.baseChange_span,
      show (fun i => (1 : Localization.Away f) ⊗ₜ[A] q (ι i))
          = ⇑(TensorProduct.mk A (Localization.Away f) _ 1) ∘ (fun i => q (ι i)) from rfl,
      Set.range_comp]
  -- surjectivity of `Ψ ∘ (chart composite)`, which is `baseChangeMkQ ∘ coordMap`
  have key : Function.Surjective ⇑(Ψ.toLinearMap ∘ₗ
      ((baseChangeMkQ (Localization.Away f) N.toSubmodule).ker.mkQ ∘ₗ
        coordMap (fun i => (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R)))) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.comp_assoc, hΨ, LinearMap.range_comp,
      range_coordMap, Submodule.map_span, ← Set.range_comp, hbc, hspan_eq]
    exact hSbcf
  -- the chart composite through the (definitionally equal) `baseChangeMkQ` kernel is surjective
  have hker : Function.Surjective ((baseChangeMkQ (Localization.Away f) N.toSubmodule).ker.mkQ ∘ₗ
      coordMap (fun i => (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))) := by
    intro y
    obtain ⟨c, hc⟩ := key (Ψ y)
    exact ⟨c, Ψ.injective hc⟩
  -- Identify the `Grassmannian.map` quotient with the ambient `baseChangeMkQ` kernel (they use
  -- the two `A`-algebra structures on `Localization.Away f`, which agree by `Algebra.algebra_ext`)
  -- and transport surjectivity.
  have halg : (IsScalarTower.toAlgHom R A (Localization.Away f)).toAlgebra
      = (inferInstance : Algebra A (Localization.Away f)) := Algebra.algebra_ext _ _ fun _ => rfl
  have hbridge : (N.map (IsScalarTower.toAlgHom R A (Localization.Away f))).toSubmodule
      = (baseChangeMkQ (Localization.Away f) N.toSubmodule).ker := by
    rw [map_toSubmodule (IsScalarTower.toAlgHom R A (Localization.Away f)) N]
    exact ker_baseChangeMkQ_congr N.toSubmodule _ _ _ _ halg
  rw [hbridge]
  exact hker

/-- **[GR-C]** Zariski-local covering by coordinate charts (Stacks 089T step (5)): every
Grassmannian element over `A` lies, after inverting some `f` outside any given prime, in
the chart of a coordinate `k`-subset. Assembly of [GR-C1] (surjectivity on a basic open)
and [GR-C2] (equal-rank surjective ⟹ bijective). -/
theorem exists_isChartAt_localizationAway (n : ℕ)
    (N : G(k, A ⊗[R] (Fin n → R); A)) (p : Ideal A) [p.IsPrime] :
    ∃ (ι : Fin k ↪ Fin n) (f : A), f ∉ p ∧
      IsChartAt (fun i =>
          (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))
        (N.map (IsScalarTower.toAlgHom R A (Localization.Away f))) := by
  obtain ⟨ι, f, hf, hsurj⟩ := exists_localizationAway_surjective n N p
  refine ⟨ι, f, hf, ?_⟩
  -- `IsChartAt` unfolds to bijectivity of the same composite; [GR-C2] over `Localization.Away f`
  -- upgrades [GR-C1]'s surjectivity, using the `Grassmannian` structure of `N.map …` for the
  -- finite-projective + constant-`rankAtStalk` hypotheses.
  exact bijective_of_surjective_of_rankAtStalk
    (N.map (IsScalarTower.toAlgHom R A (Localization.Away f))).rankAtStalk_eq _ hsurj

/-- The pi-normalization sends the tensor chart tuple to the coordinate tuple. -/
lemma piScalarRight_tmul_single (n : ℕ) (j : Fin n) :
    TensorProduct.piScalarRight R A A (Fin n) ((1 : A) ⊗ₜ[R] Pi.single j (1 : R))
      = Pi.single j (1 : A) := by
  classical
  funext l
  by_cases hl : l = j <;>
    simp [TensorProduct.piScalarRight, TensorProduct.piScalarRightHom_tmul, hl]

/-- **[GR-T2]** The covering theorem in the normalized presentation: after inverting
some `f` outside a given prime, the transported element `congr piScalarRight (N.map …)`
lies in the chart of a coordinate `k`-subset of `(Fin n → A_f)`. -/
theorem exists_isChartAt_congr_localizationAway (n : ℕ)
    (N : G(k, A ⊗[R] (Fin n → R); A)) (p : Ideal A) [p.IsPrime] :
    ∃ (ι : Fin k ↪ Fin n) (f : A), f ∉ p ∧
      IsChartAt (fun i => Pi.single (ι i) (1 : Localization.Away f))
        (congr (TensorProduct.piScalarRight R (Localization.Away f)
            (Localization.Away f) (Fin n))
          (N.map (IsScalarTower.toAlgHom R A (Localization.Away f)))) := by
  obtain ⟨ι, f, hf, hchart⟩ := exists_isChartAt_localizationAway n N p
  refine ⟨ι, f, hf, ?_⟩
  have htuple : (fun i => Pi.single (ι i) (1 : Localization.Away f)) =
      ⇑(TensorProduct.piScalarRight R (Localization.Away f)
          (Localization.Away f) (Fin n)) ∘
        (fun i => (1 : Localization.Away f) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R)) := by
    funext i
    exact (piScalarRight_tmul_single n (ι i)).symm
  rw [htuple, isChartAt_congr]
  exact hchart

end Covering

/-- **[GR-A2]** Base change preserves charts: if `N` lies in the chart at
`1 ⊗ₜ x` over `A`, then `Grassmannian.map f` of `N` lies in the chart at `1 ⊗ₜ x` over
`B` (Stacks 089T step (4), base-change stability of the subfunctors). -/
theorem isChartAt_map (x : Fin k → M) (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)) (h : IsChartAt (fun i => (1 : A) ⊗ₜ[R] x i) N) :
    IsChartAt (fun i => (1 : B) ⊗ₜ[R] x i) (N.map f) := by
  classical
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq R A B)
  -- the A-side chart composite, an isomorphism by hypothesis
  set CA : (Fin k → A) →ₗ[A] ((A ⊗[R] M) ⧸ N.toSubmodule) :=
    N.toSubmodule.mkQ ∘ₗ coordMap (fun i => (1 : A) ⊗ₜ[R] x i) with hCA
  have hA : Function.Bijective ⇑CA := h
  -- the B-side chart composite, stated at the definitionally-equal kernel form
  set CB : (Fin k → B) →ₗ[B] ((B ⊗[R] M) ⧸ (baseChangeMkQ B N.toSubmodule).ker) :=
    (baseChangeMkQ B N.toSubmodule).ker.mkQ ∘ₗ coordMap (fun i => (1 : B) ⊗ₜ[R] x i)
    with hCB
  -- key square: e ∘ CB = (baseChange of CA) ∘ eπ⁻¹, checked on the standard basis
  have key : (baseChangeMkQEquiv (B := B) N.toSubmodule).toLinearMap ∘ₗ CB =
      (CA.baseChange B) ∘ₗ (TensorProduct.piScalarRight A B B (Fin k)).symm.toLinearMap := by
    refine (Pi.basisFun B (Fin k)).ext fun i => ?_
    have hπ : (TensorProduct.piScalarRight A B B (Fin k)).symm (Pi.basisFun B (Fin k) i)
        = (1 : B) ⊗ₜ[A] Pi.single i (1 : A) := by
      rw [LinearEquiv.symm_apply_eq]
      funext j
      by_cases hj : j = i <;>
        simp [TensorProduct.piScalarRight, TensorProduct.piScalarRightHom_tmul,
          Pi.basisFun_apply, hj, one_smul, zero_smul]
    -- Reduce the `CB`-side application to a bare quotient class, keeping `baseChangeMkQ`
    -- opaque (unfolding it *and* `baseChangeMkQEquiv` in the same pass makes the domain
    -- `AddCommMonoid`/`Module` instances of the resulting `LinearEquiv` desync from the
    -- ones baked into `CB`'s stated codomain, so `simp` chokes with an instance mismatch).
    have harg : CB (Pi.basisFun B (Fin k) i) = Submodule.Quotient.mk (1 ⊗ₜ[R] x i) := by
      rw [hCB, LinearMap.comp_apply, Pi.basisFun_apply, coordMap_single, Submodule.mkQ_apply]
    have hbase : baseChangeMkQEquiv (B := B) N.toSubmodule
        (Submodule.Quotient.mk (1 ⊗ₜ[R] x i)) = baseChangeMkQ B N.toSubmodule (1 ⊗ₜ[R] x i) :=
      LinearMap.quotKerEquivOfSurjective_apply_mk (baseChangeMkQ B N.toSubmodule)
        (baseChangeMkQ_surjective N.toSubmodule) (1 ⊗ₜ[R] x i)
    have hval : baseChangeMkQ B N.toSubmodule (1 ⊗ₜ[R] x i)
        = (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (1 ⊗ₜ[R] x i) := by
      simp [baseChangeMkQ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hπ, harg, hbase, hval]
    rw [hCA]
    simp [coordMap_single]
  -- transport bijectivity through the two equivalences
  show Function.Bijective ⇑CB
  refine (Function.Bijective.of_comp_iff'
    (baseChangeMkQEquiv (B := B) N.toSubmodule).bijective ⇑CB).mp ?_
  have hco := congrArg
    (fun L : (Fin k → B) →ₗ[B] (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) => ⇑L) key
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at hco
  rw [hco]
  have hbc : Function.Bijective ⇑(CA.baseChange B) := by
    have : CA.baseChange B =
        (LinearEquiv.baseChange A B _ _ (LinearEquiv.ofBijective CA hA)).toLinearMap := rfl
    rw [this]
    exact (LinearEquiv.baseChange A B _ _ (LinearEquiv.ofBijective CA hA)).bijective
  exact hbc.comp (TensorProduct.piScalarRight A B B (Fin k)).symm.bijective

end BaseChange

section NormalizedFunctor

open TensorProduct

universe w''

variable {A B : Type w''} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **[GR-B2n]** The normalized base-change on Grassmannians of `(Fin n → ·)`: transport
back along `piScalarRight`, apply mathlib's `Grassmannian.map`, transport forward. The
wave-3 functor map — tensors never appear downstream of this seam (artifact, wave-3
packaging decision). -/
noncomputable def normMap (n : ℕ) (f : A →ₐ[R] B) (N : G(k, (Fin n → A); A)) :
    G(k, (Fin n → B); B) :=
  congr (TensorProduct.piScalarRight R B B (Fin n))
    ((congr (TensorProduct.piScalarRight R A A (Fin n)).symm N).map f)

/-- **[GR-B2n]** `normMap` preserves coordinate charts. -/
theorem isChartAt_normMap (n : ℕ) (ι : Fin k ↪ Fin n) (f : A →ₐ[R] B)
    (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    IsChartAt (fun i => Pi.single (ι i) (1 : B)) (normMap n f N) := by
  have tA : (fun i => (1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))
      = ⇑(TensorProduct.piScalarRight R A A (Fin n)).symm ∘
        (fun i => Pi.single (ι i) (1 : A)) := by
    funext i
    rw [Function.comp_apply, ← piScalarRight_tmul_single (R := R) (A := A) n (ι i),
      LinearEquiv.symm_apply_apply]
  have tB : (fun i => Pi.single (ι i) (1 : B))
      = ⇑(TensorProduct.piScalarRight R B B (Fin n)) ∘
        (fun i => (1 : B) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R)) := by
    funext i
    exact (piScalarRight_tmul_single (A := B) n (ι i)).symm
  unfold normMap
  rw [tB, isChartAt_congr]
  apply isChartAt_map
  rw [tA, isChartAt_congr]
  exact h

/-- **[GR-B2n]** The chart coordinate of a chart member: the values of its retraction on
the complementary coordinate vectors. The `ofBijective` composite is spelled out in
full — an `_` placeholder there (or routing through `retractionEquivMatrix` /
`chartToRetraction`'s subtype) makes elaboration whnf-explode (banked wave-3 finding);
the explicit form is cheap. -/
noncomputable def chartMatrix {A' : Type w''} [CommRing A'] (n : ℕ) (ι : Fin k ↪ Fin n)
    (N : G(k, (Fin n → A'); A'))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A')) N) :
    {j : Fin n // j ∉ Set.range ι} → Fin k → A' :=
  fun j => (LinearEquiv.ofBijective
      (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A'))) h).symm
    (N.toSubmodule.mkQ (Pi.single j.1 1))

/- `coordMap` unfolds to `Fintype.linearCombination`; while it is reducible, `whnf`/`isDefEq`
evaluates the coordinate combination (`Pi.single`/`Fin`-decidability) every time a
`chartMatrix … = …` equation is elaborated — which blows past the heartbeat limit, since
`chartMatrix` reduces to a `LinearEquiv.ofBijective … |>.symm` applied to such a combination.
Marking `coordMap` irreducible *after* all of its uses above keeps the seam opaque, so
chart-coordinate equations elaborate cheaply; the proofs below still unfold it where needed
through the interface lemmas `coordMap_single` / `retraction_comp_coordMap`. -/
attribute [irreducible] coordMap

unseal coordMap in
/-- Sealed-interface unfolding for `coordMap` — deliberately NOT `@[simp]` (re-exposing
it to simp would reintroduce the theorem-goal evaluation explosion the seal prevents);
use surgically. -/
lemma coordMap_apply {x : Fin k → M} (c : Fin k → R) :
    coordMap x c = ∑ i, c i • x i := by
  simp [coordMap, Fintype.linearCombination_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **[GR-B2n-4]** Kernel-uniqueness for the chart coordinate: *any* retraction `ψ` of the
coordinate sub-basis `Pi.single ∘ ι` whose kernel contains `N` reads off the chart matrix of `N`
on the complementary coordinate vectors. This is the workhorse behind naturality (and wave-3
gluing): a chart member's coordinate does not depend on which retraction realises it. -/
theorem chartMatrix_eq_of_retraction {A' : Type w''} [CommRing A'] (n : ℕ) (ι : Fin k ↪ Fin n)
    (N : G(k, (Fin n → A'); A')) (h : IsChartAt (fun i => Pi.single (ι i) (1 : A')) N)
    (ψ : (Fin n → A') →ₗ[A'] (Fin k → A'))
    (hψ1 : ∀ i, ψ (Pi.single (ι i) 1) = Pi.single i 1)
    (hψ2 : N.toSubmodule ≤ LinearMap.ker ψ) :
    chartMatrix n ι N h = fun j => ψ (Pi.single j.1 1) := by
  funext j
  unfold chartMatrix
  set E := LinearEquiv.ofBijective
    (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A'))) h with hE
  have hbar : ∀ c, Submodule.liftQ N.toSubmodule ψ hψ2 (E c) = c := by
    intro c
    have hEc : E c = N.toSubmodule.mkQ (coordMap (fun i => Pi.single (ι i) (1 : A')) c) := by
      rw [hE, LinearEquiv.ofBijective_apply, LinearMap.comp_apply]
    rw [hEc, Submodule.mkQ_apply, Submodule.liftQ_apply, retraction_comp_coordMap _ hψ1]
  have key := hbar (E.symm (N.toSubmodule.mkQ (Pi.single j.1 1)))
  rw [LinearEquiv.apply_symm_apply] at key
  rw [← key]
  exact N.toSubmodule.liftQ_apply ψ (Pi.single j.1 1)

set_option backward.isDefEq.respectTransparency false in
/-- **[GR-B2n-4]** Naturality of the chart coordinate under `normMap`: the chart matrix of
`normMap f N` is the entrywise-`f` image of the chart matrix of `N`. The retraction realising
`normMap f N` is the base change of the one realising `N` (transported through `piScalarRight`),
so its kernel is `(normMap f N).toSubmodule` by construction and its values are the `f`-images of
`N`'s coordinates; `chartMatrix_eq_of_retraction` then identifies it with `chartMatrix`. -/
theorem chartMatrix_normMap (n : ℕ) (ι : Fin k ↪ Fin n) (f : A →ₐ[R] B)
    (N : G(k, (Fin n → A); A)) (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    chartMatrix n ι (normMap n f N) (isChartAt_normMap n ι f N h)
      = fun j i => f (chartMatrix n ι N h j i) := by
  classical
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq R A B)
  set qA := TensorProduct.piScalarRight R A A (Fin n) with hqA
  set qB := TensorProduct.piScalarRight R B B (Fin n) with hqB
  set sk := TensorProduct.piScalarRight A B B (Fin k) with hsk
  set P : G(k, A ⊗[R] (Fin n → R); A) := congr qA.symm N with hP_def
  have htuple : (⇑qA.symm ∘ fun i => Pi.single (ι i) (1 : A))
      = fun i => (1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R) := by
    funext i
    exact TensorProduct.piScalarRight_symm_single R A A (Fin n) 1 (ι i)
  have hP : IsChartAt (fun i => (1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R)) P := by
    rw [← htuple]; exact (isChartAt_congr qA.symm _ N).mpr h
  set E_At := LinearEquiv.ofBijective
    (P.toSubmodule.mkQ ∘ₗ coordMap (fun i => (1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))) hP
    with hE_At
  set chartEA := LinearEquiv.ofBijective
    (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) h with hchartEA
  set ψf : (Fin n → B) →ₗ[B] (Fin k → B) :=
    sk.toLinearMap ∘ₗ E_At.symm.toLinearMap.baseChange B ∘ₗ
      baseChangeMkQ B P.toSubmodule ∘ₗ qB.symm.toLinearMap with hψf
  -- application lemma for the `A`-side chart equivalence
  have hchartEA_apply : ∀ x, chartEA x
      = N.toSubmodule.mkQ (coordMap (fun i => Pi.single (ι i) (1 : A)) x) := by
    intro x; rw [hchartEA, LinearEquiv.ofBijective_apply, LinearMap.comp_apply]
  -- `sk (1 ⊗ₜ v)` is the entrywise-`f` image of `v`
  have hsk_val : ∀ v : Fin k → A, sk ((1 : B) ⊗ₜ[A] v) = fun l => f (v l) := by
    intro v; funext l
    rw [hsk, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    show (v l) • (1 : B) = f (v l)
    rw [Algebra.smul_def, mul_one]
    rfl
  -- the value of `ψf` on a coordinate vector, through the base-change square
  have hbcmkq : ∀ (m : Fin n → R), baseChangeMkQ B P.toSubmodule ((1 : B) ⊗ₜ[R] m)
      = (1 : B) ⊗ₜ[A] P.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m) := by
    intro m; simp [baseChangeMkQ]
  have hchain : ∀ (j : Fin n), ψf (Pi.single j 1)
      = sk ((1 : B) ⊗ₜ[A]
          E_At.symm (P.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R)))) := by
    intro j
    rw [hψf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [TensorProduct.piScalarRight_symm_single, hbcmkq, LinearMap.baseChange_tmul]
    rfl
  -- the tensor chart tuple is the `qA.symm`-transport of the coordinate combination
  have hcoordP : coordMap (fun i => (1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R))
      = qA.symm.toLinearMap ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A)) := by
    refine (Pi.basisFun A (Fin k)).ext fun i => ?_
    rw [Pi.basisFun_apply, coordMap_single, LinearMap.comp_apply, coordMap_single]
    exact (TensorProduct.piScalarRight_symm_single R A A (Fin n) 1 (ι i)).symm
  -- reading off a coordinate commutes with the `congr qA.symm` transport
  have hconn : ∀ (m : Fin n → A), E_At.symm (P.toSubmodule.mkQ (qA.symm m))
      = chartEA.symm (N.toSubmodule.mkQ m) := by
    intro m
    rw [LinearEquiv.symm_apply_eq, hE_At, LinearEquiv.ofBijective_apply, LinearMap.comp_apply,
      hcoordP, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    simp only [LinearEquiv.coe_coe]
    rw [← map_sub, hP_def, congr_toSubmodule]
    apply Submodule.mem_map_of_mem
    refine (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp ?_
    rw [← Submodule.mkQ_apply, map_sub, ← hchartEA_apply, LinearEquiv.apply_symm_apply, sub_self]
  -- `ψf` is a retraction of the coordinate sub-basis (`hψ1`)
  have hR : ∀ i, ψf (Pi.single (ι i) 1) = Pi.single i 1 := by
    intro i
    rw [hchain (ι i)]
    have hEs : E_At.symm (P.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] (Pi.single (ι i) 1 : Fin n → R)))
        = Pi.single i 1 := by
      rw [← TensorProduct.piScalarRight_symm_single R A A (Fin n) 1 (ι i), hconn,
        LinearEquiv.symm_apply_eq, hchartEA_apply, coordMap_single]
    rw [hEs, hsk_val]
    funext l; simp [Pi.single_apply, apply_ite f]
  -- `ψf` reads off the entrywise-`f` image of `N`'s coordinates
  have hV : ∀ j : {j : Fin n // j ∉ Set.range ι},
      ψf (Pi.single j.1 1) = fun l => f (chartMatrix n ι N h j l) := by
    intro j
    rw [hchain j.1]
    have hval : E_At.symm (P.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] (Pi.single j.1 1 : Fin n → R)))
        = chartMatrix n ι N h j := by
      rw [← TensorProduct.piScalarRight_symm_single R A A (Fin n) 1 j.1, hconn]
      show chartEA.symm (N.toSubmodule.mkQ (Pi.single j.1 1)) = _
      unfold chartMatrix
      rfl
    rw [hval, hsk_val]
  -- `ψf` factors through `baseChangeMkQ`, so its kernel contains
  -- `(normMap f N).toSubmodule` (`hψ2`)
  have hK : (normMap n f N).toSubmodule ≤ LinearMap.ker ψf := by
    have hnm : (normMap n f N).toSubmodule
        = Submodule.map qB.toLinearMap (baseChangeMkQ B P.toSubmodule).ker := by
      show (congr qB (P.map f)).toSubmodule = _
      rw [congr_toSubmodule, map_toSubmodule f P]
    rw [hnm, Submodule.map_le_iff_le_comap]
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mem_ker, hψf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [LinearMap.mem_ker.mp hz, map_zero, map_zero]
  refine (chartMatrix_eq_of_retraction n ι (normMap n f N)
    (isChartAt_normMap n ι f N h) ψf hR hK).trans ?_
  funext j
  exact hV j

end NormalizedFunctor

section Universal

open MvPolynomial

variable (R)

/-- The generic retraction over the chart coordinate ring: the coordinate sub-basis
goes to the standard basis, the complementary coordinates to the generic matrix
variables. -/
noncomputable def genericRetraction (n : ℕ) (ι : Fin k ↪ Fin n) :
    (Fin n → MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R)
      →ₗ[MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R]
      (Fin k → MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R) := by
  classical
  exact (Pi.basisFun (MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R)
    (Fin n)).constr ℕ (fun j =>
      if h : j ∈ Set.range ι then
        Pi.single ((Equiv.ofInjective ι ι.injective).symm ⟨j, h⟩) 1
      else fun i => X (⟨j, h⟩, i))

lemma genericRetraction_single_mem (n : ℕ) (ι : Fin k ↪ Fin n) (i₀ : Fin k) :
    genericRetraction R n ι (Pi.single (ι i₀) 1) = Pi.single i₀ 1 := by
  classical
  rw [genericRetraction, ← Pi.basisFun_apply, Basis.constr_basis, dif_pos ⟨i₀, rfl⟩]
  congr 1
  exact Equiv.ofInjective_symm_apply ι.injective i₀

/-- **[GR-G seed]** The tautological (universal) chart member over the chart coordinate
ring: the kernel of the generic retraction. Its chart matrix is the generic matrix. -/
noncomputable def universalChartMember (n : ℕ) (ι : Fin k ↪ Fin n) :
    {N : G(k, (Fin n → MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R);
        MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R) //
      IsChartAt (fun i => Pi.single (ι i) 1) N} :=
  retractionToChart _ ⟨genericRetraction R n ι,
    fun i => genericRetraction_single_mem R n ι i⟩

/-- The universal chart member's coordinate is the generic matrix. -/
lemma chartMatrix_universalChartMember (n : ℕ) (ι : Fin k ↪ Fin n) :
    chartMatrix n ι (universalChartMember R n ι).1 (universalChartMember R n ι).2
      = fun j i => X (j, i) := by
  classical
  rw [chartMatrix_eq_of_retraction n ι _ _ (genericRetraction R n ι)
    (fun i => genericRetraction_single_mem R n ι i) le_rfl]
  funext j i
  rw [genericRetraction, ← Pi.basisFun_apply, Basis.constr_basis, dif_neg j.2]

end Universal

end Module.Grassmannian

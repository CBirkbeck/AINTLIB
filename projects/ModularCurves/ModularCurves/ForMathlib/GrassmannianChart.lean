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

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP). Waves 2–3 (chart functors, covering, gluing, T-points) are boarded there.
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
  sorry

section Covering

open TensorProduct

universe w'

variable {A : Type w'} [CommRing A] [Algebra R A]

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
  sorry

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
  sorry

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

end Module.Grassmannian

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.KrullDimQuotientSpan
import ModularCurves.ForMathlib.MvPolynomialMaximalHeight
import ModularCurves.ForMathlib.SmoothCotangentPrincipal

/-!
# A curve smooth over an algebraically closed field has domain local rings (T-SMOOTH-REG)

Assembling the four bricks:

* **brick 2** (`MvPolynomialMaximalHeight`) — a maximal ideal of `k[x_i : i ∈ ι]` has height
  `≥ #ι`;
* **brick 3'** (`KrullDimQuotientSpan`) — cutting by `#σ` equations drops the height of a
  prime by at most `#σ`;
* **brick 4** (`SmoothCotangentPrincipal`) — at a `k`-rational point of a formally smooth
  algebra with `rank Ω ≤ 1`, the maximal ideal satisfies `𝔪 ≤ (x) + 𝔪²`;
* **`ForMathlib/RegularLocalDomain`** — a regular local ring is a domain (Matsumura 14.3).

Together: for `A` standard smooth of relative dimension one over an algebraically closed
field `k`, every localization `A_𝔭` is a **regular local domain**. Geometrically: a smooth
curve over `k̄` is locally irreducible, which is the missing algebraic leaf of
`yRho_geometricallyIrreducible` (`ModularCurve/IrreducibilityScoping.lean`).
-/

universe u

open IsLocalRing

namespace ModularCurves

section Height

/-- **(brick 5a)** At a maximal ideal of a `k`-algebra standard smooth of relative
dimension one (`k` algebraically closed), the height is at least one: pull back to the
polynomial ring of a submersive presentation, where the height is the number of variables
(brick 2), and lose at most the number of relations (brick 3'). -/
theorem one_le_height_of_isMaximal (k : Type u) [Field k] [IsAlgClosed k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] : 1 ≤ 𝔪.height := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ :=
    (‹Algebra.IsStandardSmoothOfRelativeDimension 1 k A›).out
  haveI : Finite σ := hσ
  haveI : Finite ι := hι
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype σ := Fintype.ofFinite σ
  -- the presentation surjection and its kernel
  set f : MvPolynomial ι k →+* A := algebraMap P.Ring A with hf
  have hsurj : Function.Surjective f := P.algebraMap_surjective
  have hker : RingHom.ker f = Ideal.span (Set.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  set s : Finset (MvPolynomial ι k) := Finset.image P.relation Finset.univ with hs
  have hspan : Ideal.span (↑s : Set (MvPolynomial ι k)) = RingHom.ker f := by
    rw [hker, hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hscard : s.card ≤ Fintype.card σ := by
    rw [hs]
    simpa using Finset.card_image_le (s := (Finset.univ : Finset σ)) (f := P.relation)
  -- pull `𝔪` back
  set 𝔮 : Ideal (MvPolynomial ι k) := 𝔪.comap f with h𝔮
  haveI : 𝔮.IsMaximal := Ideal.comap_isMaximal_of_surjective f hsurj
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  have hlow : (Fintype.card ι : ℕ∞) ≤ 𝔮.height := card_le_height_of_isMaximal ‹𝔮.IsMaximal›
  have hup : 𝔮.height ≤ 𝔪.height + s.card :=
    height_comap_le_height_add_card_of_surjective f hsurj hspan 𝔪
  -- `#ι = #σ + 1`
  have hcards : Fintype.card σ ≤ Fintype.card ι := Fintype.card_le_of_injective _ P.map_inj
  have hdim' : Fintype.card ι = Fintype.card σ + 1 := by
    have hd : P.dimension = Nat.card ι - Nat.card σ := rfl
    rw [hdim] at hd
    simp only [Nat.card_eq_fintype_card] at hd
    omega
  -- combine
  have hchain : (Fintype.card ι : ℕ∞) ≤ 𝔪.height + (Fintype.card σ : ℕ∞) :=
    le_trans hlow (le_trans hup (by gcongr))
  rw [hdim'] at hchain
  push_cast at hchain
  by_contra hcon
  have hzero : 𝔪.height = 0 := Order.lt_one_iff.mp (not_le.mp hcon)
  rw [hzero, zero_add] at hchain
  have hnat : (Fintype.card σ : ℕ) + 1 ≤ (Fintype.card σ : ℕ) := by exact_mod_cast hchain
  omega

end Height

section RationalPoint

/-- **(brick 5b)** Over an algebraically closed field, a maximal ideal of a finite-type
algebra is the kernel of a `k`-point: `A ⧸ 𝔪 ≃ₐ[k] k` by Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`) plus algebraic closedness. -/
noncomputable def residueAlgEquiv (k : Type u) [Field k] [IsAlgClosed k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    (A ⧸ 𝔪) ≃ₐ[k] k :=
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite k (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ 𝔪)
  haveI : Algebra.IsIntegral k (A ⧸ 𝔪) := Algebra.IsIntegral.of_finite k (A ⧸ 𝔪)
  (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ 𝔪))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ 𝔪))).symm

/-- **(brick 5b)** The `k`-point itself. -/
noncomputable def pointAlgHom (k : Type u) [Field k] [IsAlgClosed k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    A →ₐ[k] k :=
  (residueAlgEquiv k 𝔪).toAlgHom.comp (Ideal.Quotient.mkₐ k 𝔪)

@[simp] theorem ker_pointAlgHom (k : Type u) [Field k] [IsAlgClosed k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    RingHom.ker (pointAlgHom k 𝔪).toRingHom = 𝔪 := by
  ext a
  simp only [RingHom.mem_ker, pointAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.comp_apply, AlgEquiv.coe_algHom, Ideal.Quotient.mkₐ_eq_mk,
    EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end RationalPoint

section Regular

/-- **(T-SMOOTH-REG brick 5 ★★)** The localization of a `k`-algebra standard smooth of
relative dimension one at a maximal ideal is a **regular local ring** (`k` algebraically
closed): its maximal ideal is principal (brick 4 + Nakayama) and its dimension is at least
one (brick 5a). -/
theorem isRegularLocalRing_localization_atPrime (k : Type u) [Field k] [IsAlgClosed k]
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime 𝔪) := by
  classical
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  haveI hss : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => h𝔪.ne_top (by
    rw [Ideal.eq_top_iff_one, ← h]; exact Submodule.zero_mem _)⟩⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  -- the `k`-point at `𝔪`
  letI : Algebra A k := (pointAlgHom k 𝔪).toRingHom.toAlgebra
  haveI : IsScalarTower k A k :=
    IsScalarTower.of_algebraMap_eq fun c => ((pointAlgHom k 𝔪).commutes c).symm
  have hkerm : RingHom.ker (algebraMap A k) = 𝔪 := ker_pointAlgHom k 𝔪
  -- brick 4: `𝔪 ≤ (x) + 𝔪²`
  obtain ⟨x, hx, hle⟩ := exists_le_span_singleton_sup_sq k A
    (le_of_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1))
  rw [hkerm] at hx hle
  -- transport to the localization
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl (Localization.AtPrime 𝔪) inferInstance
  set x' : Localization.AtPrime 𝔪 := algebraMap A (Localization.AtPrime 𝔪) x with hx'
  have hmax : 𝔪.map (algebraMap A (Localization.AtPrime 𝔪)) =
      maximalIdeal (Localization.AtPrime 𝔪) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 (Localization.AtPrime 𝔪)
  have hmaple : maximalIdeal (Localization.AtPrime 𝔪) ≤
      Ideal.span {x'} ⊔ (maximalIdeal (Localization.AtPrime 𝔪)) ^ 2 := by
    rw [← hmax]
    refine le_trans (Ideal.map_mono hle) ?_
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, hmax, Set.image_singleton, ← hx']
  -- Nakayama
  have hjac : maximalIdeal (Localization.AtPrime 𝔪) ≤
      (⊥ : Ideal (Localization.AtPrime 𝔪)).jacobson :=
    le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm
  have hsmul : maximalIdeal (Localization.AtPrime 𝔪) ≤ Ideal.span {x'} ⊔
      (maximalIdeal (Localization.AtPrime 𝔪)) • (maximalIdeal (Localization.AtPrime 𝔪)) := by
    rwa [smul_eq_mul, ← sq]
  have hprin : maximalIdeal (Localization.AtPrime 𝔪) ≤ Ideal.span {x'} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hjac hsmul
  -- hence `spanFinrank ≤ 1`
  have hxL : x' ∈ maximalIdeal (Localization.AtPrime 𝔪) := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hx
  have heq : maximalIdeal (Localization.AtPrime 𝔪) =
      Ideal.span ({x'} : Set (Localization.AtPrime 𝔪)) :=
    le_antisymm hprin (Ideal.span_le.mpr (by simpa using hxL))
  have hsf : (maximalIdeal (Localization.AtPrime 𝔪)).spanFinrank ≤ 1 := by
    rw [heq]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.finite_singleton x')) ?_
    simp
  -- dimension at least one
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime 𝔪) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (Localization.AtPrime 𝔪)]
    exact_mod_cast one_le_height_of_isMaximal k 𝔪
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    (Localization.AtPrime 𝔪) (le_trans ?_ hdim)
  exact_mod_cast Nat.cast_le (α := ℕ∞).mpr hsf

/-- **(T-SMOOTH-REG ★★★)** Hence the local ring at a maximal ideal is a **domain**
(`ForMathlib/RegularLocalDomain`, Matsumura 14.3). -/
theorem isDomain_localization_atPrime_of_isMaximal (k : Type u) [Field k] [IsAlgClosed k]
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (𝔪 : Ideal A) [𝔪.IsMaximal] : IsDomain (Localization.AtPrime 𝔪) :=
  letI := isRegularLocalRing_localization_atPrime k 𝔪
  IsRegularLocalRing.isDomain _

end Regular

end ModularCurves

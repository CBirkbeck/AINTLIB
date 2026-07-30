/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.TateBallResidue
import «Adic spaces».FJP.CDVFNoetherian
import «Adic spaces».NoetherianGDomain
import «Adic spaces».GeometricSeries
import «Adic spaces».Bounded

/-!
# The affinoid Nullstellensatz for Tate algebras over a noetherian unit ball

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaves 3/6/8/9/11.)  For
`K` with noetherian unit ball and a uniformizer `ϖ`, every maximal ideal `𝔪`
of `K⟨T₁,…,T_m⟩ = P K m` has residue field finite over `K`.  The route is the
DVR integral model: `B := T°/(𝔪 ∩ T°)` is a noetherian domain with `B[1/ϖ]`
the residue field; the G-domain lemma makes `B/ϖB` zero-dimensional and of
finite type over the residue ring of `𝒪_K`, hence finite; topological
Nakayama lifts finiteness to `B`, and localization finishes.
-/

@[expose] public section

open scoped Classical

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (ϖ : FiniteJetOver.Uniformizer K) {m : ℕ}

/-- The scaling constant of the integral Tate algebra at a uniformizer. -/
noncomputable abbrev piBall : ↥(unitBall (P K m)) :=
  tConstBall (E := K) (m := m) ϖ.val ϖ.norm_val_lt_one

theorem piBall_coe :
    ((piBall (m := m) ϖ) : P K m) = polyToP (MvPolynomial.C ϖ.val) := by
  show polyBall (tConstPoly (E := K) (m := m) ϖ.val ϖ.norm_val_lt_one) = _
  rw [tConstPoly, polyBall, RingHom.comp_apply, MvPolynomial.map_C]
  rfl

/-- **Leaf 3 (extracted from `Uniformizer.isNoetherianRing_P`)**: the Tate
algebra is the localization of its unit ball at the powers of the scaling
constant. -/
theorem isLocalization_powers_piBall :
    letI : Algebra ↥(unitBall (P K m)) (P K m) :=
      (unitBall (P K m)).subtype.toAlgebra
    IsLocalization (Submonoid.powers (piBall (m := m) ϖ)) (P K m) := by
  letI : Algebra ↥(unitBall (P K m)) (P K m) :=
    (unitBall (P K m)).subtype.toAlgebra
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    show IsUnit ((((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m)))) : P K m)
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact (isUnit_tP ϖ.val ϖ.isUnit_val).pow k
  · intro F
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖ϖ.val‖ ^ n * ‖F‖ ≤ 1 := by
      rcases eq_or_ne ‖F‖ 0 with h0 | h0
      · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
      · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm h0)
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos)
          ϖ.norm_val_lt_one
        exact ⟨n, by
          calc ‖ϖ.val‖ ^ n * ‖F‖ ≤ ‖F‖⁻¹ * ‖F‖ :=
                mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
    have hmem : ‖polyToP (MvPolynomial.C ϖ.val) ^ n * F‖ ≤ 1 := by
      rw [norm_pow_mul_of_scale (E := P K m)
        (fun G => by
          rw [norm_tP ϖ.val ϖ.norm_val_mul]
          exact norm_tP_mul ϖ.val ϖ.norm_val_mul G) n,
        norm_tP ϖ.val ϖ.norm_val_mul]
      exact hn
    refine ⟨(⟨polyToP (MvPolynomial.C ϖ.val) ^ n * F, hmem⟩,
      ⟨(piBall (m := m) ϖ) ^ n, n, rfl⟩), ?_⟩
    show F * ((((piBall (m := m) ϖ) ^ n : ↥(unitBall (P K m)))) : P K m) =
      polyToP (MvPolynomial.C ϖ.val) ^ n * F
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact mul_comm F _
  · intro x y h
    refine ⟨1, ?_⟩
    have hinj : Function.Injective ((unitBall (P K m)).subtype) :=
      Subtype.val_injective
    rw [hinj h]

section MaximalIdeal

variable (𝔪 : Ideal (P K m)) [h𝔪 : 𝔪.IsMaximal]

/-- The integral contraction of a maximal ideal. -/
noncomputable abbrev ballContraction : Ideal ↥(unitBall (P K m)) :=
  𝔪.comap (unitBall (P K m)).subtype

/-- The integral model of the residue field. -/
noncomputable abbrev IntegralModel : Type _ :=
  ↥(unitBall (P K m)) ⧸ ballContraction (m := m) 𝔪

instance : (ballContraction (m := m) 𝔪).IsPrime :=
  Ideal.comap_isPrime _ _

noncomputable instance : CommRing (IntegralModel (m := m) 𝔪) :=
  Ideal.Quotient.commRing _

instance : IsDomain (IntegralModel (m := m) 𝔪) :=
  Ideal.Quotient.isDomain _

include ϖ in
theorem isNoetherianRing_integralModel
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsNoetherianRing (IntegralModel (m := m) 𝔪) := by
  haveI hball : IsNoetherianRing ↥(unitBall (P K m)) :=
    FiniteJetOver.Uniformizer.isNoetherianRing_unitBall_P ϖ hK₀ m
  exact isNoetherianRing_of_surjective _ _
    (Ideal.Quotient.mk (ballContraction (m := m) 𝔪))
    Ideal.Quotient.mk_surjective

end MaximalIdeal

end FiniteJet.GraphKoszul

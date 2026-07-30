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

/-- A ring isomorphic to a field is a field. -/
theorem isField_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : IsField B) : IsField A := by
  refine ⟨?_, mul_comm, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hB.exists_pair_ne
    exact ⟨e.symm x, e.symm y, fun h => hxy (by
      have := congrArg e h
      simpa using this)⟩
  · intro a ha
    have hea : e a ≠ 0 := fun h0 => ha (by
      have := congrArg e.symm h0
      simpa using this)
    obtain ⟨b, hb⟩ := hB.mul_inv_cancel hea
    refine ⟨e.symm b, ?_⟩
    have h1 : e (a * e.symm b) = 1 := by
      rw [map_mul, RingEquiv.apply_symm_apply, hb]
    have := congrArg e.symm h1
    simpa using this

theorem piBall_notMem_ballContraction :
    piBall (m := m) ϖ ∉ ballContraction (m := m) 𝔪 := by
  intro hmem
  have hmem' : (unitBall (P K m)).subtype (piBall (m := m) ϖ) ∈ 𝔪 := hmem
  have hunit : IsUnit ((unitBall (P K m)).subtype (piBall (m := m) ϖ)) := by
    show IsUnit ((piBall (m := m) ϖ) : P K m)
    rw [piBall_coe]
    exact isUnit_tP ϖ.val ϖ.isUnit_val
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem' hunit)

/-- The scaling constant in the integral model. -/
noncomputable abbrev piBar : IntegralModel (m := m) 𝔪 :=
  Ideal.Quotient.mk _ (piBall (m := m) ϖ)

theorem piBar_ne_zero : piBar (m := m) ϖ 𝔪 ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact piBall_notMem_ballContraction ϖ 𝔪

/-- The scaling constant is not a unit of the integral model: an inverse would
exhibit `1 - ϖ·g ∈ 𝔪` with `‖ϖ·g‖ < 1`, contradicting the Neumann series. -/
theorem not_isUnit_piBar : ¬ IsUnit (piBar (m := m) ϖ 𝔪) := by
  rintro ⟨u, hu⟩
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    ((↑u⁻¹ : IntegralModel (m := m) 𝔪))
  have h1 : Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
      (1 - piBall (m := m) ϖ * g) = 0 := by
    rw [map_sub, map_one, map_mul, hg]
    rw [show Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
        (piBall (m := m) ϖ) = piBar (m := m) ϖ 𝔪 from rfl, ← hu]
    rw [Units.mul_inv]
    exact sub_self 1
  have h2 : (1 - piBall (m := m) ϖ * g) ∈ ballContraction (m := m) 𝔪 :=
    Ideal.Quotient.eq_zero_iff_mem.mp h1
  have h2' : (unitBall (P K m)).subtype (1 - piBall (m := m) ϖ * g) ∈ 𝔪 := h2
  have h3 : IsUnit ((unitBall (P K m)).subtype
      (1 - piBall (m := m) ϖ * g)) := by
    have h4 : (unitBall (P K m)).subtype (1 - piBall (m := m) ϖ * g) =
        1 - ((piBall (m := m) ϖ : P K m)) * ((g : ↥(unitBall (P K m))) :
          P K m) := rfl
    rw [h4]
    have hnorm : ‖((piBall (m := m) ϖ : P K m)) * ((g :
        ↥(unitBall (P K m))) : P K m)‖ < 1 := by
      refine lt_of_le_of_lt (norm_mul_le _ _) ?_
      have hπ : ‖((piBall (m := m) ϖ : P K m))‖ = ‖ϖ.val‖ := by
        rw [piBall_coe]
        exact norm_tP ϖ.val ϖ.norm_val_mul
      have hgle : ‖((g : ↥(unitBall (P K m))) : P K m)‖ ≤ 1 :=
        (mem_unitBall_iff _ _).mp g.2
      calc ‖((piBall (m := m) ϖ : P K m))‖ *
            ‖((g : ↥(unitBall (P K m))) : P K m)‖
          ≤ ‖((piBall (m := m) ϖ : P K m))‖ * 1 :=
            mul_le_mul_of_nonneg_left hgle (norm_nonneg _)
        _ = ‖ϖ.val‖ := by rw [mul_one, hπ]
        _ < 1 := ϖ.norm_val_lt_one
    have hnil : IsTopologicallyNilpotent
        (((piBall (m := m) ϖ : P K m)) * ((g : ↥(unitBall (P K m))) :
          P K m)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    exact hnil.isUnit_one_sub
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h2' h3)

/-- The integral model maps to the residue field. -/
noncomputable def modelToResidue :
    IntegralModel (m := m) 𝔪 →+* (P K m ⧸ 𝔪) :=
  Ideal.quotientMap 𝔪 (unitBall (P K m)).subtype le_rfl

theorem modelToResidue_mk (b : ↥(unitBall (P K m))) :
    modelToResidue (m := m) 𝔪 (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk 𝔪 ((unitBall (P K m)).subtype b) := rfl

/-- **The residue field is the localization of the integral model at the
scaling constant** ([hrw-decomposition] Tate leaf 6): units, surjectivity via
the ball localization, and injectivity mod the contraction. -/
theorem isLocalization_residue :
    letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
      (modelToResidue (m := m) 𝔪).toAlgebra
    IsLocalization (Submonoid.powers (piBar (m := m) ϖ 𝔪))
      (P K m ⧸ 𝔪) := by
  letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
    (modelToResidue (m := m) 𝔪).toAlgebra
  letI : Algebra ↥(unitBall (P K m)) (P K m) :=
    (unitBall (P K m)).subtype.toAlgebra
  haveI hloc : IsLocalization (Submonoid.powers (piBall (m := m) ϖ))
      (P K m) := isLocalization_powers_piBall ϖ
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    have h5 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        ((piBar (m := m) ϖ 𝔪) ^ k) =
        Ideal.Quotient.mk 𝔪
          (((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m))) : P K m) := by
      rw [map_pow]
      rw [show algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
          (piBar (m := m) ϖ 𝔪) =
        Ideal.Quotient.mk 𝔪 ((piBall (m := m) ϖ : ↥(unitBall (P K m))) :
          P K m) from rfl]
      rw [← map_pow]
      rw [show ((((piBall (m := m) ϖ) : ↥(unitBall (P K m))) : P K m)) ^ k =
        (((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m))) : P K m) from
        (SubmonoidClass.coe_pow _ _).symm]
    rw [h5]
    refine IsUnit.map _ ?_
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact (isUnit_tP ϖ.val ϖ.isUnit_val).pow k
  · intro z
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, sPow⟩, hb⟩ := IsLocalization.surj
      (Submonoid.powers (piBall (m := m) ϖ)) (S := P K m) F
    obtain ⟨n, hn⟩ := sPow.2
    refine ⟨(Ideal.Quotient.mk _ b, ⟨(piBar (m := m) ϖ 𝔪) ^ n, n, rfl⟩), ?_⟩
    have h6 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        ((piBar (m := m) ϖ 𝔪) ^ n) =
        Ideal.Quotient.mk 𝔪 ((sPow : ↥(unitBall (P K m))) : P K m) := by
      rw [map_pow]
      rw [show algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
          (piBar (m := m) ϖ 𝔪) =
        Ideal.Quotient.mk 𝔪 ((piBall (m := m) ϖ : ↥(unitBall (P K m))) :
          P K m) from rfl]
      rw [← map_pow, ← hn]
      rw [show ((((piBall (m := m) ϖ) : ↥(unitBall (P K m))) : P K m)) ^ n =
        (((piBall (m := m) ϖ) ^ n : ↥(unitBall (P K m))) : P K m) from
        (SubmonoidClass.coe_pow _ _).symm]
    have h7 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk 𝔪 ((b : ↥(unitBall (P K m))) : P K m) := rfl
    rw [h6, h7]
    show Ideal.Quotient.mk 𝔪 F * Ideal.Quotient.mk 𝔪 _ = _
    rw [← map_mul]
    have hb' : F * ((sPow : ↥(unitBall (P K m))) : P K m) =
        ((b : ↥(unitBall (P K m))) : P K m) := hb
    rw [hb']
  · intro x y h
    obtain ⟨bx, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨by', rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨1, ?_⟩
    have h8 : Ideal.Quotient.mk 𝔪 ((bx : ↥(unitBall (P K m))) : P K m) =
        Ideal.Quotient.mk 𝔪 ((by' : ↥(unitBall (P K m))) : P K m) := h
    have h9 : ((bx : ↥(unitBall (P K m))) : P K m) -
        ((by' : ↥(unitBall (P K m))) : P K m) ∈ 𝔪 :=
      Ideal.Quotient.eq.mp h8
    have h10 : bx - by' ∈ ballContraction (m := m) 𝔪 := h9
    rw [OneMemClass.coe_one, one_mul, one_mul]
    exact Ideal.Quotient.eq.mpr h10

/-- **The localization of the integral model away from the scaling constant is
a field** — it is the residue field of the maximal ideal. -/
theorem isField_localization_away_piBar :
    IsField (Localization.Away (piBar (m := m) ϖ 𝔪)) := by
  letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
    (modelToResidue (m := m) 𝔪).toAlgebra
  haveI hres := isLocalization_residue (m := m) ϖ 𝔪
  letI : Field (P K m ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have e := IsLocalization.algEquiv
    (Submonoid.powers (piBar (m := m) ϖ 𝔪))
    (Localization.Away (piBar (m := m) ϖ 𝔪)) (P K m ⧸ 𝔪)
  exact isField_of_ringEquiv e.toRingEquiv (Field.toIsField _)

end MaximalIdeal

end FiniteJet.GraphKoszul

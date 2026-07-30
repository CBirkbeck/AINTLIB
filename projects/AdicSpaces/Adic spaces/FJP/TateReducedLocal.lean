/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.TateWallFactors
import «Adic spaces».SemilocalFibre
import «Adic spaces».FlatCompletion
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Completed local rings of Tate algebras at maximal ideals are reduced

([hrw-decomposition] endgame block A.) Over any finite normal complete
ultrametric extension `L/K` receiving the residue field of a maximal `𝔮` of
`Q = P K m`, every maximal over `𝔮` in `P L m` is a point ideal (factor
identification), and the levelwise family through the faithfully flat base
change, the fibre factors and the Taylor level equivalences is cofinally
injective into a product of polynomial adic completions — which are domains.
The theorem is stated over an abstract such `L`; the normal closure
instantiation is a corollary.
-/

@[expose] public section

open scoped Classical NormedField Valued

open Filter IntermediateField FiniteJet.SpectralExtension

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [Algebra K L] [FiniteDimensional K L] [Normal K L]
variable {m : ℕ}

section BlockA

variable (hext : ∀ c : K, ‖algebraMap K L c‖ = ‖c‖)
variable (𝔮 : Ideal (P K m)) [h𝔮 : 𝔮.IsMaximal]

include hext in
/-- The fibre ring of the pushed maximal ideal is Artinian. -/
theorem isArtinianRing_fibre :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    IsArtinianRing (P L m ⧸ Ideal.map (mapP (m := m) hext) 𝔮) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  letI : Field (P K m ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  haveI hfin : Module.Finite (P K m) (P L m) :=
    module_finite_mapP (m := m) hext
  letI : Algebra (P K m ⧸ 𝔮)
      (P L m ⧸ Ideal.map (mapP (m := m) hext) 𝔮) :=
    (Ideal.quotientMap (Ideal.map (mapP (m := m) hext) 𝔮)
      (mapP (m := m) hext) Ideal.le_comap_map).toAlgebra
  haveI h2 : Module.Finite (P K m ⧸ 𝔮)
      (P L m ⧸ Ideal.map (mapP (m := m) hext) 𝔮) := by
    obtain ⟨T, hT⟩ := hfin.fg_top
    refine ⟨⟨T.image (Ideal.Quotient.mk
      (Ideal.map (mapP (m := m) hext) 𝔮)), ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : b ∈ Submodule.span (P K m) (T : Set (P L m)) := by
      rw [hT]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro t ht
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht))
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv
      rw [map_add]
      exact Submodule.add_mem _ hu hv
    · intro a x _ hx
      have h5 : Ideal.Quotient.mk (Ideal.map (mapP (m := m) hext) 𝔮)
          (a • x) = (Ideal.Quotient.mk 𝔮 a) •
            (Ideal.Quotient.mk (Ideal.map (mapP (m := m) hext) 𝔮) x) := by
        show Ideal.Quotient.mk (Ideal.map (mapP (m := m) hext) 𝔮)
          (mapP (m := m) hext a * x) = _
        rw [map_mul]
        rfl
      rw [h5]
      exact Submodule.smul_mem _ _ hx
  exact IsArtinianRing.of_finite (P K m ⧸ 𝔮)
    (P L m ⧸ Ideal.map (mapP (m := m) hext) 𝔮)

include hext in
/-- Maximals over the pushed ideal contract to the base maximal. -/
theorem comap_overMaximal_eq (𝔫 : Ideal (P L m)) (h𝔫 : 𝔫.IsMaximal)
    (hge : Ideal.map (mapP (m := m) hext) 𝔮 ≤ 𝔫) :
    Ideal.comap (mapP (m := m) hext) 𝔫 = 𝔮 := by
  have h1 : 𝔮 ≤ Ideal.comap (mapP (m := m) hext) 𝔫 :=
    le_trans Ideal.le_comap_map (Ideal.comap_mono hge)
  have h2 : Ideal.comap (mapP (m := m) hext) 𝔫 ≠ ⊤ := by
    intro htop
    have h3 : (1 : P K m) ∈ Ideal.comap (mapP (m := m) hext) 𝔫 := by
      rw [htop]
      exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h3
    exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  exact (h𝔮.eq_of_le h2 h1).symm

variable (ψ : (P K m ⧸ 𝔮) →+* L)
variable (hψK : ∀ c : K,
  ψ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) = algebraMap K L c)

set_option maxHeartbeats 1600000 in
include hext hψK in
/-- **Block A: the completed local ring of the Tate algebra at a maximal
ideal is reduced** (over any receiving normal extension). -/
theorem isReduced_adicCompletion_localization_tate
    (hfinq :
      letI : Algebra K (P K m ⧸ 𝔮) := (constantsToResidue 𝔮).toAlgebra
      Module.Finite K (P K m ⧸ 𝔮))
    (hint : ∀ i : Fin m, ∃ p : Polynomial ↥(FiniteJet.unitBall K),
      p.Monic ∧ Polynomial.eval₂
        (((constantsToResidue 𝔮 : K →+* (P K m ⧸ 𝔮))).comp
          (FiniteJet.unitBall K).subtype)
        (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) p = 0) :
    IsReduced (AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))
      (Localization.AtPrime 𝔮)) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  haveI hfree : Module.Free (P K m) (P L m) :=
    module_free_mapP (m := m) hext
  haveI hfin : Module.Finite (P K m) (P L m) :=
    module_finite_mapP (m := m) hext
  haveI : Nontrivial (P L m) := by
    refine ⟨0, 1, fun h01 => ?_⟩
    have h2 : MvPowerSeries.coeff (0 : Fin m →₀ ℕ) ((0 : P L m)).1 =
        MvPowerSeries.coeff (0 : Fin m →₀ ℕ) ((1 : P L m)).1 :=
      congrArg (fun F : P L m =>
        MvPowerSeries.coeff (0 : Fin m →₀ ℕ) F.1) h01
    rw [show ((0 : P L m)).1 = 0 from rfl,
      show ((1 : P L m)).1 = 1 from rfl, _root_.map_zero,
      MvPowerSeries.coeff_one, if_pos rfl] at h2
    exact one_ne_zero h2.symm
  haveI hart : IsArtinianRing
      (P L m ⧸ Ideal.map (mapP (m := m) hext) 𝔮) :=
    isArtinianRing_fibre (m := m) hext 𝔮
  -- every fibre maximal is a point ideal
  have hfactor : ∀ 𝔫 : fibreMaximals (Ideal.map (mapP (m := m) hext) 𝔮),
      ∃ (x : Fin m → L) (hx : ∀ i, ‖x i‖ ≤ 1),
        overMaximal (Ideal.map (mapP (m := m) hext) 𝔮) 𝔫 =
          pointIdeal (m := m) x hx := by
    intro 𝔫
    haveI := overMaximal_isMaximal (Ideal.map (mapP (m := m) hext) 𝔮) 𝔫
    have hover := comap_overMaximal_eq (m := m) hext 𝔮
      (overMaximal (Ideal.map (mapP (m := m) hext) 𝔮) 𝔫)
      (overMaximal_isMaximal _ 𝔫) (le_overMaximal _ 𝔫)
    exact exists_pointIdeal_of_isMaximal_over (m := m) hext 𝔮
      (overMaximal (Ideal.map (mapP (m := m) hext) 𝔮) 𝔫) hover ψ hψK
      hfinq hint
  choose xf hxf hfeq using hfactor
  -- the levelwise family into the polynomial levels
  set g : ∀ r : ℕ,
      (Localization.AtPrime 𝔮 ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) ^ r) →+*
      ∀ 𝔫 : fibreMaximals (Ideal.map (mapP (m := m) hext) 𝔮),
        (MvPolynomial (Fin m) L ⧸
          (MvPolynomial.idealOfVars (Fin m) L) ^ r) := fun r =>
    (RingHom.pi fun 𝔫 =>
      ((levelPointEquiv (m := m) (xf 𝔫) (hxf 𝔫) r) :
          (P L m ⧸ (pointIdeal (m := m) (xf 𝔫) (hxf 𝔫)) ^ r) ≃+* _).toRingHom.comp
        (((Ideal.quotEquivOfEq (congrArg (· ^ r) (hfeq 𝔫))).toRingHom).comp
          ((Ideal.Quotient.factor
            (pow_le_pow_left' (le_overMaximal _ 𝔫) r)).comp
            (levelMap (B := P L m) 𝔮 r)))).comp
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔮
        (Localization.AtPrime 𝔮) r).symm.toRingEquiv.toRingHom)
    with hgdef
  sorry

end BlockA

end FiniteJet.GraphKoszul

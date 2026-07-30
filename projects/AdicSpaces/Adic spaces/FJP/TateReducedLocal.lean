/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.TateWallFactors
import «Adic spaces».SemilocalFibre
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

end BlockA

end FiniteJet.GraphKoszul

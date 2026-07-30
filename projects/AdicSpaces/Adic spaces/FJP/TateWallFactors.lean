/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.TateTaylor
import «Adic spaces».FJP.TateScalarExtension
import «Adic spaces».FJP.TateNullstellensatz
import Mathlib.FieldTheory.Normal.Defs

/-!
# Identification of the wall factors as point ideals

([hrw-decomposition] endgame item 1.) Over a finite normal extension `L/K`
splitting the residue field of a maximal `𝔮` of `Q = P K m`, every maximal
ideal of `Q_L = P L m` lying over `𝔮` has residue field exactly `L` (minimal
polynomials of the generating residues split in `L`, and a root in a domain
picks out an element of `L`), hence is a point ideal of the closed polydisc
by the translated-span identification.
-/

@[expose] public section

open scoped Classical

open Polynomial

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [Algebra K L] [FiniteDimensional K L]
variable {m : ℕ}

section RootPick

variable {M : Type*} [CommRing M] [IsDomain M] [Algebra K M]

/-- **Root picking**: a root in a domain of a minimal polynomial that splits
in `L` is the image of an element of `L`. -/
theorem exists_eq_algebraMap_of_splits (φ : L →ₐ[K] M) {w : M}
    (p : Polynomial K) (hmonic : p.Monic)
    (hsplit : Splits (p.map (algebraMap K L)))
    (hroot : Polynomial.aeval w p = 0) :
    ∃ l : L, w = φ l := by
  have hfact := hsplit.eq_prod_roots_of_monic (hmonic.map _)
  have hmap : (p.map (algebraMap K L)).map (φ : L →+* M) =
      p.map (algebraMap K M) := by
    rw [Polynomial.map_map]
    congr 1
    exact (φ.comp_algebraMap).symm ▸ rfl
  have hevM : Polynomial.eval w (p.map (algebraMap K M)) = 0 := by
    rw [Polynomial.eval_map]
    exact hroot
  rw [← hmap, hfact, Polynomial.map_multiset_prod,
    Polynomial.eval_multiset_prod] at hevM
  have h0 := Multiset.prod_eq_zero_iff.mp hevM
  rw [Multiset.mem_map] at h0
  obtain ⟨q, hq, hq0⟩ := h0
  rw [Multiset.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  rw [Multiset.mem_map] at hr
  obtain ⟨l, -, rfl⟩ := hr
  refine ⟨l, ?_⟩
  have h2 : Polynomial.eval w
      ((Polynomial.X - Polynomial.C l).map (φ : L →+* M)) = 0 := hq0
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  exact sub_eq_zero.mp h2

end RootPick

section Residue

variable (hext : ∀ c : K, ‖algebraMap K L c‖ = ‖c‖)

/-- Base change commutes with the constants. -/
theorem mapP_constP (c : K) :
    mapP (m := m) hext (polyToP (MvPolynomial.C c)) =
      constP (m := m) (algebraMap K L c) := by
  refine Subtype.ext ?_
  rw [mapP_coe]
  show MvPowerSeries.map (algebraMap K L)
    ((MvPolynomial.C c : MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) =
    ((MvPolynomial.C (algebraMap K L c) : MvPolynomial (Fin m) L) :
      MvPowerSeries (Fin m) L)
  rw [MvPolynomial.coe_C, MvPolynomial.coe_C]
  exact MvPowerSeries.map_C _ _

variable [Normal K L]

include hext in
/-- **The residue field of a wall factor is the base extension**: for a
maximal `𝔫` of `P L m` lying over a maximal `𝔮` of `P K m` whose residue
embeds in the normal extension `L`, the constants map onto the residue ring
of `𝔫`. -/
theorem constP_residue_surjective (𝔮 : Ideal (P K m)) [h𝔮 : 𝔮.IsMaximal]
    (𝔫 : Ideal (P L m)) [h𝔫 : 𝔫.IsMaximal]
    (hover : Ideal.comap (mapP (m := m) hext) 𝔫 = 𝔮)
    (ψ : (P K m ⧸ 𝔮) →+* L)
    (hψK : ∀ c : K, ψ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) =
      algebraMap K L c)
    (hfinq :
      letI : Algebra K (P K m ⧸ 𝔮) :=
        (constantsToResidue 𝔮).toAlgebra
      Module.Finite K (P K m ⧸ 𝔮)) :
    Function.Surjective
      ((Ideal.Quotient.mk 𝔫).comp (constP (m := m) : L →+* P L m)) := by
  letI : Algebra K (P K m ⧸ 𝔮) :=
    (constantsToResidue 𝔮).toAlgebra
  haveI := hfinq
  haveI : IsDomain (P L m ⧸ 𝔫) :=
    Ideal.Quotient.isDomain 𝔫
  letI φ : L →+* (P L m ⧸ 𝔫) :=
    (Ideal.Quotient.mk 𝔫).comp (constP (m := m))
  letI : Algebra K (P L m ⧸ 𝔫) := (φ.comp (algebraMap K L)).toAlgebra
  -- the induced map on residues
  have hkill : ∀ a ∈ 𝔮, (Ideal.Quotient.mk 𝔫).comp
      (mapP (m := m) hext) a = 0 := by
    intro a ha
    rw [← hover, Ideal.mem_comap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  letI ρ : (P K m ⧸ 𝔮) →+* (P L m ⧸ 𝔫) :=
    Ideal.Quotient.lift 𝔮 ((Ideal.Quotient.mk 𝔫).comp
      (mapP (m := m) hext)) hkill
  -- ρ and ψ as K-algebra homs
  have hρK : ∀ c : K, ρ (algebraMap K (P K m ⧸ 𝔮) c) =
      algebraMap K (P L m ⧸ 𝔫) c := by
    intro c
    show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) = _
    rw [show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) =
      (Ideal.Quotient.mk 𝔫) (mapP (m := m) hext
        (polyToP (MvPolynomial.C c))) from rfl]
    rw [mapP_constP]
    rfl
  letI ρₐ : (P K m ⧸ 𝔮) →ₐ[K] (P L m ⧸ 𝔫) := { ρ with commutes' := hρK }
  letI ψₐ : (P K m ⧸ 𝔮) →ₐ[K] L := { ψ with commutes' := fun c => hψK c }
  letI φₐ : L →ₐ[K] (P L m ⧸ 𝔫) := { φ with commutes' := fun c => rfl }
  letI : Field (P K m ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  haveI : Algebra.IsIntegral K (P K m ⧸ 𝔮) :=
    Algebra.IsIntegral.of_finite _ _
  -- root picking for the images of the base residues
  have hgen : ∀ G : P K m, ∃ l : L,
      ρ (Ideal.Quotient.mk 𝔮 G) = φ l := by
    intro G
    set Gq := Ideal.Quotient.mk 𝔮 G with hGq
    have hint : IsIntegral K Gq := Algebra.IsIntegral.isIntegral Gq
    have hmono := minpoly.monic hint
    have hroot0 := minpoly.aeval K Gq
    have haev : Polynomial.aeval (ρₐ Gq) (minpoly K Gq) = 0 := by
      rw [Polynomial.aeval_algHom_apply, hroot0, map_zero]
    have hminψ : minpoly K (ψₐ Gq) = minpoly K Gq :=
      minpoly.algHom_eq ψₐ ψₐ.toRingHom.injective Gq
    have hsplit : Splits ((minpoly K Gq).map (algebraMap K L)) := by
      rw [← hminψ]
      exact Normal.splits ‹Normal K L› (ψₐ Gq)
    obtain ⟨l, hl⟩ := exists_eq_algebraMap_of_splits φₐ
      (minpoly K Gq) hmono hsplit haev
    exact ⟨l, hl⟩
  -- assemble: every residue class is a constants image
  intro z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  obtain ⟨G, hG⟩ := piToP_surjective (m := m) hext (Module.finBasis K L) F
  choose l hl using fun j => hgen (G j)
  refine ⟨∑ j, l j * (Module.finBasis K L) j, ?_⟩
  show φ (∑ j, l j * (Module.finBasis K L) j) = Ideal.Quotient.mk 𝔫 F
  rw [map_sum]
  rw [← hG]
  show ∑ j, φ (l j * (Module.finBasis K L) j) =
    Ideal.Quotient.mk 𝔫 (∑ j, mapP (m := m) hext (G j) *
      polyToP (MvPolynomial.C ((Module.finBasis K L) j)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact (hl j).symm

end Residue

end FiniteJet.GraphKoszul

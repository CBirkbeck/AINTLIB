/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Schematic density of the invertibility locus of a regular section ([KM-FMT-FLAT], engine)

The `[FMT-0]` reduction engine of the [KM-FMT-FLAT] gate (KM's step-(ii)→(iii)→(iv)
universal-case pipeline, KM 6.7.5 exemplar): a closed universal locus
(`Scheme.IdealSheafData`, the T-D15 interface shape) through which the basic open
`D(s) ↪ S` factors is all of `S`, provided `s` is a nonzerodivisor on the sections over
every affine open — *"`S[1/s]` is schematically dense when `S` has no `s`-torsion."*
ℤ-flatness (KM's "the moduli problem is flat over ℤ", First Main Theorem 5.1.1 / 6.6.1 /
6.8.1) enters ONLY through `isSMulRegular_natCast_of_flat`: torsion-free ⟹ every
`N ≠ 0` is regular. The flatness of the specific moduli spaces stays parametric
(tracked gates [FMT-1/2/3] — their spaces are still under construction by the
representability streams).

Consumers: STREAM-NISOG M3 wave (L9, L16, L19, L22, L24, L26) against
`ModularCurves.exists_factor_subschemeι_iff` (T-D14a′) and the T-D15 incidence loci.

Decomposition artifact: `.mathlib-quality/decomposition-fmt-flat.md` ([STREAM-FP], fable-FP).
-/

universe u

open CategoryTheory

/-- **[FMT-0a]** The kernel of localization away from a nonzerodivisor is zero — the
affine heart of "`D(f)` is schematically dense". -/
theorem Localization.Away.ker_algebraMap_eq_bot
    (R : Type*) [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) :
    RingHom.ker (algebraMap R (Localization.Away f)) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp <|
    IsLocalization.injective (M := Submonoid.powers f) (Localization.Away f)
      (Submonoid.powers_le.mpr hf)

/-- **[FMT-0c]** Over a ℤ-flat (equivalently torsion-free) ring, every nonzero integer is
a nonzerodivisor — the ONLY point where KM's "flat over ℤ" hypothesis is consumed. -/
theorem isSMulRegular_natCast_of_flat
    (R : Type*) [CommRing R] [Module.Flat ℤ R] {N : ℤ} (hN : N ≠ 0) :
    (N : R) ∈ nonZeroDivisors R := by
  have key : ∀ x : R, (N : R) * x = 0 → x = 0 := by
    intro x hx
    have hNx : N • x = 0 := by rwa [zsmul_eq_mul]
    have hmem : x ∈ Submodule.torsion ℤ R :=
      ⟨⟨N, mem_nonZeroDivisors_iff_ne_zero.mpr hN⟩, hNx⟩
    rwa [Module.Flat.torsion_eq_bot, Submodule.mem_bot] at hmem
  exact mem_nonZeroDivisors_iff.mpr
    ⟨key, fun x hx => key x (by rwa [mul_comm])⟩

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (s : Γ(S, ⊤))

/-- **[FMT-0b-i]** The ideal-sheaf kernel of the basic-open immersion `D(s) ↪ S` vanishes
when `s` restricts to a nonzerodivisor on the sections over every affine open. -/
theorem ker_basicOpenι_eq_bot
    (hs : ∀ U : S.affineOpens,
      S.presheaf.map (homOfLE le_top).op s ∈ nonZeroDivisors Γ(S, U.1)) :
    (S.basicOpen s).ι.ker = ⊥ := by
  ext U : 2
  simp only [IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [eq_bot_iff]
  refine (Scheme.Hom.ideal_ker_le _ U).trans ?_
  -- the app of the basic-open immersion at an affine `U` is the localization away from
  -- the restriction of `s`, hence injective when that restriction is a nonzerodivisor
  set r : Γ(S, U.1) := S.presheaf.map (homOfLE le_top).op s with hr
  have hV : (S.basicOpen s).ι ''ᵁ ((S.basicOpen s).ι ⁻¹ᵁ U.1) = S.basicOpen r := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hr,
      Scheme.basicOpen_res, inf_comm]
  letI : Algebra Γ(S, U.1) Γ(S, (S.basicOpen s).ι ''ᵁ ((S.basicOpen s).ι ⁻¹ᵁ U.1)) :=
    (S.presheaf.map (homOfLE (Set.image_preimage_subset _ _)).op).hom.toAlgebra
  haveI : IsLocalization.Away r Γ(S, (S.basicOpen s).ι ''ᵁ ((S.basicOpen s).ι ⁻¹ᵁ U.1)) :=
    U.2.isLocalization_of_eq_basicOpen (f := r)
      (homOfLE (Set.image_preimage_subset _ _)) hV
  have hinj : Function.Injective ((S.basicOpen s).ι.app U.1).hom := by
    rw [Scheme.Opens.ι_app]
    exact IsLocalization.injective (M := Submonoid.powers r)
      Γ(S, (S.basicOpen s).ι ''ᵁ ((S.basicOpen s).ι ⁻¹ᵁ U.1))
      (Submonoid.powers_le.mpr (hs U))
  exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hinj)

/-- **[FMT-0b]** The [KM-FMT-FLAT] reduction engine: a closed universal locus through
which `D(s) ↪ S` factors is all of `S` (its ideal sheaf is `⊥`), when `s` is
affine-locally a nonzerodivisor. This packages KM's universal-case pipeline — (ii) the
ambient space is flat over ℤ (supply `isSMulRegular_natCast_of_flat` at `s = N`),
(iii) the condition holds after inverting `N` (the factoring hypothesis), (iv) the locus
of truth is closed (the `IdealSheafData`) — into "the condition holds everywhere". -/
theorem IdealSheafData.eq_bot_of_basicOpenι_factors
    (Z : S.IdealSheafData)
    (hs : ∀ U : S.affineOpens,
      S.presheaf.map (homOfLE le_top).op s ∈ nonZeroDivisors Γ(S, U.1))
    (hfac : ∃ h : ↑(S.basicOpen s) ⟶ Z.subscheme, h ≫ Z.subschemeι = (S.basicOpen s).ι) :
    Z = ⊥ := by
  obtain ⟨h, hh⟩ := hfac
  have hle := h.le_ker_comp Z.subschemeι
  rw [hh, IdealSheafData.ker_subschemeι, ker_basicOpenι_eq_bot S s hs] at hle
  exact le_bot_iff.mp hle

end AlgebraicGeometry.Scheme

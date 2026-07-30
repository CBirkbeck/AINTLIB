/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.TateTaylor
import «Adic spaces».FJP.TateScalarExtension
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

end FiniteJet.GraphKoszul

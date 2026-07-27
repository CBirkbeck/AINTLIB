/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RelativePieceKeystone
import «Adic spaces».RationalBasis

/-!
# The rational basis over a general Huber base (Wedhorn 7.35(2), non-Tate)

De-Tating of the rational-basis development: the Tate route turns the
`RCoord` side condition `I ≤ √(span T)` into `span T = ⊤` through a unit of
`I`; over a general Huber base (e.g. `A_inf`) no unit exists, but a POWER of
the ambient ideal of definition lies in `span T` (radical of a finitely
generated ideal), which is exactly what the `hopen`-condition of a rational
datum needs (`genPiece_hopen_of_pow_le`). See the board's YB3a plan.
-/

noncomputable section

open TopologicalSpace

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- A span-decomposed element's fraction expands over the tray (the
cancellation core of `genPiece_hopen`, factored out). -/
theorem divByS_eq_sum_of_span {T : Finset A} {t x : A} (c : A → A)
    (hx : x = ∑ t' ∈ T, c t' * t') :
    divByS x t = ∑ t' ∈ T,
      algebraMap A (Localization.Away t) (c t') * divByS t' t := by
  classical
  have hone : ∀ y : A, divByS y t
      = algebraMap A (Localization.Away t) y
        * IsLocalization.mk' (Localization.Away t) (1 : A)
          (⟨t, ⟨1, pow_one t⟩⟩ : Submonoid.powers t) := fun y =>
    IsLocalization.mk'_eq_mul_mk'_one _ _
  rw [hone, hx, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [map_mul, mul_assoc, ← hone]

/-- **The `hopen`-condition at open span** (the general-Huber replacement
for `genPiece_hopen`'s `span T = ⊤`): a power of the ambient ideal of
definition inside `span T` suffices. A₀-side generator decomposition of
the `I`-power plus the fixed-coefficient absorb. -/
theorem genPiece_hopen_of_pow_le (P : PairOfDefinition A) (T : Finset A)
    (t : A) (M : ℕ)
    (hle : (Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) ^ M
      ≤ Ideal.span (T : Set A)) :
    ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) t ∈ locSubring P T t := by
  classical
  obtain ⟨G, hG⟩ := (P.fg.pow (n := M))
  have hgen : ∀ g : A, g ∈ Ideal.span (T : Set A) →
      ∃ c : A → A, g = ∑ t' ∈ T, c t' * t' := by
    intro g hg
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hg
    exact ⟨c, by
      rw [← hc]
      exact Finset.sum_congr rfl fun t' _ => (smul_eq_mul _ _)⟩
  have hGamb : ∀ g : ↥(G : Set P.A₀),
      ((↑(↑g : P.A₀) : A)) ∈ Ideal.span (T : Set A) := by
    intro g
    refine hle ?_
    have hgI : ((g : P.A₀)) ∈ P.I ^ M := by
      rw [← hG]
      exact Ideal.subset_span g.2
    have hmap := Ideal.mem_map_of_mem (P.A₀.subtype) hgI
    rw [Ideal.map_pow] at hmap
    exact hmap
  choose c hc using fun g : ↥(G : Set P.A₀) => hgen _ (hGamb g)
  haveI : Fintype ↥(G : Set P.A₀) := G.finite_toSet.fintype
  obtain ⟨N, hN⟩ := pod_absorb_finset_mul_pow P
    (Finset.univ.biUnion fun g : ↥(G : Set P.A₀) => T.image (c g))
  refine ⟨N + M, fun b hb => ?_⟩
  -- decompose over the fixed generators with `I^N` coefficients
  rw [pow_add] at hb
  have hb' : (b : P.A₀) ∈ (P.I ^ N) •
      (Submodule.span P.A₀ (Set.range
        (fun g : ↥(G : Set P.A₀) => (g : P.A₀)))) := by
    rw [Subtype.range_coe, ← Ideal.span, hG, Ideal.smul_eq_mul]
    exact hb
  obtain ⟨a, haI, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hb'
  -- the fraction expands generator-by-generator
  have hcoe : (↑b : A) = ∑ g ∈ a.support,
      (↑(a g) : A) * (↑(↑g : P.A₀) : A) := by
    rw [← hsum]
    push_cast [Finsupp.sum]
    exact Finset.sum_congr rfl fun g _ => rfl
  have hexp : divByS (↑b : A) t = ∑ g ∈ a.support, ∑ t' ∈ T,
      algebraMap A (Localization.Away t) ((↑(a g) : A) * c g t')
        * divByS t' t := by
    have hone : ∀ y : A, divByS y t
        = algebraMap A (Localization.Away t) y
          * IsLocalization.mk' (Localization.Away t) (1 : A)
            (⟨t, ⟨1, pow_one t⟩⟩ : Submonoid.powers t) := fun y =>
      IsLocalization.mk'_eq_mul_mk'_one _ _
    rw [hone, hcoe, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, mul_assoc, ← hone,
      divByS_eq_sum_of_span (c g) (hc g), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [← mul_assoc, ← map_mul]
  rw [hexp]
  refine Subring.sum_mem _ fun g _ => Subring.sum_mem _ fun t' ht' => ?_
  refine Subring.mul_mem _ ?_ (divByS_mem_locSubring P T t ht')
  refine algebraMap_mem_locSubring P T t ?_
  refine hN (c g t') ?_ (a g) (haI g)
  exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g,
    Finset.mem_image_of_mem _ ht'⟩

end ValuationSpectrum

end

/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.SubdivisorEq
import ModularCurves.LevelStructure.Basic
import ModularCurves.LevelStructure.Incidence
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.ForMathlib.IdealSheafComaximal
import ModularCurves.ForMathlib.SectionKerDisjoint

/-!
# The torsion ideal is contained in the kernel of a killed section (YFULL route γ, [YF-⊇])

A point `σ` of `E` over `t` killed by `N` factors through `E[N]` (its classifying map to
the torsion, followed by the inclusion), so its kernel ideal sheaf contains the torsion
ideal: `torsionIdeal N ≤ (σ.1).ker`.

This is a step of the `Y(N)` full-level `⊇` argument: each combination `[a]P + [b]Q` is
`N`-torsion, so the torsion ideal is contained in every section's kernel, hence in their
intersection — which, over the disjoint locus, equals the section-divisor's ideal.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- The torsion ideal of `E` is contained in the kernel of any `N`-killed point of `E`. -/
theorem torsionIdeal_le_ker {T : Scheme.{u}} {t : T ⟶ S} (σ : E.Point t)
    (hσ : σ.1 ≫ E.mulByHom N = t ≫ E.zero) :
    E.torsionIdeal N ≤ (σ.1).ker := by
  rw [torsionIdeal, ← E.pointToTorsion_torsionι σ hσ]
  exact (E.pointToTorsion σ hσ).le_ker_comp (E.torsionι N)

/-- `E[N]` as a relative effective Cartier divisor in `E/S` (public reconstruction of the
private `fullLevelLocusAux_torsionDivisor`): the ideal is the torsion ideal, and the
finite / flat / locally-of-finite-presentation fields are transported from `E[N] ⟶ S`
across the isomorphism `(torsionIdeal N).subscheme ≅ E[N]`. -/
noncomputable def torsionDivisor : RelEffCartierDiv E.π where
  ideal := E.torsionIdeal N
  finite := by
    obtain ⟨e, he⟩ := E.torsionIdeal_subscheme N
    rw [show (E.torsionIdeal N).subschemeι ≫ E.π = e.hom ≫ E.torsionπ N by
        rw [← he, Category.assoc, E.torsionι_π],
      MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    exact E.torsionπ_isFinite N
  flat := by
    obtain ⟨e, he⟩ := E.torsionIdeal_subscheme N
    rw [show (E.torsionIdeal N).subschemeι ≫ E.π = e.hom ≫ E.torsionπ N by
        rw [← he, Category.assoc, E.torsionι_π],
      MorphismProperty.cancel_left_of_respectsIso @Flat]
    exact E.torsionπ_flat N
  lfp := by
    obtain ⟨e, he⟩ := E.torsionIdeal_subscheme N
    rw [show (E.torsionIdeal N).subschemeι ≫ E.π = e.hom ≫ E.torsionπ N by
        rw [← he, Category.assoc, E.torsionι_π],
      MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation]
    exact MorphismProperty.pullback_snd _ _ (E.mulByHom_locallyOfFinitePresentation N)

/-- The `E[N]` divisor has degree `N²` at every point (KM 2.3.1 rank, via `torsion_rank`
transported across `(torsionIdeal N).subscheme ≅ E[N]`). -/
theorem torsionDivisor_degree (s : S) : (E.torsionDivisor N).degree s = N ^ 2 := by
  obtain ⟨e, he⟩ := E.torsionIdeal_subscheme N
  have hι : (E.torsionIdeal N).subschemeι ≫ E.π = e.hom ≫ E.torsionπ N := by
    rw [← he, Category.assoc, E.torsionι_π]
  haveI := E.torsionπ_isFinite N
  haveI := E.torsionπ_flat N
  have h1 : (E.torsionDivisor N).degree s
      = ((E.torsionIdeal N).subschemeι ≫ E.π).finrank s := rfl
  rw [h1, congrArg (fun f => Scheme.Hom.finrank f s) hι,
    Scheme.Hom.finrank_comp_left_of_isIso e.hom (E.torsionπ N)]
  exact E.torsion_rank N s

/-- **[YF-⊇] divisor chain.** If `N²` sections of `E/S`, each killed by `N`, are pairwise
pointwise-distinct (their base maps never coincide), then their section divisor `Σᵢ [σᵢ]`
equals `E[N]`. Pointwise-distinct sections of the separated `E ⟶ S` have comaximal kernels
(`sup_ker_eq_top_of_sections_pointwise_ne`), so the section divisor's ideal
`∏ᵢ ker σᵢ = ⋂ᵢ ker σᵢ`; each `ker σᵢ ⊇ torsionIdeal` (`torsionIdeal_le_ker`), so
`torsionIdeal ≤ Σ`-ideal, making it a subdivisor of `E[N]`; and both have degree `N²`
(`sectionsDivisor_degree`, `torsionDivisor_degree`), so `[YF-SUBDIV-EQ]` forces equality. -/
theorem sectionsDivisor_ideal_eq_torsionIdeal
    (P : Fin (N ^ 2) → E.Point (𝟙 S))
    (hkill : ∀ i, (P i).1 ≫ E.mulByHom N = 𝟙 S ≫ E.zero)
    (hne : (↑(Finset.univ : Finset (Fin (N ^ 2))) : Set (Fin (N ^ 2))).Pairwise
      (fun i j => ∀ u, (P i).1.base u ≠ (P j).1.base u)) :
    (RelEffCartierDiv.sectionsDivisor E.π P).ideal = E.torsionIdeal N := by
  haveI : IsSeparated E.π := E.proper.toIsSeparated
  have hle : E.torsionIdeal N ≤ (RelEffCartierDiv.sectionsDivisor E.π P).ideal := by
    rw [fullLevelLocusAux_sectionsDivisor_ideal,
      Scheme.IdealSheafData.prod_eq_biInf_of_pairwise_sup_eq_top Finset.univ _
        (fun i _ j _ hij => Scheme.IdealSheafData.sup_ker_eq_top_of_sections_pointwise_ne
          E.π (P i).1 (P j).1 (P i).2 (P j).2 (hne (Finset.mem_coe.mpr (Finset.mem_univ i))
            (Finset.mem_coe.mpr (Finset.mem_univ j)) hij))]
    exact le_iInf fun i => le_iInf fun _ => E.torsionIdeal_le_ker N (P i) (hkill i)
  have hsub : RelEffCartierDiv.IsSubdivisor (RelEffCartierDiv.sectionsDivisor E.π P)
      (E.torsionDivisor N) :=
    (RelEffCartierDiv.isSubdivisor_iff_le _ _).mpr hle
  have hdeg : ∀ s, (RelEffCartierDiv.sectionsDivisor E.π P).degree s
      = (E.torsionDivisor N).degree s := by
    intro s
    haveI : IsSeparated E.π := inferInstance
    rw [RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth P s, E.torsionDivisor_degree N s]
  exact congrArg RelEffCartierDiv.ideal
    (RelEffCartierDiv.eq_of_isSubdivisor_of_degree_eq _ _ hsub hdeg)

end EllipticCurve

end ModularCurves

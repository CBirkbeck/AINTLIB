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
import ModularCurves.Moduli.FullLevelOpenLocus

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

/-- Base-change reduction for pointwise-distinctness: if the base-changed sections
`asSection P`, `asSection Q` agree topologically at `u`, then so do the underlying
`E`-points `P, Q` (the first pullback projection of `asSection` is the point itself,
`asSection_val_fst`). Contrapositive: pointwise-distinct `E`-points give pointwise-distinct
base-changed sections — the form consumed by `sectionsDivisor_ideal_eq_torsionIdeal`. -/
theorem asSection_base_eq_imp {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) (u : T)
    (h : (Point.asSection E g P).1.base u = (Point.asSection E g Q).1.base u) :
    P.1.base u = Q.1.base u :=
  have eP : P.1.base u
      = (Limits.pullback.fst E.π g).base ((Point.asSection E g P).1.base u) :=
    (congrArg (fun m : T ⟶ E.E => m.base u) (Point.asSection_val_fst E g P)).symm
  have eQ : Q.1.base u
      = (Limits.pullback.fst E.π g).base ((Point.asSection E g Q).1.base u) :=
    (congrArg (fun m : T ⟶ E.E => m.base u) (Point.asSection_val_fst E g Q)).symm
  eP.trans ((congrArg (Limits.pullback.fst E.π g).base h).trans eQ.symm)

omit [NeZero N] in
/-- The difference of two `N`-killed points is `N`-killed (`N•(x-y) = N•x - N•y = 0`). -/
theorem sub_killed {T : Scheme.{u}} (t : T ⟶ S) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    (x - y).1 ≫ E.mulByHom N = t ≫ E.zero := by
  rw [← E.smul_eq_zero_iff_comp_mulByHom t N] at hx hy ⊢
  rw [smul_sub, hx, hy, sub_zero]

/-- **[YF-⊇ BRIDGE — vanishing from residue-field agreement, WIP frontier].** For `N`
invertible, if two `N`-killed points `x, y` of `E` over `t` agree **over the residue field**
at `u` — `fromSpecResidueField u ≫ x.1 = fromSpecResidueField u ≫ y.1` (agreement as
morphisms `Spec κ(u) ⟶ E`, not merely topologically) — then `x - y` vanishes at `u`:
`u ∈ pointVanishSet (x - y)`.

⚠ CORRECTION (this session): the earlier *topological* hypothesis `x.1 u = y.1 u` makes the
statement **FALSE** — two Galois-conjugate torsion points (e.g. a torsion point and its image
under a residue-field automorphism) share a topological image `x.1 u = y.1 u` yet their
difference is a nonzero point that vanishes nowhere, so `u ∉ pointVanishSet (x-y) = ∅`.
Genuine residue-field agreement is required. For the actual application the points are
base-changed **sections** (of `F.π`), where the residue map is forced (= retraction-inverse),
so topological agreement *does* upgrade to residue agreement — that upgrade
(`sections_residue_eq_of_base_eq`, below) is the remaining section-specific crux.

PROOF STRATEGY. `x|κ(u) = y|κ(u)` ⟹ `(x-y)|κ(u)` factors through the zero section
(`restrict`/`asSection` additivity + `sub_killed`), so the two `E[N]`-classifiers of `x-y`
and `0` agree as morphisms `Spec κ(u) ⟶ E[N]`, giving a map `Spec κ(u) ⟶` the agreement
locus whose image is `u` — hence `u ∈ range(agreementι) = pointVanishSet (x-y)` (the reverse
of `range_agreementι_subset`, now valid because agreement is at the morphism level). -/
theorem mem_pointVanishSet_of_residue_eq (hN : NIsInvertible S N) {T : Scheme.{u}}
    (t : T ⟶ S) (x y : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) (u : T)
    (h : T.fromSpecResidueField u ≫ x.1 = T.fromSpecResidueField u ≫ y.1) :
    u ∈ E.pointVanishSet N t (x - y) (E.sub_killed N t x y hx hy) := by
  sorry

/-- **[YF-⊇ CRUX — forced residue for sections, WIP frontier].** Two sections `σ₁, σ₂` of a
separated morphism `ρ` that agree topologically at `u` agree over the residue field:
`fromSpecResidueField u ≫ σ₁ = fromSpecResidueField u ≫ σ₂`. The residue map of a section is
forced (the inverse of `ρ`'s), so — unlike general morphisms — there is no Galois-conjugate
freedom. This is the upgrade that makes `mem_pointVanishSet_of_residue_eq` applicable to the
base-changed combination **sections**, hence discharges `[YF-⊇]` pointwise-distinctness. -/
theorem sections_residue_eq_of_base_eq {X U : Scheme.{u}} (ρ : X ⟶ U) [IsSeparated ρ]
    (σ₁ σ₂ : U ⟶ X) (hσ₁ : σ₁ ≫ ρ = 𝟙 U) (hσ₂ : σ₂ ≫ ρ = 𝟙 U) (u : U)
    (h : σ₁.base u = σ₂.base u) :
    U.fromSpecResidueField u ≫ σ₁ = U.fromSpecResidueField u ≫ σ₂ := by
  sorry

end EllipticCurve

end ModularCurves

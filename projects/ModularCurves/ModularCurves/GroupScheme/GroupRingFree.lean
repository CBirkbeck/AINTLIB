/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.StableCover
import ModularCurves.ForMathlib.FiniteFlatFreeAway

/-!
# Freeness of the group ring on a shrunk base patch (`[HG-C3d]`)

For the finite locally free subgroup scheme `G / S` and an affine `V ∋ s`, there is a basic
open `S.basicOpen r ∋ s` of `V` over which the group ring `Γ(G, π⁻¹(D(r)))` is **free** as a
`Γ(S, D(r))`-module (with the `appLE` algebra structure that `AffineChartPatch.groupRing`
carries). Chain: the sections over `V` form a module-finite flat finitely-presented algebra
(`HasRingHomProperty.appLE` extraction); such algebras are free near every prime
(`exists_away_free_of_finite_of_flat`); the model freeness transports to the section rings
(`Module.Free.of_isLocalizedModule_away`), which are honest localizations
(`isLocalization_basicOpen`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

/-- **`[HG-C3d]` — freeness of the group ring after shrinking.** For `s` in an affine open
`V ⊆ S` there is `r : Γ(S, V)` with `s ∈ D(r)` such that the group ring over `D(r)` is a
free module over the base ring (in the `appLE` algebra structure of `AffineChartPatch`). -/
theorem exists_basicOpen_groupRing_free (V : S.affineOpens) {s : S} (hs : s ∈ V.1) :
    ∃ r : Γ(S, V.1), s ∈ S.basicOpen r ∧
      (letI := ((G.π.appLE (S.basicOpen r) (G.π ⁻¹ᵁ S.basicOpen r) le_rfl).hom).toAlgebra
       Module.Free Γ(S, S.basicOpen r) Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r)) := by
  classical
  haveI : IsFinite G.π := G.finite
  have hπV : IsAffineOpen (G.π ⁻¹ᵁ V.1) := V.2.preimage G.π
  -- the base and group rings over `V`, with the `appLE` algebra
  letI algRA : Algebra Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1) :=
    ((G.π.appLE V.1 (G.π ⁻¹ᵁ V.1) le_rfl).hom).toAlgebra
  -- module-finite, flat, and finitely presented as an algebra
  haveI hfin : Module.Finite Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1) := by
    show (G.π.appLE V.1 (G.π ⁻¹ᵁ V.1) le_rfl).hom.Finite
    rw [Scheme.Hom.appLE_eq_app]
    exact G.π.finite_app V.1 V.2
  haveI hflat : Module.Flat Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1) := by
    have h := HasRingHomProperty.appLE (P := @Flat) (f := G.π) G.flat V
      ⟨G.π ⁻¹ᵁ V.1, hπV⟩ le_rfl
    exact h
  haveI hfp : Algebra.FinitePresentation Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1) := by
    have h := HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := G.π) G.lfp V
      ⟨G.π ⁻¹ᵁ V.1, hπV⟩ le_rfl
    exact h
  -- the prime of `s` and the freeness radius
  set p := V.2.primeIdealOf ⟨s, hs⟩ with hp
  obtain ⟨r, hrp, hfree⟩ :=
    exists_away_free_of_finite_of_flat Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1) p
  refine ⟨r, ?_, ?_⟩
  · -- membership: `s ∈ D(r)` since `r ∉ p`
    have h2 : p ∈ PrimeSpectrum.basicOpen r := (PrimeSpectrum.mem_basicOpen r p).mpr hrp
    have h3 : p ∈ V.2.fromSpec ⁻¹ᵁ S.basicOpen r := by
      rw [V.2.fromSpec_preimage_basicOpen]
      exact h2
    have h4 : V.2.fromSpec.base p ∈ S.basicOpen r := h3
    rwa [hp, V.2.fromSpec_primeIdealOf ⟨s, hs⟩] at h4
  · -- freeness: transport the model freeness to the section rings
    letI algR'M' := ((G.π.appLE (S.basicOpen r) (G.π ⁻¹ᵁ S.basicOpen r) le_rfl).hom).toAlgebra
    haveI hloc : IsLocalization.Away r Γ(S, S.basicOpen r) := V.2.isLocalization_basicOpen r
    -- the `G`-side restriction as the `A`-algebra structure of the shrunk group ring
    have hle : G.π ⁻¹ᵁ S.basicOpen r ≤ G.π ⁻¹ᵁ V.1 := fun x hx => (S.basicOpen_le r) hx
    letI algAM' : Algebra Γ(G.G, G.π ⁻¹ᵁ V.1) Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) :=
      ((G.G.presheaf.map (homOfLE hle).op).hom).toAlgebra
    -- the composite `R`-algebra structure on the shrunk group ring
    letI algRM' : Algebra Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) :=
      ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op ≫
        G.π.appLE (S.basicOpen r) (G.π ⁻¹ᵁ S.basicOpen r) le_rfl).hom).toAlgebra
    -- the `appLE` exchange square
    have happ : (G.π.appLE V.1 (G.π ⁻¹ᵁ V.1) le_rfl) ≫ G.G.presheaf.map (homOfLE hle).op
        = (S.presheaf.map (homOfLE (S.basicOpen_le r)).op) ≫
          (G.π.appLE (S.basicOpen r) (G.π ⁻¹ᵁ S.basicOpen r) le_rfl) := by
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    -- the two scalar towers
    haveI towRR'M' : IsScalarTower Γ(S, V.1) Γ(S, S.basicOpen r)
        Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) :=
      IsScalarTower.of_algebraMap_eq fun c => rfl
    haveI towRAM' : IsScalarTower Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1)
        Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) :=
      IsScalarTower.of_algebraMap_eq fun c =>
        (congrArg (fun m => (CommRingCat.Hom.hom m) c) happ).symm
    -- the shrunk group ring is the localization of the group ring at `powers r`
    haveI hlocA : IsLocalization
        (Algebra.algebraMapSubmonoid Γ(G.G, G.π ⁻¹ᵁ V.1) (Submonoid.powers r))
        Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) := by
      -- the powers of `r` map to the powers of the pulled-back section
      have h1 : Algebra.algebraMapSubmonoid Γ(G.G, G.π ⁻¹ᵁ V.1) (Submonoid.powers r)
          = Submonoid.powers (G.π.app V.1 r) := by
        rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
        congr 1
        show (G.π.appLE V.1 (G.π ⁻¹ᵁ V.1) le_rfl) r = G.π.app V.1 r
        rw [Scheme.Hom.appLE_eq_app]
      rw [h1]
      -- the target open is the `G`-side basic open
      have hopen : G.π ⁻¹ᵁ S.basicOpen r = G.G.basicOpen (G.π.app V.1 r) :=
        Scheme.preimage_basicOpen G.π r
      -- the mathlib localization over the basic-open spelling
      have h2 := hπV.isLocalization_basicOpen (G.π.app V.1 r)
      -- transport along the (thin-category) identification of the two opens
      let eΓ : Γ(G.G, G.G.basicOpen (G.π.app V.1 r)) ≃+*
          Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r) :=
        (G.G.presheaf.mapIso
          (eqToIso (congrArg Opposite.op hopen.symm))).commRingCatIsoToRingEquiv
      have hloc' := (IsLocalization.isLocalization_iff_of_ringEquiv
        (Submonoid.powers (G.π.app V.1 r)) eΓ).mp h2
      -- the transported algebra agrees with the restriction algebra (thin category of opens)
      have hcomp : (homOfLE (G.G.basicOpen_le (G.π.app V.1 r))).op ≫
          (eqToIso (congrArg Opposite.op hopen.symm)).hom = (homOfLE hle).op :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have halg : algAM' = (eΓ.toRingHom.comp
          (algebraMap Γ(G.G, G.π ⁻¹ᵁ V.1)
            Γ(G.G, G.G.basicOpen (G.π.app V.1 r)))).toAlgebra := by
        apply Algebra.algebra_ext
        intro a
        show (G.G.presheaf.map (homOfLE hle).op) a
            = eΓ ((G.G.presheaf.map
                (homOfLE (G.G.basicOpen_le (G.π.app V.1 r))).op) a)
        calc (G.G.presheaf.map (homOfLE hle).op) a
            = (G.G.presheaf.map ((homOfLE (G.G.basicOpen_le (G.π.app V.1 r))).op ≫
                (eqToIso (congrArg Opposite.op hopen.symm)).hom)) a := by
              rw [hcomp]
          _ = eΓ ((G.G.presheaf.map
                (homOfLE (G.G.basicOpen_le (G.π.app V.1 r))).op) a) := by
              rw [Functor.map_comp]; rfl
      exact halg ▸ hloc'
    exact Module.Free.of_isLocalizedModule_away r Γ(S, S.basicOpen r)
      Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r)
      (IsScalarTower.toAlgHom Γ(S, V.1) Γ(G.G, G.π ⁻¹ᵁ V.1)
        Γ(G.G, G.π ⁻¹ᵁ S.basicOpen r)).toLinearMap

/-- **`[HG-C3f]` — the free affine chart patch around every point.** For `G` killed by `N`,
every point of `E` lies in the chart open of an `AffineChartPatch` whose group ring is a
**free** module over the base ring — the complete geometric input of the per-chart
Hopf–Galois datum (`chartData`/`isHopfGalois_chartCoaction`, M6). Assembles the chart
existence (`exists_mem_stableAffineOpen`) with the freeness shrink
(`exists_basicOpen_groupRing_free`): intersect the chart with the preimage of the freeness
basic open (stable by `IsStableOpen.inf` + `isStableOpen_π_preimage`, affine as a basic
open of the affine chart). -/
theorem exists_affineChartPatch_free (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    ∃ P : G.AffineChartPatch, x ∈ P.U ∧ Module.Free P.baseRing P.groupRing := by
  obtain ⟨V, Uc, hxU, hUaff, hUst, hUover⟩ := G.exists_mem_stableAffineOpen N hkill x
  have hs : E.π.base x ∈ V.1 := hUover hxU
  obtain ⟨r, hsr, hfree⟩ := G.exists_basicOpen_groupRing_free V hs
  -- the shrunk chart: intersect with the preimage of the freeness basic open
  have hstable : G.IsStableOpen (Uc ⊓ E.π ⁻¹ᵁ S.basicOpen r) :=
    hUst.inf G (G.isStableOpen_π_preimage _)
  have haffine : IsAffineOpen (Uc ⊓ E.π ⁻¹ᵁ S.basicOpen r) := by
    have h1 : E.π ⁻¹ᵁ S.basicOpen r = E.E.basicOpen (E.π.app V.1 r) :=
      Scheme.preimage_basicOpen E.π r
    have h2 : E.E.basicOpen ((E.E.presheaf.map (homOfLE hUover).op) (E.π.app V.1 r))
        = Uc ⊓ E.E.basicOpen (E.π.app V.1 r) :=
      Scheme.basicOpen_res _ _ ((homOfLE hUover).op)
    rw [h1, ← h2]
    exact hUaff.basicOpen _
  refine ⟨⟨S.basicOpen r, V.2.basicOpen r, Uc ⊓ E.π ⁻¹ᵁ S.basicOpen r, haffine, hstable,
    inf_le_right⟩, ⟨hxU, ?_⟩, ?_⟩
  · show E.π.base x ∈ S.basicOpen r
    exact hsr
  · exact hfree

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

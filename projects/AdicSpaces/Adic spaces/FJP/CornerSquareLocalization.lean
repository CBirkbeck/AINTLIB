/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetStrictLocalization

/-!
# Strict localization over an abstract pinched corner square (T625, campaign B)

[FJP] §4 parametrized: the strict-localization chain (Lemmas 4.1, 4.3, 4.4, Prop 4.5)
over an **abstract strict Milnor pinch** of four normed ultrametric complete corners

`A = B ×_D C` : `φB : A →+* B`, `φC : A →+* C`, `ψB : B →+* D`, `ψC : C →+* D`

carrying the [FJP] §2 package: the norm identities (`φC`, `ψB` isometric; `φB`, `ψC`
1-Lipschitz; pullback max-norm identity), the exact row with uniqueness
(`milnorRow`), the additive κ=1 coefficient section of `ψC`, per-corner scaling
pseudouniformizers, and noetherianity of the corner and `P`-ring unit balls.

The paper states §4 for the finite-jet square but the proofs use only this package
([FJP] Lemma 4.1: "restricted Tate extension carries a strict Milnor square to a
strict Milnor square"); `FiniteJetStrictLocalization.lean` is its transcription at
the Jet corners. This parametrized version exists so the SAME chain instantiates at
the `⟨V⟩`-extended corners `P (Jet• F) n` (whose package facts are the `ext•` lemmas
of `FiniteJetStrictLocalization` at arity `n`) — the reviewer §5.1 strengthening.

The Koszul layer (`exists_d1_lift`, `exists_d2_lift`, `syzygy_graph_restricted`) is
already generic over a normed corner `E` and is consumed as-is.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul

variable {A B C D : Type*}
  [NormedCommRing A] [IsUltrametricDist A]
  [NormedCommRing B] [IsUltrametricDist B]
  [NormedCommRing C] [IsUltrametricDist C]
  [NormedCommRing D] [IsUltrametricDist D]

/-- **The abstract strict Milnor pinch** ([FJP] SS2's package for the square
`A = B x_D C`): homs, norm identities, the exact row with uniqueness, the kappa=1
coefficient section of `psiC`, per-corner scaling pseudouniformizers, and the
noetherianity inputs consumed by the graph-Koszul layer. -/
structure Pinch (A B C D : Type*)
    [NormedCommRing A] [IsUltrametricDist A] [NormedCommRing B] [IsUltrametricDist B]
    [NormedCommRing C] [IsUltrametricDist C] [NormedCommRing D] [IsUltrametricDist D] :
    Type _ where
  φB : A →+* B
  φC : A →+* C
  ψB : B →+* D
  ψC : C →+* D
  norm_φB_le : ∀ a, ‖φB a‖ ≤ ‖a‖
  norm_φC : ∀ a, ‖φC a‖ = ‖a‖
  norm_ψB : ∀ b, ‖ψB b‖ = ‖b‖
  norm_ψC_le : ∀ c, ‖ψC c‖ ≤ ‖c‖
  square : ∀ a, ψB (φB a) = ψC (φC a)
  row : ∀ (b : B) (c : C), ψB b = ψC c → ∃! a : A, φB a = b ∧ φC a = c
  max_norm : ∀ a : A, max ‖φB a‖ ‖φC a‖ = ‖a‖
  secD : D → C
  ψC_secD : ∀ x, ψC (secD x) = x
  norm_secD : ∀ x, ‖secD x‖ = ‖x‖
  tB : B
  tB_isUnit : IsUnit tB
  norm_tB_lt_one : ‖tB‖ < 1
  norm_tB_pos : 0 < ‖tB‖
  norm_tB_mul : ∀ x, ‖tB * x‖ = ‖tB‖ * ‖x‖
  tC : C
  tC_isUnit : IsUnit tC
  norm_tC_lt_one : ‖tC‖ < 1
  norm_tC_pos : 0 < ‖tC‖
  norm_tC_mul : ∀ x, ‖tC * x‖ = ‖tC‖ * ‖x‖
  tD : D
  tD_isUnit : IsUnit tD
  norm_tD_lt_one : ‖tD‖ < 1
  norm_tD_pos : 0 < ‖tD‖
  norm_tD_mul : ∀ x, ‖tD * x‖ = ‖tD‖ * ‖x‖

namespace Pinch

variable (S : Pinch A B C D) (m : ℕ)
/-- Coefficientwise `φB : P_A → P_B`. -/
noncomputable def extB : P A m →+* P B m :=
  mapRestricted S.φB S.norm_φB_le _

/-- Coefficientwise `φC : P_A → P_C`. -/
noncomputable def extC : P A m →+* P C m :=
  mapRestricted S.φC (fun a => le_of_eq (S.norm_φC a)) _

/-- Coefficientwise `ψB : P_B → P_D`. -/
noncomputable def extDB : P B m →+* P D m :=
  mapRestricted S.ψB (fun b => le_of_eq (S.norm_ψB b)) _

/-- Coefficientwise `ψC : P_C → P_D`. -/
noncomputable def extDC : P C m →+* P D m :=
  mapRestricted S.ψC S.norm_ψC_le _


theorem ext_square_commutes (p : P A m) :
    S.extDB m (S.extB m p) = S.extDC m (S.extC m p) := by
  refine Subtype.ext ?_
  show MvPowerSeries.map S.ψB (MvPowerSeries.map S.φB p.1) =
    MvPowerSeries.map S.ψC (MvPowerSeries.map S.φC p.1)
  refine MvPowerSeries.ext fun s => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_map]
  exact S.square _



set_option backward.isDefEq.respectTransparency false in
/-- Coefficientwise sectioning: the extended `ψC` is strictly surjective with
constant 1 ([FJP] Lemma 4.1's κ=1 section, abstractly). -/
theorem extDC_strict_surjective (d : P D m) :
    ∃ c : P C m, S.extDC m c = d ∧ ‖c‖ = ‖d‖ := by
  classical
  have hmem : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => S.secD (MvPowerSeries.coeff s d.1)) := by
    have hd : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) d.1 := d.2
    unfold MvPowerSeries.IsRestrictedGauss at hd ⊢
    refine hd.congr fun s => ?_
    show ‖MvPowerSeries.coeff s d.1‖ * _ =
      ‖MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1))‖ * _
    rw [show MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1)) =
      S.secD (MvPowerSeries.coeff s d.1) from rfl, S.norm_secD]
  refine ⟨⟨fun s => S.secD (MvPowerSeries.coeff s d.1), hmem⟩, ?_, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.ψC (fun s => S.secD (MvPowerSeries.coeff s d.1)) = d.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    show S.ψC (S.secD (MvPowerSeries.coeff s d.1)) = MvPowerSeries.coeff s d.1
    rw [S.ψC_secD]
  · rw [MvRestricted.norm_eq, MvRestricted.norm_eq, MvPowerSeries.gaussNorm,
      MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    show ‖MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1))‖ * _ = _
    rw [show MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1)) =
      S.secD (MvPowerSeries.coeff s d.1) from rfl, S.norm_secD]




set_option backward.isDefEq.respectTransparency false in
/-- The extended square is cartesian ([FJP] Lemma 4.1, abstractly): a compatible
pair comes from a unique element of `P_A`, coefficientwise via the base row and the
pullback max-norm identity. -/
theorem ext_milnorRow_exact (b : P B m) (c : P C m)
    (h : S.extDB m b = S.extDC m c) :
    ∃! p : P A m, S.extB m p = b ∧ S.extC m p = c := by
  classical
  have hcoeff : ∀ s : Fin m →₀ ℕ, S.ψB (MvPowerSeries.coeff s b.1) =
      S.ψC (MvPowerSeries.coeff s c.1) := fun s => by
    have h0 := congrArg (fun x : P D m => MvPowerSeries.coeff s x.1) h
    have h1 : MvPowerSeries.coeff s (MvPowerSeries.map S.ψB b.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.ψC c.1) := h0
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h1
  choose a ha using fun s => (S.row _ _ (hcoeff s)).exists
  have hanorm : ∀ s, ‖a s‖ =
      max ‖MvPowerSeries.coeff s b.1‖ ‖MvPowerSeries.coeff s c.1‖ := fun s => by
    rw [← S.max_norm (a s), (ha s).1, (ha s).2]
  have hres : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => a s) := by
    have hb : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) b.1 := b.2
    have hc : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) c.1 := c.2
    unfold MvPowerSeries.IsRestrictedGauss at hb hc ⊢
    have hmaxlim := hb.max hc
    rw [max_self (0 : ℝ)] at hmaxlim
    refine hmaxlim.congr fun s => ?_
    show max (‖MvPowerSeries.coeff s b.1‖ * _) (‖MvPowerSeries.coeff s c.1‖ * _) = _
    simp only [finsupp_prod_one, mul_one]
    rw [show ‖MvPowerSeries.coeff s (fun s => a s)‖ = ‖a s‖ from rfl, hanorm s]
  refine ⟨⟨fun s => a s, hres⟩, ⟨?_, ?_⟩, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.φB (fun s => a s) = b.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    exact (ha s).1
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.φC (fun s => a s) = c.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    exact (ha s).2
  · rintro q ⟨hqb, hqc⟩
    refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
    have h1 : S.φB (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s b.1 := by
      have := congrArg (fun x : P B m => MvPowerSeries.coeff s x.1) hqb
      show S.φB (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s b.1
      have h2 : MvPowerSeries.coeff s (MvPowerSeries.map S.φB q.1) =
          MvPowerSeries.coeff s b.1 := this
      rwa [MvPowerSeries.coeff_map] at h2
    have h2 : S.φC (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s c.1 := by
      have := congrArg (fun x : P C m => MvPowerSeries.coeff s x.1) hqc
      have h3 : MvPowerSeries.coeff s (MvPowerSeries.map S.φC q.1) =
          MvPowerSeries.coeff s c.1 := this
      rwa [MvPowerSeries.coeff_map] at h3
    exact (S.row _ _ (hcoeff s)).unique ⟨h1, h2⟩ ⟨(ha s).1, (ha s).2⟩

/-- Pullback-norm identity for the extended square (constants 1). -/
theorem ext_max_norm_eq (p : P A m) :
    max ‖S.extB m p‖ ‖S.extC m p‖ = ‖p‖ := by
  have h1 : ‖S.extC m p‖ = ‖p‖ := by
    rw [MvRestricted.norm_eq, MvRestricted.norm_eq]
    show MvPowerSeries.gaussNorm _ _ (MvPowerSeries.map S.φC p.1) = _
    rw [MvPowerSeries.gaussNorm, MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    rw [MvPowerSeries.coeff_map, S.norm_φC]
  have h2 : ‖S.extB m p‖ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
  rw [h1]
  exact max_eq_right h2

/-- `P_A → P_B ⊕ P_C` is injective (left exactness of the extended row),
from the base row's uniqueness. -/
theorem ext_pair_injective :
    Function.Injective (fun p : P A m =>
      (S.extB m p, S.extC m p)) := by
  intro p q h
  have hB := congrArg Prod.fst h
  have hC := congrArg Prod.snd h
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  have h1 : S.φB (MvPowerSeries.coeff s p.1) = S.φB (MvPowerSeries.coeff s q.1) := by
    have := congrArg (fun x : P B m => MvPowerSeries.coeff s x.1) hB
    have h2 : MvPowerSeries.coeff s (MvPowerSeries.map S.φB p.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.φB q.1) := this
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h2
  have h2 : S.φC (MvPowerSeries.coeff s p.1) = S.φC (MvPowerSeries.coeff s q.1) := by
    have := congrArg (fun x : P C m => MvPowerSeries.coeff s x.1) hC
    have h3 : MvPowerSeries.coeff s (MvPowerSeries.map S.φC p.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.φC q.1) := this
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h3
  have hsqp : S.ψB (S.φB (MvPowerSeries.coeff s p.1)) =
      S.ψC (S.φC (MvPowerSeries.coeff s p.1)) := S.square _
  exact (S.row (S.φB (MvPowerSeries.coeff s p.1)) (S.φC (MvPowerSeries.coeff s p.1))
    hsqp).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩



end Pinch

end FiniteJet

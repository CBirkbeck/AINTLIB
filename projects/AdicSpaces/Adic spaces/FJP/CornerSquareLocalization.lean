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



/-! ### The graph data ([FJP] (4.6)) -/

section Graph

variable [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B]
  [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D]

variable (g : A) (f : Fin m → A)

/-- The graph relations `r_i = gT_i − f_i` in `P_A` ([FJP] (4.6)). -/
noncomputable def rA : Fin m → P A m := fun i =>
  polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))

/-- The pushed relations at the vertices. -/
noncomputable def rB : Fin m → P B m := fun i => S.extB m (rA m g f i)
noncomputable def rC : Fin m → P C m := fun i => S.extC m (rA m g f i)
noncomputable def rD : Fin m → P D m := fun i => S.extDC m (S.rC m g f i)

/-- Graph ideals `I_E = im(d₁) = (r₁, …, r_m)` ([FJP] (4.6)). -/
noncomputable def IA : Ideal (P A m) := Ideal.span (Set.range (rA m g f))
noncomputable def IB : Ideal (P B m) := Ideal.span (Set.range (S.rB m g f))
noncomputable def IC : Ideal (P C m) := Ideal.span (Set.range (S.rC m g f))
noncomputable def ID : Ideal (P D m) := Ideal.span (Set.range (S.rD m g f))

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The pushed data generate the unit ideal at each vertex ([FJP] §4 after (4.6)). -/
theorem span_pushed_B (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.φB g} ∪ Set.range (fun i => S.φB (f i))) = ⊤ := by
  have h := congrArg (Ideal.map S.φB) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem span_pushed_C (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.φC g} ∪ Set.range (fun i => S.φC (f i))) = ⊤ := by
  have h := congrArg (Ideal.map S.φC) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem span_pushed_D (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.ψC (S.φC g)} ∪
      Set.range (fun i => S.ψC (S.φC (f i)))) = ⊤ := by
  have h := congrArg (Ideal.map (S.ψC.comp S.φC)) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem rB_eq (i : Fin m) : S.rB m g f i =
    polyToP (MvPolynomial.C (S.φB g) * MvPolynomial.X i -
      MvPolynomial.C (S.φB (f i))) := by
  show mapRestricted S.φB S.norm_φB_le _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] in
theorem rC_eq (i : Fin m) : S.rC m g f i =
    polyToP (MvPolynomial.C (S.φC g) * MvPolynomial.X i -
      MvPolynomial.C (S.φC (f i))) := by
  show mapRestricted S.φC (fun a => le_of_eq (S.norm_φC a)) _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

omit [NormOneClass B] [CompleteSpace B] in
theorem rD_eq (i : Fin m) : S.rD m g f i =
    polyToP (MvPolynomial.C (S.ψC (S.φC g)) * MvPolynomial.X i -
      MvPolynomial.C (S.ψC (S.φC (f i)))) := by
  show mapRestricted S.ψC S.norm_ψC_le _ (S.rC m g f i) = _
  rw [S.rC_eq, StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The pushed generators are compatible across the square. -/
theorem extDB_rB (i : Fin m) : S.extDB m (S.rB m g f i) = S.rD m g f i :=
  S.ext_square_commutes m (rA m g f i)

/-! ### Lemma 4.3 — controlled graph-ideal pullback ([FJP] (4.11)–(4.16)) -/

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] in
/-- Right strict surjectivity of the ideal row ([FJP] (4.11)). -/
theorem ideal_row_surjective (hPD : IsNoetherianRing (P D m))
    (hPDball : IsNoetherianRing (unitBall (P D m)))
    (_hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ y ∈ S.ID m g f,
      ∃ xc ∈ S.IC m g f, S.extDC m xc = y ∧ ‖xc‖ ≤ Cs * ‖y‖ := by
  classical
  have := hPD
  obtain ⟨h, hh1, hlift⟩ := exists_d1_lift (E := D) S.tD S.tD_isUnit
    S.norm_tD_lt_one S.norm_tD_pos S.norm_tD_mul hPDball (S.rD m g f)
  set Cr : ℝ := 1 + ∑ i, ‖S.rC m g f i‖ with hCr
  have hCr1 : 1 ≤ Cr := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  refine ⟨h * Cr, ?_, fun y hy => ?_⟩
  · calc (1 : ℝ) ≤ h := hh1
      _ = h * 1 := (mul_one h).symm
      _ ≤ h * Cr := mul_le_mul_of_nonneg_left hCr1 (zero_le_one.trans hh1)
  · obtain ⟨u, hu, hun⟩ := hlift y hy
    have hsec : ∀ i, ∃ c : P C m, S.extDC m c = u i ∧ ‖c‖ = ‖u i‖ := fun i =>
      S.extDC_strict_surjective m (u i)
    choose cc hcc hccn using hsec
    refine ⟨d1 (S.rC m g f) cc, ?_, ?_, ?_⟩
    · show d1 (S.rC m g f) cc ∈ Ideal.span (Set.range (S.rC m g f))
      unfold d1
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · rw [show S.extDC m (d1 (S.rC m g f) cc) =
        d1 (fun i => S.extDC m (S.rC m g f i)) (fun i => S.extDC m (cc i)) from
          d1_map (S.extDC m) _ cc,
        show (fun i => S.extDC m (S.rC m g f i)) = S.rD m g f from rfl,
        show (fun i => S.extDC m (cc i)) = u from funext hcc]
      exact hu
    · have hterm : ∀ i : Fin m, ‖cc i * S.rC m g f i‖ ≤ ‖u‖ * Cr := fun i => by
        calc ‖cc i * S.rC m g f i‖ ≤ ‖cc i‖ * ‖S.rC m g f i‖ := norm_mul_le _ _
          _ = ‖u i‖ * ‖S.rC m g f i‖ := by rw [hccn i]
          _ ≤ ‖u‖ * Cr := by
              refine mul_le_mul (norm_le_pi_norm u i) ?_ (norm_nonneg _) (norm_nonneg u)
              rw [hCr]
              refine le_add_of_nonneg_of_le zero_le_one ?_
              exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have hpartial : ∀ s : Finset (Fin m),
          ‖∑ i ∈ s, cc i * S.rC m g f i‖ ≤ ‖u‖ * Cr := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, norm_zero]
          exact mul_nonneg (norm_nonneg u) (zero_le_one.trans hCr1)
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hterm a) ih)
      show ‖d1 (S.rC m g f) cc‖ ≤ h * Cr * ‖y‖
      unfold d1
      refine (hpartial Finset.univ).trans ?_
      calc ‖u‖ * Cr ≤ h * ‖y‖ * Cr :=
            mul_le_mul_of_nonneg_right hun (zero_le_one.trans hCr1)
        _ = h * Cr * ‖y‖ := by ring

end Graph

end Pinch

end FiniteJet

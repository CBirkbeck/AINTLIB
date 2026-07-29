/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.CoeffLocalization
import «Adic spaces».WP.Chart
import «Adic spaces».SheafyRing
import «Adic spaces».StructureSheaf
import «Adic spaces».SheafyEndpoints
import «Adic spaces».RelativeStandardRefinement
import «Adic spaces».StructurePresheafBundled

/-!
# `𝒜` is (strongly) sheafy ([WP] §6.5, thm:parity-strongly-sheafy)

The two `IsSheafy` fields (finite rational covers: topological embedding + gluing)
are produced by the finite-head Čech argument:

1. Push the covering data into one head: scale entries into the unit ball, choose
   integral Bezout relations, approximate by head elements (density,
   `exists_head_approx`) and apply the small perturbation lemma — none of this
   changes the rational subsets or the section rings ([WP] proof of
   thm:parity-strongly-sheafy, first two paragraphs).
2. The pushed data are rational in the head `P_M` (apply the coefficient retraction
   `ρ_M` to the Bezout relation), and the corresponding rational subsets COVER
   `Spa(P_M, P_M°)` — via the split surjection
   `Spa(E,E°) → Spa(P_M,P_M°)` induced by the isometric pair
   `P_M → E → P_M` ([WP], "We verify that the `V_i` cover", eq:split-spectrum-map;
   the paper warns: do NOT identify `U` with the maximal-pair spectrum).
3. The head is sheafy (Wedhorn 8.28(b), `isSheafy_WPHead`); its Čech equalizer
   isomorphism has a BOUNDED inverse (closed range + open mapping — the no-Baire
   route `isInducing_of_closedRange_of_topNilpUnit` of `WedhornBanachTheorem.lean`,
   at the normed model `QHead`); gluing then proceeds coefficientwise with uniform
   norm control, and the glued family is again null
   ([WP] eq:head-cech, eq:coefficientwise-gluing-bound).

**Strong sheafiness**: the whole construction is uniform in the weight `w`; the Tate
extension `𝒜⟨V_1,…,V_s⟩` is the weighted-parity algebra at the shifted weight
(`shiftWeight`), so `isSheafy_WPA` applied at `shiftWeight w s` gives sheafiness of
every finite Tate extension ([WP] eq:strong-sheafy-decomposition: "the preceding
proof applies verbatim").  The bridge to the project's own Tate-extension
(`restrictedMvPowerSeriesSubring`) is `tateExtEquiv`.
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
/-- A common head stage for every datum of a finite rational covering
(shared W21/W22 infrastructure: `nonempty_headModelData_all` + a `Finset.sup`
of the thresholds). -/
theorem exists_common_headModel_stage (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    ∃ M : ℕ, (∃ (DHb : RationalLocData (WPHead K w M)) (hDHb : DHb.IsRational),
        rationalOpen (liftDatum DHb hDHb).T (liftDatum DHb hDHb).s =
          rationalOpen C.base.T C.base.s) ∧
      ∀ D ∈ C.covers,
        ∃ (DH : RationalLocData (WPHead K w M)) (hDH : DH.IsRational),
          rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s =
            rationalOpen D.T D.s := by
  classical
  obtain ⟨Nb, hb⟩ := nonempty_headModelData_all ϖ hK₀ C.base hC.base
  choose Np hp using fun (D : { D : RationalLocData (WPA K w) // D ∈ C.covers }) =>
    nonempty_headModelData_all ϖ hK₀ D.1 (hC.piece D.2)
  set M : ℕ := max Nb (C.covers.attach.sup Np) with hM_def
  refine ⟨M, hb M (by rw [hM_def]; exact le_max_left _ _), fun D hD => ?_⟩
  refine hp ⟨D, hD⟩ M ?_
  rw [hM_def]
  exact le_trans (Finset.le_sup (Finset.mem_attach _ ⟨D, hD⟩))
    (le_max_right _ _)

variable {K w} in
theorem rhoHead_continuous (M : ℕ) :
    Continuous (rhoHead K w M) :=
  AddMonoidHomClass.continuous_of_bound (rhoHead K w M) 1 fun f => by
    rw [one_mul]
    exact norm_rhoHead_le (K := K) (w := w) (N := M) f

variable {K w} in
/-- Norm bound extraction for power-bounded elements of `𝒜` (topological
boundedness at the unit ball against a scaling constant). -/
theorem norm_bound_of_isPowerBounded {a : WPA K w}
    (ha : TopologicalRing.IsPowerBounded a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C := by
  obtain ⟨V, hV, hSV⟩ := ha (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have h1 : (0 : ℝ) < ‖constA K w c‖ := by rw [norm_constA]; exact hc0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0
    (by rw [norm_constA]; exact hc1 : ‖constA K w c‖ < 1)
  have hnc : ‖constA K w c ^ k‖ = ‖constA K w c‖ ^ k := by
    rw [← map_pow, norm_constA, norm_pow, norm_constA]
  refine ⟨1 / ‖constA K w c‖ ^ k, by positivity, fun n => ?_⟩
  have hmem : a ^ n * constA K w c ^ k ∈ Metric.ball (0 : WPA K w) 1 := by
    refine hSV (Set.mul_mem_mul ⟨n, rfl⟩ (hball ?_))
    rw [Metric.mem_ball, dist_zero_right, hnc]
    exact hk
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hval : ‖a ^ n * constA K w c ^ k‖ = ‖constA K w c‖ ^ k * ‖a ^ n‖ := by
    rw [show constA K w c ^ k = constA K w (c ^ k) from by rw [map_pow],
      mul_comm (a ^ n), norm_constA_mul]
    rw [show ‖constA K w c‖ ^ k = ‖c‖ ^ k from by rw [norm_constA],
      norm_pow]
  rw [hval] at hmem
  rw [le_div_iff₀ (by positivity)]
  calc ‖a ^ n‖ * ‖constA K w c‖ ^ k = ‖constA K w c‖ ^ k * ‖a ^ n‖ := by ring
    _ ≤ 1 := hmem.le

variable {K w} in
/-- `rhoHead` sends power-bounded elements to power-bounded elements. -/
theorem isPowerBounded_rhoHead {a : WPA K w} (M : ℕ)
    (ha : TopologicalRing.IsPowerBounded a) :
    TopologicalRing.IsPowerBounded (rhoHead K w M a) := by
  obtain ⟨C, hC0, hC⟩ := norm_bound_of_isPowerBounded ha
  refine isPowerBounded_of_forall_norm_le hC0 fun n => ?_
  rw [← map_pow]
  exact le_trans (norm_rhoHead_le (K := K) (w := w) (N := M) _) (hC n)

variable {K w} in
theorem plus_le_comap_rhoHead (M : ℕ) :
    ((WPA K w)⁺ : Subring (WPA K w)) ≤
      ((WPHead K w M)⁺ : Subring (WPHead K w M)).comap (rhoHead K w M) :=
  fun _ ha => isPowerBounded_rhoHead M ha

variable {K w} in
theorem comap_rhoHead_mem_spa (M : ℕ) {v : Spv (WPHead K w M)}
    (hv : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺)) :
    ValuationSpectrum.comap (rhoHead K w M) v ∈ Spa (WPA K w) ((WPA K w)⁺) :=
  comap_mem_spa (rhoHead_continuous M) (plus_le_comap_rhoHead M) hv

variable {K w} in
open scoped Classical in
/-- Membership transfer along the `rhoHead` pullback: a head point lies in a head
datum's rational subset iff its pullback lies in the lifted datum's ([WP]
1156–1218, realized by the retraction instead of the split surjection — the
project's models are `𝒜`-global). -/
theorem comap_rhoHead_mem_iff (M : ℕ) (DH : RationalLocData (WPHead K w M))
    (hDH : DH.IsRational) (v : Spv (WPHead K w M))
    (hv : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺)) :
    ValuationSpectrum.comap (rhoHead K w M) v ∈
      rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s ↔
      v ∈ rationalOpen DH.T DH.s := by
  constructor
  · rintro ⟨-, hT, hs0⟩
    refine ⟨hv, fun t ht => ?_, fun hc => ?_⟩
    · have h1 := hT (headIncl K w M t) (by
        rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        exact Finset.mem_image_of_mem _ ht)
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl] at h1
      rw [comap_vle,
        show rhoHead K w M (headIncl K w M t) = t from
          rhoHead_headIncl (K := K) (w := w) (N := M) t,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s] at h1
      exact h1
    · refine hs0 ?_
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        map_zero,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s]
      exact hc
  · rintro ⟨-, hT, hs0⟩
    refine ⟨comap_rhoHead_mem_spa M hv, fun t' ht' => ?_, fun hc => ?_⟩
    · rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        at ht'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        show rhoHead K w M (headIncl K w M t) = t from
          rhoHead_headIncl (K := K) (w := w) (N := M) t,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s]
      exact hT t ht
    · refine hs0 ?_
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        map_zero,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s] at hc
      exact hc

variable {K w} in
/-- A common-stage system of head data for a whole covering, with the
rational-subset identifications — the carrier consumed by the embedding and
gluing fields (shared W21/W22 infrastructure; [WP] 1156–1218). -/
structure PushedHeadData (C : RationalCoveringData (WPA K w)) where
  /-- The common head stage. -/
  M : ℕ
  /-- The base head datum. -/
  DHb : RationalLocData (WPHead K w M)
  hDHb : DHb.IsRational
  hopenb : rationalOpen (liftDatum DHb hDHb).T (liftDatum DHb hDHb).s =
    rationalOpen C.base.T C.base.s
  /-- The per-piece head data. -/
  DHp : ↥C.covers → RationalLocData (WPHead K w M)
  hDHp : ∀ D, (DHp D).IsRational
  hopenp : ∀ D, rationalOpen (liftDatum (DHp D) (hDHp D)).T
    (liftDatum (DHp D) (hDHp D)).s = rationalOpen (D : ↥C.covers).1.T
      (D : ↥C.covers).1.s

variable {K w} in
theorem nonempty_pushedHeadData (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Nonempty (PushedHeadData C) := by
  classical
  obtain ⟨M, ⟨DHb, hDHb, hopenb⟩, hp⟩ :=
    exists_common_headModel_stage ϖ hK₀ C hC
  choose DHp hDHp hopenp using fun (D : ↥C.covers) => hp D.1 D.2
  exact ⟨⟨M, DHb, hDHb, hopenb, DHp, hDHp, hopenp⟩⟩

variable {K w} in
open scoped Classical in
/-- The head covering data associated to a pushed system. -/
noncomputable def PushedHeadData.cover {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) : RationalCoveringData (WPHead K w P.M) where
  base := P.DHb
  covers := C.covers.attach.image P.DHp
  hsubset := by
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w P.M) ((WPHead K w P.M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff P.M (P.DHp D) (P.hDHp D) v hvspa).mpr hv
    rw [P.hopenp D] at h1
    have h2 := C.hsubset D.1 D.2 h1
    rw [← P.hopenb] at h2
    exact (comap_rhoHead_mem_iff P.M P.DHb P.hDHb v hvspa).mp h2
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w P.M) ((WPHead K w P.M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff P.M P.DHb P.hDHb v hvspa).mpr hv
    rw [P.hopenb] at h1
    obtain ⟨D, hD, hmem⟩ := C.hcover _ h1
    refine ⟨P.DHp ⟨D, hD⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    have h2 : ValuationSpectrum.comap (rhoHead K w P.M) v ∈
        rationalOpen (liftDatum (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩)).T
          (liftDatum (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩)).s := by
      rw [P.hopenp ⟨D, hD⟩]
      exact hmem
    exact (comap_rhoHead_mem_iff P.M (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩) v
      hvspa).mp h2

variable {K w} in
open scoped Classical in
theorem PushedHeadData.cover_isRational {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) : P.cover.IsRational := by
  refine ⟨P.hDHb, ?_⟩
  intro DH' hDH'
  obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
  exact P.hDHp D

variable {K w} in
open scoped Classical in
theorem PushedHeadData.piece_subset {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) (D : ↥C.covers) :
    rationalOpen (P.DHp D).T (P.DHp D).s ⊆
      rationalOpen P.DHb.T P.DHb.s :=
  P.cover.hsubset (P.DHp D)
    (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))

variable {K w} in
open scoped Classical in
/-- The head-level restriction between graph models along a pushed covering
piece (the `headLocEquiv`-conjugated restriction map;
[WP] eq:cover-coefficientwise's coefficient hom). -/
noncomputable def qRestrict {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    QHead P.DHb →+* QHead (P.DHp D) :=
  ((headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).toRingHom.comp
    (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D))).comp
    (headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm.toRingHom

variable {K w} in
open scoped Classical in
/-- `qRestrict` matches the head constants (the generator law of the
naturality square). -/
theorem qRestrict_headConst {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) (x : WPHead K w P.M) :
    qRestrict ϖ hK₀ P D (headConst P.DHb x) =
      headConst (P.DHp D) x := by
  have h1 : (headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm (headConst P.DHb x) =
      P.DHb.canonicalMap x := by
    have h2 : headLocEquiv ϖ hK₀ P.DHb P.hDHb (P.DHb.canonicalMap x) =
        headConst P.DHb x := by
      rw [show headLocEquiv ϖ hK₀ P.DHb P.hDHb (P.DHb.canonicalMap x) =
        headLocFwd ϖ P.DHb P.hDHb (P.DHb.canonicalMap x) from rfl,
        show P.DHb.canonicalMap x = P.DHb.coeRingHom
          (algebraMap (WPHead K w P.M) (Localization.Away P.DHb.s) x) from rfl,
        headLocFwd_coe, headLocFwdAlg_algebraMap]
    rw [← h2, RingEquiv.symm_apply_apply]
  show headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
    (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D)
      ((headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm (headConst P.DHb x))) =
    headConst (P.DHp D) x
  rw [h1, restrictionMapHom_canonicalMap_generic]
  rw [show headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
      ((P.DHp D).canonicalMap x) =
    headLocFwd ϖ (P.DHp D) (P.hDHp D) ((P.DHp D).canonicalMap x) from rfl,
    show (P.DHp D).canonicalMap x = (P.DHp D).coeRingHom
      (algebraMap (WPHead K w P.M) (Localization.Away (P.DHp D).s) x)
      from rfl,
    headLocFwd_coe, headLocFwdAlg_algebraMap]

variable {K w} in
/-- Scalar scaling of the graph-model quotient norm: the easy half
(submultiplicativity + the nonexpansive constants). -/
theorem norm_qscale_le {M : ℕ} (DH : RationalLocData (WPHead K w M)) (c : K)
    (q : QHead DH) :
    ‖headConst DH (constHead K w M c) * q‖ ≤ ‖c‖ * ‖q‖ := by
  refine le_trans (norm_mul_le _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg q)
  refine le_trans (norm_headConst_le DH _) ?_
  exact le_of_eq (by rw [norm_constHead])

variable {K w} in
/-- Exact scalar scaling of the graph-model quotient norm. -/
theorem norm_qscale {M : ℕ} (DH : RationalLocData (WPHead K w M)) {c : K}
    (hc0 : 0 < ‖c‖) (q : QHead DH) :
    ‖headConst DH (constHead K w M c) * q‖ = ‖c‖ * ‖q‖ := by
  have hcne : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  refine le_antisymm (norm_qscale_le DH c q) ?_
  have h1 := norm_qscale_le DH c⁻¹ (headConst DH (constHead K w M c) * q)
  rw [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hcne, map_one,
    map_one, one_mul, norm_inv] at h1
  calc ‖c‖ * ‖q‖
      ≤ ‖c‖ * (‖c‖⁻¹ * ‖headConst DH (constHead K w M c) * q‖) :=
        mul_le_mul_of_nonneg_left h1 hc0.le
    _ = ‖headConst DH (constHead K w M c) * q‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc0), one_mul]

variable {K w} in
open scoped Classical in
theorem qRestrict_continuous {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    Continuous (qRestrict ϖ hK₀ P D) := by
  rw [qRestrict, RingHom.coe_comp, RingHom.coe_comp]
  refine Continuous.comp (Continuous.comp ?_ ?_) ?_
  · exact headLocEquiv_continuous ϖ hK₀ (P.DHp D) (P.hDHp D)
  · letI : UniformSpace (Localization.Away P.DHb.s) := P.DHb.uniformSpace
    letI : IsTopologicalRing (Localization.Away P.DHb.s) :=
      P.DHb.isTopologicalRing
    letI : IsUniformAddGroup (Localization.Away P.DHb.s) :=
      P.DHb.isUniformAddGroup
    exact UniformSpace.Completion.continuous_extension
  · exact headLocEquiv_symm_continuous ϖ hK₀ P.DHb P.hDHb

variable {K w} in
open scoped Classical in
/-- The head restriction is bounded (continuity at `0` + the exact
nonarchimedean window scaling with `ℤ`-powers of the window constant). -/
theorem qRestrict_bound {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ q : QHead P.DHb,
      ‖qRestrict ϖ hK₀ P D q‖ ≤ Cb * ‖q‖ := by
  classical
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have hcne : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  have hcRne : ‖c‖ ≠ 0 := ne_of_gt hc0
  have hcont := (qRestrict_continuous ϖ hK₀ P D).tendsto 0
  rw [map_zero] at hcont
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont (Metric.ball_mem_nhds 0 one_pos))
  refine ⟨1 / (‖c‖ * δ), by positivity, fun q => ?_⟩
  rcases eq_or_lt_of_le (norm_nonneg q) with hq0 | hq0
  · rw [show q = 0 from by rw [← norm_eq_zero]; exact hq0.symm, map_zero,
      norm_zero, norm_zero, mul_zero]
  have hinv1 : (1 : ℝ) < ‖c‖⁻¹ := (one_lt_inv₀ hc0).mpr hc1
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow
    (x := ‖q‖ / δ) (by positivity) hinv1
  rw [Set.mem_Ico] at hn
  -- upper: ‖c‖^(n+1)·‖q‖ < δ
  have hupper : ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ < δ := by
    have h2 := hn.2
    rw [div_lt_iff₀ hδ0] at h2
    have h3 := mul_lt_mul_of_pos_left h2 (zpow_pos hc0 (n + 1))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n + 1 : ℤ) * δ) =
      (‖c‖ * ‖c‖⁻¹) ^ (n + 1 : ℤ) * δ from by
        rw [mul_zpow, mul_assoc],
      mul_inv_cancel₀ hcRne, one_zpow, one_mul] at h3
    exact h3
  -- lower: δ·‖c‖ ≤ ‖c‖^(n+1)·‖q‖
  have hlower : δ * ‖c‖ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := by
    have h2 := hn.1
    rw [le_div_iff₀ hδ0] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (zpow_pos hc0 (n + 1)))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n : ℤ) * δ) =
      ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ * δ from by
        rw [inv_zpow, mul_assoc],
      show ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ =
        ‖c‖ ^ (n + 1 - n : ℤ) from by
        rw [zpow_sub₀ hcRne, div_eq_mul_inv],
      show (n + 1 - n : ℤ) = 1 from by ring,
      zpow_one] at h3
    calc δ * ‖c‖ = ‖c‖ * δ := by ring
      _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := h3
  -- the scaled element
  set a : K := c ^ (n + 1 : ℤ) with ha_def
  have hna : ‖a‖ = ‖c‖ ^ (n + 1 : ℤ) := by rw [ha_def, norm_zpow]
  have hna0 : 0 < ‖a‖ := by rw [hna]; exact zpow_pos hc0 _
  have hmem : ‖qRestrict ϖ hK₀ P D
      (headConst P.DHb (constHead K w P.M a) * q)‖ < 1 := by
    have h4 : headConst P.DHb (constHead K w P.M a) * q ∈
        Metric.ball (0 : QHead P.DHb) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_qscale P.DHb hna0 q, hna]
      exact hupper
    have h5 := hball h4
    rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at h5
    exact h5
  rw [map_mul, qRestrict_headConst,
    norm_qscale (P.DHp D) hna0 _, hna] at hmem
  -- extract the bound
  have hpow : (0 : ℝ) < ‖c‖ ^ (n + 1 : ℤ) := zpow_pos hc0 _
  have h6 : ‖qRestrict ϖ hK₀ P D q‖ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ :=
    calc ‖qRestrict ϖ hK₀ P D q‖ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ *
          (‖c‖ ^ (n + 1 : ℤ) * ‖qRestrict ϖ hK₀ P D q‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]
      _ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ * 1 :=
          mul_lt_mul_of_pos_left hmem (by positivity)
      _ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ := mul_one _
  refine le_trans h6.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < ‖c‖ * δ)]
  calc (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ * δ)
      ≤ (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ ^ (n + 1 : ℤ) * ‖q‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖c‖ * δ = δ * ‖c‖ := by ring
          _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := hlower
    _ = ‖q‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]

variable {K w} in
open scoped Classical in
/-- **The pushed head covering** ([WP] 1156–1218): a rational covering of `𝒜`
with common-stage head data transfers to a rational covering on the head, with
subset and covering properties by the `rhoHead` pullback. -/
theorem exists_pushedHeadCover (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    ∃ (M : ℕ) (C' : RationalCoveringData (WPHead K w M)), C'.IsRational := by
  classical
  obtain ⟨M, ⟨DHb, hDHb, hopenb⟩, hp⟩ :=
    exists_common_headModel_stage ϖ hK₀ C hC
  choose DHp hDHp hopenp using fun (D : ↥C.covers) => hp D.1 D.2
  refine ⟨M, ⟨DHb, C.covers.attach.image DHp, ?_, ?_⟩, ?_, ?_⟩
  · -- hsubset
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff M (DHp D) (hDHp D) v hvspa).mpr hv
    rw [hopenp D] at h1
    have h2 := C.hsubset D.1 D.2 h1
    rw [← hopenb] at h2
    exact (comap_rhoHead_mem_iff M DHb hDHb v hvspa).mp h2
  · -- hcover
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff M DHb hDHb v hvspa).mpr hv
    rw [hopenb] at h1
    obtain ⟨D, hD, hmem⟩ := C.hcover _ h1
    refine ⟨DHp ⟨D, hD⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    have h2 : ValuationSpectrum.comap (rhoHead K w M) v ∈
        rationalOpen (liftDatum (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩)).T
          (liftDatum (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩)).s := by
      rw [hopenp ⟨D, hD⟩]
      exact hmem
    exact (comap_rhoHead_mem_iff M (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩) v hvspa).mp h2
  · -- base rational
    exact hDHb
  · -- pieces rational
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    exact hDHp D

variable {K w} in
/-- The embedding half of the sheaf condition for `𝒜` (the
`productRestrictionSub_isEmbedding_JetA` shape, `FJP/Over/SheafTransfer.lean:667`). -/
theorem productRestrictionSub_isEmbedding_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (WPA K w) C) := by sorry

variable {K w} in
/-- The gluing half of the sheaf condition for `𝒜` (the `gluing_JetA` shape,
`FJP/Over/SheafTransfer.lean:376`; [WP] proof of thm:parity-strongly-sheafy,
coefficientwise Čech gluing with the head bound `C`). -/
theorem gluing_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (WPA K w))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by sorry

variable {K w} in
/-- **`𝒜` is sheafy** — the finite-rational-cover form
([WP] thm:parity-strongly-sheafy; the `isSheafy_JetA` assembly,
`FJP/Over/SheafTransfer.lean:730`). -/
theorem isSheafy_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ValuationSpectrum.IsSheafy (WPA K w) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_WPA ϖ hK₀ C hC
  gluing := fun C hC f hcompat => gluing_WPA ϖ hK₀ C hC f hcompat

/-- The distinguished ring of integral elements: the power-bounded subring
(the `finiteJetPlus` pattern, `FJP/Over/SheafyEndpoints.lean:87`). -/
noncomputable def wpPlus : RingOfIntegralElements (WPA K w) :=
  ⟨((WPA K w)⁺ : Subring (WPA K w)), inferInstance⟩

variable {K w} in
/-- **Pair-level sheafiness** ([WP] thm 6.2 (2), one pair; the
`finiteJet_isSheafyFor` pivot, `FJP/Over/SheafyEndpoints.lean:95`). -/
theorem wp_isSheafyFor (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyFor (WPA K w) (wpPlus K w) := by sorry

variable {K w} in
/-- **All-pairs sheafiness** (via the unconditional `A⁺`-independence
`isSheafyFor_iff_isSheafyComplete`). -/
theorem wp_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyComplete (WPA K w) := by sorry

variable {K w} in
theorem wp_isSheafyFor_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    IsSheafyFor (WPA K w) Bplus :=
  wp_isSheafyComplete ϖ hK₀ Bplus

variable {K w} in
/-- The genuine all-open structure presheaf of `Spa(𝒜, B⁺)` is a sheaf, for every
valid `B⁺` (the `finiteJet_structurePresheaf_isSheaf_all` shape,
`FJP/Over/SheafyEndpoints.lean:213`). -/
theorem wp_structurePresheaf_isSheaf_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((WPA K w)⁺ : Subring (WPA K w)) := Bplus.2
    haveI : HasLocLiftPowerBounded (WPA K w) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (WPA K w)).IsSheaf := by sorry

/-! ### Strong sheafiness ([WP] thm:parity-strongly-sheafy, last paragraph) -/

variable {K w} in
/-- Sheafiness of every shifted-weight algebra — the Tate extensions in the concrete
model ([WP] eq:strong-sheafy-decomposition: "the preceding proof applies verbatim").
This is `isSheafy_WPA` at the shifted weight; recorded as its own statement because
it is the mathematical content of strong sheafiness. -/
theorem isSheafy_WPA_shiftWeight (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    ValuationSpectrum.IsSheafy (WPA K (shiftWeight w s)) :=
  isSheafy_WPA ϖ hK₀

/-- The forward slot map of the Tate-extension bridge. -/
def slotTo (s : ℕ) (n : ℕ) : Fin s ⊕ ℕ :=
  if h : 1 ≤ n ∧ n ≤ s then Sum.inl ⟨n - 1, by omega⟩
  else if n = 0 then Sum.inr 0 else Sum.inr (n - s)

/-- The inverse slot map. -/
def slotInv (s : ℕ) : Fin s ⊕ ℕ → ℕ
  | Sum.inl i => i.1 + 1
  | Sum.inr m => if m = 0 then 0 else m + s

/-- The interleaving slot bijection of the Tate-extension bridge: `0 ↦ inr 0`,
`i ∈ [1..s] ↦ inl (i−1)`, `n > s ↦ inr (n−s)` (the exponent-side realization of
`shiftWeight`: the freed slots `1..s` carry the new Tate variables). -/
def slotEquiv (s : ℕ) : ℕ ≃ (Fin s ⊕ ℕ) where
  toFun := slotTo s
  invFun := slotInv s
  left_inv n := by
    simp only [slotTo]
    split_ifs with h1 h2
    · show n - 1 + 1 = n
      omega
    · show (if (0 : ℕ) = 0 then 0 else 0 + s) = n
      rw [if_pos rfl]
      omega
    · show (if n - s = 0 then 0 else n - s + s) = n
      rw [if_neg (by omega)]
      omega
  right_inv x := by
    rcases x with i | m
    · show slotTo s (i.1 + 1) = Sum.inl i
      simp only [slotTo]
      rw [dif_pos ⟨by omega, by have := i.2; omega⟩]
      congr 1
    · by_cases hm : m = 0
      · subst hm
        show slotTo s (if (0 : ℕ) = 0 then 0 else 0 + s) = Sum.inr 0
        rw [if_pos rfl]
        simp [slotTo]
      · show slotTo s (if m = 0 then 0 else m + s) = Sum.inr m
        rw [if_neg hm]
        simp only [slotTo]
        rw [dif_neg (by omega), if_neg (by omega)]
        congr 1
        omega

variable {K} in
/-- Stage 1 of the Tate-extension bridge: the ambient flatten
`(MvPowerSeries ℕ K)⟦Fin s⟧ ≅ K⟦Fin s ⊕ ℕ⟧ ≅ K⟦ℕ⟧` (Xia `sumAlgEquiv` +
mathlib `renameEquiv` along `slotEquiv`). -/
noncomputable def tateExtAmbient (s : ℕ) :
    MvPowerSeries (Fin s) (MvPowerSeries ℕ K) ≃+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm.trans
    (MvPowerSeries.renameEquiv K (slotEquiv s).symm)).toRingEquiv

variable {K} in
/-- Coefficients of the ambient flatten: transport the exponent through
`slotEquiv` and read the nested coefficient. -/
theorem tateExtAmbient_coeff (s : ℕ)
    (F : MvPowerSeries (Fin s) (MvPowerSeries ℕ K)) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtAmbient (K := K) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (MvPowerSeries.coeff
          (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
            Sum.inl_injective.injOn) F) := by
  have hu : u = Finsupp.embDomain (slotEquiv s).symm.toEmbedding
      (Finsupp.equivMapDomain (slotEquiv s) u) := by
    rw [Finsupp.embDomain_eq_mapDomain,
      show (⇑((slotEquiv s).symm.toEmbedding) : (Fin s ⊕ ℕ) → ℕ) =
        ⇑(slotEquiv s).symm from rfl,
      ← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_trans,
      Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]
  show MvPowerSeries.coeff u
    (MvPowerSeries.rename (⇑((slotEquiv s).symm.toEmbedding))
      ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm F)) = _
  conv_lhs => rw [hu]
  rw [MvPowerSeries.coeff_embDomain_rename]
  rfl

variable {K w} in
/-- The coefficient-value hom `𝒜 → K⟦U⟧` (two subtype layers). -/
noncomputable def wpaVal : WPA K w →+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.isSubring (R := K) (fun _ : ℕ => (1 : ℝ))).subtype).comp
    ((wpSupport K w).subtype)

variable {K w} in
theorem wpaVal_injective : Function.Injective (wpaVal (K := K) (w := w)) := by
  intro a b hab
  have h1 : a.1.1 = b.1.1 := hab
  exact Subtype.ext (Subtype.ext h1)

variable {K w} in
/-- The flatten hom on the nested Tate extension (stage 2 of the bridge). -/
noncomputable def tateExtToFlat (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) →+* MvPowerSeries ℕ K :=
  ((tateExtAmbient (K := K) s).toRingHom.comp
    (MvPowerSeries.map (wpaVal (K := K) (w := w)))).comp
    (restrictedMvPowerSeriesSubring s (WPA K w)).subtype

variable {K w} in
theorem tateExtToFlat_injective (s : ℕ) :
    Function.Injective (tateExtToFlat (K := K) (w := w) s) := by
  rw [tateExtToFlat, RingHom.coe_comp, RingHom.coe_comp]
  refine Function.Injective.comp (Function.Injective.comp ?_ ?_) ?_
  · exact (tateExtAmbient (K := K) s).injective
  · exact MvPowerSeries.map_injective (wpaVal_injective (K := K) (w := w))
  · exact Subring.subtype_injective _

variable {K w} in
/-- Coefficients of the flatten hom: nested coefficient values at the
slot-transported exponent. -/
theorem tateExtToFlat_coeff (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (wpaVal (K := K) (w := w)
          (MvPowerSeries.coeff
            (Finsupp.comapDomain Sum.inl
              (Finsupp.equivMapDomain (slotEquiv s) u)
              Sum.inl_injective.injOn) F.1)) := by
  rw [show tateExtToFlat (K := K) (w := w) s F =
    tateExtAmbient (K := K) s
      (MvPowerSeries.map (wpaVal (K := K) (w := w)) F.1) from rfl,
    tateExtAmbient_coeff, MvPowerSeries.coeff_map]

/-- The `inr`-pull of a flat exponent through the slot bijection. -/
noncomputable def slotInr (s : ℕ) (u : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
    Sum.inr_injective.injOn

theorem slotInr_apply (s : ℕ) (u : ℕ →₀ ℕ) (m : ℕ) :
    slotInr s u m = u (if m = 0 then 0 else m + s) := by
  rw [slotInr, Finsupp.comapDomain_apply, Finsupp.equivMapDomain_apply]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    rfl
  · rw [if_neg hm]
    show u ((slotEquiv s).symm (Sum.inr m)) = u (m + s)
    congr 1
    show slotInv s (Sum.inr m) = m + s
    simp only [slotInv]
    rw [if_neg hm]

theorem slotInr_zero_apply (s : ℕ) (u : ℕ →₀ ℕ) : slotInr s u 0 = u 0 := by
  rw [slotInr_apply, if_pos rfl]

/-- The parity weight at the shifted weight is computed by the `inr`-pull
(the freed slots `1..s` have weight `0`). -/
theorem wpWeight_shiftWeight_eq (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    wpWeight (shiftWeight w s) u = wpWeight w (slotInr s u) := by
  classical
  have hL : wpWeight (shiftWeight w s) u =
      ∑ n ∈ u.support.filter (fun n => u n % 2 = 1 ∧ s < n), w (n - s) := by
    rw [wpWeight, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : u n % 2 = 1 ∧ n ≠ 0
    · rw [if_pos h1]
      by_cases h2 : s < n
      · rw [if_pos ⟨h1.1, h2⟩]
        show (if n ≤ s then 0 else w (n - s)) = w (n - s)
        rw [if_neg (by omega)]
      · rw [if_neg (fun hc => h2 hc.2)]
        show (if n ≤ s then 0 else w (n - s)) = 0
        rw [if_pos (by omega)]
    · rw [if_neg h1, if_neg (fun hc => h1 ⟨hc.1, by omega⟩)]
  have hR : wpWeight w (slotInr s u) =
      ∑ m ∈ (slotInr s u).support.filter
        (fun m => slotInr s u m % 2 = 1 ∧ m ≠ 0), w m := by
    rw [wpWeight, Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun n => n - s) (fun m => m + s) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    have hv : slotInr s u (n - s) = u n := by
      rw [slotInr_apply, if_neg (by omega),
        show n - s + s = n from by omega]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [hv]
      exact Finsupp.mem_support_iff.mp hn.1
    · rw [hv]
      exact hn.2.1
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hv : slotInr s u m = u (m + s) := by
      rw [slotInr_apply, if_neg hm.2.2]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [← hv]
      exact Finsupp.mem_support_iff.mp hm.1
    · rw [← hv]
      exact hm.2.1
  · intro n hn
    rw [Finset.mem_filter] at hn
    omega
  · intro m hm
    rw [Finset.mem_filter] at hm
    omega
  · intro n _
    rfl

/-- Membership transport for the support condition along the slot bijection. -/
theorem wpMem_shiftWeight_iff (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    WPMem (shiftWeight w s) u ↔ WPMem w (slotInr s u) := by
  rw [WPMem, WPMem, wpWeight_shiftWeight_eq, slotInr_zero_apply]

/-- The `inl`-pull of a flat exponent through the slot bijection. -/
noncomputable def slotInl (s : ℕ) (u : ℕ →₀ ℕ) : Fin s →₀ ℕ :=
  Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
    Sum.inl_injective.injOn

/-- A flat exponent is determined by its two slot pulls. -/
theorem slot_ext (s : ℕ) {u₁ u₂ : ℕ →₀ ℕ} (hl : slotInl s u₁ = slotInl s u₂)
    (hr : slotInr s u₁ = slotInr s u₂) : u₁ = u₂ := by
  have h1 : Finsupp.equivMapDomain (slotEquiv s) u₁ =
      Finsupp.equivMapDomain (slotEquiv s) u₂ := by
    refine Finsupp.ext fun x => ?_
    rcases x with i | m
    · have := congrArg (fun v => v i) hl
      simpa [slotInl, Finsupp.comapDomain_apply] using this
    · have := congrArg (fun v => v m) hr
      simpa [slotInr, Finsupp.comapDomain_apply] using this
  have h2 := congrArg (Finsupp.equivMapDomain (slotEquiv s).symm) h1
  rwa [← Finsupp.equivMapDomain_trans, ← Finsupp.equivMapDomain_trans,
    Equiv.self_trans_symm, Finsupp.equivMapDomain_refl,
    Finsupp.equivMapDomain_refl] at h2

variable {K w} in
/-- The flatten hom lands in the shifted-weight support: coefficients vanish off
`WPMem (shiftWeight w s)` (the support condition of the nested `𝒜`-coefficient,
transported along the slot bijection). -/
theorem tateExtToFlat_support (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ)
    (hu : ¬ WPMem (shiftWeight w s) u) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) = 0 := by
  rw [tateExtToFlat_coeff]
  have hX := (MvPowerSeries.coeff
    (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
      Sum.inl_injective.injOn) F.1).2
  exact hX (slotInr s u)
    (fun hc => hu ((wpMem_shiftWeight_iff w s u).mpr hc))

variable {K w} in
/-- The flatten hom is Gauss-restricted at radius 1 (joint cofiniteness of the
nested coefficient families: outer nullity of the `𝒜`-coefficients, inner
Gauss-nullity of each, glued along the slot split). -/
theorem tateExtToFlat_isRestrictedGauss (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) :
    MvPowerSeries.IsRestrictedGauss (fun _ : ℕ => (1 : ℝ))
      (tateExtToFlat (K := K) (w := w) s F) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  have hT : {t : Fin s →₀ ℕ |
      ε ≤ ‖(MvPowerSeries.coeff t F.1 : WPA K w)‖}.Finite := by
    have h2 : MvPowerSeries.IsRestricted F.1 := F.2
    have h3 := Metric.tendsto_nhds.mp h2 ε hε
    rw [Filter.eventually_cofinite] at h3
    refine h3.subset fun t ht => ?_
    rw [Set.mem_setOf_eq] at ht ⊢
    intro hc
    rw [dist_zero_right] at hc
    linarith
  have hper : ∀ t : Fin s →₀ ℕ, {u : ℕ →₀ ℕ | slotInl s u = t ∧
      ε ≤ ‖MvPowerSeries.coeff (slotInr s u)
        ((MvPowerSeries.coeff t F.1 : WPA K w)).1.1‖}.Finite := by
    intro t
    have h4 : {v : ℕ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff v
        ((MvPowerSeries.coeff t F.1 : WPA K w)).1.1‖}.Finite := by
      have h5 := ((MvPowerSeries.coeff t F.1 : WPA K w)).1.2
      have h6 := Metric.tendsto_nhds.mp h5 ε hε
      rw [Filter.eventually_cofinite] at h6
      refine h6.subset fun v hv => ?_
      rw [Set.mem_setOf_eq] at hv ⊢
      intro hc
      rw [dist_zero_right,
        show (v.prod fun _ k => (1 : ℝ) ^ k) = 1 from by simp, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hc
      linarith
    refine Set.Finite.of_finite_image (f := fun u => slotInr s u)
      (h4.subset ?_) ?_
    · rintro _ ⟨u, ⟨hul, hur⟩, rfl⟩
      exact hur
    · intro u₁ h₁ u₂ h₂ hr
      rw [Set.mem_setOf_eq] at h₁ h₂
      exact slot_ext s (h₁.1.trans h₂.1.symm) hr
  refine Set.Finite.subset (Set.Finite.biUnion hT fun t _ => hper t) ?_
  intro u hu
  rw [Set.mem_setOf_eq] at hu
  have hbig : ε ≤ ‖MvPowerSeries.coeff u
      (tateExtToFlat (K := K) (w := w) s F)‖ := by
    by_contra hc
    push_neg at hc
    refine hu ?_
    rw [dist_zero_right,
      show (u.prod fun _ k => (1 : ℝ) ^ k) = 1 from by simp, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hc
  rw [tateExtToFlat_coeff] at hbig
  have hbig' : ε ≤ ‖MvPowerSeries.coeff (slotInr s u)
      ((MvPowerSeries.coeff (slotInl s u) F.1 : WPA K w)).1.1‖ := hbig
  refine Set.mem_biUnion (x := slotInl s u) ?_ ?_
  · show ε ≤ ‖(MvPowerSeries.coeff (slotInl s u) F.1 : WPA K w)‖
    refine le_trans hbig' ?_
    exact norm_coeffA_le (K := K) (w := w) _ _
  · rw [Set.mem_setOf_eq]
    exact ⟨rfl, hbig'⟩

/-- Recombine slot parts into a flat exponent. -/
noncomputable def slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.equivMapDomain (slotEquiv s).symm
    (Finsupp.sumFinsuppEquivProdFinsupp.symm (t, v))

theorem equivMapDomain_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    Finsupp.equivMapDomain (slotEquiv s) (slotRecomb s t v) =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (t, v) := by
  rw [slotRecomb, ← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self,
    Finsupp.equivMapDomain_refl]

theorem slotInl_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    slotInl s (slotRecomb s t v) = t := by
  refine Finsupp.ext fun i => ?_
  rw [slotInl, Finsupp.comapDomain_apply, equivMapDomain_slotRecomb]
  exact Finsupp.sumFinsuppEquivProdFinsupp_symm_inl _ i

theorem slotInr_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    slotInr s (slotRecomb s t v) = v := by
  refine Finsupp.ext fun m => ?_
  rw [slotInr, Finsupp.comapDomain_apply, equivMapDomain_slotRecomb]
  exact Finsupp.sumFinsuppEquivProdFinsupp_symm_inr _ m

theorem slotRecomb_slots (s : ℕ) (u : ℕ →₀ ℕ) :
    slotRecomb s (slotInl s u) (slotInr s u) = u :=
  slot_ext s (slotInl_slotRecomb s _ _) (slotInr_slotRecomb s _ _)

variable {K w} in
/-- The flatten hom, corestricted to the shifted-weight algebra. -/
noncomputable def tateExtToWPA (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) →+* WPA K (shiftWeight w s) where
  toFun F := ⟨⟨tateExtToFlat (K := K) (w := w) s F,
      tateExtToFlat_isRestrictedGauss s F⟩,
    fun u hu => tateExtToFlat_support s F u hu⟩
  map_one' := Subtype.ext (Subtype.ext (map_one
    (tateExtToFlat (K := K) (w := w) s)))
  map_mul' F G := Subtype.ext (Subtype.ext (map_mul
    (tateExtToFlat (K := K) (w := w) s) F G))
  map_zero' := Subtype.ext (Subtype.ext (map_zero
    (tateExtToFlat (K := K) (w := w) s)))
  map_add' F G := Subtype.ext (Subtype.ext (map_add
    (tateExtToFlat (K := K) (w := w) s) F G))

variable {K w} in
theorem tateExtToWPA_injective (s : ℕ) :
    Function.Injective (tateExtToWPA (K := K) (w := w) s) := by
  intro F G hFG
  refine tateExtToFlat_injective (K := K) (w := w) s ?_
  have h1 := congrArg (fun z : WPA K (shiftWeight w s) => z.1.1) hFG
  exact h1

variable {K w} in
/-- The value-level coefficient family of a shifted-weight element is null. -/
theorem shiftg_coeff_null (s : ℕ) (g : WPA K (shiftWeight w s)) :
    Filter.Tendsto (fun u : ℕ →₀ ℕ => MvPowerSeries.coeff u g.1.1)
      Filter.cofinite (nhds 0) := by
  have hg : Filter.Tendsto (fun u : ℕ →₀ ℕ =>
      ‖MvPowerSeries.coeff u g.1.1‖ * u.prod fun _ k => (1 : ℝ) ^ k)
      Filter.cofinite (nhds 0) := g.1.2
  rw [show (fun u : ℕ →₀ ℕ => ‖MvPowerSeries.coeff u g.1.1‖ *
      u.prod fun _ k => (1 : ℝ) ^ k) =
    (fun u : ℕ →₀ ℕ => ‖MvPowerSeries.coeff u g.1.1‖) from
    funext fun u => by simp] at hg
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hg

variable {K w} in
/-- The unflatten of a shifted-weight element: the `t`-th coefficient in `𝒜`. -/
noncomputable def unflattenCoeff (s : ℕ) (g : WPA K (shiftWeight w s))
    (t : Fin s →₀ ℕ) : WPA K w :=
  ⟨⟨fun v => MvPowerSeries.coeff (slotRecomb s t v) g.1.1, by
      have hinj : Function.Injective (fun v => slotRecomb s t v) := by
        intro v₁ v₂ hv
        have h1 := congrArg (slotInr s) hv
        rwa [slotInr_slotRecomb, slotInr_slotRecomb] at h1
      have hfib := (shiftg_coeff_null s g).comp hinj.tendsto_cofinite
      show Filter.Tendsto (fun v : ℕ →₀ ℕ =>
        ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ *
          v.prod fun _ k => (1 : ℝ) ^ k) Filter.cofinite (nhds 0)
      rw [show (fun v : ℕ →₀ ℕ =>
          ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ *
            v.prod fun _ k => (1 : ℝ) ^ k) =
        (fun v : ℕ →₀ ℕ =>
          ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖) from
        funext fun v => by simp]
      exact tendsto_zero_iff_norm_tendsto_zero.mp hfib⟩,
    fun v hv => by
      refine g.2 (slotRecomb s t v) ?_
      intro hc
      have h2 := (wpMem_shiftWeight_iff w s (slotRecomb s t v)).mp hc
      rw [slotInr_slotRecomb] at h2
      exact hv h2⟩

variable {K w} in
theorem unflatten_isRestricted (s : ℕ) (g : WPA K (shiftWeight w s)) :
    MvPowerSeries.IsRestricted
      (fun t : Fin s →₀ ℕ => unflattenCoeff (K := K) (w := w) s g t) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  have hε2 : 0 < ε / 2 := by linarith
  have hg : {u : ℕ →₀ ℕ |
      ε / 2 ≤ ‖MvPowerSeries.coeff u g.1.1‖}.Finite := by
    have h6 := Metric.tendsto_nhds.mp (shiftg_coeff_null s g) (ε / 2) hε2
    rw [Filter.eventually_cofinite] at h6
    refine h6.subset fun u hu => ?_
    rw [Set.mem_setOf_eq] at hu ⊢
    intro hc
    rw [dist_zero_right] at hc
    linarith
  refine Set.Finite.subset (hg.image (slotInl s)) ?_
  intro t ht
  rw [Set.mem_setOf_eq] at ht
  have hnorm : ε ≤ ‖unflattenCoeff (K := K) (w := w) s g t‖ := by
    by_contra hc
    push_neg at hc
    refine ht ?_
    rw [dist_zero_right]
    exact hc
  -- extract a fiber witness ≥ ε/2
  have hwit : ∃ v : ℕ →₀ ℕ,
      ε / 2 ≤ ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ := by
    by_contra hc
    push_neg at hc
    have hle : ‖unflattenCoeff (K := K) (w := w) s g t‖ ≤ ε / 2 := by
      rw [norm_eq_iSup_coeffA]
      refine ciSup_le fun v => ?_
      exact (hc v).le
    linarith
  obtain ⟨v, hv⟩ := hwit
  refine ⟨slotRecomb s t v, ?_, ?_⟩
  · rw [Set.mem_setOf_eq]
    exact hv
  · exact slotInl_slotRecomb s t v

variable {K w} in
theorem tateExtToWPA_surjective (s : ℕ) :
    Function.Surjective (tateExtToWPA (K := K) (w := w) s) := by
  classical
  intro g
  refine ⟨⟨fun t => unflattenCoeff (K := K) (w := w) s g t,
    unflatten_isRestricted s g⟩, ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  refine MvPowerSeries.ext fun u => ?_
  show MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s
    ⟨fun t => unflattenCoeff (K := K) (w := w) s g t,
      unflatten_isRestricted s g⟩) = MvPowerSeries.coeff u g.1.1
  rw [tateExtToFlat_coeff]
  show MvPowerSeries.coeff (slotRecomb s (slotInl s u) (slotInr s u)) g.1.1 =
    MvPowerSeries.coeff u g.1.1
  rw [slotRecomb_slots]

variable {K w} in
/-- The bridge between the project's Tate extension of `𝒜` and the shifted-weight
weighted-parity algebra: `𝒜⟨V_1,…,V_s⟩ ≅ WPA (shiftWeight w s)` (Fubini + reindex
of restricted power series; nested-vs-flat plumbing). -/
noncomputable def tateExtEquiv (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) ≃+* WPA K (shiftWeight w s) :=
  RingEquiv.ofBijective (tateExtToWPA (K := K) (w := w) s)
    ⟨tateExtToWPA_injective s, tateExtToWPA_surjective s⟩

-- The topological refinement of `tateExtEquiv` (bicontinuity for the project's
-- Tate-algebra topology on `restrictedMvPowerSeriesSubring`, cf.
-- `MvTateAlgebraTopology`) is specified at ticket level; the bare subtype carries no
-- `TopologicalSpace` instance, so the statement needs the `mvTateAlgebraTopology'`
-- `letI` and is deferred to execution.

variable {K w} in
/-- **Strong sheafiness** ([WP] thm 6.2 (2): "(𝒜,𝒜°) is strongly sheafy"): for every
`s`, the weighted-parity model of the Tate extension `𝒜⟨V_1,…,V_s⟩` is sheafy for
every valid ring of integral elements.  Combined with the identification
`tateExtEquiv` this is the statement in the project's own Tate-extension
vocabulary. -/
theorem wp_stronglySheafy (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight w s)) :=
  wp_isSheafyComplete ϖ hK₀

end WeightedParity

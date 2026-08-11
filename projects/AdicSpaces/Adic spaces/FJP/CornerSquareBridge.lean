/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.CornerSquareLocalization
import «Adic spaces».FJP.FiniteJetFunctoriality

/-!
# The graph bridge over a single abstract corner (T625, campaign B)

[FJP] §4 (4.4)/(4.19)–(4.21), the completion identification, over ONE normed
ultrametric Huber corner `E`: for a rational datum `D` on `E` with enumeration
`e`, the completed rational localization `𝒪_E(D)` is topologically the Banach
graph quotient `E_α = P_E ⧸ I_E`:

* forward `bridgeFwd : 𝒪_E(D) →+* E_α` (completion extension of the
  localization lift at the unit `s̄`);
* reverse `bridgeRev : E_α →+* 𝒪_E(D)` (evaluation `X̄ᵢ ↦ fᵢ/s`, convergent by
  the [FJP] (1.3) bound);
* `graphBridge : 𝒪_E(D) ≃+* E_α`, continuous in both directions.

This is the single-corner generalization of the `JetA`-side bridge of
`FJP/FiniteJetFunctoriality.lean` (:207–:733). Because the `Pinch` relations are
in graph-polynomial form, instantiating `E` at each vertex of a pinch square
(with the pushed datum and pushed enumeration at `B`, `C`, `D`) yields the four
vertex bridges of the localized Milnor row **definitionally** — the ideals
`Pinch.IB/IC/ID` are the `IA`-ideals of the pushed data.

The closedness of the graph ideal enters as an explicit argument `hIcl` (at the
`B`/`C`/`D`-corners it is `isClosed_graphIdeal`; at the base corner of a pinch
it is `Pinch.isClosed_IA`, which needs the square).
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul ValuationSpectrum Pinch

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] [PlusSubring E] [IsTateRing E]
  [HasLocLiftPowerBounded E]

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`
(the generic form of the Jet-concrete `DatumEnum`). -/
structure CornerEnum (D : RationalLocData E) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → E
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

/-- The canonical enumeration of a rational datum (via `Finset.equivFin`). -/
noncomputable def cornerEnum (D : RationalLocData E) : CornerEnum D where
  m := D.T.card
  f := fun i => (D.T.equivFin.symm i : E)
  hf := fun t ht => ⟨D.T.equivFin ⟨t, ht⟩, by rw [Equiv.symm_apply_apply]⟩
  hf' := fun i => (D.T.equivFin.symm i).2

namespace CornerEnum

variable (D : RationalLocData E) (e : CornerEnum D)

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The enumerated datum spans `({s} ∪ range f) = ⊤` (rationality + covering). -/
theorem span_eq_top (hD : D.IsRational) :
    Ideal.span ({D.s} ∪ Set.range e.f) = ⊤ := by
  rw [← top_le_iff, ← hD.span_eq_top]
  refine Ideal.span_mono fun t ht => ?_
  obtain ⟨i, rfl⟩ := e.hf t ht
  exact Set.mem_union_right _ ⟨i, rfl⟩

end CornerEnum

namespace CornerBridge

section Bridge

variable (D : RationalLocData E) (e : CornerEnum D)

/-- Scalars into `P_E` (constant restricted series). -/
noncomputable def bridgeConst (m : ℕ) : E →+* P E m :=
  polyToP.comp MvPolynomial.C

/-- The base map `E → E_α = P_E ⧸ I_E` (constants, then the graph quotient). -/
noncomputable def bridgeBase : E →+* locA e.m D.s e.f :=
  (Ideal.Quotient.mk (IA e.m D.s e.f)).comp (bridgeConst e.m)

/-- The variable images `X̄ᵢ ∈ E_α`. -/
noncomputable def bridgeX (i : Fin e.m) : locA e.m D.s e.f :=
  Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i))

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The graph relation in the quotient: `s̄ · X̄ᵢ = f̄ᵢ` ([FJP] (4.6)). -/
theorem bridgeBase_s_mul_X (i : Fin e.m) :
    bridgeBase D e D.s * bridgeX D e i = bridgeBase D e (e.f i) := by
  have hmem : polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (e.f i)) ∈ IA e.m D.s e.f := by
    have hrw : rA e.m D.s e.f i =
        polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
          polyToP (MvPolynomial.C (e.f i)) := by
      rw [rA, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C D.s)) *
      Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C (e.f i)))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IA e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `s̄` is a unit in `E_α` ([FJP] (4.3)). -/
theorem isUnit_bridgeBase_s (hD : D.IsRational) :
    IsUnit (bridgeBase D e D.s) := by
  have h1 : (1 : E) ∈ Ideal.span ({D.s} ∪ Set.range e.f) := by
    rw [e.span_eq_top D hD]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBase D e (d i * e.f i) =
      bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := fun i => by
    rw [RingHom.map_mul (bridgeBase D e), bridgeBase_s_mul_X]
  have happ : bridgeBase D e c * bridgeBase D e D.s +
      ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) = 1 := by
    have h0 := congrArg (bridgeBase D e) hxy
    rw [RingHom.map_one (bridgeBase D e), RingHom.map_add (bridgeBase D e),
      RingHom.map_mul (bridgeBase D e),
      show (bridgeBase D e) (∑ i, d i * e.f i) = ∑ i, bridgeBase D e (d i * e.f i) from
        map_sum (bridgeBase D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBase D e D.s *
      (bridgeBase D e c + ∑ i, bridgeBase D e (d i) * bridgeX D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBase D e D.s * bridgeBase D e c +
        ∑ i, bridgeBase D e D.s * (bridgeBase D e (d i) * bridgeX D e i)
        = bridgeBase D e c * bridgeBase D e D.s +
          ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := by
          rw [mul_comm (bridgeBase D e D.s) (bridgeBase D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

omit [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `‖X̄ᵢ‖ ≤ 1` in the graph quotient. -/
theorem norm_bridgeX_le_one (i : Fin e.m) : ‖bridgeX D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact FiniteJet.gaussNorm_X_le_one (S := E) i

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `bridgeBase` is norm-nonincreasing. -/
theorem norm_bridgeBase_le (a : E) : ‖bridgeBase D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := E) (m := e.m) (MvPolynomial.C a) : P E e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := E) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The loc-level forward map `E_s → E_α` (`IsLocalization.Away.lift` at `s̄`). -/
noncomputable def bridgeLocHom (hD : D.IsRational) :
    Localization.Away D.s →+* locA e.m D.s e.f :=
  IsLocalization.Away.lift D.s (isUnit_bridgeBase_s D e hD)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeLocHom_algebraMap (hD : D.IsRational) (a : E) :
    bridgeLocHom D e hD (algebraMap E (Localization.Away D.s) a) =
      bridgeBase D e a :=
  IsLocalization.Away.lift_eq _ _ a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The forward map sends the rational generator `fᵢ/s` to the variable `X̄ᵢ`. -/
theorem bridgeLocHom_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHom D e hD (divByS (e.f i) D.s) = bridgeX D e i := by
  have hu := isUnit_bridgeBase_s D e hD
  have hspec : divByS (e.f i) D.s * algebraMap E (Localization.Away D.s) D.s =
      algebraMap E (Localization.Away D.s) (e.f i) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHom D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHom D e hD), bridgeLocHom_algebraMap,
    bridgeLocHom_algebraMap, ← bridgeBase_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBase D e D.s) (bridgeLocHom D e hD (divByS (e.f i) D.s))]
  exact happ

set_option maxHeartbeats 800000 in
omit [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Continuity of the loc-level forward map (universal property; the generators
map to the norm-≤-1 variables `X̄ᵢ`, which are power-bounded). -/
theorem bridgeLocHom_continuous (hD : D.IsRational) :
    @Continuous _ _ D.topology _ (bridgeLocHom D e hD) := by
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ ?_ ?_
  · have h_eq : (bridgeLocHom D e hD).comp
        (algebraMap E (Localization.Away D.s)) = bridgeBase D e := by
      ext a; exact bridgeLocHom_algebraMap D e hD a
    rw [show ⇑((bridgeLocHom D e hD).comp
        (algebraMap E (Localization.Away D.s)))
        = ⇑(bridgeBase D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBase D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBase_le D e a
  · intro t ht
    obtain ⟨i, rfl⟩ := e.hf t ht
    rw [bridgeLocHom_divByS]
    exact FiniteJet.isPowerBounded_of_norm_le_one (norm_bridgeX_le_one D e i)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `E_α` is Hausdorff when the graph ideal is closed. -/
theorem locE_t2 (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    T2Space (locA e.m D.s e.f) :=
  locA_t2_of_isClosed e.m D.s e.f hIcl

/-- Forward: `𝒪_E(D) → E_α` (completion extension of the localization lift;
the target is complete Hausdorff since `I_E` is closed, [FJP] (4.21)). -/
noncomputable def bridgeFwd (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    presheafValue D →+* locA e.m D.s e.f := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_coe (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m))))
    (a : Localization.Away D.s) :
    bridgeFwd D e hD hIcl (D.coeRingHom a) = bridgeLocHom D e hD a := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  let _i := D.uniformSpace
  have : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD) a

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_canonicalMap (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (a : E) :
    bridgeFwd D e hD hIcl (D.canonicalMap a) = bridgeBase D e a := by
  rw [show D.canonicalMap a =
      D.coeRingHom (algebraMap E (Localization.Away D.s) a) from rfl,
    bridgeFwd_coe, bridgeLocHom_algebraMap]

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (bridgeFwd D e hD hIcl) := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  let _i := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

end Bridge

/-! #### The reverse direction: evaluation `P_E → 𝒪_E(D)` ([FJP] Lemma 1.1, (1.3)) -/

/-- Norm-decay restricted series are topologically restricted. -/
noncomputable def bridgeToRestricted (m : ℕ) :
    P E m →+* ↥(restrictedMvPowerSeriesSubring m E) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

section Eval

variable (D : RationalLocData E) (e : CornerEnum D)

/-- The rational generators `fᵢ/s ∈ 𝒪_E(D)`. -/
noncomputable def bridgeGen (i : Fin e.m) : presheafValue D :=
  D.coeRingHom (divByS (e.f i) D.s)

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Each generator is power-bounded. -/
theorem bridgeGen_isBounded (i : Fin e.m) :
    TopologicalRing.IsBounded (Set.range (bridgeGen D e i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (e.f i) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (e.hf' i)
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (e.f i) D.s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The evaluation `P_E →+* 𝒪_E(D)`: `Σ a_v X^v ↦ Σ ρ(a_v)·(f/s)^v`. -/
noncomputable def bridgeEval : P E e.m →+* presheafValue D :=
  (mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (bridgeGen D e) (bridgeGen_isBounded D e)).comp (bridgeToRestricted e.m)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeEval_const (a : E) :
    bridgeEval D e (polyToP (MvPolynomial.C a)) = D.canonicalMap a := by
  have hcast : bridgeToRestricted (E := E) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap E ↥(restrictedMvPowerSeriesSubring e.m E) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) E) = _
    rw [show (polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := E) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeEval_X (i : Fin e.m) :
    bridgeEval D e (polyToP (MvPolynomial.X i)) = bridgeGen D e i := by
  have hcast : bridgeToRestricted (E := E) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := E) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) E) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The evaluation kills the graph ideal. -/
theorem IA_le_ker_bridgeEval : IA e.m D.s e.f ≤ RingHom.ker (bridgeEval D e) := by
  rw [IA, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hval : bridgeEval D e (rA e.m D.s e.f i) =
      D.canonicalMap D.s * bridgeGen D e i - D.canonicalMap (e.f i) :=
    (map_sub ((bridgeEval D e).comp polyToP)
        (MvPolynomial.C D.s * MvPolynomial.X i) (MvPolynomial.C (e.f i))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEval D e).comp polyToP)
            (MvPolynomial.C D.s) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEval_const D e D.s) (bridgeEval_X D e i)))
        (bridgeEval_const D e (e.f i)))
  rw [hval, sub_eq_zero, bridgeGen]
  rw [show D.canonicalMap D.s = D.coeRingHom (algebraMap E
      (Localization.Away D.s) D.s) from rfl, ← RingHom.map_mul D.coeRingHom,
    show algebraMap E (Localization.Away D.s) D.s * divByS (e.f i) D.s =
      algebraMap E (Localization.Away D.s) (e.f i) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- Reverse: `E_α → 𝒪_E(D)` (the evaluation factors through the graph quotient). -/
noncomputable def bridgeRev : locA e.m D.s e.f →+* presheafValue D :=
  Ideal.Quotient.lift (IA e.m D.s e.f) (bridgeEval D e)
    (fun _ ha => RingHom.mem_ker.mp (IA_le_ker_bridgeEval D e ha))

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_mk (p : P E e.m) :
    bridgeRev D e (Ideal.Quotient.mk (IA e.m D.s e.f) p) = bridgeEval D e p := rfl

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_bridgeBase (a : E) :
    bridgeRev D e (bridgeBase D e a) = D.canonicalMap a :=
  bridgeEval_const D e a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_bridgeX (i : Fin e.m) :
    bridgeRev D e (bridgeX D e i) = bridgeGen D e i :=
  bridgeEval_X D e i

/-- Sums of open-subgroup members stay in the subgroup. -/
private theorem tsum_mem_of_isOpen_addSubgroup' {ι G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem fun i _ => hmem i

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E]
  [HasLocLiftPowerBounded E] in
/-- The range of the generator product powers is bounded. -/
private theorem bridgeRangeProd_isBounded :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGen D e i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGen D e i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : presheafValue D)
  | insert a s ha ih =>
      refine ((bridgeGen_isBounded D e a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGen D e i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- **Continuity of the evaluation** from the norm topology on `P_E`
([FJP] (1.3) bound). -/
theorem bridgeEval_continuous : Continuous (bridgeEval D e) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEval D e).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProd_isBounded D e (W : Set (presheafValue D))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : D.canonicalMap ⁻¹' V ∈ nhds (0 : E) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : P E e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm D.canonicalMap (bridgeGen D e)
    (bridgeToRestricted e.m p) v) ∈ (W : Set (presheafValue D))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
      (bridgeGen D e) (bridgeGen_isBounded D e) (bridgeToRestricted e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : D.canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v ∈ W
  rw [show mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v =
      (∏ i, bridgeGen D e i ^ (v i)) *
        D.canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Continuity of the reverse map (quotient topology). -/
theorem bridgeRev_continuous : Continuous (bridgeRev D e) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IA e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEval_continuous D e

/-! #### Round trips (density + Hausdorff equalizers) -/

omit [PlusSubring E] [IsTateRing E] [HasLocLiftPowerBounded E] in
/-- Polynomials are dense in `P_E`. -/
theorem polyToP_denseRange (m : ℕ) :
    DenseRange (polyToP : MvPolynomial (Fin m) E → P E m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le) (half_lt_self hε)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : P E m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : P E m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        E)).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
  by_cases hs : ε / 2 ≤ ‖MvPowerSeries.coeff s p.1‖
  · rw [Finset.sum_eq_single s
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun hns => absurd ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mpr hs)
        hns), MvPolynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hs).le
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      rw [hbs] at hb
      exact hs ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mp hb)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `rev ∘ fwd = id` on `𝒪_E(D)`. -/
theorem bridgeRev_bridgeFwd (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (x : presheafValue D) :
    bridgeRev D e (bridgeFwd D e hD hIcl x) = x := by
  let _i := D.uniformSpace
  have : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have : RegularSpace (presheafValue D) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRev D e).comp (bridgeLocHom D e hD) = D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [bridgeLocHom_algebraMap, bridgeRev_bridgeBase]
    rfl
  have hdense : DenseRange (D.coeRingHom :
      Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hagree : (fun y => bridgeRev D e (bridgeFwd D e hD hIcl y)) ∘ D.coeRingHom =
      (fun y => y) ∘ (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    funext a
    show bridgeRev D e (bridgeFwd D e hD hIcl (D.coeRingHom a)) = D.coeRingHom a
    rw [bridgeFwd_coe]
    exact DFunLike.congr_fun hcomp a
  have h_eq : (fun y => bridgeRev D e (bridgeFwd D e hD hIcl y)) = fun y => y :=
    hdense.equalizer ((bridgeRev_continuous D e).comp (bridgeFwd_continuous D e hD hIcl))
      continuous_id hagree
  exact congrFun h_eq x

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The graph-quotient projection is continuous. -/
theorem mkIA_continuous :
    Continuous (Ideal.Quotient.mk (IA e.m D.s e.f)) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (IA e.m D.s e.f)) 1
    fun a => by rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ a

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `fwd ∘ rev = id` on `E_α`. -/
theorem bridgeFwd_bridgeRev (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (y : locA e.m D.s e.f) :
    bridgeFwd D e hD hIcl (bridgeRev D e y) = y := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmkcont : Continuous (Ideal.Quotient.mk (IA e.m D.s e.f)) :=
    mkIA_continuous D e
  have hpoly : ∀ q : MvPolynomial (Fin e.m) E,
      bridgeFwd D e hD hIcl (bridgeEval D e (polyToP q)) =
        Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP q) := by
    have hhomeq : ((bridgeFwd D e hD hIcl).comp ((bridgeEval D e).comp polyToP)) =
        (Ideal.Quotient.mk (IA e.m D.s e.f)).comp
          (polyToP : MvPolynomial (Fin e.m) E →+* P E e.m) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show bridgeFwd D e hD hIcl (bridgeEval D e (polyToP (MvPolynomial.C a))) =
          Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C a))
        rw [bridgeEval_const, bridgeFwd_canonicalMap]
        rfl
      · show bridgeFwd D e hD hIcl (bridgeEval D e (polyToP (MvPolynomial.X i))) =
          Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i))
        rw [bridgeEval_X, bridgeGen, bridgeFwd_coe, bridgeLocHom_divByS]
        rfl
    intro q
    exact DFunLike.congr_fun hhomeq q
  have h_eq : (fun z : P E e.m => bridgeFwd D e hD hIcl (bridgeEval D e z)) =
      fun z : P E e.m => Ideal.Quotient.mk (IA e.m D.s e.f) z := by
    refine (polyToP_denseRange e.m).equalizer
      ((bridgeFwd_continuous D e hD hIcl).comp (bridgeEval_continuous D e)) hmkcont ?_
    funext q
    exact hpoly q
  exact congrFun h_eq p

/-- **The graph bridge** ([FJP] (4.19)/(4.21)): the completed rational
localization is the Banach graph quotient, as topological rings. -/
noncomputable def graphBridge (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    presheafValue D ≃+* locA e.m D.s e.f where
  toFun := bridgeFwd D e hD hIcl
  invFun := bridgeRev D e
  left_inv := bridgeRev_bridgeFwd D e hD hIcl
  right_inv := bridgeFwd_bridgeRev D e hD hIcl
  map_mul' := map_mul (bridgeFwd D e hD hIcl)
  map_add' := map_add (bridgeFwd D e hD hIcl)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem graphBridge_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (graphBridge D e hD hIcl) :=
  bridgeFwd_continuous D e hD hIcl

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem graphBridge_symm_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (graphBridge D e hD hIcl).symm :=
  bridgeRev_continuous D e

end Eval

end CornerBridge

end FiniteJet

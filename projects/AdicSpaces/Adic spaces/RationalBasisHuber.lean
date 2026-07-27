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

open TopologicalSpace Pointwise

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

/-- The side condition supplies a power inclusion (radical of fg). -/
theorem RCoord.pow_le {I : Ideal A} (hIfg : I.FG) (p : RCoord A I) :
    ∃ M : ℕ, I ^ M ≤ Ideal.span ((p.1.1 : Finset A) : Set A) :=
  Ideal.exists_pow_le_of_le_radical_of_fg p.2 hIfg

/-- **The valid rational datum of a side-condition coordinate over a general
Huber base** (no unit in `I` needed): validity through the open-span
constructor at a power inclusion. -/
noncomputable def RCoord.toDatumOpen (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) : RationalLocData A :=
  { P := P
    T := p.1.1
    s := p.1.2
    hopen := genPiece_hopen_of_pow_le P p.1.1 p.1.2
      (RCoord.pow_le hIfg p).choose
      (by rw [← hIeq]; exact (RCoord.pow_le hIfg p).choose_spec) }

@[simp] theorem RCoord.toDatumOpen_P (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) :
    (p.toDatumOpen P hIeq hIfg).P = P := rfl

@[simp] theorem RCoord.toDatumOpen_T (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) :
    (p.toDatumOpen P hIeq hIfg).T = p.1.1 := rfl

@[simp] theorem RCoord.toDatumOpen_s (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) :
    (p.toDatumOpen P hIeq hIfg).s = p.1.2 := rfl

/-- The ambient ideal of definition is finitely generated. -/
theorem span_image_pairIdeal_fg (P : PairOfDefinition A) :
    (Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))).FG := by
  rw [show Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))
    = Ideal.map P.A₀.subtype P.I from rfl]
  exact Ideal.FG.map P.fg _

/-- **Validity of the open-span datum**: `span T` contains the open image
of a power of the ideal of definition, and a subgroup with an open subset
is open. -/
theorem RCoord.toDatumOpen_isRational (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) :
    (p.toDatumOpen P hIeq hIfg).IsRational := by
  obtain ⟨M, hM⟩ := RCoord.pow_le hIfg p
  have himg : (Subtype.val '' ((P.I ^ M : Ideal P.A₀) : Set P.A₀) : Set A)
      ⊆ (Ideal.span ((p.1.1 : Finset A) : Set A) : Set A) := by
    rintro x ⟨y, hy, rfl⟩
    refine hM ?_
    rw [hIeq, show Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))
      = Ideal.map P.A₀.subtype P.I from rfl, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  show IsOpen ((Ideal.span (((p.toDatumOpen P hIeq hIfg).T : Finset A)
    : Set A) : Ideal A) : Set A)
  rw [RCoord.toDatumOpen_T]
  refine AddSubgroup.isOpen_of_mem_nhds
    (H := (Ideal.span ((p.1.1 : Finset A) : Set A)).toAddSubgroup)
    (g := 0) ?_
  exact Filter.mem_of_superset
    ((P.pow_image_isOpen M).mem_nhds ⟨0, by simp, by simp⟩) himg

/-- The `Spa`-trace of a side-condition coordinate (open-span form). -/
theorem RCoord.spaOpen_toDatumOpen (P : PairOfDefinition A) {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG) (p : RCoord A I) :
    spaOpen (p.toDatumOpen P hIeq hIfg)
      = {v : ↥(Spa A A⁺) | ιSpvR I (v : Spv A) p = true} := by
  ext v
  rw [Set.mem_setOf_eq, ιSpvR_eq_true_iff]
  constructor
  · rintro ⟨-, hvle, hs0⟩
    exact ⟨hvle, hs0⟩
  · rintro ⟨hvle, hs0⟩
    exact ⟨v.2, hvle, hs0⟩

/-- **Validity from a power certificate** (extracted general form): a datum
whose tray span absorbs a power of its pair's ambient ideal of definition is
rational. -/
theorem RationalLocData.isRational_of_pow_le {D : RationalLocData A} (M : ℕ)
    (hle : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M
      ≤ Ideal.span (D.T : Set A)) : D.IsRational := by
  have himg : (Subtype.val '' ((D.P.I ^ M : Ideal D.P.A₀) : Set D.P.A₀) : Set A)
      ⊆ (Ideal.span ((D.T : Finset A) : Set A) : Set A) := by
    rintro x ⟨y, hy, rfl⟩
    refine hle ?_
    rw [show Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))
      = Ideal.map D.P.A₀.subtype D.P.I from rfl, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  show IsOpen ((Ideal.span ((D.T : Finset A) : Set A) : Ideal A) : Set A)
  refine AddSubgroup.isOpen_of_mem_nhds
    (H := (Ideal.span ((D.T : Finset A) : Set A)).toAddSubgroup)
    (g := 0) ?_
  exact Filter.mem_of_superset
    ((D.P.pow_image_isOpen M).mem_nhds ⟨0, by simp, by simp⟩) himg

section InterOpen

variable [DecidableEq A]

/-- **The intersection datum at power certificates** (the open-span form of
`interDatum`): the combined tray absorbs the summed power. -/
noncomputable def RationalLocData.interDatumOpen (D E : RationalLocData A)
    (M₁ M₂ : ℕ)
    (hle₁ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₁
      ≤ Ideal.span (D.T : Set A))
    (hle₂ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₂
      ≤ Ideal.span (E.T : Set A)) : RationalLocData A :=
  { P := D.P
    T := D.interTray E
    s := D.s * E.s
    hopen := genPiece_hopen_of_pow_le D.P (D.interTray E) (D.s * E.s)
      (M₁ + M₂) (by
        rw [pow_add]
        calc (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₁
              * (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₂
            ≤ Ideal.span (D.T : Set A) * Ideal.span (E.T : Set A) :=
              Ideal.mul_mono hle₁ hle₂
          _ = Ideal.span ((D.T : Set A) * (E.T : Set A)) :=
              Ideal.span_mul_span' _ _
          _ ≤ Ideal.span ((D.interTray E : Finset A) : Set A) :=
              Ideal.span_mono (by
                rintro _ ⟨t, ht, u, hu, rfl⟩
                refine Finset.mem_coe.mpr (Finset.mem_image.mpr
                  ⟨(t, u), ?_, rfl⟩)
                exact Finset.mem_product.mpr
                  ⟨Finset.mem_insert_of_mem ht,
                    Finset.mem_insert_of_mem hu⟩)) }

/-- The certificate of the intersection datum. -/
theorem RationalLocData.interDatumOpen_pow_le (D E : RationalLocData A)
    (M₁ M₂ : ℕ)
    (hle₁ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₁
      ≤ Ideal.span (D.T : Set A))
    (hle₂ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₂
      ≤ Ideal.span (E.T : Set A)) :
    (Ideal.span (((D.interDatumOpen E M₁ M₂ hle₁ hle₂).P.A₀).subtype ''
        (((D.interDatumOpen E M₁ M₂ hle₁ hle₂).P.I
          : Ideal (D.interDatumOpen E M₁ M₂ hle₁ hle₂).P.A₀)
          : Set (D.interDatumOpen E M₁ M₂ hle₁ hle₂).P.A₀))) ^ (M₁ + M₂)
      ≤ Ideal.span
        (((D.interDatumOpen E M₁ M₂ hle₁ hle₂).T : Finset A) : Set A) := by
  show (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ (M₁ + M₂)
    ≤ Ideal.span ((D.interTray E : Finset A) : Set A)
  rw [pow_add]
  calc (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₁
        * (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₂
      ≤ Ideal.span (D.T : Set A) * Ideal.span (E.T : Set A) :=
        Ideal.mul_mono hle₁ hle₂
    _ = Ideal.span ((D.T : Set A) * (E.T : Set A)) :=
        Ideal.span_mul_span' _ _
    _ ≤ Ideal.span ((D.interTray E : Finset A) : Set A) :=
        Ideal.span_mono (by
          rintro _ ⟨t, ht, u, hu, rfl⟩
          refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(t, u), ?_, rfl⟩)
          exact Finset.mem_product.mpr
            ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_of_mem hu⟩)

/-- The intersection datum realises the intersection (open-span form;
`rationalOpen` never mentions the pair). -/
theorem RationalLocData.interDatumOpen_rationalOpen [PlusSubring A]
    (D E : RationalLocData A) (M₁ M₂ : ℕ)
    (hle₁ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₁
      ≤ Ideal.span (D.T : Set A))
    (hle₂ : (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M₂
      ≤ Ideal.span (E.T : Set A)) :
    rationalOpen (D.interDatumOpen E M₁ M₂ hle₁ hle₂).T
        (D.interDatumOpen E M₁ M₂ hle₁ hle₂).s
      = rationalOpen D.T D.s ∩ rationalOpen E.T E.s := by
  show rationalOpen (D.interTray E) (D.s * E.s) = _
  rw [RationalLocData.interTray_eq_mul,
    ← rationalOpen_inter (insert D.s D.T) (insert E.s E.T) D.s E.s
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _),
    rationalOpen_insert_s, rationalOpen_insert_s]

end InterOpen

/-- The whole-space datum's `Spa`-trace (general Huber). -/
theorem spaOpen_globalLocData_huber (P : PairOfDefinition A)
    [PlusSubring A] :
    spaOpen (globalLocData P) = Set.univ := by
  have h := spaOpens_globalLocData (A := A) P
  simpa [spaOpens, SetLike.ext'_iff] using congrArg
    (fun U : Opens ↥(Spa A A⁺) => (U : Set ↥(Spa A A⁺))) h

/-- Finite intersections of side-condition traces are valid rational opens
with certificates (open-span fold). -/
theorem exists_spaOpen_eq_sInter_huber [PlusSubring A] [DecidableEq A]
    (P : PairOfDefinition A)
    {I : Ideal A}
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (hIfg : I.FG)
    (𝒮 : Set (Set ↥(Spa A A⁺))) (h𝒮 : 𝒮.Finite)
    (hsub : 𝒮 ⊆ {S | ∃ p : RCoord A I,
      S = {v : ↥(Spa A A⁺) | ιSpvR I (v : Spv A) p = true}}) :
    ∃ D : RationalLocData A, D.P = P ∧
      (∃ M : ℕ, (Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) ^ M
        ≤ Ideal.span (D.T : Set A))
      ∧ spaOpen D = ⋂₀ 𝒮 := by
  induction 𝒮, h𝒮 using Set.Finite.induction_on with
  | empty =>
    refine ⟨globalLocData P, rfl, ⟨0, ?_⟩, by
      rw [Set.sInter_empty, spaOpen_globalLocData_huber]⟩
    rw [pow_zero, show (globalLocData P).T = {1} from rfl]
    rw [Finset.coe_singleton, Ideal.span_singleton_one]
    exact le_top
  | @insert S 𝒮' hS h𝒮' ih =>
    obtain ⟨D', hD'P, ⟨M', hM'⟩, hD'eq⟩ := ih fun x hx =>
      hsub (Set.mem_insert_of_mem _ hx)
    obtain ⟨q, rfl⟩ := hsub (Set.mem_insert _ _)
    obtain ⟨M, hM⟩ := RCoord.pow_le hIfg q
    have hleq : (Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) ^ M
        ≤ Ideal.span (((q.toDatumOpen P hIeq hIfg).T : Finset A) : Set A) := by
      rw [RCoord.toDatumOpen_T, ← hIeq]
      exact hM
    have hleD' : (Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) ^ M'
        ≤ Ideal.span ((D'.T : Finset A) : Set A) := hM'
    refine ⟨(q.toDatumOpen P hIeq hIfg).interDatumOpen D'
        M M' hleq hleD',
      rfl, ⟨M + M',
        (q.toDatumOpen P hIeq hIfg).interDatumOpen_pow_le D'
          M M' hleq hleD'⟩, ?_⟩
    · show spaOpen _ = _
      unfold spaOpen
      rw [show ((q.toDatumOpen P hIeq hIfg).interDatumOpen D'
            M M' hleq hleD').T
          = (q.toDatumOpen P hIeq hIfg).interTray D' from rfl,
        show ((q.toDatumOpen P hIeq hIfg).interDatumOpen D'
            M M' hleq hleD').s
          = (q.toDatumOpen P hIeq hIfg).s * D'.s from rfl,
        RationalLocData.interTray_eq_mul,
        ← rationalOpen_inter (insert (q.toDatumOpen P hIeq hIfg).s
            (q.toDatumOpen P hIeq hIfg).T) (insert D'.s D'.T)
            (q.toDatumOpen P hIeq hIfg).s D'.s
          (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _),
        rationalOpen_insert_s, rationalOpen_insert_s, Set.preimage_inter]
      rw [show (Subtype.val ⁻¹' rationalOpen (q.toDatumOpen P hIeq hIfg).T
            (q.toDatumOpen P hIeq hIfg).s
          : Set ↥(Spa A A⁺)) = spaOpen (q.toDatumOpen P hIeq hIfg) from rfl,
        show (Subtype.val ⁻¹' rationalOpen D'.T D'.s
          : Set ↥(Spa A A⁺)) = spaOpen D' from rfl,
        RCoord.spaOpen_toDatumOpen, hD'eq, Set.sInter_insert]

/-- The subspace topology of `Spa (A, A⁺)` is generated by the traces of the
side-condition rational subsets (the `RCoord`-profile is inducing and the sierpiński
product topology is generated coordinatewise). -/
theorem spa_topology_eq_generateFrom_huber (P : PairOfDefinition A) (I : Ideal A)
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    (inferInstance : TopologicalSpace ↥(Spa A A⁺)) =
      generateFrom {S | ∃ p : RCoord A I,
        S = {v : ↥(Spa A A⁺) | ιSpvR I (v : Spv A) p = true}} := by
  have hInd := isInducing_ιSpvPropR_spa (A := A) P I hIeq
  rw [hInd.eq_induced]
  show TopologicalSpace.induced _ (Pi.topologicalSpace) = _
  rw [show (Pi.topologicalSpace : TopologicalSpace (RCoord A I → Prop)) =
      ⨅ p : RCoord A I, TopologicalSpace.induced (fun x => x p) sierpinskiSpace from rfl,
    induced_iInf]
  simp only [induced_compose]
  rw [show (sierpinskiSpace : TopologicalSpace Prop) =
      generateFrom {{True}} from rfl]
  simp only [induced_generateFrom_eq]
  rw [← generateFrom_iUnion]
  congr 1
  ext S
  simp only [Set.mem_iUnion, Set.image_singleton, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Function.comp_apply]
    show ιSpvPropR I (v : Spv A) p = True ↔ _
    rw [show ιSpvPropR I (v : Spv A) p = (ιSpvR I (v : Spv A) p = true) from rfl,
      eq_iff_iff, iff_true]
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Function.comp_apply]
    show _ ↔ ιSpvPropR I (v : Spv A) p = True
    rw [show ιSpvPropR I (v : Spv A) p = (ιSpvR I (v : Spv A) p = true) from rfl,
      eq_iff_iff, iff_true]

/-- **The rational basis of `Spa (A, A⁺)` over a general Huber base**
(Wedhorn Theorem 7.35(2), non-Tate form): every open neighbourhood
contains a valid rational open neighbourhood. -/
theorem exists_isRational_spaOpen_subset_huber [DecidableEq A]
    {V : Set ↥(Spa A A⁺)} (hV : IsOpen V) {v : ↥(Spa A A⁺)} (hv : v ∈ V) :
    ∃ D : RationalLocData A, D.IsRational ∧ v ∈ spaOpen D ∧ spaOpen D ⊆ V := by
  obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := A)
  set I : Ideal A := Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)) with hI
  have hIfg : I.FG := span_image_pairIdeal_fg P
  have htop := spa_topology_eq_generateFrom_huber (A := A) P I hI
  obtain ⟨B, hB, hvB, hBV⟩ :=
    (isTopologicalBasis_of_subbasis htop).exists_subset_of_mem_open hv hV
  obtain ⟨𝒮, ⟨h𝒮fin, h𝒮sub⟩, rfl⟩ := hB
  obtain ⟨D, hDP, ⟨M, hcert⟩, hDeq⟩ := exists_spaOpen_eq_sInter_huber
    P hI hIfg 𝒮 h𝒮fin h𝒮sub
  refine ⟨D, ?_, hDeq ▸ hvB, hDeq ▸ hBV⟩
  refine RationalLocData.isRational_of_pow_le M ?_
  rw [hDP]
  exact hcert

/-- **Every valid datum carries a power certificate at its own pair**: the
open tray span contains an open image of a pair-ideal power, hence the
ambient ideal power. -/
theorem exists_pow_le_of_isRational (D : RationalLocData A)
    (hD : D.IsRational) :
    ∃ M : ℕ, (Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))) ^ M
      ≤ Ideal.span (D.T : Set A) := by
  have hbasis := D.P.hasBasis_nhds_zero
  have hnhds : ((Ideal.span (D.T : Set A) : Ideal A) : Set A) ∈ nhds (0 : A) :=
    hD.mem_nhds (Ideal.zero_mem _)
  obtain ⟨M, -, hM⟩ := hbasis.mem_iff.mp hnhds
  refine ⟨M, ?_⟩
  rw [show Ideal.span (D.P.A₀.subtype '' (D.P.I : Set D.P.A₀))
    = Ideal.map D.P.A₀.subtype D.P.I from rfl, ← Ideal.map_pow]
  rw [Ideal.map]
  refine Ideal.span_le.mpr ?_
  intro x hx
  exact hM hx

end ValuationSpectrum

end

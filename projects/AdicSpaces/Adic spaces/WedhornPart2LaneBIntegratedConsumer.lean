/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPart2LaneAInternalizedConsumer
import «Adic spaces».WedhornLaneBSeparationInterface

/-!
# Integrated Lane A and Lane B consumers for Tate acyclicity

This file combines the Lane A consumers for Part 2 of Tate acyclicity with Lane B
separation suppliers. It provides variants using either `C1SupplierStrong_local` or explicit
single-`t` structural data, together with generic separation and prime-extension-closed forms.

Each family includes a full form with an explicit local-cover nonemptiness hypothesis and an
allow-empty form in which nonemptiness is derived from the rational-open cover piece.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- Compatible sections glue when Lane A is supplied by `C1SupplierStrong_local` and Lane B by
a separation supplier with local-cover nonemptiness. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface C f₀
      separation_supplier per_E_nonempty)
    hLaneA

/-- Compatible sections glue from `C1SupplierStrong_local` and a separation supplier without an
explicit local-cover nonemptiness hypothesis. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface_allow_empty C f₀
      separation_supplier)
    hLaneA

/-- Compatible sections glue from `C1SupplierStrong_local`, prime-extension-closed separation
hypotheses, and local-cover nonemptiness. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed P C f₀ hloc_noeth
      hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen per_E_nonempty)
    hLaneA

/-- Compatible sections glue from `C1SupplierStrong_local` and prime-extension-closed separation
hypotheses without an explicit local-cover nonemptiness hypothesis. -/
theorem
tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed_allow_empty P C f₀
      hloc_noeth hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen)
    hLaneA

/-- Compatible sections glue when Lane A is supplied by single-`t` structural data and Lane B by
a separation supplier with local-cover nonemptiness. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_struct f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface C f₀
      separation_supplier per_E_nonempty)
    hLaneA

/-- Compatible sections glue from single-`t` structural data and a separation supplier without
an explicit local-cover nonemptiness hypothesis. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_struct f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface_allow_empty C f₀
      separation_supplier)
    hLaneA

/-- Compatible sections glue from single-`t` structural data, prime-extension-closed separation
hypotheses, and local-cover nonemptiness. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_struct f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed P C f₀ hloc_noeth
      hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen per_E_nonempty)
    hLaneA

/-- Compatible sections glue from single-`t` structural data and prime-extension-closed separation
hypotheses without an explicit local-cover nonemptiness hypothesis. -/
theorem
tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_prime_extension_closed_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_struct f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed_allow_empty P C f₀
      hloc_noeth hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen)
    hLaneA

end ValuationSpectrum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPerTFactoredBranchLink
import «Adic spaces».WedhornLocalizedCor732Application
import «Adic spaces».WedhornStandardCoverRefinement

/-!
# Wedhorn local Cor 7.32 → factored chain bridge

Constructs the concrete `h_local_Cor732` premise of the localized
rational-open inclusion chain from a unified named `M_power_decay`
residual hypothesis carrying the structural Wedhorn 8.34(ii)
arithmetic, and threads through `exists_dominating_unit_in_localization`
(commit accepted upstream) for the σ-strict-domination output.

## Identification of the localized Cor 7.32 supplier

The exact current theorem that applies localized Cor 7.32 is:

* `exists_dominating_unit_in_localization`
  (`Adic spaces/WedhornLocalizedCor732Application.lean:84`).

Its output is `∃ σ : (Localization.Away s)ˣ, ∀ w ∈ Spa _ _, ∃ τ ∈ T_loc,
w.vle (σ : _) τ ∧ ¬ w.vle τ (σ : _)` — i.e., the σ-strict-domination
data on the localized Spa, taking explicit Tate / pseudouniformizer
hypotheses (`hLin`, `π_loc`, `hI_loc`, `hπ_loc_tn`, `hπ_loc_unit`,
`hArch_loc`, `T_loc`, `hT_loc`).

## What this file provides

* `h_T_test_compat_loc_canonical_via_M_power_decay` — the **bridge** from
  a unified M-power-decay residual hypothesis to the canonical
  compat output (consumed by
  `rationalOpen_subset_base_via_local_Cor732_chain`). Single one-line
  composition through `h_T_test_compat_loc_canonical_via_Wedhorn_structural`
  (commit `764ecac`).

* `rationalOpen_subset_base_via_M_power_decay` — the **caller-facing
  composed theorem**: takes the Cor 7.32 σ-strict-domination output (over
  the canonical test family `localizedTestFamily`), the denominator-cleared
  identity `algebraMap f = σ_loc * (∏ T_D.image algebraMap)`, and the
  unified `M_power_decay` residual, producing the base rational-open
  inclusion `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`
  on `Spa(A, A⁺)`.

## The single named residual

The M-power-decay structural fact — the genuine Wedhorn 8.34(ii) Route
B content — is exposed as the **unified named hypothesis**
`M_power_decay_target` (in the bridge's signature). Concretely, it
asserts that at every `w ∈ Spa(Localization.Away s, locSubring P T s)`
satisfying f-membership, the structural Wedhorn inequality
`w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')` holds for
every `t' ∈ T_D.image algebraMap`, alongside the per-w non-vanishing
of `T_D.image algebraMap` and `algebraMap s_D`. This is not derivable
from σ-strict-domination alone (audit at
`WedhornMultiDominatingUnit.lean:234–304`); it is the Cor 7.32-σ-construction's
specific structural output.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Does NOT edit Tertiary's value-group-localization file or any other
  in-flight file.
* Reuses `h_T_test_compat_loc_canonical_via_Wedhorn_structural` (commit
  `764ecac`) and `rationalOpen_subset_base_via_local_Cor732_chain`
  (commit `4197d87`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **Bridge: M-power-decay residual → canonical compat output**.

Takes a unified M-power-decay structural hypothesis and produces the
canonical compat output for `localizedTestFamily s T_D s_D`. Single
line composition through
`h_T_test_compat_loc_canonical_via_Wedhorn_structural` (commit `764ecac`):
the unified residual is split into the five suppliers consumed there. -/
theorem h_T_test_compat_loc_canonical_via_M_power_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_M_power_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (algebraMap A (Localization.Away s) s)
                (algebraMap A (Localization.Away s) s_D *
                  (σ_loc : Localization.Away s) *
                  (∏ t ∈ (T_D.image
                    (algebraMap A (Localization.Away s))).erase t', t))) ∧
          (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
              ¬ w.vle t'' 0) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact h_T_test_compat_loc_canonical_via_Wedhorn_structural P T s hopen T_D s_D σ_loc
    -- α_s_D suppliers (specialised at τ = algebraMap s_D):
    (fun w hw_spa hw_f hστ ↦
      ((h_M_power_decay w hw_spa hw_f
        (algebraMap A (Localization.Away s) s_D)
        (Finset.mem_insert_self _ _) hστ).2.1))
    (fun w hw_spa hw_f hστ ↦
      ((h_M_power_decay w hw_spa hw_f
        (algebraMap A (Localization.Away s) s_D)
        (Finset.mem_insert_self _ _) hστ).1))
    -- α_T_D suppliers:
    (fun τ hτ w hw_spa hw_f hστ ↦
      ((h_M_power_decay w hw_spa hw_f τ
        (Finset.mem_insert_of_mem hτ) hστ).2.1))
    (fun τ hτ w hw_spa hw_f hστ ↦
      ((h_M_power_decay w hw_spa hw_f τ
        (Finset.mem_insert_of_mem hτ) hστ).1))
    -- α_T_D s_D non-degeneracy:
    (fun τ hτ w hw_spa hw_f hστ ↦
      ((h_M_power_decay w hw_spa hw_f τ
        (Finset.mem_insert_of_mem hτ) hστ).2.2))

/-- **Caller-facing composed theorem**: from the localized Cor 7.32
σ-strict-domination output (over the canonical test family) and the
unified M-power-decay residual, derive the base rational-open
inclusion `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`.

This is the cleanest end-to-end consumer signature for downstream
Wedhorn 8.34(ii) callers: only Tate / Cor 7.32 setup data, the
σ-strict-domination supplier, the denominator-cleared identity, and
the M-power-decay residual remain external. -/
theorem rationalOpen_subset_base_via_M_power_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A)
    (h_T_le_T_base : T ⊆ T_base)
    (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (hσ_loc_dominates :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_M_power_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (algebraMap A (Localization.Away s) s)
                (algebraMap A (Localization.Away s) s_D *
                  (σ_loc : Localization.Away s) *
                  (∏ t ∈ (T_D.image
                    (algebraMap A (Localization.Away s))).erase t', t))) ∧
          (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
              ¬ w.vle t'' 0) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_local_Cor732_chain P T s hopen hA₀_le
    T_base T_D s_D h_T_le_T_base f σ_loc h_alg
    (localizedTestFamily s T_D s_D) hσ_loc_dominates
    (h_T_test_compat_loc_canonical_via_M_power_decay P T s hopen T_D s_D
      σ_loc h_M_power_decay)

/-! ### The single named residual: the M-power-decay structural fact

The unified `h_M_power_decay` premise consumed above is the **single
named residual**: a theorem-level statement carrying the genuine
Wedhorn 8.34(ii) Route B M-power-decay content. It is NOT a placeholder
`sorry`-blob — it is a concrete Lean theorem with full hypotheses,
ready to be discharged in a future ticket. The exact target signature:

```
theorem M_power_decay_target
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    -- Wedhorn 8.34(ii) Cor 7.32 structural data:
    (π_loc : (locPairOfDefinition P T s hopen).A₀)
    (M : ℕ)
    (hσ_loc_eq_pow : (σ_loc : Localization.Away s) =
      ((locPairOfDefinition P T s hopen).A₀.subtype π_loc) ^ (M + 1))
    (hπ_loc_tn : IsTopologicallyNilpotent
      ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
    -- Tate / pseudouniformizer hypotheses for the local Spa:
    (hA₀_le : P.A₀ ≤ A⁺)
    -- ... (further Cor 7.32 hypotheses as needed) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (algebraMap A (Localization.Away s) s)
              (algebraMap A (Localization.Away s) s_D *
                (σ_loc : Localization.Away s) *
                (∏ t ∈ (T_D.image
                  (algebraMap A (Localization.Away s))).erase t', t))) ∧
        (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
            ¬ w.vle t'' 0) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0
```

The `σ_loc = π_loc^(M+1)` form ties σ to a topologically-nilpotent
pseudouniformizer power, with `M` chosen to discharge the structural
inequality uniformly. This construction follows Wedhorn 8.34(ii)
Step 2 ("set `f := σ * t * D.s^(N-1)` for an exponent `N` chosen
large enough that σ's domination of `T_test` clears denominators") +
Spa-quasi-compactness (`isCompact_spa_of_tate_pseudouniformizer`).

Per the existing audit at `WedhornMultiDominatingUnit.lean:234–304`,
the proof of this residual is the genuinely-new Wedhorn 8.34(ii)
Route B content; it does not reduce to σ-strict-domination alone.

This file's bridge is the caller-ready packaging that consumes the
residual once it lands. -/

/-! ### Localized Cor 7.32 Laurent piece membership (T027)

Localized variant of T026's
`cor732_laurent_piece_membership_at` (in `WedhornStandardCoverRefinement.lean`),
specialised at `A := Localization.Away s` with the localized topology
and plus-subring instances, using `localizedTestFamily s T_D s_D` as
the test family.

This is the **per-`w` Laurent piece membership supplier** for the
localized Wedhorn 8.34(ii) chain, replacing the parked
σ-power-decay branch suppliers from T021 with Wedhorn's actual
Laurent cover refinement (PDF page 84). At each
`w ∈ Spa(Localization.Away s, locSubring P T s)`, given the localized
Cor 7.32 σ-strict-domination output over `localizedTestFamily s T_D s_D`,
there exists `τ ∈ localizedTestFamily s T_D s_D` such that `w` lies in
the σ_loc-rescaled Laurent piece
`rationalOpen ({(1 : Localization.Away s)} : Finset _) (σ_loc⁻¹ * τ)`. -/

omit [PlusSubring A] in
/-- **Localized Cor 7.32 Laurent piece membership at `w`** (T027 main
theorem). At every `w ∈ Spa(Localization.Away s, locSubring P T s)`,
given a localized σ-strict-domination over `localizedTestFamily s T_D s_D`
(the existential output of `exists_dominating_unit_in_localization`
specialised at `T_loc := localizedTestFamily s T_D s_D`), there exists
`τ ∈ localizedTestFamily s T_D s_D` such that `w` lies in the σ_loc-
rescaled Laurent piece. Direct instantiation of T026's
`cor732_laurent_piece_membership_at` at `A := Localization.Away s` with
the localized instances.

This theorem replaces the **σ-power-decay-shaped** branch supplier in
T021's parked chain (`AlphaS_DBranchPerTSigmaPowerDecay`,
`AlphaT_DBranchPerTSigmaPowerDecay`) with the **Laurent-piece
membership** form, matching Wedhorn 8.34(ii)'s actual proof
mechanism (PDF page 84 / Lemma 8.33 cover-level acyclicity). -/
theorem localized_cor732_laurent_piece_membership_at
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ∃ τ ∈ localizedTestFamily s T_D s_D,
        w ∈ rationalOpen
          ({(1 : Localization.Away s)} : Finset (Localization.Away s))
          (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
            τ) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro w hw
  exact cor732_laurent_piece_membership_at hσ_loc_dom hw

omit [PlusSubring A] in
/-- **Existential localized Cor 7.32 Laurent piece membership** —
combines `exists_dominating_unit_in_localization` (the localized
Cor 7.32 σ-supplier) with `localized_cor732_laurent_piece_membership_at`
to expose the per-`w` Laurent piece membership directly from the
localized Tate / pseudouniformizer hypotheses, without an explicit
σ_loc parameter.

Output: ∃ σ_loc : (Localization.Away s)ˣ, ∀ w ∈ Spa, ∃ τ ∈ localizedTestFamily,
w ∈ rationalOpen {1} (σ_loc⁻¹ * τ). -/
theorem exists_localized_cor732_laurent_piece_membership
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0),
    ∃ σ_loc : (Localization.Away s)ˣ,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s))
            (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
              τ) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  obtain ⟨σ_loc, hσ_loc_dom⟩ :=
    exists_dominating_unit_in_localization P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
      (localizedTestFamily s T_D s_D) hT_loc
  refine ⟨σ_loc, ?_⟩
  exact localized_cor732_laurent_piece_membership_at P T s hopen
    T_D s_D σ_loc hσ_loc_dom

end ValuationSpectrum

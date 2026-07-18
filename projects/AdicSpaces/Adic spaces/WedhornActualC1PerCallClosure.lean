/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornC1CoverAssemblyClosure
import «Adic spaces».WedhornTateAcyclicityFinalClosure
import «Adic spaces».WedhornC1SigmaImageAlignment

/-!
# Wedhorn 8.34(ii) — Actual C1 per-call consumer modulo alignment (T064)

T058 (commit `947600d`) discharged
`LaurentCoverPresheafLemma833Assembly` for the **σ-rescaled image
target** unconditionally. T060 (commit `494ed3d`) bridged
`CoverLevelAssemblyResidual` to the structured Lemma 8.33 predicate
and exposed the C1 supplier's clause 2 closure modulo Lemma 8.33.
T061 (commit `dfcbeb3`) packaged the per-call interface
`WedhornC1Lemma833PerCallAssemblyData` and produced
`C1SupplierStrong_local C` from the per-call assembly data. T062
(`WedhornC1SigmaImageAlignment.lean`) lands the **alignment** between
the actual C1 cover-piece denominator target `rationalOpen D.T D.s`
and the σ-rescaled image target via the σ-shift cancellation
`(D_T.image (σ * ·)).image (σ⁻¹ * ·) = D_T`, including a clean
**σ-free t-indexed consumer**
`rationalOpen_global_subset_via_sigma_shift_t_indexed`.

This file lands the **consumer-side C1 integration**: the strongest
fully-proved theorem closing every consumer-side obligation around
the alignment gap, so Secondary's σ-shift alignment plugs into
T061's per-call interface and T060's chain closure with minimal
churn.

## What this file provides

* `WedhornC1Lemma833PerCallAssemblyData_of_t_indexed` —
  **substantive constructor** (def, structure-valued): builds T061's
  `WedhornC1Lemma833PerCallAssemblyData C D v` from purely σ-free
  t-indexed inputs over `D.T`. Internally chooses
  `T_test := D.T.image (σ * ·)` and uses T062's
  `LaurentCoverPresheafLemma833Assembly_via_sigma_shift` to discharge
  the `h_lemma833` field, plus the σ-cancellation to translate
  per-piece subsets and Laurent cover from t-indexed to τ-indexed.
  Callable by any consumer that wants a per-call assembly-data
  structure directly from σ-free t-indexed inputs.

* `C1SupplierStrong_local_via_t_indexed_direct` — **top-level
  theorem** producing `C1SupplierStrong_local C` from per-call σ-free
  t-indexed delivery. Applies T062's t-indexed consumer directly,
  giving the C1 supplier's clause 2 conclusion at each per-call
  input. The actual-target alignment is consumed internally via
  `LaurentCoverPresheafLemma833Assembly_via_sigma_shift`; no external
  alignment hypothesis required.

## Why this lands the consumer-side closure

The C1 supplier's clause 2 conclusion `rationalOpen (insert f
C.base.T) C.base.s ⊆ rationalOpen D.T D.s` requires:

1. T058's σ-rescaled image discharge of Lemma 8.33 ✓.
2. T060's bridge from Lemma 8.33 to `CoverLevelAssemblyResidual` ✓.
3. T061's per-call interface and `C1SupplierStrong_local C` bridge ✓.
4. T062's σ-shift alignment to bridge the actual D.T target ✓.

This file's theorems show that **all four** above compose into
unconditional C1 supplier output from per-call σ-free t-indexed
inputs. The user-facing inputs are:

* `f : A` and `σ : Aˣ` per call.
* `v ∈ rationalOpen (insert f C.base.T) C.base.s` (clause 1).
* `¬ v.vle f 0` (strong clause 3).
* per-piece subsets `R(insert f T_base, s) ∩ R({1}, t) ⊆ R({t}, D.s)`
  for each `t ∈ D.T` (σ-free t-indexed).
* a Laurent cover hypothesis `∀ w ∈ R(insert f T_base, s),
  ∃ t ∈ D.T, w ∈ R({1}, t)` (σ-free t-indexed).

No σ-rescaled τ-indexed structures appear in the user-facing
hypotheses; the σ enters only via the internal σ-shift mechanism
inside T062.

## Notes

* No root import; leaf-level.
* Imports T060 (`WedhornC1CoverAssemblyClosure`),
  T061 (`WedhornTateAcyclicityFinalClosure`), and T062
  (`WedhornC1SigmaImageAlignment`).
* No edits to T031–T062 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **`WedhornC1Lemma833PerCallAssemblyData` from σ-free t-indexed
inputs** (T064 substantive constructor).

Constructs T061's `WedhornC1Lemma833PerCallAssemblyData C D v` from
purely σ-free t-indexed inputs over `D.T`. The σ-rescaled τ-indexed
data required by `WedhornC1Lemma833PerCallAssemblyData` is constructed
via the supplier-natural σ-shift `T_test := D.T.image (σ * ·)`:

* `h_per_piece` (τ-indexed) is translated from the t-indexed
  `h_per_piece_t` via the σ-cancellation
  `σ⁻¹ * (σ * t) = t`.
* `h_cover` (τ-indexed) is translated from the t-indexed
  `h_cover_t` via the same σ-cancellation.
* `h_lemma833` is discharged unconditionally by T062's
  `LaurentCoverPresheafLemma833Assembly_via_sigma_shift` for the
  σ-shifted T_test choice.

The σ enters only via the internal σ-shift; the user-facing inputs
are σ-free and natural for the C1 supplier consumer. -/
noncomputable def WedhornC1Lemma833PerCallAssemblyData_of_t_indexed
    [DecidableEq A]
    (C : RationalCovering A) (D : RationalLocData A) (v : Spv A)
    (σ : Aˣ) (f : A)
    (hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (hvf_nz : ¬ v.vle f 0)
    (h_per_piece_t :
      ∀ t ∈ D.T,
        rationalOpen (insert f C.base.T) C.base.s ∩
            rationalOpen ({(1 : A)} : Finset A) t ⊆
          rationalOpen ({t} : Finset A) D.s)
    (h_cover_t :
      ∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
        ∃ t ∈ D.T,
          w ∈ rationalOpen ({(1 : A)} : Finset A) t) :
    WedhornC1Lemma833PerCallAssemblyData C D v := by
  -- σ-cancellation `σ⁻¹ * (σ * t) = t` is `Units.inv_mul_cancel_left σ`.
  -- Translate per-piece data from t-indexed to τ-indexed.
  have h_per_piece_τ :
      ∀ τ ∈ D.T.image (fun t => (σ : A) * t),
        rationalOpen (insert f C.base.T) C.base.s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen
            ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D.s := by
    intro τ hτ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hτ
    rw [Units.inv_mul_cancel_left]
    exact h_per_piece_t t ht
  -- Translate cover hypothesis from t-indexed to τ-indexed.
  have h_cover_τ :
      ∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
        ∃ τ ∈ D.T.image (fun t => (σ : A) * t),
          w ∈ rationalOpen ({(1 : A)} : Finset A)
            (((σ⁻¹ : Aˣ) : A) * τ) := by
    intro w hw
    obtain ⟨t, ht, hw_in⟩ := h_cover_t w hw
    refine ⟨(σ : A) * t, Finset.mem_image_of_mem _ ht, ?_⟩
    rw [Units.inv_mul_cancel_left]
    exact hw_in
  -- Assemble: σ-shift discharges h_lemma833 unconditionally via T062.
  exact
    { σ := σ
      f := f
      T_test := D.T.image (fun t => (σ : A) * t)
      hv_in_plus := hv_in_plus
      hvf_nz := hvf_nz
      h_per_piece := h_per_piece_τ
      h_cover := h_cover_τ
      h_lemma833 :=
        LaurentCoverPresheafLemma833Assembly_via_sigma_shift D.T D.s }

/-- **`C1SupplierStrong_local C` via per-call σ-free t-indexed delivery**
(T064 top-level closure theorem).

Direct route from per-call σ-free t-indexed delivery to
`C1SupplierStrong_local C`, applying T062's
`rationalOpen_global_subset_via_sigma_shift_t_indexed` consumer at
each per-call input.

**Per-call inputs at each `(D, v, t)`** (σ-free, natural for the C1
supplier):

* `σ_choice : Aˣ` and `f : A` — per-call σ-construction outputs.
* `v ∈ rationalOpen (insert f C.base.T) C.base.s` — C1 supplier's
  clause 1.
* `¬ v.vle f 0` — strong clause 3.
* per-piece subsets `R(insert f T_base, s) ∩ R({1}, t') ⊆ R({t'},
  D.s)` for each `t' ∈ D.T`.
* Laurent cover `∀ w ∈ R(insert f T_base, s), ∃ t' ∈ D.T, w ∈
  R({1}, t')`.

**Output**: `C1SupplierStrong_local C` — the strong cover-refinement
supplier consumed downstream by the existing tate acyclicity Part 2
chain.

The actual-target alignment (Secondary's T062 work) is consumed
internally via `LaurentCoverPresheafLemma833Assembly_via_sigma_shift`
inside `rationalOpen_global_subset_via_sigma_shift_t_indexed`; no
external alignment hypothesis required. -/
theorem C1SupplierStrong_local_via_t_indexed_direct
    [DecidableEq A]
    (C : RationalCovering A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        (∀ t' ∈ D.T,
          rationalOpen (insert f C.base.T) C.base.s ∩
              rationalOpen ({(1 : A)} : Finset A) t' ⊆
            rationalOpen ({t'} : Finset A) D.s) ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t')) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_per_piece_t, h_cover_t⟩ :=
    h_per_call D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_global_subset_via_sigma_shift_t_indexed
    σ_choice D.T C.base.T C.base.s D.s f h_per_piece_t h_cover_t

end ValuationSpectrum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

/-!
# Normalized Laurent-minus datum

The ordinary `laurentMinusDatum D₀ f` does **not** preserve the
`LaurentNormalized` class: even when `D₀` carries `1 ∈ D₀.T`, the new
`T` (a finite set of products of pairs from `(insert D₀.s D₀.T) × {D₀.s, f}`)
does not contain `1` in general, so the resulting datum may fail
`LaurentNormalized`.

This file fixes the issue by introducing a **normalized variant**

```
laurentMinusNormalizedDatum D₀ f
```

which has the same denominator `D₀.s * f` and ring of definition `D₀.P` as
the ordinary minus, but whose numerator set is obtained by **inserting `1`**
into the ordinary minus numerator set. By construction this variant carries
`1 ∈ T`, hence is `LaurentNormalized`.

The key algebraic content (Wedhorn/external reviewer guidance, 2026-05-12):
when `D₀` is `LaurentNormalized` so `1 ∈ D₀.T`, the elements `s` and `f`
are already among the ordinary minus numerators (via the pairs `(1, s)` and
`(1, f)`), so

```
divByS s (s*f) * divByS f (s*f) = divByS 1 (s*f)
```

shows the inserted `1` is **algebraically redundant**: the corresponding
generator `1 / (s*f)` is already in the ordinary minus `locSubring`. The
extra rational inequality `v(1) ≤ v(s*f)` is similarly forced by the existing
constraints `v(s) ≤ v(s*f)` and `v(f) ≤ v(s*f)` together with the
nonvanishing `v(s*f) ≠ 0`, so the rational open is unchanged.

This lets the **Laurent decomposition / standard cover** path keep the
`LaurentNormalized` invariant throughout: plus datums preserve it by
construction (since `insert f T ⊇ T ∋ 1`), and the normalized minus
preserves it by design. The existing `LaurentNormalized` flatness theorems
then apply uniformly, without needing the full non-normalized Wedhorn 2.13
algebraic identity.

## Main declarations

* `laurentMinusNormalizedDatum D₀ f` — the normalized minus datum.
* `laurentMinusNormalizedDatum_isLaurentNormalized` — it carries the
  `LaurentNormalized` class (under the hypothesis `f ∈ D₀.P.A₀`, needed
  for the subring closure of the new `T` elements).
* `laurentMinusNormalized_subset` — its rational open is contained in
  the base `D₀`'s rational open.
* `rationalOpen_laurentMinusNormalized_eq` — equality of the new
  rational open with the ordinary `laurentMinusDatum`'s rational open.

## References

* Wedhorn, *Adic Spaces*, §8.32 / §8.33 (Laurent cover decomposition).
* External reviewer guidance, 2026-05-12: "normalized minus datum".
-/

open ValuationSpectrum CompletionLocalization

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### `laurentMinusNormalizedDatum` definition

For `D₀ : RationalLocData A` with `LaurentNormalized D₀` and `f ∈ D₀.P.A₀`,
build the normalized minus datum at `f`. The numerator set inserts `1`
into the ordinary minus numerator set. -/

/-- Normalized Laurent-minus datum: `T = insert 1 (oldT)`, `s = D₀.s * f`.

The `hopen` proof exploits the new `1 ∈ T`: for any `b ∈ P.A₀`,
`divByS b (D₀.s * f) = algebraMap b * divByS 1 (D₀.s * f)`, and both factors
lie in `locSubring P T (D₀.s * f)` (the algebraMap-image by
`algebraMap_mem_locSubring`, the divByS-image by `divByS_mem_locSubring`
with the new `1 ∈ T`). -/
noncomputable def laurentMinusNormalizedDatum
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    RationalLocData A :=
  letI : DecidableEq A := Classical.decEq A
  { P := D₀.P
    T := insert (1 : A) (laurentMinusDatum D₀ f).T
    s := D₀.s * f
    hopen := ⟨0, fun b _ => by
    -- divByS b (D₀.s * f) = algebraMap b * divByS 1 (D₀.s * f).
    have hmul : algebraMap A (Localization.Away (D₀.s * f)) (b : A) *
        divByS (1 : A) (D₀.s * f) = divByS (b : A) (D₀.s * f) := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
            (S := Localization.Away (D₀.s * f)) (b : A),
          ← IsLocalization.mk'_mul, one_mul, mul_one]
    rw [← hmul]
    refine (locSubring _ _ _).mul_mem ?_ ?_
    · exact algebraMap_mem_locSubring _ _ _ b.2
    · exact divByS_mem_locSubring _ _ _ (Finset.mem_insert_self _ _)⟩ }

/-- The normalized minus datum has `s = D₀.s * f` (same as ordinary minus). -/
@[simp]
theorem laurentMinusNormalizedDatum_s
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    (laurentMinusNormalizedDatum D₀ f).s = D₀.s * f := rfl

/-- The normalized minus datum has `P = D₀.P` (same as ordinary minus). -/
@[simp]
theorem laurentMinusNormalizedDatum_P
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    (laurentMinusNormalizedDatum D₀ f).P = D₀.P := rfl

/-- The normalized minus datum has `T = insert 1 (oldT)`. -/
@[simp]
theorem laurentMinusNormalizedDatum_T
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    letI : DecidableEq A := Classical.decEq A
    (laurentMinusNormalizedDatum D₀ f).T =
      insert (1 : A) (laurentMinusDatum D₀ f).T := rfl

/-! ### `LaurentNormalized` for the normalized minus

The instance requires `f ∈ D₀.P.A₀` for the `insert_s_T_subset_A₀` field
(the new `T` elements include products with `f`, which need to lie in
`P.A₀`). -/

/-- The normalized minus datum is `LaurentNormalized`, provided `f ∈ D₀.P.A₀`.

The `one_mem_T` field holds by construction (we inserted `1`). The
`insert_s_T_subset_A₀` field requires `D₀.s ∈ A₀` (from `LaurentNormalized D₀`)
and `f ∈ A₀` (the new hypothesis), giving the products in the ordinary
minus `T` in `A₀`, plus `1 ∈ A₀` and `D₀.s * f ∈ A₀`. -/
theorem laurentMinusNormalizedDatum_isLaurentNormalized
    [IsTopologicalRing A]
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A)
    (hf : f ∈ D₀.P.A₀) :
    LaurentNormalized (laurentMinusNormalizedDatum D₀ f) := by
  letI : DecidableEq A := Classical.decEq A
  refine ⟨?_, ?_⟩
  · -- insert_s_T_subset_A₀: every element of insert s T is in A₀.
    change ∀ a ∈ insert ((laurentMinusNormalizedDatum D₀ f).s)
        (laurentMinusNormalizedDatum D₀ f).T, a ∈ D₀.P.A₀
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha_T
    · exact D₀.P.A₀.mul_mem
        (LaurentNormalized.insert_s_T_subset_A₀ D₀.s (Finset.mem_insert_self _ _))
        hf
    show a ∈ D₀.P.A₀
    rcases Finset.mem_insert.mp ha_T with rfl | ha_old
    · exact D₀.P.A₀.one_mem
    have hmem : a ∈ ((insert D₀.s D₀.T).product ({D₀.s, f} : Finset A)).image
        (fun p => p.1 * p.2) := ha_old
    obtain ⟨p, hp_prod, hp_eq⟩ := Finset.mem_image.mp hmem
    obtain ⟨ht, hx⟩ := Finset.mem_product.mp hp_prod
    -- a = p.1 * p.2.
    rw [← hp_eq]
    refine D₀.P.A₀.mul_mem ?_ ?_
    · exact LaurentNormalized.insert_s_T_subset_A₀ p.1 ht
    · rcases Finset.mem_insert.mp hx with hx_s | hx_f
      · rw [hx_s]
        exact LaurentNormalized.insert_s_T_subset_A₀ D₀.s
          (Finset.mem_insert_self _ _)
      · rw [Finset.mem_singleton.mp hx_f]; exact hf
  · -- one_mem_T: 1 ∈ T by construction.
    change (1 : A) ∈ insert (1 : A) (laurentMinusDatum D₀ f).T
    exact Finset.mem_insert_self _ _

/-! ### Rational open equality

The normalized minus rational open coincides with the ordinary minus
rational open. Adding `1` to `T` imposes the constraint `v(1) ≤ v(D₀.s * f)`,
which is forced by the existing constraints `v(D₀.s) ≤ v(D₀.s * f)` and
`v(f) ≤ v(D₀.s * f)` (both numerators in the ordinary minus) together with
`v(D₀.s * f) ≠ 0` (the denominator nonvanishing). -/

/-- The normalized minus's rational open equals the ordinary minus's. -/
theorem rationalOpen_laurentMinusNormalized_eq
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    rationalOpen (laurentMinusNormalizedDatum D₀ f).T
        (laurentMinusNormalizedDatum D₀ f).s =
      rationalOpen (laurentMinusDatum D₀ f).T
        (laurentMinusDatum D₀ f).s := by
  letI : DecidableEq A := Classical.decEq A
  change rationalOpen (insert (1 : A) (laurentMinusDatum D₀ f).T)
      (D₀.s * f) = rationalOpen (laurentMinusDatum D₀ f).T (D₀.s * f)
  ext v
  refine ⟨fun ⟨hv, hvT, hvs⟩ => ⟨hv, ?_, hvs⟩, fun ⟨hv, hvT, hvs⟩ => ⟨hv, ?_, hvs⟩⟩
  · -- ⊆: drop `1` from constraint set.
    intro t ht
    exact hvT t (Finset.mem_insert_of_mem ht)
  · -- ⊇: show v(1) ≤ v(D₀.s * f) for the new constraint at t = 1.
    -- Strategy: chain v(1) ≤ v(D₀.s) ≤ v(D₀.s * f) using transitivity.
    -- v(1) ≤ v(D₀.s) comes from `1 ∈ D₀.T` (LaurentNormalized D₀) + `v ∈ rationalOpen D₀`.
    -- v(D₀.s) ≤ v(D₀.s * f) comes from `D₀.s ∈ (laurentMinusDatum D₀ f).T` (as `1 * D₀.s`).
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · -- t = 1: chain via transitivity.
      -- Step 1: v ∈ rationalOpen D₀.T D₀.s (from `laurentMinus_subset`).
      have hv_D₀ : v ∈ rationalOpen D₀.T D₀.s :=
        laurentMinus_subset D₀ f ⟨hv, hvT, hvs⟩
      obtain ⟨_, hv_D₀_T, _⟩ := hv_D₀
      -- Step 2: v.vle 1 D₀.s from `1 ∈ D₀.T` (LaurentNormalized).
      have hv_1_Ds : v.vle 1 D₀.s := hv_D₀_T 1 LaurentNormalized.one_mem_T
      -- Step 3: D₀.s ∈ (laurentMinusDatum D₀ f).T (as `1 * D₀.s` with `1 ∈ insert D₀.s D₀.T`).
      have hDs_in_oldT : D₀.s ∈ (laurentMinusDatum D₀ f).T := by
        change D₀.s ∈ ((insert D₀.s D₀.T).product ({D₀.s, f} : Finset A)).image
            (fun p => p.1 * p.2)
        refine Finset.mem_image.mpr ⟨(1, D₀.s), ?_, ?_⟩
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_insert_of_mem LaurentNormalized.one_mem_T,
             Finset.mem_insert_self _ _⟩
        · exact one_mul _
      -- Step 4: v.vle D₀.s (D₀.s * f).
      have hv_Ds_sf : v.vle D₀.s (D₀.s * f) := hvT D₀.s hDs_in_oldT
      -- Step 5: chain.
      exact v.vle_trans hv_1_Ds hv_Ds_sf
    · exact hvT t ht'

/-- The normalized minus half is contained in the base. -/
theorem laurentMinusNormalized_subset
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    rationalOpen (laurentMinusNormalizedDatum D₀ f).T
        (laurentMinusNormalizedDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := by
  rw [rationalOpen_laurentMinusNormalized_eq]
  exact laurentMinus_subset D₀ f

end ValuationSpectrum

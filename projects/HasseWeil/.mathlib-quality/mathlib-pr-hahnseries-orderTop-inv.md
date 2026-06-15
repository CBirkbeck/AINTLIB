# Mathlib PR prep: HahnSeries inv/div orderTop and leadingCoeff

**Goal**: upstream four lemmas from `HasseWeil/HahnSeriesAux.lean` to mathlib.

## Lemmas

In `Mathlib/RingTheory/HahnSeries/Summable.lean`, `Field` section
(after `instField`, around line 891), insert:

```lean
@[simp]
theorem orderTop_inv_eq_neg {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.orderTop = -s.orderTop := by
  have hs_inv : s⁻¹ ≠ 0 := inv_ne_zero hs
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_ord_mul : (s * s⁻¹).orderTop = s.orderTop + s⁻¹.orderTop :=
    orderTop_mul s s⁻¹
  rw [h_mul_one, orderTop_one] at h_ord_mul
  have hs_ord : s.orderTop ≠ ⊤ := orderTop_ne_top.mpr hs
  have hs_inv_ord : s⁻¹.orderTop ≠ ⊤ := orderTop_ne_top.mpr hs_inv
  lift s.orderTop to Γ using hs_ord with a ha
  lift s⁻¹.orderTop to Γ using hs_inv_ord with b hb
  rw [← WithTop.coe_add, show (0 : WithTop Γ) = ((0 : Γ) : WithTop Γ) from rfl,
      WithTop.coe_eq_coe] at h_ord_mul
  have hab : b = -a := by
    have h1 : a + b = 0 := h_ord_mul.symm
    have h2 : b + a = 0 := by rw [add_comm]; exact h1
    exact eq_neg_of_add_eq_zero_left h2
  rw [hab]; rfl

theorem orderTop_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).orderTop = s.orderTop - t.orderTop := by
  rw [div_eq_mul_inv, orderTop_mul s t⁻¹, orderTop_inv_eq_neg ht,
      sub_eq_add_neg]

theorem leadingCoeff_inv {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_lead_mul : (s * s⁻¹).leadingCoeff = s.leadingCoeff * s⁻¹.leadingCoeff :=
    leadingCoeff_mul s s⁻¹
  rw [h_mul_one, leadingCoeff_one] at h_lead_mul
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← h_lead_mul])

theorem leadingCoeff_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  rw [div_eq_mul_inv, leadingCoeff_mul, leadingCoeff_inv ht, div_eq_mul_inv]
```

## Variable scope

These lemmas all live in mathlib's existing `Field` section
(line ~854 of `Summable.lean`):

```lean
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
```

## Naming

Follows mathlib convention: `<thing>_<op>_<form>`.
- `orderTop_inv_eq_neg` (existing `orderTop_neg` analogue at addition level)
- `orderTop_div` (existing `orderTop_mul` analogue)
- `leadingCoeff_inv` (existing `leadingCoeff_mul` / `leadingCoeff_neg`)
- `leadingCoeff_div`

## Usage in Hasse-Weil

The four lemmas are used to discharge `localExpand_mulByInt_y_orderTop` and
`localExpand_mulByInt_y_leadingCoeff` in `HasseWeil/BridgeMulByInt.lean`,
which in turn close the BRIDGE-001 chain for `[n]`.

Once upstreamed, `HasseWeil/HahnSeriesAux.lean` can be deleted; the imports
from `Mathlib.RingTheory.HahnSeries.Summable` will pick up these lemmas
directly.

## PR checklist (for the author)

- [ ] Branch off mathlib4 master.
- [ ] Add the four lemmas to `Mathlib/RingTheory/HahnSeries/Summable.lean`'s
      `Field` section (around line 891, after `instField`).
- [ ] Run `lake build` locally; verify no regressions.
- [ ] Open PR with title `feat(HahnSeries/Summable): orderTop and leadingCoeff for inv/div over a field`.
- [ ] PR description: brief mathematical content + downstream use in Hasse-Weil.
- [ ] Wait for mathlib reviewer (mathlib4 has a `t-algebra` label and reviewers like @sgouezel, @mariainesdff for this area).

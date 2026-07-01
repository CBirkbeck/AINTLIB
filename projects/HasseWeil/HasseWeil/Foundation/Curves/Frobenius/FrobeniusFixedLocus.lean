import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Frobenius fixed locus in the algebraic closure of a finite field

For a finite field `K` with `q = Fintype.card K` elements, an element of the algebraic
closure `AlgebraicClosure K` is fixed by the `q`-power map (the arithmetic Frobenius) iff it
lies in the image of `K`:

```
a ^ q = a  ↔  a ∈ Set.range (algebraMap K (AlgebraicClosure K))
```

This is the elementary field-theoretic input to Route B (Silverman V.1): the `K`-rational
points are exactly the fixed points of Frobenius.

## Main results

* `HasseWeil.range_algebraMap_eq_roots_X_pow_card_sub_X`: the image of `K` in the algebraic
  closure is exactly the (finset of) roots of `X ^ q - X`.
* `HasseWeil.frobenius_fixed_iff_mem_baseField`: `a ^ q = a ↔ a ∈ range (algebraMap …)`.

## Strategy

`X ^ q - X` over `L = AlgebraicClosure K` is separable (its derivative is `-1`, because
`(q : L) = 0`), has `natDegree = q`, and splits (`L` is algebraically closed); hence it has
exactly `q` distinct roots. The `q` images of `K` under `algebraMap` are distinct
(`algebraMap` is injective) and are all roots (`FiniteField.pow_card`), so they are *all* the
roots. The fixed-point characterisation follows since `a ^ q = a` iff `a` is a root.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.
* `FiniteField.pow_card`, `FiniteField.roots_X_pow_card_sub_X`.
-/

open Polynomial

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K]

local notation "L" => AlgebraicClosure K

/-- A `DecidableEq` instance on the algebraic closure, used to form the finsets of roots and
of the image of `K`. The arguments below are classical, so this is `noncomputable`. -/
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- The polynomial `X ^ q - X` over the algebraic closure, where `q = Fintype.card K`. -/
private noncomputable abbrev frobPoly : L[X] := X ^ Fintype.card K - X

private theorem frobPoly_ne_zero : (frobPoly (K := K)) ≠ 0 :=
  FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card

private theorem frobPoly_natDegree : (frobPoly (K := K)).natDegree = Fintype.card K :=
  FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card

/-- The cardinality of `K`, cast into the algebraic closure, is `0` (matching characteristics). -/
private theorem card_cast_eq_zero : (Fintype.card K : L) = 0 := by
  have h : (algebraMap K L) (Fintype.card K : K) = (algebraMap K L) (0 : K) := by
    rw [FiniteField.cast_card_eq_zero]
  rwa [map_natCast, map_zero] at h

/-- `X ^ q - X` is separable over the algebraic closure (derivative is `-1`). -/
private theorem frobPoly_separable : (frobPoly (K := K)).Separable := by
  rw [separable_def]
  have hderiv : derivative (frobPoly (K := K)) = -1 := by
    rw [derivative_sub, derivative_X, derivative_X_pow, card_cast_eq_zero, C_0,
      zero_mul, zero_sub]
  rw [hderiv]
  exact (isCoprime_one_right (x := frobPoly (K := K))).neg_right

/-- An element of `L` is a root of `X ^ q - X` iff it is fixed by the `q`-power map. -/
private theorem mem_roots_frobPoly_iff (a : L) :
    a ∈ (frobPoly (K := K)).roots ↔ a ^ Fintype.card K = a := by
  rw [mem_roots frobPoly_ne_zero, IsRoot.def]
  simp only [eval_sub, eval_pow, eval_X, sub_eq_zero]

/-- The roots of `X ^ q - X` in `L`, as a finset. -/
private noncomputable def frobRootsFinset : Finset L := (frobPoly (K := K)).roots.toFinset

private theorem mem_frobRootsFinset_iff (a : L) :
    a ∈ (frobRootsFinset (K := K)) ↔ a ^ Fintype.card K = a := by
  rw [frobRootsFinset, Multiset.mem_toFinset, mem_roots_frobPoly_iff]

/-- The image of `K` in the algebraic closure as a finset. -/
private noncomputable def baseImageFinset : Finset L :=
  Finset.univ.image (algebraMap K L)

private theorem mem_baseImageFinset_iff (a : L) :
    a ∈ (baseImageFinset (K := K)) ↔ a ∈ Set.range (algebraMap K L) := by
  rw [baseImageFinset]
  simp [Finset.mem_image, Set.mem_range]

/-- Every element of `K` is, after mapping to `L`, fixed by the `q`-power map. -/
private theorem baseImage_subset_roots :
    (baseImageFinset (K := K)) ⊆ (frobRootsFinset (K := K)) := by
  intro a ha
  rw [mem_baseImageFinset_iff] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [mem_frobRootsFinset_iff, ← map_pow, FiniteField.pow_card]

/-- The image of `K` has exactly `q` elements (`algebraMap` is injective). -/
private theorem card_baseImageFinset : (baseImageFinset (K := K)).card = Fintype.card K := by
  rw [baseImageFinset, Finset.card_image_of_injective _ (algebraMap K L).injective,
    Finset.card_univ]

/-- The root set of `X ^ q - X` in `L` has exactly `q` elements: it has at most `q`
(separable ⇒ nodup, degree `q`) and at least `q` (the `q` images of `K`). -/
private theorem card_frobRootsFinset : (frobRootsFinset (K := K)).card = Fintype.card K := by
  apply le_antisymm
  · -- `card roots.toFinset ≤ card roots ≤ natDegree = q`
    calc (frobRootsFinset (K := K)).card
        ≤ Multiset.card (frobPoly (K := K)).roots := Multiset.toFinset_card_le _
      _ ≤ (frobPoly (K := K)).natDegree := Polynomial.card_roots' _
      _ = Fintype.card K := frobPoly_natDegree
  · -- `q = card (image of K) ≤ card roots`
    rw [← card_baseImageFinset]
    exact Finset.card_le_card baseImage_subset_roots

/-- **The image of `K` is exactly the root set of `X ^ q - X` in the algebraic closure.** -/
theorem range_algebraMap_eq_roots_X_pow_card_sub_X :
    (baseImageFinset (K := K)) = (frobRootsFinset (K := K)) :=
  Finset.eq_of_subset_of_card_le baseImage_subset_roots
    (by rw [card_frobRootsFinset, card_baseImageFinset])

/-- **Frobenius fixed-point criterion.** For a finite field `K`, an element of the algebraic
closure is fixed by the `q`-power map (`q = Fintype.card K`) iff it lies in the image of `K`. -/
theorem frobenius_fixed_iff_mem_baseField (a : AlgebraicClosure K) :
    a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
  rw [← mem_frobRootsFinset_iff, ← mem_baseImageFinset_iff,
    range_algebraMap_eq_roots_X_pow_card_sub_X]

end HasseWeil

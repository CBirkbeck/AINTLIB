import HasseWeil.EC.MulByIntBaseCase

/-!
# Composition of multiplication-by-integer isogenies (T-III-4-020b)

Target: `(mulByInt W m).comp (mulByInt W n) = mulByInt W (m*n)` as isogenies.

The uniqueness framework (`mulByInt_pullback_unique` in `MulByIntBaseCase.lean`)
reduces this to showing the composition sends the generic coordinates to the
`[m*n]`-images. At the x-coordinate level this is the **division polynomial
composition identity** (Silverman III.4.2 core):

  `(W.Φ n).eval₂ (mulByInt_x W m) · (W.ΨSq (m·n)).eval₂ (x_gen) =
   (W.Φ (m·n)).eval₂ (x_gen) · (W.ΨSq n).eval₂ (mulByInt_x W m)`

plus the analogous identity for y.

## Strategy

This file proves the easy cases unconditionally (`m = 1`, `n = 1`, and the
hom-level identity), and gives a witness-parametric form
`mulByInt_comp_eq_mul_of_composition_identity` for the general case. The
general case requires the full composition identity as an hypothesis — that
identity is the subject of T-III-4-020b's core work.

## Main results

* `mulByInt_comp_mulByInt_one_right` — `[m].comp [1] = [m]` (unconditional).
* `mulByInt_one_comp_mulByInt_left` — `[1].comp [m] = [m]` (unconditional).
* `mulByInt_comp_toAddMonoidHom` — `([m].comp [n]).toAddMonoidHom =
  [m*n].toAddMonoidHom` (unconditional, at point level).
* `mulByInt_comp_eq_mul_of_pullback_witness` — witness-parametric form:
  given the pullback identity, conclude isogeny equality.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.2.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-! ### Identity cases: `[1].comp` and `.comp [1]` -/

/-- `[m].comp [1] = [m]`: composing `[m]` with `[1]` (on the right) is `[m]`,
    because `[1]` has identity pullback and point map. Unconditional. -/
theorem mulByInt_comp_mulByInt_one_right (m : ℤ) :
    (mulByInt W.toAffine m).comp (mulByInt W.toAffine 1) = mulByInt W.toAffine m := by
  change Isogeny.mk
      ((mulByInt W.toAffine 1).pullback.comp (mulByInt W.toAffine m).pullback)
      ((mulByInt W.toAffine m).toAddMonoidHom.comp (mulByInt W.toAffine 1).toAddMonoidHom) =
    mulByInt W.toAffine m
  have h_pb : (mulByInt W.toAffine 1).pullback.comp (mulByInt W.toAffine m).pullback =
      (mulByInt W.toAffine m).pullback := by
    rw [mulByInt_one_pullback_eq_id W, AlgHom.id_comp]
  have h_hom : (mulByInt W.toAffine m).toAddMonoidHom.comp
      (mulByInt W.toAffine 1).toAddMonoidHom = (mulByInt W.toAffine m).toAddMonoidHom := by
    ext P
    change (m : ℤ) • ((1 : ℤ) • P) = (m : ℤ) • P
    simp
  rw [h_pb, h_hom]

/-- `[1].comp [m] = [m]`: composing `[1]` with `[m]` (on the left) is `[m]`,
    because `[1]` has identity pullback and point map. Unconditional. -/
theorem mulByInt_one_comp_mulByInt_left (m : ℤ) :
    (mulByInt W.toAffine 1).comp (mulByInt W.toAffine m) = mulByInt W.toAffine m := by
  change Isogeny.mk
      ((mulByInt W.toAffine m).pullback.comp (mulByInt W.toAffine 1).pullback)
      ((mulByInt W.toAffine 1).toAddMonoidHom.comp (mulByInt W.toAffine m).toAddMonoidHom) =
    mulByInt W.toAffine m
  have h_pb : (mulByInt W.toAffine m).pullback.comp (mulByInt W.toAffine 1).pullback =
      (mulByInt W.toAffine m).pullback := by
    rw [mulByInt_one_pullback_eq_id W, AlgHom.comp_id]
  have h_hom : (mulByInt W.toAffine 1).toAddMonoidHom.comp
      (mulByInt W.toAffine m).toAddMonoidHom = (mulByInt W.toAffine m).toAddMonoidHom := by
    ext P
    change (1 : ℤ) • ((m : ℤ) • P) = (m : ℤ) • P
    simp
  rw [h_pb, h_hom]

/-! ### Point-level composition (unconditional) -/

/-- `([m].comp [n]).toAddMonoidHom = [m*n].toAddMonoidHom`: the point-level
    composition of `[m]` and `[n]` is `[m*n]`. Unconditional. -/
theorem mulByInt_comp_toAddMonoidHom (m n : ℤ) :
    ((mulByInt W.toAffine m).comp (mulByInt W.toAffine n)).toAddMonoidHom =
      (mulByInt W.toAffine (m * n)).toAddMonoidHom := by
  ext P
  change (m : ℤ) • ((n : ℤ) • P) = (m * n : ℤ) • P
  rw [← mul_smul]

/-! ### Witness-parametric form for the general case

The pullback equality `(mulByInt W m).pullback.comp (mulByInt W n).pullback =
(mulByInt W (m*n)).pullback` is the hard part. Together with the
unconditional `toAddMonoidHom` identity above, it gives the full isogeny
equality. -/

/-- **Witness-parametric T-III-4-020** (pullback level): given the pullback
    identity as hypothesis, conclude isogeny equality for `[m] ∘ [n] = [m*n]`.
    The hypothesis is discharged by T-III-4-020b (the division polynomial
    composition formula). -/
theorem mulByInt_comp_eq_mul_of_pullback_witness (m n : ℤ)
    (h_pb : (mulByInt W.toAffine n).pullback.comp (mulByInt W.toAffine m).pullback =
      (mulByInt W.toAffine (m * n)).pullback) :
    (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) =
      mulByInt W.toAffine (m * n) := by
  have h_hom := mulByInt_comp_toAddMonoidHom W m n
  change ((mulByInt W.toAffine m).comp (mulByInt W.toAffine n)).toAddMonoidHom = _ at h_hom
  show Isogeny.mk _ ((mulByInt W.toAffine m).comp (mulByInt W.toAffine n)).toAddMonoidHom =
    mulByInt W.toAffine (m * n)
  rw [h_pb, h_hom]

/-! ### Further reduction: pullback identity via generator witnesses

`mulByInt_pullback_unique` lets us reduce the pullback identity to agreement on
the generic x and y coordinates. This is the most direct witness form for
T-III-4-020b: the caller only needs to establish the composition identity on
the two generators. -/

/-- **Witness-parametric via generator agreement**: if the composition
    `(mulByInt W n).pullback ∘ (mulByInt W m).pullback` sends `x_gen` to
    `mulByInt_x W (m*n)` and `y_gen` to `mulByInt_y W (m*n)`, then
    `[m] ∘ [n] = [m*n]` as isogenies.

    Given `m, n, m*n ≠ 0`, the hypothesis on generators is reduced via
    `mulByInt_pullback_unique` to the pullback-level equality, then combined
    with `mulByInt_comp_toAddMonoidHom` for the point-level half. -/
theorem mulByInt_comp_eq_mul_of_generator_witness (m n : ℤ)
    (_hm : m ≠ 0) (_hn : n ≠ 0) (hmn : m * n ≠ 0)
    (h_x : (mulByInt W.toAffine n).pullback
        ((mulByInt W.toAffine m).pullback (x_gen W)) = mulByInt_x W (m * n))
    (h_y : (mulByInt W.toAffine n).pullback
        ((mulByInt W.toAffine m).pullback
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (AdjoinRoot.root W.toAffine.polynomial))) = mulByInt_y W (m * n)) :
    (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) =
      mulByInt W.toAffine (m * n) := by
  apply mulByInt_comp_eq_mul_of_pullback_witness
  exact mulByInt_pullback_unique W (m * n) hmn
    ((mulByInt W.toAffine n).pullback.comp (mulByInt W.toAffine m).pullback) h_x h_y

/-! ### `mulByInt_x` and `mulByInt_y` of `-n`

Since `W.Φ (-n) = W.Φ n` and `W.ΨSq (-n) = W.ΨSq n` in mathlib, the
rational-map images are equal. Useful for `[-n]` computations. -/

/-- `mulByInt_x W (-n) = mulByInt_x W n`: the `[n]`-image of the x-coordinate
    is preserved under negation. Direct from `W.Φ_neg` and `W.ΨSq_neg`. -/
@[simp] theorem mulByInt_x_neg (n : ℤ) : mulByInt_x W (-n) = mulByInt_x W n := by
  unfold mulByInt_x Φ_ff ΨSq_ff
  rw [Φ_neg, ΨSq_neg]

/-! ### x-coordinate composition identity for `[-1]`

The `[-1]` case of the composition identity follows from `mulByInt_x_neg`
combined with the substitution law (`mulByInt_pullback_mulByInt_x`). This
is a concrete instance of T-III-4-020b: the core x-coordinate identity for
`[m] ∘ [-1]` on x_gen. -/

/-- The `[-1]`-pullback sends `x_gen` to itself. Direct from
    `mulByInt_x_neg` + `mulByInt_pullback_x`. -/
theorem mulByInt_pullback_x_neg_one :
    (mulByInt W.toAffine (-1)).pullback (x_gen W) = x_gen W := by
  change (mulByInt W.toAffine (-1)).pullback
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) = _
  rw [mulByInt_pullback_x W (-1) (by norm_num : (-1 : ℤ) ≠ 0), mulByInt_x_neg,
    mulByInt_x_one]

/-- **X-coordinate composition identity for `[-1]·n`**: the composition
    `[-1].pullback ∘ [n].pullback` sends `x_gen` to `mulByInt_x W (-n)`.

    Concrete instance of T-III-4-020b. -/
theorem mulByInt_comp_pullback_x_neg_one (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (x_gen W)) =
      mulByInt_x W (n * -1) := by
  have h_inner : (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n :=
    mulByInt_pullback_x W n hn
  rw [h_inner, mulByInt_pullback_mulByInt_x W (-1) n (by norm_num : (-1 : ℤ) ≠ 0),
    mulByInt_x_neg, mulByInt_x_one, show n * -1 = -n from by ring, mulByInt_x_neg]
  change Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (x_gen W) (W.Φ n) /
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (x_gen W) (W.ΨSq n) =
    mulByInt_x W n
  have h_eq : ∀ (p : Polynomial F),
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (x_gen W) p =
        algebraMap (Polynomial F) W.toAffine.FunctionField p := by
    intro p
    rw [← Polynomial.aeval_def,
      show x_gen W = algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X from by
        unfold x_gen
        exact IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
          W.toAffine.FunctionField Polynomial.X,
      Polynomial.aeval_algebraMap_apply]
    simp
  rw [h_eq, h_eq]
  unfold mulByInt_x Φ_ff ΨSq_ff
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField]

/-! ### More x-coordinate composition instances -/

/-- **X-coordinate composition for `[-1]·(-1) = 1`**: both pullbacks of `x_gen`
    through `[-1]` leave it unchanged, matching `mulByInt_x W 1 = x_gen`. -/
theorem mulByInt_comp_pullback_x_neg_one_neg_one :
    (mulByInt W.toAffine (-1)).pullback
        ((mulByInt W.toAffine (-1)).pullback (x_gen W)) =
      mulByInt_x W ((-1 : ℤ) * -1) := by
  rw [mulByInt_pullback_x_neg_one, mulByInt_pullback_x_neg_one]
  exact (mulByInt_x_one W).symm

/-- **X-coordinate composition for `[m]·1 = m`**: `(mulByInt W 1).pullback`
    acts as identity, and `mulByInt_x W m = mulByInt_x W (m * 1)`. -/
theorem mulByInt_comp_pullback_x_one_right (m : ℤ) (hm : m ≠ 0) :
    (mulByInt W.toAffine 1).pullback
        ((mulByInt W.toAffine m).pullback (x_gen W)) =
      mulByInt_x W (m * 1) := by
  rw [mul_one, mulByInt_one_pullback_eq_id]
  exact mulByInt_pullback_x W m hm

/-- **X-coordinate composition for `1·n = n`**: the outer `(mulByInt W n).pullback`
    sends `x_gen` to `mulByInt_x W n`, and the inner `(mulByInt W 1).pullback`
    fixes `x_gen`. So composition sends `x_gen → mulByInt_x W n = mulByInt_x W (1 * n)`. -/
theorem mulByInt_comp_pullback_x_one_left (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback
        ((mulByInt W.toAffine 1).pullback (x_gen W)) =
      mulByInt_x W (1 * n) := by
  rw [one_mul, mulByInt_one_pullback_eq_id]
  exact mulByInt_pullback_x W n hn

end HasseWeil

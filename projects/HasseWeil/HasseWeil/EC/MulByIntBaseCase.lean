import HasseWeil.OmegaPullbackCoeff

/-!
# Base case identities for `[1]` on division polynomials (T-III-4-020 prep)

The `mulByInt W n` infrastructure (division polynomials `Φ_n, ΨSq_n, ψ_n, ω_n`,
and the rational-map image `mulByInt_x W n = Φ_n/ΨSq_n`,
`mulByInt_y W n = ω_n/ψ_n^3`) is parameterised over `n : ℤ`. For `n = 1` these
identities collapse to the generic point itself, establishing that `[1]` acts
as the identity on the generic coordinates.

These base-case lemmas are the foundation for the full `mulByInt_comp_eq_mul`
development (T-III-4-020): closing `[1] = id_isogeny` as a Lean equality, and
eventually `[m]∘[n] = [m·n]`.

## Main results

* `mulByInt_x_one` — `Φ_1/ΨSq_1 = x_gen` in `K(E)`.
* `mulByInt_y_one` — `ω_1/ψ_1³ = y_gen` in `K(E)`.

Both are direct rewrites using the mathlib identities `WeierstrassCurve.Φ_one`,
`WeierstrassCurve.ΨSq_one`, `WeierstrassCurve.ω_one`, `WeierstrassCurve.ψ_one`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4 (division polynomials).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Φ_1 / ΨSq_1 = x_gen` in `K(E)`: the `[1]`-image of the generic x-coordinate
    is itself. Direct from `Φ_one` (= X) and `ΨSq_one` (= 1). -/
theorem mulByInt_x_one : mulByInt_x W 1 = x_gen W := by
  unfold mulByInt_x x_gen Φ_ff ΨSq_ff
  rw [WeierstrassCurve.Φ_one, WeierstrassCurve.ΨSq_one]
  simp [map_one, div_one]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `ω_1 / ψ_1³ = y_gen` in `K(E)`: the `[1]`-image of the generic y-coordinate
    is itself. Direct from `ω_one` (= Y) and `ψ_one` (= 1). -/
theorem mulByInt_y_one :
    mulByInt_y W 1 =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial) := by
  unfold mulByInt_y ω_ff ψ_ff
  rw [WeierstrassCurve.ω_one, WeierstrassCurve.ψ_one]
  simp [Affine.CoordinateRing.mk, map_one, one_pow, div_one]

/-- `(mulByInt W 1).pullback` sends the generic x-coordinate to itself. Direct
    corollary of `mulByInt_x_one` combined with `mulByInt_pullback_x`. -/
theorem mulByInt_pullback_x_one :
    (mulByInt W.toAffine 1).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) := by
  rw [mulByInt_pullback_x W 1 one_ne_zero, mulByInt_x_one]
  rfl

/-- `(mulByInt W 1).pullback` sends the generic y-coordinate to itself. Direct
    corollary of `mulByInt_y_one` combined with `mulByInt_pullback_y`. -/
theorem mulByInt_pullback_y_one :
    (mulByInt W.toAffine 1).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial) := by
  rw [mulByInt_pullback_y W 1 one_ne_zero, mulByInt_y_one]

/-! ### `[1] = id_isogeny` (T-III-4-020a)

The multiplication-by-one isogeny has identity pullback on the function field.
Proved by the standard reduction chain for AlgHom equality on
`K(E) = Frac(AdjoinRoot W.polynomial)`:

1. `AlgHom.coe_ringHom_injective` — reduce to underlying `RingHom`.
2. `IsLocalization.ringHom_ext` — reduce to agreement on `algebraMap R → K(E)`.
3. `AdjoinRoot.ringHom_ext` — split into agreement on base and root.
4. `Polynomial.ringHom_ext` — split base agreement into F and X.

Each reduced subgoal is discharged by `AlgHom.commutes` (for the base `F`
inclusion), `mulByInt_pullback_x_one` (for the x-generator `Polynomial.X`),
or `mulByInt_pullback_y_one` (for the y-generator `AdjoinRoot.root`). -/
theorem mulByInt_one_pullback_eq_id :
    (mulByInt W.toAffine 1).pullback =
      AlgHom.id F W.toAffine.FunctionField := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.coe_id, id_eq]
      exact (mulByInt W.toAffine 1).pullback.commutes a
    · simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.coe_id, id_eq]
      exact mulByInt_pullback_x_one W
  · simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.coe_id, id_eq]
    exact mulByInt_pullback_y_one W

/-- The `toAddMonoidHom` of `mulByInt W 1` is `AddMonoidHom.id` extensionally:
    on every point P, `1 • P = P`. -/
theorem mulByInt_one_toAddMonoidHom_eq_id :
    (mulByInt W.toAffine 1).toAddMonoidHom = AddMonoidHom.id _ := by
  ext P
  show (1 : ℤ) • P = P
  exact one_zsmul P

/-- `mulByInt W 1 = Isogeny.id` as Isogeny structures (propositionally). Both
    fields agree: `pullback` via `mulByInt_one_pullback_eq_id`, `toAddMonoidHom`
    via `mulByInt_one_toAddMonoidHom_eq_id`. -/
theorem mulByInt_one_eq_id :
    mulByInt W.toAffine 1 = Isogeny.id W.toAffine := by
  have h_pb := mulByInt_one_pullback_eq_id W
  have h_hom := mulByInt_one_toAddMonoidHom_eq_id W
  rcases hα : mulByInt W.toAffine 1 with ⟨pb, hom⟩
  rw [hα] at h_pb h_hom
  simp only at h_pb h_hom
  rw [h_pb, h_hom]
  rfl

/-- **Additive decomposition at hom level**: `[m + n].toAddMonoidHom =
    [m].toAddMonoidHom + [n].toAddMonoidHom`. Direct from `add_zsmul`. -/
theorem mulByInt_add_toAddMonoidHom (m n : ℤ) :
    (mulByInt W.toAffine (m + n)).toAddMonoidHom =
      (mulByInt W.toAffine m).toAddMonoidHom + (mulByInt W.toAffine n).toAddMonoidHom := by
  ext P
  show (m + n) • P = m • P + n • P
  exact add_zsmul P m n

/-- **`[k+1] = [k] + [1]` at hom level**, the natural decomposition for inductive
    arguments via BRIDGE-003. Direct corollary of `mulByInt_add_toAddMonoidHom`. -/
theorem mulByInt_succ_toAddMonoidHom (k : ℤ) :
    (mulByInt W.toAffine (k + 1)).toAddMonoidHom =
      (mulByInt W.toAffine k).toAddMonoidHom + (mulByInt W.toAffine 1).toAddMonoidHom :=
  mulByInt_add_toAddMonoidHom W k 1

/-! ### Consequences: `[1] ∘ [1] = [1]` and `[1]̂ = [1]` (T-III-6-006 for m=1) -/

/-- `[1].comp [1] = [1]` as isogenies: composing the identity isogeny with
    itself gives the identity isogeny. Uses `mulByInt_one_pullback_eq_id`. -/
theorem mulByInt_one_comp_mulByInt_one :
    (mulByInt W.toAffine 1).comp (mulByInt W.toAffine 1) = mulByInt W.toAffine 1 := by
  change Isogeny.mk
      ((mulByInt W.toAffine 1).pullback.comp (mulByInt W.toAffine 1).pullback)
      ((mulByInt W.toAffine 1).toAddMonoidHom.comp (mulByInt W.toAffine 1).toAddMonoidHom) =
    mulByInt W.toAffine 1
  have hhom : (mulByInt W.toAffine 1).toAddMonoidHom.comp
      (mulByInt W.toAffine 1).toAddMonoidHom = (mulByInt W.toAffine 1).toAddMonoidHom := by
    ext P
    change (1 : ℤ) • ((1 : ℤ) • P) = (1 : ℤ) • P
    simp
  rw [mulByInt_one_pullback_eq_id, AlgHom.id_comp, hhom]
  rw [← mulByInt_one_pullback_eq_id W]

/-- `[1] ∘ [1] = [[1].degree]` — the `IsDualOf`-conjunct shape (cf.
    `EC.mulByInt_isDualOf_self`; the legacy `isogDual_mulByInt_of_comp` was
    deleted with the refuted `exists_dual`). Combines
    `mulByInt_one_comp_mulByInt_one` with `mulByInt_degree` (giving
    `[1].degree = 1`). -/
theorem mulByInt_one_comp_eq_mulByInt_degree :
    (mulByInt W.toAffine 1).comp (mulByInt W.toAffine 1) =
      mulByInt W.toAffine ((mulByInt W.toAffine 1).degree : ℤ) := by
  rw [mulByInt_one_comp_mulByInt_one, mulByInt_degree W.toAffine 1 one_ne_zero]
  norm_num

/-! ### Uniqueness of `mulByInt_pullbackAlgHom` (T-III-4-020b infrastructure)

Any F-algebra endomorphism of `K(E)` that sends the generic coordinates
`x_gen → mulByInt_x W n` and `y_gen → mulByInt_y W n` must equal
`(mulByInt W.toAffine n).pullback`. This is a uniqueness consequence of the
ringHom_ext reduction chain used in `mulByInt_one_pullback_eq_id`.

This lemma is the core tool for T-III-4-020 (general `[m]∘[n] = [m·n]`):
once we establish that the composition `(mulByInt W m).pullback.comp
(mulByInt W n).pullback` sends `x_gen → mulByInt_x W (m*n)` and similar for
y, uniqueness forces it to equal `(mulByInt W (m*n)).pullback`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **Substitution law for AlgHoms on K(E)**: for any F-algebra endomorphism `f`
    of `K(E)` and polynomial `p ∈ F[X]`, applying `f` to the image of `p` in
    `K(E)` equals evaluating `p` at `f(x)` where `x = algebraMap F[X] KE X`.

    This is the key fact that the `mulByInt W m` pullback acts on polynomial
    images by "substituting x → x_m" — because it is an F-algebra endomorphism
    of a polynomial-generated (up to FractionRing) F-algebra. -/
theorem algHom_apply_polynomial
    (f : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (p : Polynomial F) :
    f (algebraMap (Polynomial F) W.toAffine.FunctionField p) =
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField)
        (f (algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X)) p := by
  have h : algebraMap (Polynomial F) W.toAffine.FunctionField p =
      Polynomial.aeval
        (algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X) p := by
    rw [Polynomial.aeval_algebraMap_apply]
    simp
  rw [h, ← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]

/-- **Uniqueness**: `(mulByInt W.toAffine n).pullback` is the unique F-algebra
    endomorphism of `K(E)` sending the generic coordinates to the `[n]`-image.

    This generalizes `mulByInt_one_pullback_eq_id` beyond the n=1 case. -/
theorem mulByInt_pullback_unique (n : ℤ) (hn : n ≠ 0)
    (f : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (h_x : f (x_gen W) = mulByInt_x W n)
    (h_y : f (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.root W.toAffine.polynomial)) = mulByInt_y W n) :
    f = (mulByInt W.toAffine n).pullback := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      -- F-base: both sides send algebraMap F a to algebraMap F a (via AlgHom.commutes)
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      -- AdjoinRoot.of W.polynomial (C a) = algebraMap F R a (via tower)
      have h_tower : (AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a) =
          algebraMap F W.toAffine.CoordinateRing a := by
        show algebraMap (Polynomial F) W.toAffine.CoordinateRing (Polynomial.C a) = _
        rw [show Polynomial.C a = algebraMap F (Polynomial F) a from rfl]
        exact (IsScalarTower.algebraMap_apply F (Polynomial F) W.toAffine.CoordinateRing a).symm
      rw [h_tower,
        show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (algebraMap F W.toAffine.CoordinateRing a) = algebraMap F _ a from
          (IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing _ a).symm]
      rw [f.commutes a, (mulByInt W.toAffine n).pullback.commutes a]
    · -- x-gen agreement
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      have h_LHS : f (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)) = mulByInt_x W n := by
        change f (x_gen W) = mulByInt_x W n
        exact h_x
      have h_RHS : (mulByInt W.toAffine n).pullback
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)) = mulByInt_x W n := by
        change (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n
        exact mulByInt_pullback_x W n hn
      rw [h_LHS, h_RHS]
  · simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [h_y, mulByInt_pullback_y W n hn]

/-! ### Pullback of `Φ_ff` and `ΨSq_ff` via substitution (T-III-4-020b prep) -/

/-- The pullback along `[m]` of the polynomial generator `X` is `mulByInt_x W m`:
    `X` maps to `x_gen W` via the scalar tower, then `mulByInt_pullback_x` applies.
    Shared by `mulByInt_pullback_Φ_ff` and `mulByInt_pullback_ΨSq_ff`. -/
private theorem mulByInt_pullback_algebraMap_X (m : ℤ) (hm : m ≠ 0) :
    (mulByInt W.toAffine m).pullback
        (algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X) =
      mulByInt_x W m := by
  have h : algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X = x_gen W := by
    unfold x_gen
    exact IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField Polynomial.X
  rw [h]; exact mulByInt_pullback_x W m hm

/-- The pullback along `[m]` of `Φ_ff W n` is `(W.Φ n).eval₂ (algebraMap F KE) (mulByInt_x W m)`.

    Direct application of `algHom_apply_polynomial` after normalizing `Φ_ff` to
    `algebraMap (Poly F) KE (W.Φ n)` via the scalar tower. -/
theorem mulByInt_pullback_Φ_ff (m n : ℤ) (hm : m ≠ 0) :
    (mulByInt W.toAffine m).pullback (Φ_ff W n) =
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField)
        (mulByInt_x W m) (W.Φ n) := by
  have h_norm : Φ_ff W n =
      algebraMap (Polynomial F) W.toAffine.FunctionField (W.Φ n) := by
    unfold Φ_ff
    exact (IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField (W.Φ n)).symm
  rw [h_norm, algHom_apply_polynomial W (mulByInt W.toAffine m).pullback (W.Φ n),
    mulByInt_pullback_algebraMap_X W m hm]

/-- The pullback along `[m]` of `ΨSq_ff W n` is
    `(W.ΨSq n).eval₂ (algebraMap F KE) (mulByInt_x W m)`. -/
theorem mulByInt_pullback_ΨSq_ff (m n : ℤ) (hm : m ≠ 0) :
    (mulByInt W.toAffine m).pullback (ΨSq_ff W n) =
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField)
        (mulByInt_x W m) (W.ΨSq n) := by
  have h_norm : ΨSq_ff W n =
      algebraMap (Polynomial F) W.toAffine.FunctionField (W.ΨSq n) := by
    unfold ΨSq_ff
    exact (IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField (W.ΨSq n)).symm
  rw [h_norm, algHom_apply_polynomial W (mulByInt W.toAffine m).pullback (W.ΨSq n),
    mulByInt_pullback_algebraMap_X W m hm]

/-- The pullback along `[m]` of `mulByInt_x W n = Φ_ff W n / ΨSq_ff W n`. -/
theorem mulByInt_pullback_mulByInt_x (m n : ℤ) (hm : m ≠ 0) :
    (mulByInt W.toAffine m).pullback (mulByInt_x W n) =
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField)
        (mulByInt_x W m) (W.Φ n) /
      Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField)
        (mulByInt_x W m) (W.ΨSq n) := by
  have h : (mulByInt W.toAffine m).pullback (mulByInt_x W n) =
      (mulByInt W.toAffine m).pullback (Φ_ff W n) /
      (mulByInt W.toAffine m).pullback (ΨSq_ff W n) := by
    show (mulByInt W.toAffine m).pullback (Φ_ff W n / ΨSq_ff W n) = _
    exact map_div₀ _ _ _
  rw [h, mulByInt_pullback_Φ_ff W m n hm, mulByInt_pullback_ΨSq_ff W m n hm]

/-! ### T-III-4-020b witness form for `mulByInt_comp_eq_mul` at the x-coordinate

The general-m `mulByInt_comp_eq_mul` reduces to two identities (one for each
generic coordinate) via `mulByInt_pullback_unique`. Here we state the
x-coordinate identity as a witness hypothesis — the caller must discharge
Silverman's division polynomial composition formula.

Once the composition formula is formalized, the corresponding y-coordinate
identity, and then `mulByInt_comp_eq_mul` itself, follow from routine
composition of `mulByInt_pullback_unique` with these substitution lemmas. -/

end HasseWeil

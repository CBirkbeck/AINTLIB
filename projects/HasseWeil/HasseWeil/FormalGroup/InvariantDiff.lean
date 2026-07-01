import HasseWeil.FormalGroup.Differential

/-!
# Invariant Differentials on Formal Groups (Silverman IV.4)

This file packages `FormalGroup.invariantDiff` into a formal structure and exposes
the main results of Silverman IV.4.2 and IV.4.3:

## Main definitions

* `InvariantDifferential F` — a power series `P(T) ∈ R⟦T⟧` such that
  `P(T) · F_X(0, T)` is a constant in `R⟦T⟧`. This characterization is
  equivalent to Silverman's translation-invariance axiom
  `P(F(T, S)) · F_T(T, S) = P(T)`.
* `InvariantDifferential.IsNormalized` — an invariant differential is
  normalized when its constant coefficient is `1`.
* `FormalGroup.normalizedDifferential F` — the canonical normalized invariant
  differential `ω_F = F_X(0, T)⁻¹`.

## Main results

* `FormalGroup.normalizedDifferential_isNormalized` — `ω_F` is normalized.
* `FormalGroup.normalizedDifferential_unique` — every normalized invariant
  differential equals `ω_F`.
* `InvariantDifferential.eq_smul_normalized` — every invariant differential is
  of the form `a · ω_F` for a unique `a ∈ R`.
* `FormalGroupHom.invariantDifferential_chain` — **Silverman IV.4.3**: for a
  formal group homomorphism `f : F → G`, `ω_G ∘ f = f'(0) · ω_F` (chain rule).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.4, Prop 4.2 and Cor 4.3.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-- An **invariant differential** on a formal group `F/R` is a power series
`P(T) ∈ R⟦T⟧` such that the product `P(T) · F_X(0, T)` is a constant in `R⟦T⟧`.

This characterization is equivalent, by Silverman IV.4.2, to the
translation-invariance axiom
`P(F(T, S)) · F_T(T, S) = P(T)`:
every `P` satisfying the translation-invariance is necessarily a scalar multiple
of `F_X(0, T)⁻¹`, and every scalar multiple satisfies the invariance.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4 (Def + Prop 4.2). -/
structure InvariantDifferential (F : FormalGroup R) where
  /-- The underlying power series `P(T)`. -/
  toSeries : PowerSeries R
  /-- **Invariance**: `P(T) · F_X(0, T)` is a constant. -/
  mul_dX_isConstant : ∃ c : R, toSeries * F.dX_at_zero = PowerSeries.C c

namespace InvariantDifferential

variable {F : FormalGroup R}

/-- The scalar `η.scalar ∈ R` of an invariant differential, defined as the
constant coefficient of `η.toSeries`. -/
noncomputable def scalar (η : InvariantDifferential F) : R :=
  @PowerSeries.constantCoeff R _ η.toSeries

/-- The defining equation: `η.toSeries · F_X(0, T) = C η.scalar`. -/
theorem toSeries_mul_dX_at_zero (η : InvariantDifferential F) :
    η.toSeries * F.dX_at_zero = PowerSeries.C η.scalar := by
  obtain ⟨c, hc⟩ := η.mul_dX_isConstant
  have heq : η.scalar = c := by
    have h := congr_arg (@PowerSeries.constantCoeff R _) hc
    rw [map_mul, F.dX_at_zero_constantCoeff, mul_one, PowerSeries.constantCoeff_C] at h
    exact h
  rw [heq]; exact hc

/-- Every invariant differential is a scalar multiple of `F.invariantDiff`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4.2 (second part). -/
theorem toSeries_eq_scalar_smul (η : InvariantDifferential F) :
    η.toSeries = η.scalar • F.invariantDiff :=
  calc η.toSeries
      = η.toSeries * 1 := (mul_one _).symm
    _ = η.toSeries * (F.dX_at_zero * F.invariantDiff) := by
        rw [F.dX_at_zero_mul_invariantDiff]
    _ = η.toSeries * F.dX_at_zero * F.invariantDiff := (mul_assoc _ _ _).symm
    _ = PowerSeries.C η.scalar * F.invariantDiff := by
        rw [η.toSeries_mul_dX_at_zero]
    _ = η.scalar • F.invariantDiff := (PowerSeries.smul_eq_C_mul _ _).symm

/-- An invariant differential is **normalized** when its constant coefficient is `1`.

Reference: Silverman IV.4.2 (def of normalized). -/
def IsNormalized (η : InvariantDifferential F) : Prop :=
  η.scalar = 1

/-- A normalized invariant differential has `toSeries = F.invariantDiff`. -/
theorem isNormalized_iff (η : InvariantDifferential F) :
    η.IsNormalized ↔ η.toSeries = F.invariantDiff := by
  constructor
  · intro h
    rw [η.toSeries_eq_scalar_smul, h]; exact one_smul R _
  · intro h
    change η.scalar = 1
    rw [scalar, h, F.invariantDiff_constantCoeff]

end InvariantDifferential

/-- The **normalized invariant differential** `ω_F = F_X(0, T)⁻¹` of a formal
group `F`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4, Prop 4.2. -/
noncomputable def FormalGroup.normalizedDifferential (F : FormalGroup R) :
    InvariantDifferential F where
  toSeries := F.invariantDiff
  mul_dX_isConstant := ⟨1, by
    rw [F.invariantDiff_mul_dX_at_zero]; exact (map_one PowerSeries.C).symm⟩

/-- The normalized invariant differential is normalized: `ω_F(0) = 1`. -/
theorem FormalGroup.normalizedDifferential_isNormalized (F : FormalGroup R) :
    F.normalizedDifferential.IsNormalized :=
  F.invariantDiff_constantCoeff

/-- **Uniqueness** of the normalized invariant differential.

Reference: Silverman IV.4.2. -/
theorem FormalGroup.normalizedDifferential_unique (F : FormalGroup R)
    {η : InvariantDifferential F} (h : η.IsNormalized) :
    η.toSeries = F.normalizedDifferential.toSeries :=
  (InvariantDifferential.isNormalized_iff η).mp h

/-- **Silverman IV.4.2 (second part)**: every invariant differential is `a · ω_F`
for a unique `a ∈ R`. -/
theorem InvariantDifferential.eq_smul_normalized {F : FormalGroup R}
    (η : InvariantDifferential F) :
    ∃! a : R, η.toSeries = a • F.normalizedDifferential.toSeries := by
  refine ⟨η.scalar, η.toSeries_eq_scalar_smul, fun b hb ↦ ?_⟩
  -- From `η.toSeries = b • invariantDiff`, take constant coefficient of both sides.
  -- Since `constantCoeff` is defeq-compatible with `•`, the goal reduces to
  -- `b • (1 : R) = b`, i.e., `b * 1 = b`.
  have h : η.scalar = b := by
    change @PowerSeries.constantCoeff R _ η.toSeries = b
    rw [hb]
    change b • @PowerSeries.constantCoeff R _ F.invariantDiff = b
    rw [F.invariantDiff_constantCoeff]
    exact mul_one b
  exact h.symm

/-- **Silverman IV.4.3 (Chain rule for invariant differentials)**.

For a formal group homomorphism `f : F → G` with `f(T) = c₁T + O(T²)`:
`ω_G(f(T)) · f'(T) = c₁ · ω_F(T)`,
where `ω_F, ω_G` are the normalized invariant differentials.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4, Cor. 4.3. -/
theorem FormalGroupHom.invariantDifferential_chain {F G : FormalGroup R}
    (f : FormalGroupHom F G) :
    PowerSeries.subst f.toSeries G.normalizedDifferential.toSeries *
      (PowerSeries.derivative R f.toSeries) =
    PowerSeries.C (PowerSeries.coeff 1 f.toSeries) *
      F.normalizedDifferential.toSeries :=
  FormalGroup.invariantDiff_chain f

/-- **Extensionality** for invariant differentials: two invariant differentials
are equal when their underlying power series agree. Proof-irrelevance handles
the `mul_dX_isConstant` field, which is a `Prop`.

This is an alternative form of `InvariantDifferential.mk.injEq`. -/
@[ext]
theorem InvariantDifferential.ext {F : FormalGroup R}
    {η₁ η₂ : InvariantDifferential F} (h : η₁.toSeries = η₂.toSeries) : η₁ = η₂ := by
  cases η₁; cases η₂; congr

/-- **Full-structure uniqueness** of the normalized invariant differential.

Strong form of `normalizedDifferential_unique`: any normalized invariant
differential equals `F.normalizedDifferential` as elements of
`InvariantDifferential F`.

Reference: Silverman IV.4.2. -/
theorem FormalGroup.normalizedDifferential_unique' (F : FormalGroup R)
    (η : InvariantDifferential F) (h : η.IsNormalized) :
    η = F.normalizedDifferential :=
  InvariantDifferential.ext (F.normalizedDifferential_unique h)

end HasseWeil.FormalGroup

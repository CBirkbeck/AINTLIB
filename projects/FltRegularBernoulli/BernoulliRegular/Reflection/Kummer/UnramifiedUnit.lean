module

public import BernoulliRegular.Reflection.Kummer.Presentation
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Unit decomposition of the Kummer generator (REF-18 step 2)

For an unramified cyclic degree-`p` extension `E = K(α)` of `K = ℚ(ζ_p)`
presented as `α^p = γ` with `γ ∈ K`, classical Kummer theory (Washington
§10.2) shows that

> `E/K` is unramified ⟺ for every prime `q ⊂ 𝓞_K`, `v_q(γ) ∈ p · ℤ`.

Equivalently, `(γ) = J^p` for some fractional ideal `J` of `K`.
Specialising to a `J` that is principal — say `J = (β)` — we get
`(γ) = (β)^p`, i.e. `γ/β^p` has trivial principal-ideal class. Since the
fractional-ideal-of-a-unit is `(1)`, the element `γ/β^p` lifts to an
element `u ∈ (𝓞_K)ˣ`, yielding the **unit decomposition**

> `γ = u · β^p`, `u ∈ (𝓞_K)ˣ`, `β ∈ K^×`.

This file refines this picture into atomic, mathematically meaningful
predicates on a `KummerPresentation`:

## Main definitions

* `KummerPresentation.GenIsPowOfFractionalIdealClass`:
  `(γ)` is a `p`-th power in the group of fractional-ideal classes,
  i.e. `∃ J, toPrincipalIdeal _ _ γ = J^p` (including non-principal `J`).
  This is the **weak form** equivalent to the unramifiedness criterion
  `v_q(γ) ∈ p · ℤ` for every prime `q`.

* `KummerPresentation.GenIsPowOfPrincipalFractionalIdeal`:
  `∃ β : K^×, (γ) = (β)^p` as fractional ideals. This is the **strong
  form** in which the `J` of the weak form is itself principal — the
  representative chosen to feed the unit decomposition.

* `KummerPresentation.GenEqUnitMulPow`:
  `∃ (u : (𝓞_K)ˣ) (β : K^×), γ = (u : K) * β^p`. This is the
  **unit-decomposition** form consumed by the χ-eigenspace alignment in
  the Kummer-to-unit-quotient bridge.

## Main reductions

* `KummerPresentation.genEqUnitMulPow_of_genIsPowOfPrincipalFractionalIdeal`:
  the strong-form `(γ) = (β)^p` implies `γ = u · β^p`. This is the
  **substantive algebraic step** of this file. The proof uses
  `FractionalIdeal.spanSingleton_eq_spanSingleton`:

  > `spanSingleton (γ/β^p) = spanSingleton 1` iff `∃ u : (𝓞_K)ˣ, u • 1 = γ/β^p`.

  Combined with the principal-ideal hypothesis, this exhibits `γ/β^p` as
  a unit, hence `γ = u · β^p`.

* `KummerPresentation.genIsPowOfFractionalIdealClass_of_genIsPowOfPrincipalFractionalIdeal`:
  the strong form is a special case of the weak form. The principal
  `(β)^p` is a fractional-ideal class.

## Pipeline shape

```
unramified E/K
      ↓ (Kummer-Dedekind: not in this file; supplied later)
GenIsPowOfFractionalIdealClass --- weak form, valuation criterion
      ↓ (principal-ideal lift: choose β with [J] = [(β)] mod p-th powers)
GenIsPowOfPrincipalFractionalIdeal --- strong form
      ↓ (this file's substantive reduction)
GenEqUnitMulPow --- final unit decomposition
```

The step from `GenIsPowOfFractionalIdealClass` to
`GenIsPowOfPrincipalFractionalIdeal` is the `Cl/Cl^p` lift of the
fractional-ideal class `[J]`; it is supplied by the principal-ideal
content of the Hilbert class field input (the class group `p`-quotient lifts to a chosen
representative). It is left as a downstream obligation here.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2 ("unramified
  Kummer extensions and pseudo-units").
* Diekmann, *FLT for regular primes*, §6.
* Borevich-Shafarevich, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField FractionalIdeal Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular


namespace KummerPresentation

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

/-!
### Atomic predicates: the three forms of the unit-decomposition statement
-/

/-- **Weak form.** The principal fractional ideal `(γ)` is a `p`-th power in the
group of (invertible) fractional ideals — equivalently, `γ` has `p`-divisible
valuation at every prime of `𝓞 K`.

This is the form delivered directly by the Kummer-Dedekind ramification
analysis of `E = K(γ^{1/p})/K`: the extension is unramified iff for every
prime `q`, `v_q(γ) ∈ p · ℤ`. -/
def GenIsPowOfFractionalIdealClass (P : KummerPresentation Ext) : Prop :=
  ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, toPrincipalIdeal (𝓞 K) K P.genUnit = J ^ p

/-- **Strong form.** `(γ) = (β)^p` as fractional ideals for some `β ∈ K^×` —
i.e. the `J` of the weak form is itself principal.

This is the chosen representative that feeds the unit decomposition. The
principal-ideal lift requires choosing a class-group representative. In the
Hilbert class field input, this is supplied by a Hilbert `p`-class field
generator. -/
def GenIsPowOfPrincipalFractionalIdeal (P : KummerPresentation Ext) : Prop :=
  ∃ β : Kˣ, toPrincipalIdeal (𝓞 K) K P.genUnit = (toPrincipalIdeal (𝓞 K) K β) ^ p

/-- **Unit-decomposition form.** `γ = u · β^p` for some unit `u ∈ (𝓞_K)ˣ` and
some `β ∈ K^×`.

This is the final form fed into the χ-eigenspace alignment of the
Kummer-to-unit-quotient bridge. -/
def GenEqUnitMulPow (P : KummerPresentation Ext) : Prop :=
  ∃ (u : (𝓞 K)ˣ) (β : Kˣ), (P.gen : K) = (algebraMap (𝓞 K) K (u : 𝓞 K)) * (β : K) ^ p

/-!
### Reductions between the three forms
-/

/-- The strong form is a special case of the weak form: principal `(β)^p` is in
particular a `p`-th power in the fractional-ideal class group. -/
theorem genIsPowOfFractionalIdealClass_of_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfPrincipalFractionalIdeal) :
    P.GenIsPowOfFractionalIdealClass := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨toPrincipalIdeal (𝓞 K) K β, hβ⟩

/-- **Substantive reduction.** From `(γ) = (β)^p` as fractional ideals, we
obtain `γ = u · β^p` for some unit `u ∈ (𝓞_K)ˣ`.

The proof uses the principal-ideal characterisation
`spanSingleton x = spanSingleton y ↔ ∃ u : Rˣ, u • x = y` to exhibit
`γ · (β^p)⁻¹ = u · 1` for some unit `u`, then transports back to `γ = u · β^p`. -/
theorem genEqUnitMulPow_of_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfPrincipalFractionalIdeal) :
    P.GenEqUnitMulPow := by
  obtain ⟨β, hβ⟩ := h
  -- `hβ : toPrincipalIdeal _ _ γ = (toPrincipalIdeal _ _ β)^p`. Pass to the
  -- underlying spanSingleton equality `(γ) = (β^p)` as fractional ideals.
  have hspan : spanSingleton (𝓞 K)⁰ ((P.genUnit : K)) =
      spanSingleton (𝓞 K)⁰ (((β ^ p : Kˣ) : K)) := by
    have h1 := congrArg Units.val (hβ.trans (map_pow _ β p).symm)
    simpa only [coe_toPrincipalIdeal] using h1
  -- Apply `spanSingleton_eq_spanSingleton`.
  obtain ⟨u, hu⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton
    (R := 𝓞 K) (S := (𝓞 K)⁰) (P := K)).mp hspan
  -- `hu : u • γ = β^p` in `K`. Solve for `γ`: `γ = u⁻¹ • β^p`.
  refine ⟨u⁻¹, β, ?_⟩
  -- Goal: `(P.gen : K) = (algebraMap _ _ u⁻¹.val) * β^p`.
  have hg : (P.genUnit : K) = u⁻¹ • ((β ^ p : Kˣ) : K) := eq_inv_smul_iff.2 hu
  rw [← P.genUnit_val, hg, Units.val_pow_eq_pow_val, Units.smul_def, Algebra.smul_def]

/-!
### Composite reduction: from the weak form (`(γ) = J^p`) to the unit
decomposition, modulo the principal-ideal lift of `J`.

The principal-ideal lift is a separate input: given a witness for
`GenIsPowOfFractionalIdealClass` (`(γ) = J^p` in the fractional-ideal group),
we need to choose a `β : K^×` representing the class of `J` (modulo `p`-th
powers) so that `(γ) = (β)^p`. In a Hilbert `p`-class-field setting, the
existence of such a `β` is the substantive class-group input.

Once both are available, the composition gives the unit decomposition.
-/

/-- **Composite reduction.** From the weak form together with a principal-ideal
representative for the fractional-ideal class, derive the unit decomposition.

This packages the two steps:

* `(γ) = J^p` in the fractional-ideal group (weak form), and
* `J = (β)` as a chosen principal representative (class-group lift),

into the strong form `(γ) = (β)^p`, then applies the substantive reduction. -/
theorem genEqUnitMulPow_of_genIsPowOfFractionalIdealClass_with_principal_lift
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfFractionalIdealClass)
    (lift : ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      toPrincipalIdeal (𝓞 K) K P.genUnit = J ^ p →
      ∃ β : Kˣ, J = toPrincipalIdeal (𝓞 K) K β) :
    P.GenEqUnitMulPow := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨β, hβ⟩ := lift J hJ
  apply genEqUnitMulPow_of_genIsPowOfPrincipalFractionalIdeal
  refine ⟨β, ?_⟩
  rw [hJ, hβ]

/-!
### `KummerPresentation` exposed view of the unit decomposition

The following theorem unwinds `GenEqUnitMulPow` into the more usable shape

  `∃ u : (𝓞_K)ˣ, ∃ β : K, β ≠ 0 ∧ P.gen = (algebraMap _ _ u) * β^p`,

matching the existence statement requested by the bridge construction step
2 in `REF-18 ↔ Reflection bridge`.
-/

/-- **Existence form of the unit decomposition.**

If `(γ) = (β)^p` for some `β ∈ K^×`, then there exist a unit `u ∈ (𝓞_K)ˣ`
and a `β ∈ K` with `β ≠ 0` such that `γ = (algebraMap u) * β^p`.

This is the form requested by the Kummer-to-unit-quotient bridge:
`γ ∈ (𝓞_K)ˣ · (K^×)^p`, i.e. `γ`'s class in `K^×/(K^×)^p` factors through
the unit quotient. -/
theorem exists_unit_decomposition_of_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfPrincipalFractionalIdeal) :
    ∃ (u : (𝓞 K)ˣ) (β : K), β ≠ 0 ∧
      (P.gen : K) = (algebraMap (𝓞 K) K (u : 𝓞 K)) * β ^ p := by
  obtain ⟨u, β, hβ⟩ := P.genEqUnitMulPow_of_genIsPowOfPrincipalFractionalIdeal h
  exact ⟨u, β, β.ne_zero, hβ⟩

/-- **`u • β^p` form** of the unit decomposition: an alternative phrasing using
the `(𝓞_K)ˣ`-action on `K`, matching the task's requested statement
`P.gen = u • β^p`. The action `u • x = (algebraMap u) * x` is the standard
unit-action on a `(𝓞_K)`-algebra. -/
theorem exists_unit_smul_pow_of_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfPrincipalFractionalIdeal) :
    ∃ (u : (𝓞 K)ˣ) (β : K), β ≠ 0 ∧ (P.gen : K) = u • (β ^ p) := by
  obtain ⟨u, β, hβne, hβ⟩ :=
    exists_unit_decomposition_of_genIsPowOfPrincipalFractionalIdeal P h
  refine ⟨u, β, hβne, ?_⟩
  -- Goal: P.gen = u • β^p; we have P.gen = algebraMap u * β^p.
  rw [hβ, Units.smul_def, Algebra.smul_def]

/-!
### Converse: the unit decomposition implies the strong form

The unit decomposition `γ = u · β^p` (with `u : (𝓞_K)ˣ` and `β ∈ K^×`) implies
`(γ) = (β)^p` as fractional ideals: principal ideals of units are trivial, so

  `(γ) = (algebraMap u) · (β^p) = 1 · (β^p) = (β)^p`

in the group of invertible fractional ideals. This makes the strong form and
the unit-decomposition form equivalent.
-/

/-- **Converse reduction.** The unit decomposition `γ = u · β^p` implies the
strong fractional-ideal form `(γ) = (β)^p`. -/
theorem genIsPowOfPrincipalFractionalIdeal_of_genEqUnitMulPow
    (P : KummerPresentation Ext)
    (h : P.GenEqUnitMulPow) :
    P.GenIsPowOfPrincipalFractionalIdeal := by
  obtain ⟨u, β, hγ⟩ := h
  -- `hγ : (P.gen : K) = (algebraMap u) * (β:K)^p`.  Take principal ideals.
  -- The principal ideal of `algebraMap u` is `(1)`, since `u` is a unit in 𝓞K
  -- and `algebraMap` sends units to units, so its spanSingleton is `(1)`.
  refine ⟨β, ?_⟩
  -- Goal: `toPrincipalIdeal _ _ P.genUnit = (toPrincipalIdeal _ _ β) ^ p`.
  -- Equivalent at spanSingleton level.
  apply Units.ext
  rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, coe_toPrincipalIdeal,
    spanSingleton_pow, P.genUnit_val, hγ, ← spanSingleton_mul_spanSingleton]
  -- Goal: spanSingleton _ (algebraMap u) * spanSingleton _ ((β:K)^p)
  --      = spanSingleton _ ((β:K)^p).
  -- Use `algebraMap u = u • 1`, then `spanSingleton (u • 1) = spanSingleton 1 = 1`.
  conv_rhs => rw [← one_mul (spanSingleton _ ((β : K) ^ p))]
  congr 1
  -- Goal: spanSingleton _ (algebraMap u) = 1.
  -- Use `spanSingleton_eq_spanSingleton`: `spanSingleton x = spanSingleton 1`
  -- iff `∃ v : (𝓞 K)ˣ, v • x = 1`, which holds with `v = u⁻¹`.
  rw [show (1 : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (1 : K) from spanSingleton_one.symm,
    FractionalIdeal.spanSingleton_eq_spanSingleton (R := 𝓞 K) (S := (𝓞 K)⁰) (P := K)]
  refine ⟨u⁻¹, ?_⟩
  -- Goal: u⁻¹ • (algebraMap u) = 1.
  rw [Units.smul_def, Algebra.smul_def, ← map_mul, ← Units.val_mul]
  simp

end KummerPresentation

end BernoulliRegular

end





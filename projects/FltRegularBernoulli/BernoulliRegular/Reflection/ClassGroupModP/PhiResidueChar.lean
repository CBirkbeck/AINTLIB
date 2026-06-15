module

public import BernoulliRegular.Reflection.ClassGroupModP.Module
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Ref19Universal
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# `phi η : ClassGroup (𝓞 K) → ZMod p` from the universal REF-19 hypothesis

This file constructs the canonical-residue character on the class group:

  `phi η [I] := pthSymbolAtIdeal_canonical η (integralRep [I])`

for `[I] ∈ ClassGroup (𝓞 K)` and a fixed hyperprimary `η : 𝓞 K`,
under the universal REF-19 hypothesis.

The well-definedness modulo principal-ideal-class equivalence is the
content of REF-20 (`pthSymbolAtIdeal_canonical_eq_of_eq_principal_mul`
and friends from `Furtwaengler/PhiClassFunction.lean`).

## Approach

We use `ClassGroup.integralRep` to choose an integer representative
and apply `pthSymbolAtIdeal_canonical η` to it. The choice of
representative is via `Quotient.out`, so the resulting function on
`ClassGroup (𝓞 K)` is well-defined as a function (not a homomorphism)
purely by the representative-choosing.

For `phiOnClassGroup` to be a *homomorphism* requires the
well-definedness theorem to relate symbol values across class
representatives — which follows from REF-19 (universal vanishing on
principal ideals). We expose this as the `_well_def` hypothesis on the
constructor.

## Main definitions

* `phiOnClassGroup η _ : ClassGroup (𝓞 K) → ZMod p` — the
  canonical-residue character (function form, not yet a homomorphism).
* `phiOnClassGroup_def` — direct unfolding by `Quotient.out`.
* `phiOnClassGroupHom` — the REF-20 homomorphism
  `ClassGroup (𝓞 K) →* Multiplicative (ZMod p)`.
* `exists_phiOnClassGroupHom_of_ref19PerGammaSupplier` — the consumer-facing
  REF-20 endpoint from the REF-19 per-γ supplier.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **`phi η` on `ClassGroup (𝓞 K)`** via integer-ideal representatives
chosen by `Quotient.out` + `ClassGroup.integralRep`. -/
noncomputable def phiOnClassGroup
    {η : 𝓞 K} (_h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (c : ClassGroup (𝓞 K)) : ZMod p :=
  pthSymbolAtIdeal_canonical (p := p) (K := K) η
    (ClassGroup.integralRep (Quotient.out c).val)

/-- **Definitional unfolding** for `phiOnClassGroup`. -/
theorem phiOnClassGroup_def
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (c : ClassGroup (𝓞 K)) :
    phiOnClassGroup h_ref19 c =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (ClassGroup.integralRep (Quotient.out c).val) :=
  rfl

/-- **Class invariance of `pthSymbolAtIdeal_canonical η`**: under the
universal REF-19 hypothesis, two integer ideals in the same class give
equal symbol values.

The proof uses `ClassGroup.mk0_eq_mk0_iff` to extract `x, y ≠ 0` with
`span(x) · I₁ = span(y) · I₂`, then applies multiplicativity and REF-19
to identify the two symbols.

This is the substantive class invariance content underlying
`phiOnClassGroup`'s well-definedness as a homomorphism. -/
theorem pthSymbolAtIdeal_canonical_class_invariant
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I₁ I₂ : (Ideal (𝓞 K))⁰}
    (h_class : ClassGroup.mk0 I₁ = ClassGroup.mk0 I₂) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η I₁.val =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I₂.val := by
  -- Extract x, y ≠ 0 with span(x) · I₁ = span(y) · I₂.
  obtain ⟨x, y, hx_ne, hy_ne, h_eq⟩ :=
    ClassGroup.mk0_eq_mk0_iff.mp h_class
  -- Apply pthSymbolAtIdeal η to both sides via multiplicativity.
  have hI₁ : (I₁ : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I₁.2
  have hI₂ : (I₂ : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I₂.2
  have hspan_x : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hx_ne
  have hspan_y : Ideal.span ({y} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hy_ne
  have h_apply :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({x} : Set (𝓞 K)) * I₁.val) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({y} : Set (𝓞 K)) * I₂.val) := by
    rw [h_eq]
  rw [pthSymbolAtIdeal_canonical_mul_ideal η hspan_x hI₁,
      pthSymbolAtIdeal_canonical_mul_ideal η hspan_y hI₂,
      h_ref19 x hx_ne, h_ref19 y hy_ne, zero_add, zero_add] at h_apply
  exact h_apply

/-- **Agreement theorem**: `phiOnClassGroup h_ref19 (ClassGroup.mk0 I)`
equals `pthSymbolAtIdeal_canonical η I.val` for any integer ideal
representative `I`. -/
theorem phiOnClassGroup_mk0
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (I : (Ideal (𝓞 K))⁰) :
    phiOnClassGroup h_ref19 (ClassGroup.mk0 I) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val := by
  unfold phiOnClassGroup
  apply pthSymbolAtIdeal_canonical_class_invariant h_ref19
    (I₁ := ⟨ClassGroup.integralRep _,
      ClassGroup.integralRep_mem_nonZeroDivisors
        (Quotient.out (ClassGroup.mk0 I)).ne_zero⟩)
    (I₂ := I)
  show ClassGroup.mk0 ⟨ClassGroup.integralRep _, _⟩ = ClassGroup.mk0 I
  rw [ClassGroup.mk0_integralRep]
  show ClassGroup.mk (FractionRing (𝓞 K)) (Quotient.out (ClassGroup.mk0 I)) =
    ClassGroup.mk0 I
  rw [← ClassGroup.Quot_mk_eq_mk]
  exact Quot.out_eq _

/-- **One-class evaluation**: `phiOnClassGroup h_ref19 1 = 0`.

The identity class is `ClassGroup.mk0 (1 : (Ideal (𝓞 K))⁰)`, and
`pthSymbolAtIdeal η 1 = 0`. -/
theorem phiOnClassGroup_one
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η) :
    phiOnClassGroup h_ref19 (1 : ClassGroup (𝓞 K)) = 0 := by
  rw [← map_one (ClassGroup.mk0 (R := 𝓞 K))]
  rw [phiOnClassGroup_mk0 h_ref19]
  simp

/-- **Multiplicativity** (additivity in `ZMod p`):
`phiOnClassGroup h_ref19 (c₁ * c₂) = phiOnClassGroup h_ref19 c₁ + phiOnClassGroup h_ref19 c₂`. -/
theorem phiOnClassGroup_mul
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (c₁ c₂ : ClassGroup (𝓞 K)) :
    phiOnClassGroup h_ref19 (c₁ * c₂) =
      phiOnClassGroup h_ref19 c₁ + phiOnClassGroup h_ref19 c₂ := by
  -- Find integer representatives.
  obtain ⟨I₁, hI₁⟩ := ClassGroup.mk0_surjective c₁
  obtain ⟨I₂, hI₂⟩ := ClassGroup.mk0_surjective c₂
  -- Replace c₁, c₂ by mk0 I₁, mk0 I₂.
  rw [← hI₁, ← hI₂, ← map_mul (ClassGroup.mk0 (R := 𝓞 K)),
      phiOnClassGroup_mk0 h_ref19, phiOnClassGroup_mk0 h_ref19,
      phiOnClassGroup_mk0 h_ref19]
  -- Goal: pthSymbolAtIdeal η (I₁ * I₂).val = pthSymbolAtIdeal η I₁ + pthSymbolAtIdeal η I₂
  change pthSymbolAtIdeal_canonical (p := p) (K := K) η (I₁ * I₂ : (Ideal _)⁰).val =
    pthSymbolAtIdeal_canonical (p := p) (K := K) η I₁.val +
    pthSymbolAtIdeal_canonical (p := p) (K := K) η I₂.val
  rw [Submonoid.coe_mul]
  exact pthSymbolAtIdeal_canonical_mul_ideal η
    (mem_nonZeroDivisors_iff_ne_zero.mp I₁.2)
    (mem_nonZeroDivisors_iff_ne_zero.mp I₂.2)

/-- **Power form**: `phiOnClassGroup h_ref19 (c^n) = n • phi c`. Standard
consequence of multiplicativity, by induction on `n`. -/
theorem phiOnClassGroup_pow
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (c : ClassGroup (𝓞 K)) (n : ℕ) :
    phiOnClassGroup h_ref19 (c ^ n) = (n : ZMod p) * phiOnClassGroup h_ref19 c := by
  induction n with
  | zero => simp [phiOnClassGroup_one]
  | succ k ih =>
    rw [pow_succ, phiOnClassGroup_mul, ih]
    push_cast
    ring

/-- **`p`-th power kill**: `phiOnClassGroup h_ref19 (c^p) = 0`. Since
`(p : ZMod p) = 0`. -/
theorem phiOnClassGroup_pow_p_eq_zero
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (c : ClassGroup (𝓞 K)) :
    phiOnClassGroup h_ref19 (c ^ p) = 0 := by
  rw [phiOnClassGroup_pow h_ref19 c p, ZMod.natCast_self, zero_mul]

/-- **Descent to ClassGroupModP**: `phiOnClassGroup` factors through
`ClassGroupModP K p`. Concretely, the underlying function is
constant on `(powMonoidHom p).range`-cosets.

Witnessed via `phiOnClassGroup_pow_p_eq_zero`: any element in the
`p`-th-power subgroup has `phi = 0`. -/
theorem phiOnClassGroup_eq_zero_on_pow_p_range
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (x : ClassGroup (𝓞 K))
    (hx : x ∈ (powMonoidHom p : ClassGroup (𝓞 K) →* _).range) :
    phiOnClassGroup h_ref19 x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change phiOnClassGroup h_ref19 (y ^ p) = 0
  exact phiOnClassGroup_pow_p_eq_zero h_ref19 y

/-- **`phi η` as a MonoidHom**: `ClassGroup (𝓞 K) →* Multiplicative (ZMod p)`.

The function `phiOnClassGroup h_ref19`, viewed as a homomorphism into
the multiplicative form of `ZMod p`. Discharges `map_one'` via
`phiOnClassGroup_one` and `map_mul'` via `phiOnClassGroup_mul`. -/
def phiOnClassGroupHom
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η) :
    ClassGroup (𝓞 K) →* Multiplicative (ZMod p) where
  toFun c := Multiplicative.ofAdd (phiOnClassGroup h_ref19 c)
  map_one' := by
    change Multiplicative.ofAdd (phiOnClassGroup h_ref19 1) = 1
    rw [phiOnClassGroup_one]
    rfl
  map_mul' c₁ c₂ := by
    change Multiplicative.ofAdd (phiOnClassGroup h_ref19 (c₁ * c₂)) =
      Multiplicative.ofAdd (phiOnClassGroup h_ref19 c₁) *
      Multiplicative.ofAdd (phiOnClassGroup h_ref19 c₂)
    rw [phiOnClassGroup_mul]
    rfl

/-- **`phi η` as a MonoidHom on `ClassGroupModP K p`** via `QuotientGroup.lift`.

The MonoidHom `phiOnClassGroupHom h_ref19` kills the `(powMonoidHom p).range`
subgroup (by `phiOnClassGroup_eq_zero_on_pow_p_range`), so it descends
to a MonoidHom on the quotient. -/
def phiOnClassGroupModPHom
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η) :
    ClassGroupModP K p →* Multiplicative (ZMod p) :=
  QuotientGroup.lift _ (phiOnClassGroupHom h_ref19) <| by
    intro x hx
    change Multiplicative.ofAdd (phiOnClassGroup h_ref19 x) = 1
    rw [phiOnClassGroup_eq_zero_on_pow_p_range h_ref19 x hx]
    rfl

/-- **`phi η` as a `ZMod p`-linear map**:
`Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p`.

Composition: `phiOnClassGroupModPHom h_ref19` (a multiplicative hom)
is converted to additive via `MonoidHom.toAdditive`, then to a
`ZMod p`-linear map via `AddMonoidHom.toZModLinearMap`. -/
noncomputable def phiOnClassGroupModPLinear
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η) :
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p (phiOnClassGroupModPHom h_ref19).toAdditive

/-! ### REF-20 endpoints from the REF-19 per-γ supplier -/

/-- **REF-20 existence endpoint from the universal REF-19 hypothesis.**

The canonical residue-symbol target is represented internally by the exponent
group `ZMod p`; therefore the multiplicative `μ_p`-valued character is exposed
as a homomorphism to `Multiplicative (ZMod p)`.  On every nonzero ideal
representative it evaluates to the canonical residue symbol
`pthSymbolAtIdeal_canonical η I`. -/
theorem exists_phiOnClassGroupHom
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η) :
    ∃ φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p),
      ∀ I : (Ideal (𝓞 K))⁰,
        φ (ClassGroup.mk0 I) =
          Multiplicative.ofAdd
            (pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val) := by
  refine ⟨phiOnClassGroupHom h_ref19, ?_⟩
  intro I
  change
    Multiplicative.ofAdd (phiOnClassGroup h_ref19 (ClassGroup.mk0 I)) =
      Multiplicative.ofAdd
        (pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val)
  rw [phiOnClassGroup_mk0 h_ref19 I]

/-- **REF-20 class-group character from the REF-19 per-γ supplier.**

This is the consumer-facing homomorphism after REF-18'/REF-19 has supplied
principal-ideal vanishing for every nonzero `γ`. -/
noncomputable def phiOnClassGroupHom_of_ref19PerGammaSupplier
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η) :
    ClassGroup (𝓞 K) →* Multiplicative (ZMod p) :=
  phiOnClassGroupHom (ref19UniversalHypothesis_of_supplier h_supplier)

/-- Evaluation of the REF-20 class-group character on an ideal representative. -/
theorem phiOnClassGroupHom_of_ref19PerGammaSupplier_mk0
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η)
    (I : (Ideal (𝓞 K))⁰) :
    phiOnClassGroupHom_of_ref19PerGammaSupplier h_supplier (ClassGroup.mk0 I) =
      Multiplicative.ofAdd
        (pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val) := by
  change
    Multiplicative.ofAdd
        (phiOnClassGroup (ref19UniversalHypothesis_of_supplier h_supplier)
          (ClassGroup.mk0 I)) =
      Multiplicative.ofAdd
        (pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val)
  rw [phiOnClassGroup_mk0 (ref19UniversalHypothesis_of_supplier h_supplier) I]

/-- **REF-20 existence endpoint from the REF-19 per-γ supplier.**

This packages both parts of REF-20 in one statement: the class-group character
exists as a homomorphism, and its value on any nonzero ideal representative is
exactly the canonical residue symbol. -/
theorem exists_phiOnClassGroupHom_of_ref19PerGammaSupplier
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η) :
    ∃ φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p),
      ∀ I : (Ideal (𝓞 K))⁰,
        φ (ClassGroup.mk0 I) =
          Multiplicative.ofAdd
            (pthSymbolAtIdeal_canonical (p := p) (K := K) η I.val) := by
  refine ⟨phiOnClassGroupHom_of_ref19PerGammaSupplier h_supplier, ?_⟩
  exact phiOnClassGroupHom_of_ref19PerGammaSupplier_mk0 h_supplier

/-- The REF-20 character descended to the elementary `p`-quotient
`ClassGroupModP K p`, from the REF-19 per-γ supplier. -/
noncomputable def phiOnClassGroupModPHom_of_ref19PerGammaSupplier
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η) :
    ClassGroupModP K p →* Multiplicative (ZMod p) :=
  phiOnClassGroupModPHom (ref19UniversalHypothesis_of_supplier h_supplier)

/-- The REF-20 character as the downstream `ZMod p`-linear map on
`Additive (ClassGroupModP K p)`, from the REF-19 per-γ supplier. -/
noncomputable def phiOnClassGroupModPLinear_of_ref19PerGammaSupplier
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η) :
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  phiOnClassGroupModPLinear (ref19UniversalHypothesis_of_supplier h_supplier)

end Furtwaengler

end BernoulliRegular

module

public import BernoulliRegular.Reflection.ClassGroupModP.Module
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.SingularKummer.SingularLinearAction

/-!
# Galois action on `ClassGroupModP K p` (Atom B)

This file provides the **`(ZMod p)ˣ`-action on `Additive (ClassGroupModP K p)`**
needed by `PhiBasedReflectionData` (one of the four substantive atomic
inputs of the reflection chain).

## Strategy

The cyclotomic Galois group `Δ ≃ (ZMod p)ˣ` acts on `Cl(𝓞 K)` via the
ring-of-integers automorphism `cyclotomicRingOfIntegersEquiv a` (which
induces an action on integer ideals `cyclotomicGaloisConjugate a`,
preserves principal ideals, and hence descends to ClassGroup). The
action descends further to `ClassGroupModP K p` (since `σ_a` preserves
the subgroup of `p`-th powers).

The action is then transported to `Additive (ClassGroupModP K p)` and
viewed as `ZMod p`-linear endomorphisms (using the `ZMod p`-module
structure from `Module.lean`).

## Hypothesis-based interface

Constructing the action requires substantial work on `FractionalIdeal`
and the `ClassGroup` quotient that mathlib does not currently provide
for general `RingEquiv`s (only `AlgEquiv`s of the localization). We
therefore expose the action as a **named bundled hypothesis**
`CyclotomicGalAction p K` whose instances can be supplied by any
construction (whether via class-field-theoretic infrastructure, via
the `(Ideal R)⁰`-quotient route, or via direct equivariance).

## Substantive open content

The substantive content of Atom B is constructing an instance of
`CyclotomicGalAction p K` for the cyclotomic setup. This requires:

* The descent of `cyclotomicGaloisConjugate` from `(Ideal R)⁰` to
  `ClassGroup R` via `ClassGroup.mk0_eq_mk0_iff` well-definedness.
* The descent from `ClassGroup R` to `ClassGroupModP R p`.
* The transport to `Additive` and `ZMod p`-linear structure.

See the `## Construction sketch` section in this file for the
mathematical recipe.

## Construction sketch

For `a : CyclotomicUnitDelta p` and `[I] ∈ ClassGroup (𝓞 K)`:

* Choose an integer representative `I' ∈ (Ideal (𝓞 K))⁰` with
  `ClassGroup.mk0 I' = [I]` (via `ClassGroup.mk0_surjective`).
* Set `σ_a [I] := ClassGroup.mk0 (cyclotomicGaloisConjugate a I')`.
* Well-definedness: if `mk0 I'₁ = mk0 I'₂`, then by
  `ClassGroup.mk0_eq_mk0_iff`, ∃ `x, y ≠ 0`,
  `(x) · I'₁ = (y) · I'₂`. Apply `cyclotomicGaloisConjugate_mul_ideal`
  and the principal-ideal preservation
  `cyclotomicGaloisConjugate (Ideal.span {γ}) = Ideal.span {σ_a γ}`
  (a `Ideal.map_span` consequence) to get
  `(σ_a x) · σ_a I'₁ = (σ_a y) · σ_a I'₂`, hence
  `mk0 (σ_a I'₁) = mk0 (σ_a I'₂)` via `mk0_eq_mk0_iff`.
* Multiplicativity in `a` follows from
  `cyclotomicGaloisConjugate_mul`.

The descent to `ClassGroupModP K p` then follows from
`cyclotomicGaloisConjugate_pow_ideal`: `σ_a (I^p) = (σ_a I)^p`, so the
action sends `p`-th powers to `p`-th powers.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Cyclotomic Galois action on `ClassGroupModP K p`** (Atom B).

A `CyclotomicGalAction p K` is the substantive bundle:

* a `(ZMod p)ˣ →* Module.End (ZMod p) (Additive (ClassGroupModP K p))`
  monoid homomorphism (the action),
* the unit at `1`: `galAction 1 = id` (automatic from `MonoidHom`).

Constructing this for the cyclotomic setup is one of the four
substantive open atoms of the reflection chain (REF-26's Atom B).
The action exists by classical class-field-theoretic principle
(Galois group acts on class group via ideal pushforward) but
constructing it concretely requires `ClassGroup` quotient machinery
not currently in mathlib for general `RingEquiv` inputs. -/
abbrev CyclotomicGalAction : Type _ :=
  (ZMod p)ˣ →* Module.End (ZMod p) (Additive (ClassGroupModP K p))

/-- **Named existence hypothesis** for `CyclotomicGalAction`. -/
def CyclotomicGalActionHypothesis : Prop :=
  Nonempty (CyclotomicGalAction p K)

/-- Extract the underlying action from the existence hypothesis. -/
noncomputable def CyclotomicGalActionHypothesis.someAction
    (h : CyclotomicGalActionHypothesis p K) : CyclotomicGalAction p K :=
  h.some

omit [IsCyclotomicExtension {p} ℚ K] in
/-- A concrete `CyclotomicGalAction` instance proves the existence
hypothesis. -/
theorem CyclotomicGalActionHypothesis.of_action
    (a : CyclotomicGalAction p K) : CyclotomicGalActionHypothesis p K :=
  ⟨a⟩

/-! ### Intermediate construction: σ_a action on integer ideals as classes

The cyclotomic Galois action on integer ideals
(`cyclotomicGaloisConjugate`) preserves nonzero ideals (via
`cyclotomicGaloisConjugate_ne_bot`), so it lifts to an action on
`(Ideal (𝓞 K))⁰`. Composing with `ClassGroup.mk0` gives a
`MonoidHom (Ideal R)⁰ →* ClassGroup R` per `a`, which is the
"σ_a-shifted class" of an integer ideal.

This is the FIRST step of constructing the full action on `ClassGroup`:
descent from `(Ideal R)⁰` to `ClassGroup` via `ClassGroup.mk0` requires
the well-definedness up to principal-ideal equivalence (which is an
adaptation of `pthSymbolAtIdeal_canonical_class_invariant`'s proof
strategy from `PhiResidueChar.lean`).

Substantive open content: this MonoidHom is the per-`a` action on
integer ideal classes; lifting to a full `ClassGroup → ClassGroup`
endomorphism requires the well-definedness lift. -/

variable {p K}

/-- The σ_a action on `(Ideal (𝓞 K))⁰` lifted from
`cyclotomicGaloisConjugate`. -/
noncomputable def cyclotomicGaloisConjugateNonZeroDivisors
    (a : CyclotomicUnitDelta p) :
    (Ideal (𝓞 K))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I := ⟨Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a I.val,
    by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Furtwaengler.cyclotomicGaloisConjugate_ne_bot a
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩
  map_one' := Subtype.ext (by
    change Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a (1 : Ideal _) =
      (1 : Ideal _)
    rw [Ideal.one_eq_top, Furtwaengler.cyclotomicGaloisConjugate_top])
  map_mul' I J := Subtype.ext (by
    change Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a (I.val * J.val) =
      Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a I.val *
      Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a J.val
    exact Furtwaengler.cyclotomicGaloisConjugate_mul_ideal a I.val J.val)

/-- σ_a-shifted class of an integer ideal. -/
noncomputable def cyclotomicGaloisShiftedClass
    (a : CyclotomicUnitDelta p) :
    (Ideal (𝓞 K))⁰ →* ClassGroup (𝓞 K) :=
  ClassGroup.mk0.comp (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a)

/-- **Class invariance of `cyclotomicGaloisShiftedClass`**: if two
integer ideals are in the same class, their σ_a-shifted classes are
also equal. -/
theorem cyclotomicGaloisShiftedClass_class_invariant
    (a : CyclotomicUnitDelta p) {I₁ I₂ : (Ideal (𝓞 K))⁰}
    (h_class : ClassGroup.mk0 I₁ = ClassGroup.mk0 I₂) :
    cyclotomicGaloisShiftedClass (p := p) (K := K) a I₁ =
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I₂ := by
  -- Extract x, y ≠ 0 with span(x) · I₁ = span(y) · I₂.
  obtain ⟨x, y, hx_ne, hy_ne, h_eq⟩ :=
    ClassGroup.mk0_eq_mk0_iff.mp h_class
  -- Apply σ_a to both sides via Ideal.map.
  unfold cyclotomicGaloisShiftedClass cyclotomicGaloisConjugateNonZeroDivisors
  -- Need: mk0 (σ_a I₁) = mk0 (σ_a I₂).
  -- Use mk0_eq_mk0_iff with σ_a x, σ_a y.
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  refine ⟨cyclotomicRingOfIntegersEquiv (p := p) K a x,
    cyclotomicRingOfIntegersEquiv (p := p) K a y, ?_, ?_, ?_⟩
  · -- σ_a x ≠ 0
    intro h
    apply hx_ne
    have := (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (a₁ := x) (a₂ := 0) (by rw [h, map_zero])
    exact this
  · -- σ_a y ≠ 0
    intro h
    apply hy_ne
    have := (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (a₁ := y) (a₂ := 0) (by rw [h, map_zero])
    exact this
  · -- span(σ_a x) · σ_a I₁ = span(σ_a y) · σ_a I₂
    change Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a x} : Set _) *
        Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a I₁.val =
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a y} : Set _) *
        Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a I₂.val
    -- Use Ideal.map_span and cyclotomicGaloisConjugate_mul_ideal.
    have hx_span : Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a x} : Set _) =
        Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a
          (Ideal.span ({x} : Set (𝓞 K))) := by
      unfold Furtwaengler.cyclotomicGaloisConjugate
      rw [Ideal.map_span, Set.image_singleton]
    have hy_span : Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a y} : Set _) =
        Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a
          (Ideal.span ({y} : Set (𝓞 K))) := by
      unfold Furtwaengler.cyclotomicGaloisConjugate
      rw [Ideal.map_span, Set.image_singleton]
    rw [hx_span, hy_span,
        ← Furtwaengler.cyclotomicGaloisConjugate_mul_ideal,
        ← Furtwaengler.cyclotomicGaloisConjugate_mul_ideal,
        h_eq]

/-- **σ_a action on `ClassGroup (𝓞 K)`** descended via integer-ideal
representatives (using `ClassGroup.mk0_surjective` + the
`cyclotomicGaloisShiftedClass_class_invariant` well-definedness).

For `c ∈ ClassGroup`, takes any integer representative `I` (via
`Function.surjInv ClassGroup.mk0_surjective`) and returns
`cyclotomicGaloisShiftedClass a I`. By class invariance, the result is
independent of the choice of integer representative — but the
implementation uses `Function.surjInv`, which makes a `Classical.choice`. -/
noncomputable def cyclotomicGalActionOnClassGroup
    (a : CyclotomicUnitDelta p) (c : ClassGroup (𝓞 K)) :
    ClassGroup (𝓞 K) :=
  cyclotomicGaloisShiftedClass (p := p) (K := K) a
    (Function.surjInv ClassGroup.mk0_surjective c)

/-- The action evaluated on an integer representative agrees with
`cyclotomicGaloisShiftedClass`. -/
theorem cyclotomicGalActionOnClassGroup_mk0
    (a : CyclotomicUnitDelta p) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicGalActionOnClassGroup (p := p) (K := K) a (ClassGroup.mk0 I) =
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I := by
  unfold cyclotomicGalActionOnClassGroup
  apply cyclotomicGaloisShiftedClass_class_invariant a
  -- The chosen rep via surjInv satisfies mk0 (surjInv c) = c.
  exact Function.surjInv_eq ClassGroup.mk0_surjective (ClassGroup.mk0 I)

/-- **Multiplicativity** of the action. -/
theorem cyclotomicGalActionOnClassGroup_mul
    (a : CyclotomicUnitDelta p) (c₁ c₂ : ClassGroup (𝓞 K)) :
    cyclotomicGalActionOnClassGroup (p := p) (K := K) a (c₁ * c₂) =
      cyclotomicGalActionOnClassGroup (p := p) (K := K) a c₁ *
      cyclotomicGalActionOnClassGroup (p := p) (K := K) a c₂ := by
  obtain ⟨I₁, hI₁⟩ := ClassGroup.mk0_surjective c₁
  obtain ⟨I₂, hI₂⟩ := ClassGroup.mk0_surjective c₂
  rw [← hI₁, ← hI₂, ← map_mul (ClassGroup.mk0 (R := 𝓞 K)),
      cyclotomicGalActionOnClassGroup_mk0,
      cyclotomicGalActionOnClassGroup_mk0,
      cyclotomicGalActionOnClassGroup_mk0,
      ← map_mul (cyclotomicGaloisShiftedClass (p := p) (K := K) a)]

/-- **Identity-preservation** of the action. -/
theorem cyclotomicGalActionOnClassGroup_one
    (a : CyclotomicUnitDelta p) :
    cyclotomicGalActionOnClassGroup (p := p) (K := K) a (1 : ClassGroup (𝓞 K)) =
      1 := by
  conv_lhs => rw [show (1 : ClassGroup (𝓞 K)) = ClassGroup.mk0 (1 : (Ideal (𝓞 K))⁰) by
    rw [MonoidHom.map_one]]
  rw [cyclotomicGalActionOnClassGroup_mk0, map_one]

/-- **The σ_a action on `ClassGroup` as a `MonoidHom`**. -/
noncomputable def cyclotomicGalActionMonoidHom
    (a : CyclotomicUnitDelta p) :
    ClassGroup (𝓞 K) →* ClassGroup (𝓞 K) where
  toFun := cyclotomicGalActionOnClassGroup (p := p) (K := K) a
  map_one' := cyclotomicGalActionOnClassGroup_one a
  map_mul' := cyclotomicGalActionOnClassGroup_mul a

/-- **Descent to ClassGroupModP**: the σ_a action on `ClassGroup`
preserves the `(powMonoidHom p).range` subgroup, so it descends to a
MonoidHom on `ClassGroupModP K p`. -/
noncomputable def cyclotomicGalActionMonoidHomModP
    (a : CyclotomicUnitDelta p) :
    ClassGroupModP K p →* ClassGroupModP K p :=
  QuotientGroup.map _ _ (cyclotomicGalActionMonoidHom (p := p) (K := K) a) <| by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    -- Want: cyclotomicGalActionMonoidHom a (y^p) ∈ (powMonoidHom p).range.
    refine ⟨cyclotomicGalActionMonoidHom (p := p) (K := K) a y, ?_⟩
    change (cyclotomicGalActionMonoidHom (p := p) (K := K) a y) ^ p =
      cyclotomicGalActionMonoidHom (p := p) (K := K) a (y ^ p)
    rw [map_pow]

/-- **The σ_a action as a `ZMod p`-linear endomorphism** on
`Additive (ClassGroupModP K p)`. Composes
`cyclotomicGalActionMonoidHomModP a` (multiplicative) with
`MonoidHom.toAdditive` and `AddMonoidHom.toZModLinearMap`. -/
noncomputable def cyclotomicGalActionLinearModP
    (a : CyclotomicUnitDelta p) :
    Module.End (ZMod p) (Additive (ClassGroupModP K p)) :=
  AddMonoidHom.toZModLinearMap p (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a).toAdditive

/-! ### Multiplicativity of the action in `a` -/

/-- The action with `a = 1` is the identity on `ClassGroup`. -/
theorem cyclotomicGalActionMonoidHom_one_apply (c : ClassGroup (𝓞 K)) :
    cyclotomicGalActionMonoidHom (p := p) (K := K) 1 c = c := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  rw [← hI]
  change cyclotomicGalActionOnClassGroup (p := p) (K := K) 1 (ClassGroup.mk0 I) =
    ClassGroup.mk0 I
  rw [cyclotomicGalActionOnClassGroup_mk0]
  change ClassGroup.mk0 ⟨Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) 1 I.val,
    _⟩ = ClassGroup.mk0 I
  congr 1
  apply Subtype.ext
  change Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) 1 I.val = I.val
  exact Furtwaengler.cyclotomicGaloisConjugate_one I.val

/-- The action is multiplicative in `a`: `σ_{a*b} = σ_a ∘ σ_b`. -/
theorem cyclotomicGalActionMonoidHom_mul_apply
    (a b : CyclotomicUnitDelta p) (c : ClassGroup (𝓞 K)) :
    cyclotomicGalActionMonoidHom (p := p) (K := K) (a * b) c =
      cyclotomicGalActionMonoidHom (p := p) (K := K) a
        (cyclotomicGalActionMonoidHom (p := p) (K := K) b c) := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  rw [← hI]
  -- Reduce both sides to integer-ideal form via `_mk0`.
  change cyclotomicGalActionOnClassGroup (p := p) (K := K) (a * b) (ClassGroup.mk0 I) =
    cyclotomicGalActionOnClassGroup (p := p) (K := K) a
      (cyclotomicGalActionOnClassGroup (p := p) (K := K) b (ClassGroup.mk0 I))
  rw [cyclotomicGalActionOnClassGroup_mk0 (a := a * b),
      cyclotomicGalActionOnClassGroup_mk0 (a := b)]
  -- RHS: cyclotomicGalActionOnClassGroup a (cyclotomicGaloisShiftedClass b I)
  -- = cyclotomicGalActionOnClassGroup a (mk0 (σ_b I))
  change cyclotomicGaloisShiftedClass (p := p) (K := K) (a * b) I =
    cyclotomicGalActionOnClassGroup (p := p) (K := K) a
      (ClassGroup.mk0 (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) b I))
  rw [cyclotomicGalActionOnClassGroup_mk0 (a := a)]
  -- LHS: shiftedClass (a*b) I = mk0 (σ_{a*b} I)
  -- RHS: shiftedClass a (σ_b I) = mk0 (σ_a (σ_b I))
  -- Use map equality at the underlying ideal level via congrArg.
  change ClassGroup.mk0
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) (a * b) I) =
    ClassGroup.mk0 (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) b I))
  congr 1
  apply Subtype.ext
  change Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) (a * b) I.val =
    Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a
      (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b I.val)
  exact Furtwaengler.cyclotomicGaloisConjugate_mul a b I.val

/-- The σ_a action on `ClassGroupModP` is the identity at `a = 1`. -/
theorem cyclotomicGalActionMonoidHomModP_one_apply (c : ClassGroupModP K p) :
    cyclotomicGalActionMonoidHomModP (p := p) (K := K) 1 c = c := by
  refine QuotientGroup.induction_on c ?_
  intro x
  change QuotientGroup.mk (cyclotomicGalActionMonoidHom (p := p) (K := K) 1 x) =
    QuotientGroup.mk x
  rw [cyclotomicGalActionMonoidHom_one_apply]

/-- The σ_a action on `ClassGroupModP` is multiplicative in `a`. -/
theorem cyclotomicGalActionMonoidHomModP_mul_apply
    (a b : CyclotomicUnitDelta p) (c : ClassGroupModP K p) :
    cyclotomicGalActionMonoidHomModP (p := p) (K := K) (a * b) c =
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (cyclotomicGalActionMonoidHomModP (p := p) (K := K) b c) := by
  refine QuotientGroup.induction_on c ?_
  intro x
  change QuotientGroup.mk (cyclotomicGalActionMonoidHom (p := p) (K := K) (a * b) x) =
    cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
      (QuotientGroup.mk (cyclotomicGalActionMonoidHom (p := p) (K := K) b x))
  change QuotientGroup.mk (cyclotomicGalActionMonoidHom (p := p) (K := K) (a * b) x) =
    QuotientGroup.mk (cyclotomicGalActionMonoidHom (p := p) (K := K) a
      (cyclotomicGalActionMonoidHom (p := p) (K := K) b x))
  rw [cyclotomicGalActionMonoidHom_mul_apply]

/-- The σ_a action on the full class group as a multiplicative equivalence. -/
noncomputable def cyclotomicGalActionMulEquiv
    (a : CyclotomicUnitDelta p) :
    ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) where
  toFun := cyclotomicGalActionMonoidHom (p := p) (K := K) a
  invFun := cyclotomicGalActionMonoidHom (p := p) (K := K) a⁻¹
  left_inv x := by
    rw [← cyclotomicGalActionMonoidHom_mul_apply (p := p) (K := K) a⁻¹ a x]
    simpa using cyclotomicGalActionMonoidHom_one_apply (p := p) (K := K) x
  right_inv x := by
    rw [← cyclotomicGalActionMonoidHom_mul_apply (p := p) (K := K) a a⁻¹ x]
    simpa using cyclotomicGalActionMonoidHom_one_apply (p := p) (K := K) x
  map_mul' x y :=
    map_mul (cyclotomicGalActionMonoidHom (p := p) (K := K) a) x y

@[simp]
theorem cyclotomicGalActionMulEquiv_apply
    (a : CyclotomicUnitDelta p) (x : ClassGroup (𝓞 K)) :
    cyclotomicGalActionMulEquiv (p := p) (K := K) a x =
      cyclotomicGalActionMonoidHom (p := p) (K := K) a x :=
  rfl

/-- The σ-action on the full class group as a monoid hom into multiplicative
equivalences. -/
noncomputable def cyclotomicGalActionMulEquivHom :
    CyclotomicUnitDelta p →* ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) where
  toFun := cyclotomicGalActionMulEquiv (p := p) (K := K)
  map_one' := by
    ext x
    exact cyclotomicGalActionMonoidHom_one_apply (p := p) (K := K) x
  map_mul' a b := by
    ext x
    exact cyclotomicGalActionMonoidHom_mul_apply (p := p) (K := K) a b x

/-- The σ-action on `Additive (ClassGroup (𝓞 K))` as additive equivalences. -/
noncomputable def cyclotomicGalActionAddEquivHom :
    CyclotomicUnitDelta p →*
      Multiplicative (Additive (ClassGroup (𝓞 K)) ≃+ Additive (ClassGroup (𝓞 K))) where
  toFun a := Multiplicative.ofAdd (cyclotomicGalActionMulEquiv (p := p) (K := K) a).toAdditive
  map_one' := by
    ext x
    exact Additive.ext <| cyclotomicGalActionMonoidHom_one_apply (p := p) (K := K) x.toMul
  map_mul' a b := by
    ext x
    exact Additive.ext <| cyclotomicGalActionMonoidHom_mul_apply (p := p) (K := K) a b x.toMul

@[simp]
theorem cyclotomicGalActionAddEquivHom_apply_toMul
    (a : CyclotomicUnitDelta p) (x : Additive (ClassGroup (𝓞 K))) :
    (Multiplicative.toAdd (cyclotomicGalActionAddEquivHom (p := p) (K := K) a) x).toMul =
      cyclotomicGalActionMonoidHom (p := p) (K := K) a x.toMul :=
  rfl

/-- The σ_a action on `ClassGroupModP` as a multiplicative equivalence. -/
noncomputable def cyclotomicGalActionMulEquivModP
    (a : CyclotomicUnitDelta p) :
    ClassGroupModP K p ≃* ClassGroupModP K p where
  toFun := cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
  invFun := cyclotomicGalActionMonoidHomModP (p := p) (K := K) a⁻¹
  left_inv x := by
    rw [← cyclotomicGalActionMonoidHomModP_mul_apply (p := p) (K := K) a⁻¹ a x]
    simpa using cyclotomicGalActionMonoidHomModP_one_apply (p := p) (K := K) x
  right_inv x := by
    rw [← cyclotomicGalActionMonoidHomModP_mul_apply (p := p) (K := K) a a⁻¹ x]
    simpa using cyclotomicGalActionMonoidHomModP_one_apply (p := p) (K := K) x
  map_mul' x y :=
    map_mul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a) x y

@[simp]
theorem cyclotomicGalActionMulEquivModP_apply
    (a : CyclotomicUnitDelta p) (x : ClassGroupModP K p) :
    cyclotomicGalActionMulEquivModP (p := p) (K := K) a x =
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) a x :=
  rfl

/-- The σ-action on `ClassGroupModP` as a monoid hom into multiplicative
equivalences. -/
noncomputable def cyclotomicGalActionMulEquivModPHom :
    CyclotomicUnitDelta p →* ClassGroupModP K p ≃* ClassGroupModP K p where
  toFun := cyclotomicGalActionMulEquivModP (p := p) (K := K)
  map_one' := by
    ext x
    exact cyclotomicGalActionMonoidHomModP_one_apply (p := p) (K := K) x
  map_mul' a b := by
    ext x
    exact cyclotomicGalActionMonoidHomModP_mul_apply (p := p) (K := K) a b x

/-- The σ-action on `Additive (ClassGroupModP K p)` as linear equivalences.

This is the equivalence-valued version of `cyclotomicGalActionInstance`, used
by the character-projection API. -/
noncomputable def cyclotomicGalActionLinearEquivModP :
    CyclotomicUnitDelta p →*
      Additive (ClassGroupModP K p) ≃ₗ[ZMod p] Additive (ClassGroupModP K p) :=
  Reflection.SingularKummer.SingularLinearAction.mulActionToAdditiveLinearAction
    (p := p) (cyclotomicGalActionMulEquivModPHom (p := p) (K := K))

@[simp]
theorem cyclotomicGalActionLinearEquivModP_apply
    (a : CyclotomicUnitDelta p) (v : Additive (ClassGroupModP K p)) :
    cyclotomicGalActionLinearEquivModP (p := p) (K := K) a v =
      cyclotomicGalActionLinearModP (p := p) (K := K) a v := by
  apply Additive.ext
  rfl

/-- **Atom B's `CyclotomicGalAction` instance**: bundles
`cyclotomicGalActionLinearModP` per `a ∈ (ZMod p)ˣ` as a MonoidHom
into `Module.End`. -/
noncomputable def cyclotomicGalActionInstance :
    CyclotomicGalAction p K where
  toFun := cyclotomicGalActionLinearModP (p := p) (K := K)
  map_one' := by
    apply LinearMap.ext
    intro v
    change cyclotomicGalActionMonoidHomModP (p := p) (K := K) 1 v.toMul = v.toMul
    exact cyclotomicGalActionMonoidHomModP_one_apply v.toMul
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change cyclotomicGalActionMonoidHomModP (p := p) (K := K) (a * b) v.toMul =
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (cyclotomicGalActionMonoidHomModP (p := p) (K := K) b v.toMul)
    exact cyclotomicGalActionMonoidHomModP_mul_apply a b v.toMul

end BernoulliRegular

end

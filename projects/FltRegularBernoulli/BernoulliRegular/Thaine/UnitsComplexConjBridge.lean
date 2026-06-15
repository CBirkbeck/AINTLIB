import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace

/-!
# T-EIG-B0: Bridge between `unitsComplexConj` and `cyclotomicSigmaOfUnit (-1)`

The mathlib `IsCMField.unitsComplexConj K` is the units-level complex
conjugation, while `cyclotomicSigmaOfUnit p K (-1)` is the Galois-group
element corresponding to `-1 ∈ (ZMod p)ˣ`. The project already has:

* `cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal` (in
  `UnitQuotient/FreeLatticeComparison/ConjugationTrace.lean`):
  `cyclotomicSigmaOfUnit p K (-1) = cyclotomicComplexConjGal p K hp_two`.

* `cyclotomicUnitsComplexConj_apply_coe` (same file): the val of
  `cyclotomicUnitsComplexConj K = IsCMField.unitsComplexConj K` equals
  the action of `cyclotomicRingOfIntegersComplexConj K = IsCMField.ringOfIntegersComplexConj K`.

The remaining bridge — that `cyclotomicComplexConjGal`'s smul-action on
`𝓞 K` matches `IsCMField.ringOfIntegersComplexConj K` — is the content
of this file.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **Bridge: `IsCMField.unitsComplexConj` val equals `cyclotomicSigmaOfUnit (-1)` smul**.

The complex conjugation on `(𝓞 K)ˣ` (mathlib's `IsCMField.unitsComplexConj K`)
extracts to the same `𝓞 K`-value as the Galois-action of
`cyclotomicSigmaOfUnit p K (-1)`. -/
theorem unitsComplexConj_val_eq_cyclotomicSigmaOfUnit_neg_one_smul
    (hp_two : 2 < p) (x : (𝓞 K)ˣ) :
    ((NumberField.IsCMField.unitsComplexConj K x : (𝓞 K)ˣ) : 𝓞 K) =
    cyclotomicSigmaOfUnit (p := p) K (-1) • ((x : (𝓞 K)ˣ) : 𝓞 K) := by
  -- Step 1: rewrite the LHS via `cyclotomicUnitsComplexConj_apply_coe`.
  rw [show (NumberField.IsCMField.unitsComplexConj K x : (𝓞 K)ˣ) =
        cyclotomicUnitsComplexConj (p := p) K hp_two x from rfl]
  rw [cyclotomicUnitsComplexConj_apply_coe (p := p) K hp_two x]
  -- Goal: cyclotomicRingOfIntegersComplexConj p K hp_two (x : 𝓞 K) =
  --       cyclotomicSigmaOfUnit p K (-1) • (x : 𝓞 K).
  -- Step 2: rewrite `cyclotomicSigmaOfUnit p K (-1)` via the existing equality.
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_two]
  -- Goal: cyclotomicRingOfIntegersComplexConj p K hp_two (x : 𝓞 K) =
  --       cyclotomicComplexConjGal p K hp_two • (x : 𝓞 K).
  -- Step 3: Both sides equal `complexConj K (x : K)` at the K-level.
  -- For an AlgEquiv σ ∈ Gal(K/ℚ), σ • y for y ∈ 𝓞 K satisfies (σ • y : K) = σ (y : K).
  apply RingOfIntegers.ext
  -- Goal: (cyclotomicRingOfIntegersComplexConj p K hp_two (x : 𝓞 K) : K) =
  --       (cyclotomicComplexConjGal p K hp_two • (x : 𝓞 K) : K)
  rw [show (cyclotomicRingOfIntegersComplexConj (p := p) K hp_two
        ((x : (𝓞 K)ˣ) : 𝓞 K) : K) =
      NumberField.IsCMField.complexConj K ((x : (𝓞 K)ˣ) : K) from rfl]
  -- The Galois-group smul on 𝓞 K extracts via `(σ • y : K) = σ (y : K)`.
  -- Use `IsScalarTower` / the existing project pattern.
  show NumberField.IsCMField.complexConj K _ =
      (cyclotomicComplexConjGal (p := p) K hp_two • _ : 𝓞 K)
  -- The smul on 𝓞 K via Gal(K/ℚ) is by AlgEquiv applied; use definitional unfolding.
  rfl

end BernoulliRegular

end

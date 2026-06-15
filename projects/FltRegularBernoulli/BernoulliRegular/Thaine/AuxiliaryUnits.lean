import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# T-THAINE-1: Cyclotomic units in auxiliary cyclotomic extensions

For Thaine's annihilator theorem (`[Wash97 2nd ed §15]`,
`[Rubin00 Ch. 3-4]`), one introduces auxiliary primes ℓ ≡ 1 (mod p^n)
and works with cyclotomic units in the extension `K(ζ_ℓ)`. The Thaine
construction takes the cyclotomic unit `(1 - ζ_ℓ) ∈ 𝓞_{K(ℓ)}` and
descends via `norm_{K(ℓ)/K}` (or the `1 - σ_τ` Kolyvagin "derivative" in
later tickets) to obtain Stickelberger-style annihilator data on `K`.

This file ships the foundational definitions for the auxiliary
cyclotomic units. The Thaine setting requires `ℓ ≠ p` (so the auxiliary
extension is unramified at the primes of interest); this is captured at
the call site.

* **`auxiliaryZetaToInteger`** — the canonical primitive `ℓ`-th root of
  unity, packaged as an element of `𝓞 M` via `IsPrimitiveRoot.toInteger`.
* **`auxiliaryCyclotomicUnitOneMinus`** — `(1 - ζ_ℓ) ∈ 𝓞 M`, the
  conventional cyclotomic-unit form.
* **`auxiliaryCyclotomicUnitMinusOne`** — `(ζ_ℓ - 1) ∈ 𝓞 M`.

Downstream (`T-THAINE-2/3/4`) builds on this API.

## References

* [Wash97 2nd ed] §15.1 (auxiliary cyclotomic-unit construction).
* [Rubin00] *Euler Systems*, §3 (cyclotomic Euler system).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace Thaine

/-- **`auxiliaryZetaToInteger`**: the canonical primitive `ℓ`-th root of
unity in `M = K(ζ_ℓ)`, packaged as an element of `𝓞 M`. -/
noncomputable def auxiliaryZetaToInteger
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [IsCyclotomicExtension {ℓ} K M] : 𝓞 M :=
  haveI : NeZero ℓ := ⟨Fact.out (p := ℓ.Prime) |>.ne_zero⟩
  (IsCyclotomicExtension.zeta_spec ℓ K M).toInteger

/-- The auxiliary `ζ_ℓ` (as `𝓞 M`) is a primitive `ℓ`-th root of unity. -/
theorem auxiliaryZetaToInteger_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [IsCyclotomicExtension {ℓ} K M] :
    IsPrimitiveRoot (auxiliaryZetaToInteger ℓ K M) ℓ := by
  haveI : NeZero ℓ := ⟨Fact.out (p := ℓ.Prime) |>.ne_zero⟩
  exact (IsCyclotomicExtension.zeta_spec ℓ K M).toInteger_isPrimitiveRoot

/-- **`auxiliaryCyclotomicUnitOneMinus`**: `1 - ζ_ℓ ∈ 𝓞 M`. -/
noncomputable def auxiliaryCyclotomicUnitOneMinus
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [IsCyclotomicExtension {ℓ} K M] : 𝓞 M :=
  1 - auxiliaryZetaToInteger ℓ K M

/-- **`auxiliaryCyclotomicUnitMinusOne`**: `ζ_ℓ - 1 ∈ 𝓞 M`. -/
noncomputable def auxiliaryCyclotomicUnitMinusOne
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [IsCyclotomicExtension {ℓ} K M] : 𝓞 M :=
  auxiliaryZetaToInteger ℓ K M - 1

/-- The two forms differ by a sign. -/
theorem auxiliaryCyclotomicUnitOneMinus_eq_neg
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [IsCyclotomicExtension {ℓ} K M] :
    auxiliaryCyclotomicUnitOneMinus ℓ K M =
      -(auxiliaryCyclotomicUnitMinusOne ℓ K M) := by
  unfold auxiliaryCyclotomicUnitOneMinus auxiliaryCyclotomicUnitMinusOne
  ring

end Thaine

end BernoulliRegular

end

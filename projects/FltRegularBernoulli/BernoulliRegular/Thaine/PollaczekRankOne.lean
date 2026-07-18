module

public import BernoulliRegular.Thaine.RankOneComponent
public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
public import BernoulliRegular.Reflection.SubstantiveAtoms

/-!
# T-Q1-RANK-ONE specialisation: Pollaczek-generator equivalence

Per the 2026-05-07 reviewer followup (patch 1 second half), this file
ships the Pollaczek-generator specialisation of the rank-one atomic
lemma:

> `(∀ α : (𝓞 K)ˣ, pollaczekUnitPlus p K i ≠ α^p) ↔ e_i(E⁺/C_S)[p] = 0`.

The substantive eigenspace decomposition (`e_i (E⁺ ⊗ ℤ_p) ≃ ℤ_p` via
the Dirichlet unit theorem at character `ω^i`, plus the identification
of `pollaczekUnitPlus p K i` as a generator of `e_i (C_S ⊗ ℤ_p)`) is
left as parametric data; the rank-one atomic lemma then provides the
equivalence.

## Parametric data

The specialisation theorem takes:

* `Λ` : a PID (intended `ℤ_p`).
* `pΛ : Λ` : a prime element.
* `E : Type*` with `[AddCommGroup E] [Module Λ E]` : a free rank-one
  Λ-module (intended: `e_i (E⁺ ⊗ Λ)`).
* `φ : E ≃ₗ[Λ] Λ` : the rank-one identification.
* `c : E` : the Pollaczek-unit image in `E` (intended: image of
  `pollaczekUnitPlus p K i` under tensor-with-Λ + e_i-projection).
* `hc : c ≠ 0` : non-degeneracy.
* `linkage` : the bridge predicate
  `(∀ α, pollaczekUnitPlus ≠ α^p) ↔ ¬ ∃ y : E, c = pΛ • y`.

## Conclusion

By `rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible`,
the K-side certificate is equivalent to the eigenspace torsion condition
`(E ⧸ Λ·c)[pΛ] = 0`, which represents `e_i(E⁺/C_S)[p] = 0`.

This is patch 1 second half of the reviewer's recommended attack. The
substantive eigenspace machinery (constructing the parametric data from
the multiplicative unit module of `K⁺`) is the next significant
infrastructure piece.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace Thaine

/-- **Pollaczek-generator specialisation of the rank-one atomic lemma**.

Given the parametric eigenspace data (the rank-one Λ-module `E`, the
linear iso `φ : E ≃ₗ[Λ] Λ`, the nonzero generator `c : E`, and the
linkage predicate identifying the K-side certificate with `c ∉ pΛ • E`),
the K-side certificate is equivalent to the torsion-vanishing condition
on the quotient `E ⧸ Λ·c`.

For the FLT37 application: `Λ = ℤ_{37}`, `pΛ = 37`, `E = e_{32}(E⁺ ⊗ ℤ_{37})`,
`c = pollaczek's image`, and the linkage comes from the eigenspace
decomposition machinery (named-theorem boundary).

This combines:
* `rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible`
  (T-Q1-RANK-ONE atomic, module form).
* The parametric eigenspace identifications (named-theorem boundary).
* `pollaczekUnitPlus p K i` from `FLT37/.../Symmetrisation.lean`. -/
theorem pollaczek_rankOne_specialisation
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ]
    {pΛ : Λ} (hp_prime : Prime pΛ)
    (p i : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]
    {E : Type*} [AddCommGroup E] [Module Λ E]
    (φ : E ≃ₗ[Λ] Λ) {c : E} (hc : c ≠ 0)
    (linkage :
      (∀ α : (𝓞 K)ˣ,
          ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
            ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) ↔
      ¬ ∃ y : E, c = pΛ • y) :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) ↔
    ∀ x : E ⧸ Submodule.span Λ ({c} : Set E), pΛ • x = 0 → x = 0 := by
  rw [linkage]
  exact rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible
    hp_prime φ hc

/-- **Construct `pollaczekUnitComponent` via the rank-one specialisation**.

Bridge from the rank-one specialisation to the existing FLT37 bridge
architecture (`FLT37UnitClassBridgeRefined.pollaczekUnitComponent`).

Given:
* The eigenspace identification `id : ClassGroupComponentIdentification p K`.
* The rank-one identification `(Λ, pΛ, E, φ, c, linkage)` for character `i`.
* A linkage between the eigenspace torsion vanishing on `E ⧸ Λ·c` and
  `id.componentNontrivial i` being false (the substantive eigenspace-to-
  class-group connection, parametric here).

Produces the K-side certificate ⟹ `¬ id.componentNontrivial i` implication
needed to fill `FLT37UnitClassBridgeRefined.pollaczekUnitComponent`.

The substantive content is `eigenspaceTrivial`, which connects the
abstract eigenspace torsion vanishing to the project's
`ClassGroupComponentIdentification.componentNontrivial` predicate. This
is parametric here; substantive proof requires the eigenspace
decomposition machinery (Dirichlet at character + idempotent action). -/
theorem pollaczekUnitComponent_of_rankOne
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]
    (id : ClassGroupComponentIdentification p K) (i : ℕ)
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ]
    {pΛ : Λ} (hp_prime : Prime pΛ)
    {E : Type*} [AddCommGroup E] [Module Λ E]
    (φ : E ≃ₗ[Λ] Λ) {c : E} (hc : c ≠ 0)
    (linkage :
      (∀ α : (𝓞 K)ˣ,
          ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
            ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) ↔
      ¬ ∃ y : E, c = pΛ • y)
    (eigenspaceTrivial :
      (∀ x : E ⧸ Submodule.span Λ ({c} : Set E), pΛ • x = 0 → x = 0) →
      ¬ id.componentNontrivial i) :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
    ¬ id.componentNontrivial i := fun h_cert ↦
  eigenspaceTrivial <|
    (pollaczek_rankOne_specialisation hp_prime p i K φ hc linkage).mp h_cert

end Thaine

end BernoulliRegular

end

import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.UnitClassBridge
import BernoulliRegular.Thaine.PollaczekRankOne

/-!
# T-THAINE-6: FLT37 specialization — parametric Thaine + Reflection bundle

This file packages the two parametric inputs needed for the
content-bearing `cor8_19Bridge_of_componentTrivialities` (T-PIVOT-1-REFINE)
into named structures: `ThaineSingleCharDischarge` (the Pollaczek
side, ω^i) and `ReflectionOtherDischarge` (the Spiegelungssatz side,
χ ≠ ω^i). Together they provide a real `Cor8_19Bridge` parametric on
the eigenspace identification.

## Conceptual chain

```
ThaineSingleCharDischarge p K id i     -- Pollaczek/Thaine at ω^i
ReflectionOtherDischarge p K id i      -- Spiegelungssatz at j ≠ ω^i
        |
        v
cor8_19Bridge_of_componentTrivialities  -- T-PIVOT-1-REFINE
        |
        v
Cor8_19Bridge p K i
```

The substantive content (Thaine's annihilator theorem at single
character) lives inside `ThaineSingleCharDischarge`'s field
`thaine_at_i`. The substantive Spiegelungssatz application lives inside
`ReflectionOtherDischarge`'s field `reflection_other`. Both are
parametric: they consume an instance of `ClassGroupComponentIdentification`
and produce per-index discharges.

For `p = 37`, `i = 32`: instantiating these two parametric structures
gives the Cor 8.19 bridge for FLT37. The actual content of `thaine_at_i`
is what `T-THAINE-3/4/5` build up to (Kolyvagin derivative classes,
Thaine annihilator descent, single-character Kučera corollary).

## References

* T-PIVOT-1-REFINE (`UnitClassBridge.lean`,
  `cor8_19Bridge_of_componentTrivialities`).
* `BernoulliRegular.Reflection.SubstantiveAtoms` —
  `ClassGroupComponentIdentification`.
* [Wash97 2nd ed §15] (Thaine/Kolyvagin/Rubin), [Rubin00] *Euler Systems*,
  Kučera (single-character corollary).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **`ThaineSingleCharDischarge p K id i`**: the parametric form of
"Thaine's annihilator at single character ω^i". Given the eigenspace
identification `id`, the Pollaczek certificate (i.e., `pollaczekUnitPlus`
not a `p`-th power) forces the i-th eigencomponent to be trivial.

Filling this is the substantive content of `T-THAINE-3/4/5`:
the Kolyvagin derivative class construction (Wash97 §15.2) reduces
`pollaczekUnitPlus ∉ (E)^p` to `id.componentNontrivial i = False`. -/
structure ThaineSingleCharDischarge
    (id : ClassGroupComponentIdentification p K) (i : ℕ) where
  thaine_at_i :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
      ¬ id.componentNontrivial i

/-- **`ReflectionOtherDischarge p K id i`**: the parametric form of
"Spiegelungssatz + Herbrand–Ribet at non-irregular indices". For every
even reflection-range index `j ≠ i`, the j-th eigencomponent is trivial.

Filling this uses the existing project Reflection package + the
Herbrand–Ribet identification of `Cl(K)⁻(ω^k)` non-triviality with
`p ∣ B_{p−k}`. For `p = 37`, only the reflected irregular eigenspace
can be non-trivial; all others vanish via Spiegelungssatz. -/
structure ReflectionOtherDischarge
    (id : ClassGroupComponentIdentification p K) (i : ℕ) where
  reflection_other :
    ∀ j : ℕ, IsReflectionComponentIndex p j → Even j → j ≠ i →
      ¬ id.componentNontrivial j

/-- **`cor8_19Bridge_of_thaineAndReflection`** — assemble Thaine
single-character + Reflection-other into a real `Cor8_19Bridge` via the
content-bearing constructor `cor8_19Bridge_of_componentTrivialities`. -/
def cor8_19Bridge_of_thaineAndReflection {i : ℕ}
    (id : ClassGroupComponentIdentification p K)
    (thaine : ThaineSingleCharDischarge p K id i)
    (reflection : ReflectionOtherDischarge p K id i) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_componentTrivialities (p := p) (K := K) (i := i) id
    thaine.thaine_at_i reflection.reflection_other

/-- Build the single-character Thaine discharge from the rank-one Pollaczek
specialisation plus the remaining eigenspace-to-class-group triviality bridge.

This is only an adapter: the `eigenspaceTrivial` argument is the substantive
Kučera/Thaine class-group step, so this theorem does not hide that source
result behind `ThaineSingleCharDischarge`. -/
def thaineSingleCharDischarge_of_rankOne {i : ℕ}
    (id : ClassGroupComponentIdentification p K)
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
    ThaineSingleCharDischarge p K id i where
  thaine_at_i :=
    Thaine.pollaczekUnitComponent_of_rankOne id i hp_prime φ hc linkage
      eigenspaceTrivial

end BernoulliRegular

end

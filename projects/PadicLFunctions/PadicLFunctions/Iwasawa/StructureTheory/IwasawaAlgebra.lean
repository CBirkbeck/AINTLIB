import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.Algebra.Module.PID

/-!
# The Iwasawa algebra `Λ = 𝒪⟦T⟧` and distinguished polynomials  (S13-S1)

The Λ-module structure theory underlying the Iwasawa Main Conjecture (RJW,
arXiv:2309.15692, §13.1, where it is *stated without proof*; the proofs are
Washington, *Introduction to Cyclotomic Fields*, Ch. 13, Thm 13.12 etc.).
This file is the foundational layer **S13-S1**: it fixes the Iwasawa algebra and
re-exposes mathlib's distinguished-polynomial and Weierstrass-preparation API in
the shape the later structure theorem (`StructureTheorem.lean`) needs.

## Main declarations

* `Iwasawa.IwasawaAlgebra 𝒪` (local notation `Λ`): the Iwasawa algebra
  `Λ = 𝒪⟦T⟧`, realised as `PowerSeries 𝒪`.  For the standing case `𝒪 = ℤ_p`
  (`L = ℚ_p`) this is the classical `Λ ≅ ℤ_p⟦T⟧` (RJW TeX 3631).
* `Iwasawa.IsDistinguished`: a polynomial over a local ring is *distinguished* if
  it is monic with all non-leading coefficients in the maximal ideal `𝔪`
  (RJW TeX 3644) — a thin wrapper for `Polynomial.IsDistinguishedAt` at
  `𝔪 = IsLocalRing.maximalIdeal 𝒪`.
* `Iwasawa.exists_unit_mul_distinguished`: **Weierstrass preparation** — a power
  series with nonzero residue factors as `unit · distinguished polynomial`
  (RJW TeX 3644; Washington §13.1), reusing
  `PowerSeries.exists_isWeierstrassFactorization`.

## Reuse

`Mathlib.RingTheory.PowerSeries.*` (the ring `𝒪⟦T⟧`), `Polynomial.IsDistinguishedAt`
(`Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished`), and the Weierstrass
machinery in `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`.
-/

noncomputable section

namespace Iwasawa

open PowerSeries

variable (𝒪 : Type*) [CommRing 𝒪]

/-- The **Iwasawa algebra** `Λ = 𝒪⟦T⟧`, realised as the ring of formal power series
over `𝒪`.  For `𝒪 = ℤ_p` this is the classical `Λ ≅ ℤ_p⟦T⟧` (RJW TeX 3631). -/
abbrev IwasawaAlgebra : Type _ := PowerSeries 𝒪

@[inherit_doc] scoped notation "Λ[" 𝒪 "]" => IwasawaAlgebra 𝒪

local notation "Λ" => IwasawaAlgebra 𝒪

variable [IsLocalRing 𝒪]

/-- A polynomial over a local ring `𝒪` is **distinguished** if it is monic and all
its non-leading coefficients lie in the maximal ideal `𝔪` (RJW TeX 3644).  Thin
wrapper for `Polynomial.IsDistinguishedAt` at `𝔪 = IsLocalRing.maximalIdeal 𝒪`. -/
abbrev IsDistinguished (f : Polynomial 𝒪) : Prop :=
  f.IsDistinguishedAt (IsLocalRing.maximalIdeal 𝒪)

/-- **Weierstrass preparation** (RJW TeX 3644; Washington §13.1): a power series
`g ∈ Λ = 𝒪⟦T⟧` whose reduction mod `𝔪` is nonzero factors as `g = u · f` with `u`
a unit of `Λ` and `f` a distinguished polynomial, where `𝒪` is `𝔪`-adically
complete.  Reuses `PowerSeries.exists_isWeierstrassFactorization`. -/
theorem exists_unit_mul_distinguished
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {g : Λ} (hg : g.map (IsLocalRing.residue 𝒪) ≠ 0) :
    ∃ (u : Λˣ) (f : Polynomial 𝒪), IsDistinguished 𝒪 f ∧ g = u * f := by
  sorry

end Iwasawa

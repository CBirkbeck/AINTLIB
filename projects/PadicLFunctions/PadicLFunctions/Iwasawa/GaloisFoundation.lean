import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The Galois foundation for the Iwasawa Main Conjecture  (RJW §13.2) — ground-up construction

**Status: foundation in progress. This file builds the *real* objects of RJW §13.2 from the ground
up — there are NO abstract type-variable stand-ins and NO structures bundling the content.** It
replaces the retracted §13 "capstone", which assumed `X⁺_∞` etc. as `Type*` variables and bundled the
connecting isomorphisms as hypotheses (and therefore proved nothing about the actual Galois modules).

## The objects to construct (RJW §13.2, verbatim targets)

Write `Fₙ = ℚ(μ_{pⁿ})` and `Fₙ⁺` its maximal real subfield, `F∞ = ⋃ₙ Fₙ`, `F∞⁺ = ⋃ₙ Fₙ⁺`.

* `Mₙ` = the maximal abelian `p`-extension of `Fₙ` unramified outside `pₙ`; `Mₙ⁺` likewise for `Fₙ⁺`.
* `Lₙ` = the maximal *unramified* abelian `p`-extension of `Fₙ`; `Lₙ⁺` likewise.
* `M∞ = ⋃ₙ Mₙ`, `M∞⁺ = ⋃ₙ Mₙ⁺`, `L∞ = ⋃ₙ Lₙ`, `L∞⁺ = ⋃ₙ Lₙ⁺`.
* `X∞  = Gal(M∞/F∞)`,  `X∞⁺ = Gal(M∞⁺/F∞⁺)`,  `Y∞ = Gal(L∞/F∞)`,  `Y∞⁺ = Gal(L∞⁺/F∞⁺)`.
* (Remark 13.7) `Γ = Gal(F∞/F)` acts on `X∞` by `σ · x = σ̃ x σ̃⁻¹` (any lift `σ̃ ∈ Gal(M∞/ℚ)`),
  extending to a `Λ(Γ)`-module structure; identically `Λ(Γ⁺)` acts on `X∞⁺`, `Y∞⁺`.

## What mathlib provides vs. what must be built (honest dependency map)

PROVIDED: cyclotomic fields (`IsCyclotomicExtension`, `CyclotomicField`); `maximalRealSubfield` for CM
fields (`IsCMField`); finite-extension ramification (`IsUnramifiedAt`, `RamificationInertia/*`);
infinite Galois theory (`FieldTheory/Galois/{Infinite,Profinite,KrullTopology}`); `cyclotomicCharacter`.

THE WALL (not in mathlib — this is the genuine foundation work): there is **no** "maximal abelian
`p`-extension of a number field unramified outside a set `S`" as a field. `Mₙ`, `Lₙ` and their Galois
groups `Xₙ = Gal(Mₙ/Fₙ)` must be built as quotients of the absolute Galois group `G_{Fₙ}`:
`Xₙ` is the maximal pro-`p` abelian quotient of `G_{Fₙ}` killed by the inertia subgroups at all primes
`∤ pₙ` — assembled from `IsUnramifiedAt` + the abelianized/pro-`p` quotient of the Krull-topological
`G_{Fₙ}`. Then `X∞ = lim Xₙ` (or `Gal` of the union), with the `Λ(Γ)`-action of Remark 13.7.

This is a substantial, mathlib-PR-scale development. It is built here bottom-up; nothing downstream may
assume `Xₙ`/`X∞` until they are genuinely constructed.

## Bricks 1–2 (this file)

* **Brick 1** — the actual fields `Fₙ = ℚ(μ_{pⁿ})`, the layers of the tower.
* **Brick 2** — the real subfield `Fₙ⁺ = maximalRealSubfield Fₙ` (RJW: the maximal totally real
  subfield, i.e. the fixed field of complex conjugation), the CM structure of `Fₙ` (giving
  `[Fₙ : Fₙ⁺] = 2`), and the finite-level Galois group `Gal(Fₙ/ℚ) ≅ (ℤ/pⁿ)ˣ` (RJW §13.2 / the
  cyclotomic character at finite level). All real objects, no placeholders.
-/

noncomputable section

namespace Iwasawa.GaloisFoundation

variable (p : ℕ) [Fact p.Prime]

/-- `Fₙ = ℚ(μ_{pⁿ})`, the `n`-th layer of the cyclotomic tower (RJW §9, §13.2). -/
abbrev Fcyc (n : ℕ) : Type _ := CyclotomicField (p ^ n) ℚ

/-- `Fₙ` is a cyclotomic extension of `ℚ` for `μ_{pⁿ}` — the defining property of the tower layer. -/
instance instIsCyclotomic (n : ℕ) :
    IsCyclotomicExtension {p ^ n} ℚ (Fcyc p n) :=
  CyclotomicField.isCyclotomicExtension (p ^ n) ℚ

/-- The conductor `pⁿ` is nonzero (so the cyclotomic API for `Fₙ` is available unconditionally). -/
instance instNeZeroPow (n : ℕ) : NeZero (p ^ n) :=
  ⟨pow_ne_zero n (Fact.out (p := p.Prime)).pos.ne'⟩

/-- `Fₙ` is a number field. -/
instance instNumberField (n : ℕ) : NumberField (Fcyc p n) :=
  inferInstanceAs (NumberField (CyclotomicField (p ^ n) ℚ))

open NumberField in
/-- `Fₙ⁺`, the maximal real subfield of `Fₙ = ℚ(μ_{pⁿ})` (RJW §13.2): the fixed field of complex
conjugation, i.e. the maximal totally real subfield. This is the base of the *real* tower `F∞⁺`.
A genuine `Subfield (Fcyc p n)`, defined unconditionally (no CM hypothesis needed to *define* it). -/
def FcycPlus (n : ℕ) : Subfield (Fcyc p n) :=
  maximalRealSubfield (Fcyc p n)

open NumberField in
/-- For odd `p` and `n ≥ 1` we have `2 < pⁿ`. -/
theorem two_lt_pow (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : 2 < p ^ n :=
  calc 2 < 3 := by norm_num
    _ ≤ p := (Fact.out (p := p.Prime)).two_le.lt_of_ne (Ne.symm hp2)
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out (p := p.Prime)).pos hn

open NumberField in
/-- `Fₙ = ℚ(μ_{pⁿ})` is a CM field whenever `2 < pⁿ` (in particular for odd `p`, `n ≥ 1`); this is
where `Fₙ⁺ = maximalRealSubfield Fₙ` becomes a genuine quadratic subextension, `[Fₙ : Fₙ⁺] = 2`. -/
theorem isCMField_Fcyc {n : ℕ} (h : 2 < p ^ n) : IsCMField (Fcyc p n) :=
  IsCyclotomicExtension.Rat.isCMField (Fcyc p n) (S := {p ^ n}) ⟨p ^ n, rfl, h⟩

/-- The finite-level Galois group `Gal(Fₙ/ℚ) ≅ (ℤ/pⁿ)ˣ` (RJW §13.2; the source of `Γ` and of the
cyclotomic character at finite level). A genuine multiplicative equivalence. -/
def galEquiv (n : ℕ) : (Fcyc p n ≃ₐ[ℚ] Fcyc p n) ≃* (ZMod (p ^ n))ˣ :=
  IsCyclotomicExtension.autEquivPow (Fcyc p n)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _))

end Iwasawa.GaloisFoundation

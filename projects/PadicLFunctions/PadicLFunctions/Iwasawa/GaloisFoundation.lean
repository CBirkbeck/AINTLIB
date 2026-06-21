import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Algebraic.Integral

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

/-! ### Brick 3 — the cyclotomic `ℤ_p`-tower `F∞ = ⋃ₙ Fₙ`, nested in one ambient closure

The abstract fields `Fcyc p n = CyclotomicField (pⁿ) ℚ` are pairwise unrelated *types*; the tower
`F∞ = ⋃ Fₙ` needs the `Fₙ` as genuine subfields of one ambient field. We fix `Ω = ℚ̄` and realise
each `Fₙ = ℚ(μ_{pⁿ})` as the `IntermediateField` generated by a primitive `pⁿ`-th root of unity.
Each nested `Fₙ` still satisfies `IsCyclotomicExtension {pⁿ} ℚ Fₙ`, so the brick-2 finite-level API
(CM structure, `Gal ≅ (ℤ/pⁿ)ˣ`) applies to it verbatim. `F∞` is then the supremum `⨆ₙ Fₙ`. -/

/-- The ambient field: a fixed algebraic closure of `ℚ`, inside which the whole tower lives. -/
abbrev Om : Type := AlgebraicClosure ℚ

/-- `(pⁿ : ℚ) ≠ 0` — needed for the "enough roots of unity" instance on `Ω`. -/
instance instNeZeroPowRat (n : ℕ) : NeZero ((p ^ n : ℕ) : ℚ) :=
  ⟨by exact_mod_cast (instNeZeroPow p n).ne⟩

/-- `Ω = ℚ̄` is algebraic over `ℚ`. (Registered explicitly: the library instance
`AlgebraicClosure.isAlgebraic` is elaborated under reduced transparency and is not found by bare
instance search, so we re-expose it as a clean instance here.) -/
instance instIsAlgebraicOm : Algebra.IsAlgebraic ℚ Om := AlgebraicClosure.isAlgebraic ℚ

/-- `Ω = ℚ̄` is integral over `ℚ` (now synthesised from `instIsAlgebraicOm`). -/
instance instIsIntegralOm : Algebra.IsIntegral ℚ Om := Algebra.IsAlgebraic.isIntegral

/-- A chosen primitive `pⁿ`-th root of unity in `Ω = ℚ̄` (exists: `ℚ̄` is algebraically closed). -/
def zeta (n : ℕ) : Om := (HasEnoughRootsOfUnity.exists_primitiveRoot Om (p ^ n)).choose

/-- `zeta p n` is indeed a primitive `pⁿ`-th root of unity. -/
theorem zeta_spec (n : ℕ) : IsPrimitiveRoot (zeta p n) (p ^ n) :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot Om (p ^ n)).choose_spec

/-- `Fₙ = ℚ(μ_{pⁿ})`, realised as the `IntermediateField` of `Ω` generated by `zeta p n`. -/
def F (n : ℕ) : IntermediateField ℚ Om := IntermediateField.adjoin ℚ {zeta p n}

/-- Each nested layer `Fₙ` is a cyclotomic extension — so all finite-level API applies to it. -/
instance instIsCyclotomicF (n : ℕ) : IsCyclotomicExtension {p ^ n} ℚ (F p n) :=
  (zeta_spec p n).intermediateField_adjoin_isCyclotomicExtension (K := ℚ)

/-- The tower is increasing: `Fₙ ⊆ Fₙ₊₁`. (`ζₙ` is a `pⁿ⁺¹`-th root of unity, hence a power of the
primitive `ζₙ₊₁`, hence lies in `Fₙ₊₁`.) -/
theorem F_mono (n : ℕ) : F p n ≤ F p (n + 1) := by
  have hpow : zeta p n ^ p ^ (n + 1) = 1 := by
    rw [pow_succ, pow_mul, (zeta_spec p n).pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ := (zeta_spec p (n + 1)).eq_pow_of_pow_eq_one hpow
  rw [F, F, IntermediateField.adjoin_simple_le_iff, ← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

/-- The tower is monotone in the order `≤` on `ℕ`. -/
theorem F_monotone : Monotone (F p) :=
  monotone_nat_of_le_succ (F_mono p)

/-- `F∞ = ⋃ₙ Fₙ`, the cyclotomic `ℤ_p`-extension of `ℚ`, as an `IntermediateField` of `Ω`. -/
def Finf : IntermediateField ℚ Om := ⨆ n, F p n

/-- Every layer embeds in `F∞`. -/
theorem F_le_Finf (n : ℕ) : F p n ≤ Finf p := le_iSup (F p) n

/-! ### Brick 4 — the Galois group `Γ = Gal(F∞/ℚ)` of the cyclotomic tower

`F∞/ℚ` is Galois: it is the compositum `⨆ₙ Fₙ` of the Galois layers `Fₙ` (`normal_iSup`), and is
separable since `ℚ` is perfect. The Galois group `Γ` then carries the profinite Krull topology
(`IsGalois` + `FieldTheory/Galois/Infinite`). Abstractly `Γ ≅ ℤ_p^×`; that identification, and the
`ℤ_p`-quotient `Γ⁺ = Gal(F∞⁺/ℚ)`, are the next bricks. -/

/-- Each layer `Fₙ/ℚ` is Galois (cyclotomic extension). -/
instance instIsGaloisF (n : ℕ) : IsGalois ℚ (F p n) :=
  IsCyclotomicExtension.isGalois {p ^ n} ℚ (F p n)

/-- Each layer `Fₙ/ℚ` is normal (direct indexed instance, so the `⨆`-normality below synthesises). -/
instance instNormalF (n : ℕ) : Normal ℚ (F p n) := inferInstance

/-- `F∞` is algebraic over `ℚ` (it sits inside the algebraic `Ω`). -/
instance instIsAlgebraicFinf : Algebra.IsAlgebraic ℚ (Finf p) :=
  Algebra.IsAlgebraic.tower_bot ℚ (Finf p) Om

/-- `F∞/ℚ` is normal — a compositum of the normal layers `Fₙ`. -/
instance instNormalFinf : Normal ℚ (Finf p) := by
  rw [Finf]
  exact IntermediateField.normal_iSup (t := fun n => F p n) (h := fun i => instNormalF p i)

/-- `F∞/ℚ` is Galois (normal + separable, the latter since `ℚ` is perfect). -/
instance instIsGaloisFinf : IsGalois ℚ (Finf p) := ⟨⟩

/-- `Γ = Gal(F∞/ℚ)`, the Galois group of the cyclotomic `ℤ_p`-tower. Via `IsGalois` it carries the
profinite (Krull) topology. A genuine group of field automorphisms — no placeholder. -/
abbrev Gamma : Type := Finf p ≃ₐ[ℚ] Finf p

/-! ### Brick 4b — the maximal real tower `F∞⁺ = ⋃ₙ Fₙ⁺` and `Γ⁺ = Gal(F∞⁺/ℚ)`

`Fₙ⁺ = ℚ(ζₙ + ζₙ⁻¹)` is the maximal totally real subfield of `Fₙ` (RJW §13.2). We realise it as a
nested `IntermediateField` of `Ω`, generated by the real element `ηₙ = ζₙ + ζₙ⁻¹`. Monotonicity of
the real tower rests on the power-sum fact `ξᵐ + ξ⁻ᵐ ∈ ℚ(ξ + ξ⁻¹)` (a Chebyshev recurrence). -/

/-- Power-sum lemma: for `ξ ≠ 0`, every `ξᵐ + ξ⁻ᵐ` lies in `ℚ(ξ + ξ⁻¹)`. This is what makes
`ℚ(ξ + ξ⁻¹)` the maximal real subfield closed under the tower maps. -/
theorem powSum_mem_adjoin {ξ : Om} (hξ : ξ ≠ 0) (m : ℕ) :
    ξ ^ m + ξ⁻¹ ^ m ∈ IntermediateField.adjoin ℚ ({ξ + ξ⁻¹} : Set Om) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [pow_zero]; exact add_mem (one_mem _) (one_mem _)
  | one => simp only [pow_one]; exact IntermediateField.mem_adjoin_simple_self ℚ _
  | more k ih1 ih2 =>
    have h1 : ξ * ξ⁻¹ = 1 := mul_inv_cancel₀ hξ
    have key : ξ ^ (k + 2) + ξ⁻¹ ^ (k + 2)
        = (ξ + ξ⁻¹) * (ξ ^ (k + 1) + ξ⁻¹ ^ (k + 1)) - (ξ ^ k + ξ⁻¹ ^ k) := by
      linear_combination (-(ξ ^ k + ξ⁻¹ ^ k)) * h1
    rw [key]
    exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih2) ih1

/-- `ζₙ ≠ 0` (it is a root of unity). -/
theorem zeta_ne_zero (n : ℕ) : zeta p n ≠ 0 := (zeta_spec p n).ne_zero (instNeZeroPow p n).ne

/-- `Fₙ⁺ = ℚ(ζₙ + ζₙ⁻¹)`, the maximal real subfield of `Fₙ`, as a nested `IntermediateField` of `Ω`. -/
def FPlus (n : ℕ) : IntermediateField ℚ Om :=
  IntermediateField.adjoin ℚ {zeta p n + (zeta p n)⁻¹}

/-- The real subfield sits inside the full layer: `Fₙ⁺ ≤ Fₙ`. -/
theorem FPlus_le_F (n : ℕ) : FPlus p n ≤ F p n := by
  rw [FPlus, F, IntermediateField.adjoin_simple_le_iff]
  exact add_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
    (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _))

/-- The real tower is increasing: `Fₙ⁺ ⊆ Fₙ₊₁⁺`. (`ζₙ = ζₙ₊₁ᵏ`, and `ζₙ₊₁ᵏ + ζₙ₊₁⁻ᵏ ∈ ℚ(ζₙ₊₁+ζₙ₊₁⁻¹)`
by the power-sum lemma.) -/
theorem FPlus_mono (n : ℕ) : FPlus p n ≤ FPlus p (n + 1) := by
  have hpow : zeta p n ^ p ^ (n + 1) = 1 := by
    rw [pow_succ, pow_mul, (zeta_spec p n).pow_eq_one, one_pow]
  obtain ⟨k, -, hk⟩ := (zeta_spec p (n + 1)).eq_pow_of_pow_eq_one hpow
  rw [FPlus, FPlus, IntermediateField.adjoin_simple_le_iff, ← hk]
  have hne : zeta p (n + 1) ≠ 0 := zeta_ne_zero p (n + 1)
  rw [← inv_pow]
  exact powSum_mem_adjoin hne k

/-- `F∞⁺ = ⋃ₙ Fₙ⁺`, the cyclotomic `ℤ_p`-extension of the maximal real field — the field over which
the Iwasawa Main Conjecture (RJW Thm 13.11) is stated. -/
def FinfPlus : IntermediateField ℚ Om := ⨆ n, FPlus p n

/-- `Γ⁺ = Gal(F∞⁺/ℚ)`, abstractly `≅ ℤ_p` — the Iwasawa group of RJW §13.2 / Thm 13.11. A genuine
group of field automorphisms. -/
abbrev GammaPlus : Type := FinfPlus p ≃ₐ[ℚ] FinfPlus p

/-! ### Brick 5 — toward `X⁺_∞`: number-field structure and the absolute Galois groups

`X⁺_∞ = Gal(M⁺_∞/F⁺_∞)`, where `M⁺_∞` is the maximal abelian pro-`p` extension of `F∞⁺` unramified
outside `p` (RJW §13.2). The faithful route (chosen): build `M⁺_∞` through its **finite layers**, each
finite over a **number field** `Fₙ⁺` — where mathlib's finite-extension ramification (`IsUnramifiedAt`,
rings of integers, `LiesOver`) applies — then take the compositum inside `Ω` and `X⁺_∞ = Gal`. This
brick lays the two prerequisites: (i) `Fₙ`, `Fₙ⁺` are genuinely number fields (finite over `ℚ`), so
they have rings of integers and primes; (ii) the absolute Galois groups, the ambient for `M⁺_∞ ⊆ Ω`. -/

/-- `Fₙ = ℚ(μ_{pⁿ})` is finite-dimensional over `ℚ` (cyclotomic). -/
instance instFiniteDimensionalF (n : ℕ) : FiniteDimensional ℚ (F p n) :=
  IsCyclotomicExtension.finiteDimensional {p ^ n} ℚ (F p n)

/-- `Fₙ` is a number field — so it has a ring of integers `𝓞_{Fₙ}` and primes. -/
instance instNumberFieldF (n : ℕ) : NumberField (F p n) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalF p n

/-- `Fₙ⁺ = ℚ(ζₙ+ζₙ⁻¹)` is finite-dimensional over `ℚ` (a single algebraic generator). -/
instance instFiniteDimensionalFPlus (n : ℕ) : FiniteDimensional ℚ (FPlus p n) := by
  rw [FPlus]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

/-- `Fₙ⁺` is a number field — so it has a ring of integers `𝓞_{Fₙ⁺}` and primes. -/
instance instNumberFieldFPlus (n : ℕ) : NumberField (FPlus p n) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalFPlus p n

/-- The absolute Galois group `G_{Fₙ⁺} = Gal(ℚ̄/Fₙ⁺)` (`Ω` is an algebraic closure of `Fₙ⁺`).
`Mₙ⁺` will be cut out inside `Ω` as a subextension fixed by an appropriate closed subgroup. -/
abbrev AbsGalFPlus (n : ℕ) : Type := Om ≃ₐ[FPlus p n] Om

/-- The absolute Galois group `G_{F∞⁺} = Gal(ℚ̄/F∞⁺)`. `X⁺_∞` is a quotient of (the abelianisation
of) this group; `M⁺_∞ ⊆ Ω` is the corresponding fixed field. -/
abbrev AbsGalFinfPlus : Type := Om ≃ₐ[FinfPlus p] Om

end Iwasawa.GaloisFoundation

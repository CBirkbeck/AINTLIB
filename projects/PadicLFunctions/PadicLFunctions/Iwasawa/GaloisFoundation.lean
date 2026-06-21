import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Abelian
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

/-! ### General infrastructure: compositum of abelian extensions is abelian

`Gal(⨆ᵢ Eᵢ / F)` is commutative when each `Eᵢ/F` is abelian Galois. This is mathlib-missing (only
`normal_iSup` exists for the *normal* analogue, nothing for *abelian*), and is the keystone for the
`Λ(Γ⁺)`-module structure on `X⁺_∞`. Stated generally; a candidate for `Common/`/mathlib. -/

open IntermediateField in
/-- `Kᵢ`, viewed inside `↥(⨆ⱼ Kⱼ)` via `comap`, maps back to `Kᵢ` — used to transfer `IsAbelianGalois`. -/
noncomputable def restrAlgHom {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
    (K : ι → IntermediateField F E) (i : ι) :
    ↥(IntermediateField.comap (⨆ j, K j).val (K i)) →ₐ[F] ↥(K i) :=
  AlgHom.codRestrict (((⨆ j, K j).val).comp (IntermediateField.comap (⨆ j, K j).val (K i)).val)
    (K i).toSubalgebra (fun y => y.2)

open IntermediateField in
/-- **Compositum of abelian Galois extensions is abelian.** If each `Kᵢ/F` is abelian Galois, then the
Galois group of the compositum `⨆ᵢ Kᵢ` over `F` is commutative. -/
theorem isMulCommutative_iSup {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} (K : ι → IntermediateField F E) [∀ i, IsAbelianGalois F (K i)] :
    IsMulCommutative (↥(⨆ i, K i) ≃ₐ[F] ↥(⨆ i, K i)) := by
  haveI inst : ∀ i, IsAbelianGalois F ↥(comap (⨆ j, K j).val (K i)) :=
    fun i => IsAbelianGalois.of_algHom (restrAlgHom K i)
  have hsup : ⨆ i, comap (⨆ j, K j).val (K i) = ⊤ := by
    have hmap : map (⨆ j, K j).val (⨆ i, comap (⨆ j, K j).val (K i)) = ⨆ j, K j := by
      rw [IntermediateField.map_iSup]
      refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
      · rw [map_comap_eq]; exact inf_le_left.trans (le_iSup K i)
      · refine le_trans ?_ (le_iSup _ i)
        rw [map_comap_eq, inf_eq_left.mpr (by rw [IntermediateField.fieldRange_val]; exact le_iSup K i)]
    have htop : map (⨆ j, K j).val (⊤ : IntermediateField F ↥(⨆ j, K j)) = ⨆ j, K j := by
      apply SetLike.coe_injective; simp [IntermediateField.coe_map]
    exact (map_injective (⨆ j, K j).val) (hmap.trans htop.symm)
  rw [isMulCommutative_iff]; intro σ τ
  have key : ∀ i, ∀ x ∈ comap (⨆ j, K j).val (K i), (σ * τ) x = (τ * σ) x := by
    intro i x hx
    haveI := (inst i).toIsMulCommutative
    have hh : AlgEquiv.restrictNormalHom (comap (⨆ j, K j).val (K i)) (σ * τ)
            = AlgEquiv.restrictNormalHom (comap (⨆ j, K j).val (K i)) (τ * σ) := by
      rw [map_mul, map_mul]
      exact isMulCommutative_iff.mp (inst i).toIsMulCommutative _ _
    apply Subtype.val_injective
    rw [← AlgEquiv.restrictNormalHom_apply (comap (⨆ j, K j).val (K i)) (σ * τ) ⟨x, hx⟩,
        ← AlgEquiv.restrictNormalHom_apply (comap (⨆ j, K j).val (K i)) (τ * σ) ⟨x, hx⟩,
        congrArg (fun g => (g ⟨x, hx⟩ : ↥(comap (⨆ j, K j).val (K i)))) hh]
  refine AlgEquiv.ext fun y => ?_
  have hy : y ∈ adjoin F (⋃ i, (comap (⨆ j, K j).val (K i) : Set ↥(⨆ j, K j))) := by
    rw [← IntermediateField.iSup_eq_adjoin, hsup]; trivial
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx; exact key i x hxi
  | algebraMap x => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]

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

/-! ### Brick 6 — the maximal extensions `M⁺ₙ`, `L⁺ₙ` and the Galois modules `X⁺_∞`, `Y⁺_∞`

**Verbatim from RJW §13.2** (the protagonists of the Galois side of the Main Conjecture):
* `M⁺ₙ` = maximal abelian `p`-extension of `F⁺ₙ` unramified outside `p⁺ₙ`,
* `L⁺ₙ` = maximal unramified abelian `p`-extension of `F⁺ₙ`,
* `M⁺_∞ = ⋃ₙ M⁺ₙ`, `L⁺_∞ = ⋃ₙ L⁺ₙ`,
* `X⁺_∞ = Gal(M⁺_∞/F⁺_∞)`, `Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)`.

Each maximal extension is realised as the compositum (`⨆`) inside `Ω` of its **finite** abelian
`p`-power layers carrying the required ramification — so the ramification condition is checked on
finite extensions of the number field `F⁺ₙ`, where mathlib's `IsUnramifiedAt` and
`FltRegular.NumberTheory.Unramified` apply. Since `p⁺ₙ` is the unique prime of `F⁺ₙ` above `p`,
"unramified outside `p⁺ₙ`" means: unramified at every prime `P` of `𝓞_L` with residue characteristic
`≠ p`, i.e. `p ∉ P`. This is the genuine construction — no `Type*` stand-in, no bundled isomorphism. -/

open NumberField in
/-- A finite layer `L` over the number field `F⁺ₙ` is itself a number field (tower `ℚ → F⁺ₙ → L`),
so it has a ring of integers `𝓞_L` and primes. -/
theorem numberField_of_finite_layer (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    [FiniteDimensional (FPlus p n) L] : NumberField L := by
  haveI : FiniteDimensional ℚ (FPlus p n) := instFiniteDimensionalFPlus p n
  haveI : FiniteDimensional ℚ (L : Type _) := Module.Finite.trans (FPlus p n) (L : Type _)
  exact ⟨⟩

open NumberField in
/-- (RJW §13.2) `L/F⁺ₙ` is **unramified outside `p`**: it is unramified at every prime `P` of `𝓞_L`
whose residue characteristic is `≠ p` (equivalently `p ∉ P`). As `p⁺ₙ` is the unique prime of `F⁺ₙ`
above `p`, this is exactly RJW's "unramified outside `p⁺ₙ`". -/
def IsUnramifiedOutsideP (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    [FiniteDimensional (FPlus p n) L] : Prop :=
  haveI := numberField_of_finite_layer p n L
  ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (p : 𝓞 L) ∉ P → Algebra.IsUnramifiedAt (𝓞 (FPlus p n)) P

/-- A finite **abelian `p`-power** layer over `F⁺ₙ` that is **unramified outside `p`** — the building
block of `M⁺ₙ`. A genuine predicate (not a bundled hypothesis): finiteness, Galois, commutative Galois
group, `p`-power degree, and the ramification condition above. -/
def IsAdmissibleM (n : ℕ) (L : IntermediateField (FPlus p n) Om) : Prop :=
  ∃ h : FiniteDimensional (FPlus p n) L,
    IsGalois (FPlus p n) L ∧
    (∀ σ τ : L ≃ₐ[FPlus p n] L, σ * τ = τ * σ) ∧
    (∃ k : ℕ, Module.finrank (FPlus p n) L = p ^ k) ∧
    @IsUnramifiedOutsideP p _ n L h

/-- `M⁺ₙ` = maximal abelian `p`-extension of `F⁺ₙ` unramified outside `p⁺ₙ` (RJW §13.2), realised as
the compositum inside `Ω` of all its finite admissible layers. A genuine field, not a stand-in. -/
def MPlusN (n : ℕ) : IntermediateField (FPlus p n) Om :=
  ⨆ (L : IntermediateField (FPlus p n) Om) (_ : IsAdmissibleM p n L), L

/-- A finite abelian `p`-power layer over `F⁺ₙ` that is **unramified everywhere** — the building
block of `L⁺ₙ` (the `p`-Hilbert class field tower). -/
def IsAdmissibleL (n : ℕ) (L : IntermediateField (FPlus p n) Om) : Prop :=
  ∃ _ : FiniteDimensional (FPlus p n) L,
    IsGalois (FPlus p n) L ∧
    (∀ σ τ : L ≃ₐ[FPlus p n] L, σ * τ = τ * σ) ∧
    (∃ k : ℕ, Module.finrank (FPlus p n) L = p ^ k) ∧
    Algebra.Unramified (NumberField.RingOfIntegers (FPlus p n)) (NumberField.RingOfIntegers L)

/-- `L⁺ₙ` = maximal unramified abelian `p`-extension of `F⁺ₙ` (RJW §13.2; the `p`-Hilbert class
field of `F⁺ₙ`), as the compositum inside `Ω` of its finite admissible layers. -/
def LPlusN (n : ℕ) : IntermediateField (FPlus p n) Om :=
  ⨆ (L : IntermediateField (FPlus p n) Om) (_ : IsAdmissibleL p n L), L

/-- `M⁺_∞ = ⋃ₙ M⁺ₙ` (RJW §13.2): the maximal abelian pro-`p` extension of `F⁺_∞` unramified outside
`p`, realised as the `F⁺_∞`-compositum inside `Ω` of the finite-level `M⁺ₙ`. An `IntermediateField`
over `F⁺_∞`, so its relative Galois group is immediate. -/
def MinfPlus : IntermediateField (FinfPlus p) Om :=
  IntermediateField.adjoin (FinfPlus p) (⋃ n, (↑(MPlusN p n) : Set Om))

/-- `L⁺_∞ = ⋃ₙ L⁺ₙ` (RJW §13.2): the maximal unramified abelian pro-`p` extension of `F⁺_∞`. -/
def LinfPlus : IntermediateField (FinfPlus p) Om :=
  IntermediateField.adjoin (FinfPlus p) (⋃ n, (↑(LPlusN p n) : Set Om))

/-- `X⁺_∞ = Gal(M⁺_∞/F⁺_∞)` (RJW §13.2) — **the central Galois module of the Iwasawa Main Conjecture**
(Thm 13.11: `X⁺_∞ ≅ Λ(Γ⁺)/I(Γ⁺)ζp`). A genuine relative Galois group of the constructed fields, which
carries the `Λ(Γ⁺)`-action of Remark 13.7. No `Type*` stand-in, no bundled isomorphism. -/
abbrev XinfPlus : Type := MinfPlus p ≃ₐ[FinfPlus p] MinfPlus p

/-- `Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)` (RJW §13.2); classically `≅ lim Cl(F⁺ₙ)⊗ℤp`, and `= 0` for a Vandiver
prime (Cor 13.16(i)). A genuine relative Galois group. -/
abbrev YinfPlus : Type := LinfPlus p ≃ₐ[FinfPlus p] LinfPlus p

/-! #### `L⁺ ⊆ M⁺` — the containment underlying the Galois SES `0→Gal(M⁺_∞/L⁺_∞)→X⁺_∞→Y⁺_∞→0`

An unramified-everywhere layer is in particular unramified outside `p`, so every admissible-`L` layer
is an admissible-`M` layer (reusing mathlib's `Algebra.formallyUnramified_iff_forall`: global
unramified ⟺ unramified at every prime). Hence `L⁺ₙ ⊆ M⁺ₙ` and `L⁺_∞ ⊆ M⁺_∞`. -/

open NumberField in
/-- Unramified everywhere ⟹ unramified outside `p`: every `L⁺`-layer is an `M⁺`-layer. -/
theorem isAdmissibleM_of_isAdmissibleL (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    (hL : IsAdmissibleL p n L) : IsAdmissibleM p n L := by
  obtain ⟨hfin, hgal, hab, hpp, hunr⟩ := hL
  refine ⟨hfin, hgal, hab, hpp, ?_⟩
  intro P _ _
  haveI := numberField_of_finite_layer p n L
  haveI : Algebra.FormallyUnramified (𝓞 (FPlus p n)) (𝓞 L) := hunr.formallyUnramified
  exact Algebra.formallyUnramified_iff_forall.mp ‹_› ⟨P, ‹_›⟩

/-- `L⁺ₙ ⊆ M⁺ₙ`. -/
theorem LPlusN_le_MPlusN (n : ℕ) : LPlusN p n ≤ MPlusN p n :=
  iSup₂_le fun L hL => le_iSup₂_of_le L (isAdmissibleM_of_isAdmissibleL p n L hL) le_rfl

/-- `L⁺_∞ ⊆ M⁺_∞`. -/
theorem LinfPlus_le_MinfPlus : LinfPlus p ≤ MinfPlus p := by
  rw [LinfPlus, MinfPlus, IntermediateField.adjoin_le_iff]
  refine Set.iUnion_subset fun n => (SetLike.coe_subset_coe.mpr (LPlusN_le_MPlusN p n)).trans ?_
  exact (Set.subset_iUnion (fun n => (↑(MPlusN p n) : Set Om)) n).trans
    (IntermediateField.subset_adjoin _ _)

/-! #### `Mₙ⁺/Fₙ⁺` and `M∞⁺/F∞⁺` are abelian — toward the `Λ(Γ⁺)`-action and the SES

Each admissible layer is abelian Galois (the `IsAdmissibleM` predicate's fields), so the compositum
`Mₙ⁺` is abelian by `isMulCommutative_iSup`. -/

/-- An admissible layer is an abelian Galois extension of `Fₙ⁺`. -/
theorem isAbelianGalois_of_isAdmissibleM {n : ℕ} {L : IntermediateField (FPlus p n) Om}
    (h : IsAdmissibleM p n L) : IsAbelianGalois (FPlus p n) L :=
  haveI : IsGalois (FPlus p n) L := h.2.1
  haveI : IsMulCommutative (L ≃ₐ[FPlus p n] L) := ⟨⟨h.2.2.1⟩⟩
  ⟨⟩

/-- The `IsAdmissibleM`-collapsed layer `⨆ (_ : IsAdmissibleM L), L` (which is `L` or `⊥`) is always
abelian Galois — so the keystone `isMulCommutative_iSup` applies to `M⁺ₙ = ⨆ L, ⨆ (_:adm), L`. -/
instance isAbelianGalois_admissibleSummand (n : ℕ) (L : IntermediateField (FPlus p n) Om) :
    IsAbelianGalois (FPlus p n) ↥(⨆ _ : IsAdmissibleM p n L, L) := by
  by_cases h : IsAdmissibleM p n L
  · rw [iSup_pos h]; exact isAbelianGalois_of_isAdmissibleM p h
  · rw [iSup_neg h]; infer_instance

/-- `Gal(Mₙ⁺/Fₙ⁺)` is commutative (compositum of abelian layers). -/
theorem isMulCommutative_galMPlusN (n : ℕ) :
    IsMulCommutative (↥(MPlusN p n) ≃ₐ[FPlus p n] ↥(MPlusN p n)) :=
  isMulCommutative_iSup (fun L : IntermediateField (FPlus p n) Om => ⨆ _ : IsAdmissibleM p n L, L)

/-- An admissible-`L` layer is an abelian Galois extension of `Fₙ⁺`. -/
theorem isAbelianGalois_of_isAdmissibleL {n : ℕ} {L : IntermediateField (FPlus p n) Om}
    (h : IsAdmissibleL p n L) : IsAbelianGalois (FPlus p n) L :=
  haveI : IsGalois (FPlus p n) L := h.2.1
  haveI : IsMulCommutative (L ≃ₐ[FPlus p n] L) := ⟨⟨h.2.2.1⟩⟩
  ⟨⟩

instance isAbelianGalois_admissibleLSummand (n : ℕ) (L : IntermediateField (FPlus p n) Om) :
    IsAbelianGalois (FPlus p n) ↥(⨆ _ : IsAdmissibleL p n L, L) := by
  by_cases h : IsAdmissibleL p n L
  · rw [iSup_pos h]; exact isAbelianGalois_of_isAdmissibleL p h
  · rw [iSup_neg h]; infer_instance

/-- `Gal(Lₙ⁺/Fₙ⁺)` is commutative (compositum of unramified abelian layers). -/
theorem isMulCommutative_galLPlusN (n : ℕ) :
    IsMulCommutative (↥(LPlusN p n) ≃ₐ[FPlus p n] ↥(LPlusN p n)) :=
  isMulCommutative_iSup (fun L : IntermediateField (FPlus p n) Om => ⨆ _ : IsAdmissibleL p n L, L)

end Iwasawa.GaloisFoundation

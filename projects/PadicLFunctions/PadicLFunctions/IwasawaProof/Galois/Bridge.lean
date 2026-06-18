import PadicLFunctions.Coleman.Tower
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The `CyclotomicField ↪ ℂ_[p]` bridge  (S13-G, BRIDGE)

The forced connector between the two representations of the cyclotomic tower used in Stage G
(`.mathlib-quality/plan-G.md`, decision 2026-06-18):

* the **global / class-group / Galois side** lives on mathlib's `CyclotomicField (p^n) ℚ`
  (where `NumberField`, `ClassGroup`, adic-completion API exist), and
* the **local / units / Coleman side** (§12) is welded to `ℂ_[p]` (explicit roots `zetaSys`,
  the uniformiser `π_n = ζ−1`, operator norms, power series — it cannot move).

This file builds the `ℚ`-algebra embedding `CyclotomicField (p^n) ℚ ↪ ℂ_[p]` sending the canonical
primitive root to the project's chosen root `zetaSys p n`, so the abstract cyclotomic field is
realised concretely inside `ℂ_[p]`, compatibly with §12's analytic data.

## Main declarations

* `Iwasawa.Galois.cyclotomicEmbedding p n`: the `ℚ`-algebra hom `CyclotomicField (p^n) ℚ →ₐ[ℚ] ℂ_[p]`
  with `ζ ↦ zetaSys p n`.
-/

noncomputable section

namespace Iwasawa.Galois

open Polynomial IsCyclotomicExtension PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

instance instNeZeroPPow (n : ℕ) : NeZero (p ^ n) :=
  ⟨pow_ne_zero n hp.out.ne_zero⟩

instance instNeZeroPPowRat (n : ℕ) : NeZero ((p ^ n : ℕ) : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (pow_ne_zero n hp.out.ne_zero)⟩

instance instIsCyclo (n : ℕ) :
    IsCyclotomicExtension {p ^ n} ℚ (CyclotomicField (p ^ n) ℚ) :=
  CyclotomicField.isCyclotomicExtension (p ^ n) ℚ

/-- The canonical primitive `p^n`-th root of unity of `CyclotomicField (p^n) ℚ`. -/
noncomputable abbrev cycloZeta (n : ℕ) : CyclotomicField (p ^ n) ℚ :=
  zeta (p ^ n) ℚ (CyclotomicField (p ^ n) ℚ)

theorem cycloZeta_primitiveRoot (n : ℕ) : IsPrimitiveRoot (cycloZeta p n) (p ^ n) :=
  zeta_spec (p ^ n) ℚ (CyclotomicField (p ^ n) ℚ)

/-- **The bridge embedding** `CyclotomicField (p^n) ℚ ↪ ℂ_[p]`, sending the canonical primitive
root `ζ` to the project's chosen root `zetaSys p n` (both primitive `p^n`-th roots, hence sharing
the cyclotomic minimal polynomial over `ℚ`).  Realises the abstract cyclotomic field inside `ℂ_[p]`,
the forced connector between Stage G's mathlib side and §12's analytic `ℂ_[p]` side. -/
noncomputable def cyclotomicEmbedding (n : ℕ) : CyclotomicField (p ^ n) ℚ →ₐ[ℚ] ℂ_[p] :=
  ((cycloZeta_primitiveRoot p n).powerBasis ℚ).lift (zetaSys p n) <| by
    have hirr : Irreducible (cyclotomic (p ^ n) ℚ) := cyclotomic.irreducible_rat (NeZero.pos _)
    have hmin : minpoly ℚ ((cycloZeta_primitiveRoot p n).powerBasis ℚ).gen = cyclotomic (p ^ n) ℚ := by
      rw [(cycloZeta_primitiveRoot p n).powerBasis_gen ℚ]
      exact ((cycloZeta_primitiveRoot p n).minpoly_eq_cyclotomic_of_irreducible hirr).symm
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact zetaSys_primitiveRoot p n

@[simp] theorem cyclotomicEmbedding_zeta (n : ℕ) :
    cyclotomicEmbedding p n (cycloZeta p n) = zetaSys p n := by
  have hg : ((cycloZeta_primitiveRoot p n).powerBasis ℚ).gen = cycloZeta p n :=
    (cycloZeta_primitiveRoot p n).powerBasis_gen ℚ
  calc cyclotomicEmbedding p n (cycloZeta p n)
      = cyclotomicEmbedding p n (((cycloZeta_primitiveRoot p n).powerBasis ℚ).gen) := by rw [hg]
    _ = zetaSys p n := PowerBasis.lift_gen _ _ _

end Iwasawa.Galois

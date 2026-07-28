/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Weighted-parity combinatorics ([WP] §6.1)

The exponent-level layer of the weighted-parity example of
[WP] = `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex` §6.

Monomials of the ambient restricted power-series ring are indexed by `t : ℕ →₀ ℕ`,
with index `0` playing the paper's `W` and index `n ≥ 1` playing `U_n`.  For a weight
function `w : ℕ → ℕ` (the paper's example is `w = id`; Tate extensions use a shifted
weight vanishing on finitely many indices) we define the parity weight

  `wpWeight w t = ∑_{n ≥ 1, t n odd} w n`      ([WP] eq:parity-weight, ω(ν))

and the support monoid

  `WPMem w t ↔ wpWeight w t ≤ t 0`             ([WP] eq:parity-monoid, S)

together with the head submonoids (tail support bounded by `N`) and the head/tail
splitting of exponents that underlies the `c₀`-decomposition of [WP] §6.4.
-/

@[expose] public section

namespace WeightedParity

open Finset

/-! ### The parity weight -/

/-- The parity weight `ω(ν) = ∑_{n ≥ 1, ν_n odd} w n` of an exponent `t : ℕ →₀ ℕ`
([WP] eq:parity-weight, with the generalized weight `w`; the paper's example is
`w = id`).  Index `0` (the `W`-variable) never contributes. -/
def wpWeight (w : ℕ → ℕ) (t : ℕ →₀ ℕ) : ℕ :=
  ∑ n ∈ t.support, if t n % 2 = 1 ∧ n ≠ 0 then w n else 0

@[simp] theorem wpWeight_zero (w : ℕ → ℕ) : wpWeight w 0 = 0 := by sorry

/-- The weight only sees parity: it is unchanged by adding an even exponent vector.
Key computational form of [WP] eq:parity-weight. -/
theorem wpWeight_add_two_nsmul (w : ℕ → ℕ) (t s : ℕ →₀ ℕ) :
    wpWeight w (t + 2 • s) = wpWeight w t := by sorry

/-- Subadditivity `ω(ν+μ) ≤ ω(ν) + ω(μ)` ([WP] eq:omega-subadditive): `(ν+μ)_n` is odd
iff exactly one of `ν_n, μ_n` is odd. -/
theorem wpWeight_add_le (w : ℕ → ℕ) (s t : ℕ →₀ ℕ) :
    wpWeight w (s + t) ≤ wpWeight w s + wpWeight w t := by sorry

/-- Disjoint-support additivity of the parity weight (used silently by
[WP] eq:parity-factorization and eq:tail-multiplication). -/
theorem wpWeight_add_of_disjoint (w : ℕ → ℕ) {s t : ℕ →₀ ℕ}
    (h : Disjoint s.support t.support) :
    wpWeight w (s + t) = wpWeight w s + wpWeight w t := by sorry

@[simp] theorem wpWeight_single (w : ℕ → ℕ) (n : ℕ) (k : ℕ) :
    wpWeight w (Finsupp.single n k) = if k % 2 = 1 ∧ n ≠ 0 then w n else 0 := by sorry

/-! ### The support monoid `S` -/

/-- Membership in the weighted-parity support monoid
`S = {(a,ν) : a ≥ ω(ν)}` ([WP] eq:parity-monoid): the `W`-exponent `t 0` dominates the
parity weight of the `U`-part. -/
def WPMem (w : ℕ → ℕ) (t : ℕ →₀ ℕ) : Prop :=
  wpWeight w t ≤ t 0

@[simp] theorem wpMem_zero (w : ℕ → ℕ) : WPMem w 0 := by sorry

/-- `S` is closed under addition ([WP] line "The inequality (eq:omega-subadditive) shows
that `S` is closed under addition"). -/
theorem WPMem.add {w : ℕ → ℕ} {s t : ℕ →₀ ℕ} (hs : WPMem w s) (ht : WPMem w t) :
    WPMem w (s + t) := by sorry

/-- The `W`-monomial exponents are in `S`. -/
theorem wpMem_single_zero (w : ℕ → ℕ) (k : ℕ) : WPMem w (Finsupp.single 0 k) := by sorry

/-- The allowed `U_n`-monomial `W^{w n}·U_n` ([WP] `Y_n = W^n U_n` at `w = id`,
eq:finite-stage-substitution). -/
theorem wpMem_single_add_single (w : ℕ → ℕ) (n : ℕ) :
    WPMem w (Finsupp.single 0 (w n) + Finsupp.single n 1) := by sorry

/-- Even pure-`U` exponents are in `S` ([WP] `Z_n = U_n²`). -/
theorem wpMem_two_nsmul_single (w : ℕ → ℕ) (n : ℕ) (k : ℕ) :
    WPMem w (2 • Finsupp.single n k) := by sorry

/-! ### Heads ([WP] §6.1, finite stages) -/

/-- Membership in the `N`-th head: in `S`, with `U`-support contained in `{1,…,N}`
([WP] lem:finite-stage-normal-form — "the monomials in (eq:parity-monoid) involving
only `U_1,…,U_N`"). -/
def HeadMem (w : ℕ → ℕ) (N : ℕ) (t : ℕ →₀ ℕ) : Prop :=
  WPMem w t ∧ ∀ n, N < n → t n = 0

theorem HeadMem.wpMem {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (h : HeadMem w N t) :
    WPMem w t := h.1

theorem HeadMem.add {w : ℕ → ℕ} {N : ℕ} {s t : ℕ →₀ ℕ}
    (hs : HeadMem w N s) (ht : HeadMem w N t) : HeadMem w N (s + t) := by sorry

theorem HeadMem.mono {w : ℕ → ℕ} {N M : ℕ} (hNM : N ≤ M) {t : ℕ →₀ ℕ}
    (h : HeadMem w N t) : HeadMem w M t := by sorry

/-! ### Tails and the head/tail splitting ([WP] §6.4) -/

/-- A tail multi-index for the `N`-th head: supported on `{n : n > N}`
([WP] §6.4, `μ = (μ_n)_{n>N}`). -/
def IsTailIdx (N : ℕ) (μ : ℕ →₀ ℕ) : Prop :=
  ∀ n, n ≤ N → μ n = 0

/-- Tail multi-indices form an additive submonoid of the exponent monoid. -/
noncomputable def tailIdxSubmonoid (N : ℕ) : AddSubmonoid (ℕ →₀ ℕ) where
  carrier := {μ | IsTailIdx N μ}
  zero_mem' := by sorry
  add_mem' := by sorry

/-- The type of tail multi-indices ([WP] §6.4). -/
def TailIdx (N : ℕ) : Type :=
  ↥(tailIdxSubmonoid N)

namespace TailIdx

noncomputable instance (N : ℕ) : AddCommMonoid (TailIdx N) :=
  inferInstanceAs (AddCommMonoid ↥(tailIdxSubmonoid N))

@[simp] theorem add_val {N : ℕ} (μ ν : TailIdx N) : (μ + ν).1 = μ.1 + ν.1 := rfl

@[simp] theorem zero_val {N : ℕ} : (0 : TailIdx N).1 = 0 := rfl

noncomputable instance (N : ℕ) : DecidableEq (TailIdx N) := Classical.decEq _

end TailIdx

/-- The exponent of the tail basis monomial `e_μ = W^{ω(μ)} U^μ`
([WP] eq:tail-basis, under the substitution eq:finite-stage-substitution). -/
noncomputable def tailShift (w : ℕ → ℕ) {N : ℕ} (μ : TailIdx N) : ℕ →₀ ℕ :=
  Finsupp.single 0 (wpWeight w μ.1) + μ.1

theorem wpMem_tailShift (w : ℕ → ℕ) {N : ℕ} (μ : TailIdx N) :
    WPMem w (tailShift w μ) := by sorry

/-- The head part of an allowed exponent: restrict to indices `≤ N` and subtract the
tail weight from the `W`-exponent.  This is the exponent-level content of
[WP] eq:tail-decomposition. -/
noncomputable def headPart (w : ℕ → ℕ) (N : ℕ) (t : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  (t.filter fun n => n ≤ N).update 0 (t 0 - wpWeight w (t.filter fun n => N < n))

/-- The tail part of an exponent: restrict to indices `> N`. -/
noncomputable def tailPart (N : ℕ) (t : ℕ →₀ ℕ) : TailIdx N :=
  ⟨t.filter fun n => N < n, by sorry⟩

theorem headMem_headPart {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (ht : WPMem w t) :
    HeadMem w N (headPart w N t) := by sorry

/-- The head/tail reconstruction: every allowed exponent splits uniquely as
(head exponent) + (tail-basis exponent) ([WP] eq:tail-decomposition at the level of
monomials; uses disjoint-support additivity of `ω`). -/
theorem headPart_add_tailShift {w : ℕ → ℕ} {N : ℕ} {t : ℕ →₀ ℕ} (ht : WPMem w t) :
    headPart w N t + tailShift w (tailPart N t) = t := by sorry

/-- Uniqueness half of the splitting: a head exponent plus a tail-basis exponent
recovers its parts. -/
theorem headPart_of_headMem_add {w : ℕ → ℕ} {N : ℕ} {h : ℕ →₀ ℕ} (hh : HeadMem w N h)
    (μ : TailIdx N) : headPart w N (h + tailShift w μ) = h := by sorry

theorem tailPart_of_headMem_add {w : ℕ → ℕ} {N : ℕ} {h : ℕ →₀ ℕ} (hh : HeadMem w N h)
    (μ : TailIdx N) : tailPart N (h + tailShift w μ) = μ := by sorry

/-! ### The shifted weight (Tate extensions, [WP] §6.5 eq:strong-sheafy-decomposition) -/

/-- The weight for the Tate extension `𝒜⟨V_1,…,V_s⟩`: the first `s` `U`-variables are
freed (weight `0`, i.e. they become the auxiliary Tate variables `V_i`), the rest carry
the shifted original weight.  [WP] §6.5: "for auxiliary Tate variables `V_1,…,V_s` one
has, isometrically, `𝒜⟨V⟩ ≅ ⊕̂ 𝒜_N⟨V⟩ e_μ`" — in this formalization the Tate extension
is the same weighted-parity construction at the shifted weight. -/
def shiftWeight (w : ℕ → ℕ) (s : ℕ) : ℕ → ℕ :=
  fun n => if n ≤ s then 0 else w (n - s)

/-- Shifting by `0` does not change the parity weight (the two weight functions differ
only at index `0`, which `wpWeight` ignores). -/
@[simp] theorem wpWeight_shiftWeight_zero (w : ℕ → ℕ) (t : ℕ →₀ ℕ) :
    wpWeight (shiftWeight w 0) t = wpWeight w t := by sorry

end WeightedParity

module

public import Mathlib
public import DedekindResidue.CompletedZeta.Normalisation

/-!
# The completed Dedekind zeta function, by characterisation  (SP1-FE interface)

Mathlib's `NumberField.dedekindZeta` is the `L`-series only — genuine (an honest convergent
sum) exactly on the half-plane `Re s > 1` and junk elsewhere. The completed zeta
`Λ_K(s) = |Δ_K|^{s/2}·Γℝ(s)^{r₁}·Γℂ(s)^{r₂}·ζ_K(s)` therefore cannot be *defined* through it
on all of `ℂ` without lying in the critical strip.

Instead we **characterise** it, with no placeholder anywhere:

* `completedZetaPrefactor K s = |Δ_K|^{s/2}·γ_K(s)` — genuine (a `cpow` and Gamma factors);
* `IsCompletedDedekindZeta K Λ` — `Λ` agrees with `completedZetaPrefactor · ζ_K` on
  `Re s > 1` **and** `s(s-1)Λ(s)` is entire.

By the identity theorem the two conditions determine `Λ` **uniquely**
(`IsCompletedDedekindZeta.unique`), so quantifying over `Λ` with this predicate *is*
talking about "the" completed Dedekind zeta. Hecke's theorem — the target of SP1-AGE —
is the **existence** statement (construct `Λ` as a Mellin transform of the ideal-class
theta integrals); the functional equation `Λ(1-s) = Λ(s)` is proven of that construction.

This interface is what the GRH predicate (`GRH.lean`) and Theorem 1 consume; nothing here
is a stub.
-/

namespace DedekindResidue

@[expose] public section

open NumberField

/-- The prefactor `|Δ_K|^{s/2} · Γℝ(s)^{r₁} · Γℂ(s)^{r₂}` completing the Dedekind zeta
function. Genuine on all of `ℂ` (a `cpow` of the positive real `|Δ_K|` and the Deligne
Gamma factors of `Normalisation.lean`). -/
noncomputable def completedZetaPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|discr K| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s

/-- **Characterisation of the completed Dedekind zeta function** `Λ_K`:
1. on the half-plane of absolute convergence `Re s > 1` (where mathlib's `dedekindZeta`
   is the honest convergent `L`-series), `Λ` is `|Δ_K|^{s/2}·γ_K(s)·ζ_K(s)`;
2. `s(s-1)·Λ(s)` is entire — `Λ` is analytic away from (at most simple) poles at `s = 0, 1`.

These two conditions determine `Λ` uniquely among continuous functions
(`IsCompletedDedekindZeta.unique`): this predicate **is** "the" completed Dedekind zeta,
stated without first constructing the meromorphic continuation. Hecke's theorem
(SP1-AGE/FE: existence of such a `Λ` via the theta-Mellin construction, with the functional
equation `Λ(1-s) = Λ(s)`) is what makes the predicate inhabited. -/
def IsCompletedDedekindZeta (K : Type*) [Field K] [NumberField K] (Λ : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → Λ s = completedZetaPrefactor K s * dedekindZeta K s)
    ∧ Differentiable ℂ (fun s => s * (s - 1) * Λ s)

/-- **Uniqueness.** Any two functions satisfying the completed-zeta characterisation agree
away from the poles `s = 0, 1`: the entire functions `s(s-1)Λᵢ(s)` agree on the open
half-plane `Re s > 1`, hence everywhere by the identity theorem; cancel `s(s-1)`.
(No condition can pin the values *at* `0` and `1` — the genuine `Λ_K` has simple poles
there, so those values are junk by nature.) -/
theorem IsCompletedDedekindZeta.eqOn {K : Type*} [Field K] [NumberField K]
    {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsCompletedDedekindZeta K Λ₁)
    (h₂ : IsCompletedDedekindZeta K Λ₂) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Λ₁ s = Λ₂ s := by
  have hagree : ∀ s : ℂ, s * (s - 1) * Λ₁ s = s * (s - 1) * Λ₂ s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpre : Set.EqOn (fun s => s * (s - 1) * Λ₁ s) (fun s => s * (s - 1) * Λ₂ s)
        {s : ℂ | 1 < s.re} := by
      intro s hs
      simp only
      rw [h₁.1 s hs, h₂.1 s hs]
    have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num [Complex.ofReal_re]
    have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := fun s => s * (s - 1) * Λ₁ s) (g := fun s => s * (s - 1) * Λ₂ s)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr h₁.2)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr h₂.2)
      isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (hpre.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
    exact fun s => this (Set.mem_univ s)
  have h := hagree s
  have hne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  exact mul_left_cancel₀ hne h

end

end DedekindResidue

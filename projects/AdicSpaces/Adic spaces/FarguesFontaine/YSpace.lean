/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.FrobeniusAction
import «Adic spaces».RationalSubsets

/-!
# The space 𝒴 = Spa(A_inf, A_inf) ∖ V(p·[ϖ]) and its window covering

This file defines the punctured space `𝒴` of the Fargues--Fontaine construction and
develops the "radius" comparison machinery, entirely at the level of the valuative
relation (no real-valued radius function κ is needed):

* `Y` : the subset `{v ∈ Spa(A_inf, A_inf) : v(p[ϖ]) ≠ 0}`, an open, `φ`-stable subset;
* `KGE q v` / `KLE q v` : rank-free renderings of "κ(v) ≥ q" / "κ(v) ≤ q" for `q ∈ ℚ`,
  by clearing denominators: `κ(v) ≥ a/b ⟺ v([ϖ])^b ≤ v(p)^a`;
* the windows `windowU n`, `windowV n` (Kedlaya's `U_n`, `V_n`), their covering of `Y`,
  the `φ`-translation `φ^k(U_n) = U_{n-k}` (in the action convention `g • v = v ∘ φ^{-g}`),
  within-family disjointness, and openness.

## Sources

* [BFHHLWY][bfhhlwy2018], Definition 2.1.1: "𝒴_{E,F} = Spa(W_{E°}(F°)) \ {|p[ϖ]| = 0}".
* [Kedlaya, AWS 2017][kedlaya-aws], Remark 3.1.9 (verbatim, R Tate, ϖ a
  pseudouniformizer): "Y_S is the subspace of v ∈ Spa(A_inf, A_inf) for which
  v(p[ϖ]) ≠ 0. This space can be covered by the subspaces
  U_n := {v ∈ Y_S : v(p)^{cp^n} ≤ v(ϖ) ≤ v(p)^{p^n}},
  V_n := {v ∈ Y_S : v(p)^{p^{n+1}} ≤ v(ϖ) ≤ v(p)^{cp^n}} (n ∈ ℤ), where c ∈ (1,p) ∩ Q is
  arbitrary. The action of φ permutes the U_n (among themselves) and the V_n (among
  themselves), and hence is properly discontinuous."
* [Scholze–Weinstein][sw2020], §12.2 (the map κ and κ∘φ = pκ; our `KGE`/`KLE` are the
  log-free form of κ-comparisons).
-/

open TopologicalRing ValuationSpectrum WittVector Pointwise

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- Strict comparison of values: `v(a) < v(b)`, i.e. `v(a) ≤ v(b)` and not conversely. -/
def vlt (v : Spv (Ainf p F)) (a b : Ainf p F) : Prop :=
  v.vle a b ∧ ¬ v.vle b a

/-- **The space 𝒴**: the subset of `Spa(A_inf, A_inf)` where `p·[ϖ]` does not vanish.

Source: [BFHHLWY, Def 2.1.1]: "𝒴_{E,F} = Spa(W_{E°}(F°)) \ {|p[ϖ]| = 0}";
[Kedlaya-AWS, Rem. 3.1.9]: "Y_S is the subspace of v ∈ Spa(A_inf, A_inf) for which
v(p[ϖ]) ≠ 0". -/
def Y : Set (Spv (Ainf p F)) :=
  {v ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) |
    ¬ v.vle ((p : Ainf p F) * teichPi p F ϖ) 0}

theorem Y_subset_spa : Y p F ϖ ⊆ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
  fun _ hv => hv.1

/-- `𝒴` is the trace on `Spa` of the basic open subset attached to `p·[ϖ]`. -/
theorem Y_eq_spa_inter_basicOpen :
    Y p F ϖ =
      Spa (Ainf p F) (ringPlus (Ainf p F)) ∩
        basicOpen ((p : Ainf p F) * teichPi p F ϖ) ((p : Ainf p F) * teichPi p F ϖ) := by
  sorry

/-- `𝒴` is open in `Spa(A_inf, A_inf)` (subspace topology). -/
theorem isOpen_Y :
    IsOpen (Subtype.val ⁻¹' Y p F ϖ :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
  sorry

/-- `𝒴` does not depend on the choice of pseudo-uniformizer: any two pseudo-uniformizers
divide powers of each other in `O_F`, and Teichmüller is multiplicative.

Source: [Kedlaya-AWS §11.2-style]: "this is independent of the choice of ϖ, as for any
other choice ϖ', there is some n such that ϖ | (ϖ')^n and ϖ' | ϖ^n". -/
theorem Y_indep (ϖ' : PseudoUniformizer F) : Y p F ϖ = Y p F ϖ' := by sorry

/-- `𝒴` is stable under the `φ^ℤ`-action.

Source: [SW, §12.2]: "The Frobenius automorphism ... preserves 𝒴". -/
theorem smul_mem_Y (g : Multiplicative ℤ) {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) :
    g • v ∈ Y p F ϖ := by sorry

section ElementFacts

variable {p F ϖ}
variable {v : Spv (Ainf p F)}

/-- On `𝒴`, `v(p) ≠ 0`. -/
theorem v_p_ne_zero (hv : v ∈ Y p F ϖ) : ¬ v.vle (p : Ainf p F) 0 := by sorry

/-- On `𝒴`, `v([ϖ]) ≠ 0`. -/
theorem v_teichPi_ne_zero (hv : v ∈ Y p F ϖ) : ¬ v.vle (teichPi p F ϖ) 0 := by sorry

/-- On `𝒴`, `v(p) < 1` strictly. From continuity of `v` and `p ∈ I`: the open set
`{a : v(a) < v(p)}` contains some `I^N ∋ p^N`, so `v(p)^N < v(p)`, forcing `v(p) < 1`.

Source: this is the standard argument that on the analytic locus the ideal of definition
has value < 1; cf. [SW, §12.2] (κ well-defined on 𝒴) and [Wedhorn, §7]-style continuity
manipulations. -/
theorem vlt_p_one (hv : v ∈ Y p F ϖ) : vlt p F v (p : Ainf p F) 1 := by sorry

/-- On `𝒴`, `v([ϖ]) < 1` strictly. Same continuity argument as `vlt_p_one`. -/
theorem vlt_teichPi_one (hv : v ∈ Y p F ϖ) : vlt p F v (teichPi p F ϖ) 1 := by sorry

/-- Cofinality of `p`-powers: for `v ∈ 𝒴` and any `g` with `v(g) ≠ 0`, some `v(p^n)` lies
strictly below `v(g)`. From continuity: `{a : v(a) < v(g)}` is an open neighbourhood of
`0`, hence contains `I^n ∋ p^n`.

Source: continuity of valuations, [Wedhorn, Def. 7.7]-style; used implicitly for the
covering in [Kedlaya-AWS, Rem. 3.1.9]. -/
theorem exists_pow_p_vlt (hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) :
    ∃ n : ℕ, vlt p F v ((p : Ainf p F) ^ n) g := by sorry

/-- Cofinality of `[ϖ]`-powers, as for `exists_pow_p_vlt`. -/
theorem exists_pow_teichPi_vlt (hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) :
    ∃ n : ℕ, vlt p F v (teichPi p F ϖ ^ n) g := by sorry

end ElementFacts

/-! ### The rank-free κ-comparison predicates -/

/-- `KGE q v` renders "κ(v) ≥ q": for `q = a/b` in lowest terms (`b > 0`),
`v([ϖ])^b ≤ v(p)^a`, stated on ring elements via multiplicativity.

For `q ≤ 0` the numerator truncates to `0` and the predicate is `v([ϖ]^b) ≤ 1`, which is
true on `Spa(A_inf, A_inf)`; all lemmas assume `0 < q`.

Source: log-free form of [SW, §12.2]'s κ; matches the inequalities of
[Kedlaya-AWS, Rem. 3.1.9] with denominators cleared. -/
def KGE (q : ℚ) (v : Spv (Ainf p F)) : Prop :=
  v.vle (teichPi p F ϖ ^ q.den) ((p : Ainf p F) ^ q.num.toNat)

/-- `KLE q v` renders "κ(v) ≤ q": `v(p)^a ≤ v([ϖ])^b` for `q = a/b` in lowest terms. -/
def KLE (q : ℚ) (v : Spv (Ainf p F)) : Prop :=
  v.vle ((p : Ainf p F) ^ q.num.toNat) (teichPi p F ϖ ^ q.den)

variable {p F ϖ}

/-- Representation-independence of `KGE`: for any fraction `a/b = q` with `b > 0`,
`KGE q v ↔ v([ϖ]^b) ≤ v(p^a)`. This is the denominator-clearing workhorse
(cross-multiplication inside the value monoid). -/
theorem KGE_iff {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q)
    {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) :
    KGE p F ϖ q v ↔ v.vle (teichPi p F ϖ ^ b) ((p : Ainf p F) ^ a) := by sorry

/-- Representation-independence of `KLE`, as for `KGE_iff`. -/
theorem KLE_iff {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q)
    {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) :
    KLE p F ϖ q v ↔ v.vle ((p : Ainf p F) ^ a) (teichPi p F ϖ ^ b) := by sorry

/-- Totality: at every positive rational `q`, either `κ(v) ≥ q` or `κ(v) ≤ q`
(linearity of the valuative order). -/
theorem KGE_or_KLE {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q) :
    KGE p F ϖ q v ∨ KLE p F ϖ q v := by sorry

/-- Order-incompatibility: `κ(v) ≤ q'` and `κ(v) ≥ q` cannot both hold when `q' < q`
(on `𝒴`, where `0 < v(p) < 1`). Cross-multiply and use the exponent-flip rule
`v(p)^m ≤ v(p)^k → m ≥ k`.

This single lemma drives all window disjointness. -/
theorem not_KGE_of_KLE_of_lt {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q q' : ℚ}
    (hq' : 0 < q') (hlt : q' < q) (hle : KLE p F ϖ q' v) :
    ¬ KGE p F ϖ q v := by sorry

/-! ### The windows U_n, V_n (Kedlaya, AWS Remark 3.1.9) -/

/-- The constant `c := (p+1)/2 ∈ (1, p) ∩ ℚ` of [Kedlaya-AWS, Rem. 3.1.9] (any rational
in `(1,p)` works; we fix this one). Valid for every prime, including `p = 2`
(`c = 3/2`). Stated with its own explicit binder (independent of the section
variables). -/
def cFF (p : ℕ) : ℚ := ((p : ℚ) + 1) / 2

theorem one_lt_cFF {p : ℕ} (hp : 1 < p) : 1 < cFF p := by sorry

theorem cFF_lt_p {p : ℕ} (hp : 1 < p) : cFF p < (p : ℚ) := by sorry

variable (p F ϖ)

/-- Kedlaya's window `U_n = {v ∈ Y : v(p)^{c·p^n} ≤ v([ϖ]) ≤ v(p)^{p^n}}`, in
`KGE`/`KLE` form: `κ(v) ∈ [p^n, c·p^n]`.

Source: [Kedlaya-AWS, Rem. 3.1.9], verbatim in the module docstring. -/
def windowU (n : ℤ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ ((p : ℚ) ^ n) v ∧ KLE p F ϖ (cFF p * (p : ℚ) ^ n) v}

/-- Kedlaya's window `V_n = {v ∈ Y : v(p)^{p^{n+1}} ≤ v([ϖ]) ≤ v(p)^{c·p^n}}`:
`κ(v) ∈ [c·p^n, p^{n+1}]`.

Source: [Kedlaya-AWS, Rem. 3.1.9]. -/
def windowV (n : ℤ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ (cFF p * (p : ℚ) ^ n) v ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v}

/-- **The covering**: `𝒴 = ⋃_n (U_n ∪ V_n)`.

Proof plan: cofinality (`exists_pow_p_vlt`, `exists_pow_teichPi_vlt`) pins κ(v) into some
interval `[p^{-N}, p^N]`; among the finitely many `n` in range, take the largest with
`KGE (p^n)`; totality (`KGE_or_KLE`) then places `v` in `U_n` or `V_n`.

Source: [Kedlaya-AWS, Rem. 3.1.9]: "This space can be covered by the subspaces U_n ...
V_n". -/
theorem Y_eq_iUnion_windows :
    Y p F ϖ = (⋃ n : ℤ, windowU p F ϖ n) ∪ ⋃ n : ℤ, windowV p F ϖ n := by sorry

/-- **Translation**: the action shifts windows, `φ^k(U_n) = U_{n-k}` in the convention
`g • v = v ∘ φ^{-g}` (so κ(g • v) = κ(v)/p^g).

Source: [Kedlaya-AWS, Rem. 3.1.9]: "The action of φ permutes the U_n (among
themselves)"; [SW, §12.2]: "κ∘φ = pκ", "φ sends 𝒴_{[a,b]} isomorphically to
𝒴_{[ap,bp]}". -/
theorem zsmul_windowU (k n : ℤ) :
    (Multiplicative.ofAdd k) • windowU p F ϖ n = windowU p F ϖ (n - k) := by sorry

/-- Translation for the `V`-family: `φ^k(V_n) = V_{n-k}`. -/
theorem zsmul_windowV (k n : ℤ) :
    (Multiplicative.ofAdd k) • windowV p F ϖ n = windowV p F ϖ (n - k) := by sorry

/-- **Within-family disjointness** for the `U`-family: `U_n ∩ U_m = ∅` for `n ≠ m`.
Uses `1 < c < p` strictly, via `not_KGE_of_KLE_of_lt` (the κ-intervals `[p^n, c·p^n]` are
pairwise disjoint because `c < p`).

Source: [Kedlaya-AWS, Rem. 3.1.9] (implicit in "hence is properly discontinuous"). -/
theorem windowU_disjoint {n m : ℤ} (h : n ≠ m) :
    Disjoint (windowU p F ϖ n) (windowU p F ϖ m) := by sorry

/-- Within-family disjointness for the `V`-family (κ-intervals `[c·p^n, p^{n+1}]`,
disjoint because `1 < c`). -/
theorem windowV_disjoint {n m : ℤ} (h : n ≠ m) :
    Disjoint (windowV p F ϖ n) (windowV p F ϖ m) := by sorry

/-- Windows are open: `U_n` is the intersection of `𝒴` with two `basicOpen` conditions
(each `KGE`/`KLE` inequality together with the nonvanishing from `𝒴` is a rational-open
condition). -/
theorem isOpen_windowU (n : ℤ) :
    IsOpen (Subtype.val ⁻¹' windowU p F ϖ n :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by sorry

/-- Windows are open (`V`-family). -/
theorem isOpen_windowV (n : ℤ) :
    IsOpen (Subtype.val ⁻¹' windowV p F ϖ n :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by sorry

end FarguesFontaine

end

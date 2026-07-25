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
  rw [basicOpen_self]
  rfl

/-- `𝒴` is open in `Spa(A_inf, A_inf)` (subspace topology). -/
theorem isOpen_Y :
    IsOpen (Subtype.val ⁻¹' Y p F ϖ :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
  convert continuous_subtype_val.isOpen_preimage _
    (isOpen_basicOpen ((p : Ainf p F) * teichPi p F ϖ)
      ((p : Ainf p F) * teichPi p F ϖ)) using 1
  ext v
  simp only [Set.mem_preimage, Y, basicOpen_self, Set.mem_setOf_eq, v.2, true_and]

private theorem p_mem_Iinf : (p : Ainf p F) ∈ Iinf p F ϖ := by
  rw [Iinf]
  exact Ideal.subset_span (Set.mem_insert _ _)

private theorem teichPi_mem_Iinf : teichPi p F ϖ ∈ Iinf p F ϖ := by
  rw [Iinf]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

private theorem exists_pow_succ_vlt {v : Spv (Ainf p F)}
    (hv : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))) {a b : Ainf p F}
    (ha : a ∈ Iinf p F ϖ) (hb : ¬ v.vle b 0) :
    ∃ n : ℕ, vlt p F v (a ^ (n + 1)) b := by
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hUopen : IsOpen {x : Ainf p F | vlt p F v x b} := by
    have hopen := hv.1 (ValuativeRel.valuation (Ainf p F) b)
    convert hopen using 1
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_iff_le_not_ge.mpr
        ⟨((ValuativeRel.valuation (Ainf p F)).vle_iff_le).mp h1,
          fun hge => h2 (((ValuativeRel.valuation (Ainf p F)).vle_iff_le).mpr hge)⟩
    · intro hlt
      exact ⟨((ValuativeRel.valuation (Ainf p F)).vle_iff_le).mpr hlt.le,
        fun h => hlt.not_ge (((ValuativeRel.valuation (Ainf p F)).vle_iff_le).mp h)⟩
  have hU0 : {x : Ainf p F | vlt p F v x b} ∈ nhds (0 : Ainf p F) :=
    hUopen.mem_nhds ⟨v.zero_vle b, hb⟩
  obtain ⟨N, hN⟩ := (isAdic_iff.mp (isAdic_Iinf p F ϖ)).2 _ hU0
  refine ⟨N, hN ?_⟩
  exact SetLike.mem_coe.mpr
    (Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.pow_mem_pow ha (N + 1)))

private theorem vlt_one_of_not_vle_pow {v : Spv (Ainf p F)} {a : Ainf p F} {n : ℕ}
    (h2 : ¬ v.vle a (a ^ (n + 1))) : vlt p F v a 1 := by
  have hnot : ¬ v.vle 1 a := fun h1a => h2 (by
    have hchain : ∀ k : ℕ, v.vle a (a ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using (v.vle_total a a).elim id id
      | succ m ih =>
          refine v.vle_trans ih ?_
          have hmul := v.mul_vle_mul_left h1a (a ^ (m + 1))
          rwa [one_mul, ← pow_succ'] at hmul
    exact hchain n)
  exact ⟨(v.vle_total _ _).resolve_right hnot, hnot⟩

section ElementFacts

variable {p F ϖ}
variable {v : Spv (Ainf p F)}

/-- On `𝒴`, `v(p) ≠ 0`. -/
theorem v_p_ne_zero (hv : v ∈ Y p F ϖ) : ¬ v.vle (p : Ainf p F) 0 := fun h =>
  hv.2 (by have := v.mul_vle_mul_left h (teichPi p F ϖ); rwa [zero_mul] at this)

/-- On `𝒴`, `v([ϖ]) ≠ 0`. -/
theorem v_teichPi_ne_zero (hv : v ∈ Y p F ϖ) : ¬ v.vle (teichPi p F ϖ) 0 := fun h =>
  hv.2 (by
    have := v.mul_vle_mul_left h ((p : Ainf p F))
    rwa [zero_mul, mul_comm] at this)

/-- On `𝒴`, `v(p) < 1` strictly. From continuity of `v` and `p ∈ I`: the open set
`{a : v(a) < v(p)}` contains some `I^N ∋ p^N`, so `v(p)^N < v(p)`, forcing `v(p) < 1`.

Source: this is the standard argument that on the analytic locus the ideal of definition
has value < 1; cf. [SW, §12.2] (κ well-defined on 𝒴) and [Wedhorn, §7]-style continuity
manipulations. -/
theorem vlt_p_one (hv : v ∈ Y p F ϖ) : vlt p F v (p : Ainf p F) 1 := by
  obtain ⟨n, -, h2⟩ :=
    exists_pow_succ_vlt p F ϖ hv.1 (p_mem_Iinf p F ϖ) (v_p_ne_zero hv)
  exact vlt_one_of_not_vle_pow p F h2

/-- On `𝒴`, `v([ϖ]) < 1` strictly. Same continuity argument as `vlt_p_one`. -/
theorem vlt_teichPi_one (hv : v ∈ Y p F ϖ) : vlt p F v (teichPi p F ϖ) 1 := by
  obtain ⟨n, -, h2⟩ :=
    exists_pow_succ_vlt p F ϖ hv.1 (teichPi_mem_Iinf p F ϖ) (v_teichPi_ne_zero hv)
  exact vlt_one_of_not_vle_pow p F h2

/-- Cofinality of `p`-powers: for `v ∈ 𝒴` and any `g` with `v(g) ≠ 0`, some `v(p^n)` lies
strictly below `v(g)`. From continuity: `{a : v(a) < v(g)}` is an open neighbourhood of
`0`, hence contains `I^n ∋ p^n`.

Source: continuity of valuations, [Wedhorn, Def. 7.7]-style; used implicitly for the
covering in [Kedlaya-AWS, Rem. 3.1.9]. -/
theorem exists_pow_p_vlt (hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) :
    ∃ n : ℕ, vlt p F v ((p : Ainf p F) ^ n) g := by
  obtain ⟨n, h⟩ := exists_pow_succ_vlt p F ϖ hv.1 (p_mem_Iinf p F ϖ) hg
  exact ⟨n + 1, h⟩

/-- Cofinality of `[ϖ]`-powers, as for `exists_pow_p_vlt`. -/
theorem exists_pow_teichPi_vlt (hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) :
    ∃ n : ℕ, vlt p F v (teichPi p F ϖ ^ n) g := by
  obtain ⟨n, h⟩ := exists_pow_succ_vlt p F ϖ hv.1 (teichPi_mem_Iinf p F ϖ) hg
  exact ⟨n + 1, h⟩

end ElementFacts

/-- `𝒴` does not depend on the choice of pseudo-uniformizer: any two pseudo-uniformizers
divide powers of each other in `O_F`, and Teichmüller is multiplicative.

Source: [Kedlaya-AWS §11.2-style]: "this is independent of the choice of ϖ, as for any
other choice ϖ', there is some n such that ϖ | (ϖ')^n and ϖ' | ϖ^n". -/
theorem Y_indep (ϖ' : PseudoUniformizer F) : Y p F ϖ = Y p F ϖ' := by
  have key : ∀ (α β : PseudoUniformizer F) (v : Spv (Ainf p F)), v ∈ Y p F α →
      ¬ v.vle ((p : Ainf p F) * teichPi p F β) 0 := by
    intro α β v hv hle
    have hprime : (v.supp).IsPrime := inferInstance
    rcases hprime.mem_or_mem ((v.mem_supp_iff _).mpr hle) with hp' | hβ
    · exact v_p_ne_zero hv ((v.mem_supp_iff _).mp hp')
    · obtain ⟨k, hk⟩ := exists_teichPi_pow_mem_span_teichPi p F β α
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hk
      have hpow : teichPi p F α ^ k ∈ v.supp := hc ▸ Ideal.mul_mem_left _ c hβ
      exact v_teichPi_ne_zero hv
        ((v.mem_supp_iff _).mp (hprime.mem_of_pow_mem _ hpow))
  ext v
  exact ⟨fun hv => ⟨hv.1, key ϖ ϖ' v hv⟩, fun hv => ⟨hv.1, key ϖ' ϖ v hv⟩⟩

private theorem frob_teichmuller (x : OF F) :
    frob p F (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p) := by
  show WittVector.frobenius _ = _
  rw [frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

private theorem frobeniusEquiv_pow_apply (m : ℕ) (x : OF F) :
    ((_root_.frobeniusEquiv (OF F) p) ^ m : RingAut (OF F)) x = x ^ p ^ m := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', RingAut.mul_apply, ih,
        show _root_.frobeniusEquiv (OF F) p (x ^ p ^ m) = (x ^ p ^ m) ^ p from rfl,
        ← pow_mul, ← pow_succ]

private theorem frob_zpow_teichmuller (j : ℤ) (x : OF F) :
    (frob p F ^ j : RingAut (Ainf p F)) (WittVector.teichmuller p x)
      = WittVector.teichmuller p
        ((_root_.frobeniusEquiv (OF F) p ^ j : RingAut (OF F)) x) := by
  induction j using Int.induction_on generalizing x with
  | zero => simp
  | succ j ih =>
      rw [zpow_add_one, zpow_add_one, RingAut.mul_apply, RingAut.mul_apply,
        show frob p F (WittVector.teichmuller p x)
          = WittVector.teichmuller p (_root_.frobeniusEquiv (OF F) p x) from
            frob_teichmuller p F x,
        ih]
  | pred j ih =>
      have hφinv : (frob p F).symm (WittVector.teichmuller p x)
          = WittVector.teichmuller p ((_root_.frobeniusEquiv (OF F) p).symm x) := by
        apply (frob p F).injective
        rw [RingEquiv.apply_symm_apply, frob_teichmuller]
        congr 1
        rw [show ((_root_.frobeniusEquiv (OF F) p).symm x) ^ p
            = _root_.frobeniusEquiv (OF F) p ((_root_.frobeniusEquiv (OF F) p).symm x)
          from rfl, RingEquiv.apply_symm_apply]
      rw [zpow_sub_one, zpow_sub_one, RingAut.mul_apply, RingAut.mul_apply,
        show ((frob p F : RingAut (Ainf p F))⁻¹) (WittVector.teichmuller p x)
          = (frob p F).symm (WittVector.teichmuller p x) from rfl, hφinv, ih,
        show ((_root_.frobeniusEquiv (OF F) p : RingAut (OF F))⁻¹) x
          = (_root_.frobeniusEquiv (OF F) p).symm x from rfl]

/-- `𝒴` is stable under the `φ^ℤ`-action.

Source: [SW, §12.2]: "The Frobenius automorphism ... preserves 𝒴". -/
theorem smul_mem_Y (g : Multiplicative ℤ) {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) :
    g • v ∈ Y p F ϖ := by
  refine ⟨smul_mem_spa_Ainf p F g hv.1, fun hle => ?_⟩
  have hsmul_vle : ∀ a b : Ainf p F, (g • v).vle a b ↔ v.vle (g⁻¹ • a) (g⁻¹ • b) := by
    intro a b
    change (comap (MulSemiringAction.toRingHom _ _ g⁻¹) v).vle a b ↔ _
    rw [comap_vle]
    rfl
  rw [hsmul_vle, smul_zero, smul_mul'] at hle
  set j : ℤ := Multiplicative.toAdd g⁻¹ with hj
  have hsmul : ∀ a : Ainf p F, g⁻¹ • a = (frob p F ^ j : RingAut (Ainf p F)) a := by
    intro a
    rw [← ofAdd_toAdd g⁻¹, ofAdd_zsmul_def]
  have hprime : (v.supp).IsPrime := inferInstance
  rcases hprime.mem_or_mem ((v.mem_supp_iff _).mpr hle) with hp' | hϖ'
  · refine v_p_ne_zero hv ((v.mem_supp_iff _).mp ?_)
    rwa [hsmul, map_natCast] at hp'
  · rw [hsmul, teichPi, frob_zpow_teichmuller] at hϖ'
    set b : OF F := (_root_.frobeniusEquiv (OF F) p ^ j : RingAut (OF F))
      (PseudoUniformizer.toOF F ϖ) with hb
    have hbpow : b ^ p ^ (-j).toNat = PseudoUniformizer.toOF F ϖ ^ p ^ j.toNat := by
      rw [hb, ← frobeniusEquiv_pow_apply p F ((-j).toNat), ← RingAut.mul_apply,
        ← zpow_natCast (_root_.frobeniusEquiv (OF F) p) ((-j).toNat), ← zpow_add,
        show ((-j).toNat : ℤ) + j = (j.toNat : ℤ) from by omega,
        zpow_natCast, frobeniusEquiv_pow_apply]
    have hmem : teichPi p F ϖ ^ p ^ j.toNat ∈ v.supp := by
      have h1 : WittVector.teichmuller p b ^ p ^ (-j).toNat ∈ v.supp :=
        Ideal.pow_mem_of_mem _ hϖ' _ (pow_pos (Fact.out : Nat.Prime p).pos _)
      rwa [← map_pow, hbpow, map_pow, ← teichPi] at h1
    exact v_teichPi_ne_zero hv
      ((v.mem_supp_iff _).mp (hprime.mem_of_pow_mem _ hmem))

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

private theorem pow_le_pow_iff_cross {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {x y : Γ₀} {a b c d : ℕ} (hcross : a * d = c * b) (hb : b ≠ 0) (hd : d ≠ 0) :
    x ^ d ≤ y ^ c ↔ x ^ b ≤ y ^ a := by
  rw [← pow_le_pow_iff_left₀ (zero_le') (zero_le') hb (a := x ^ d) (b := y ^ c),
    ← pow_le_pow_iff_left₀ (zero_le') (zero_le') hd (a := x ^ b) (b := y ^ a),
    ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm d b, ← hcross]

/-- The cross-multiplication identity behind representation-independence: for `0 < q`
and `q = a/b` with `0 < b`, one has `a·q.den = q.num.toNat·b` in `ℕ`. -/
private theorem cross_eq {q : ℚ} (hq : 0 < q) {a b : ℕ} (hb : 0 < b)
    (hab : q = (a : ℚ) / b) : a * q.den = q.num.toNat * b := by
  have h1 : (a : ℚ) / b = (q.num : ℚ) / q.den := by rw [← hab, Rat.num_div_den]
  rw [div_eq_div_iff (by exact_mod_cast hb.ne' : (b : ℚ) ≠ 0)
    (by exact_mod_cast q.den_pos.ne' : (q.den : ℚ) ≠ 0)] at h1
  have h2 : ((q.num.toNat : ℤ) : ℚ) = (q.num : ℚ) := by
    rw [Int.toNat_of_nonneg (Rat.num_pos.mpr hq).le]
  exact_mod_cast h2 ▸ h1

/-- Representation-independence of `KGE`: for any fraction `a/b = q` with `b > 0`,
`KGE q v ↔ v([ϖ]^b) ≤ v(p^a)`. This is the denominator-clearing workhorse
(cross-multiplication inside the value monoid). -/
theorem KGE_iff {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q)
    {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) :
    KGE p F ϖ q v ↔ v.vle (teichPi p F ϖ ^ b) ((p : Ainf p F) ^ a) := by
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  rw [KGE, hbridge, hbridge, map_pow, map_pow, map_pow, map_pow]
  exact pow_le_pow_iff_cross (cross_eq hq hb hab) hb.ne' q.den_nz

/-- Representation-independence of `KLE`, as for `KGE_iff`. -/
theorem KLE_iff {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q)
    {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) :
    KLE p F ϖ q v ↔ v.vle ((p : Ainf p F) ^ a) (teichPi p F ϖ ^ b) := by
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  have hcross := cross_eq hq hb hab
  have hnum : q.num.toNat ≠ 0 :=
    fun h0 => absurd (Rat.num_pos.mpr hq) (Int.toNat_eq_zero.mp h0).not_gt
  have ha : a ≠ 0 := by
    intro rfl
    simp only [zero_mul] at hcross
    have hne : q.num.toNat * b ≠ 0 := Nat.mul_ne_zero hnum hb.ne'
    omega
  rw [KLE, hbridge, hbridge, map_pow, map_pow, map_pow, map_pow]
  exact pow_le_pow_iff_cross
    (show b * q.num.toNat = q.den * a from by rw [mul_comm b, mul_comm q.den]; exact hcross.symm)
    ha hnum

/-- Totality: at every positive rational `q`, either `κ(v) ≥ q` or `κ(v) ≤ q`
(linearity of the valuative order). -/
theorem KGE_or_KLE {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q) :
    KGE p F ϖ q v ∨ KLE p F ϖ q v :=
  v.vle_total _ _

/-- Order-incompatibility: `κ(v) ≤ q'` and `κ(v) ≥ q` cannot both hold when `q' < q`
(on `𝒴`, where `0 < v(p) < 1`). Cross-multiply and use the exponent-flip rule
`v(p)^m ≤ v(p)^k → m ≥ k`.

This single lemma drives all window disjointness. -/
theorem not_KGE_of_KLE_of_lt {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {q q' : ℚ}
    (hq' : 0 < q') (hlt : q' < q) (hle : KLE p F ϖ q' v) :
    ¬ KGE p F ϖ q v := by
  intro hge
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  set X := ValuativeRel.valuation (Ainf p F) (teichPi p F ϖ) with hX
  set Ypv := ValuativeRel.valuation (Ainf p F) ((p : Ainf p F)) with hYpv
  have hy0 : (0 : _) < Ypv := by
    refine zero_lt_iff.mpr (fun h0 => v_p_ne_zero hv ?_)
    rw [hbridge]
    simp only [map_zero, le_zero_iff]
    exact h0
  have hy1 : Ypv < 1 := by
    obtain ⟨h1, h2⟩ := vlt_p_one hv
    rw [hbridge] at h1 h2
    rw [map_one] at h1 h2
    exact lt_of_le_not_ge h1 h2
  have hKLE : Ypv ^ q'.num.toNat ≤ X ^ q'.den := by
    have := hle
    rw [KLE, hbridge, map_pow, map_pow] at this
    exact this
  have hKGE : X ^ q.den ≤ Ypv ^ q.num.toNat := by
    have := hge
    rw [KGE, hbridge, map_pow, map_pow] at this
    exact this
  have hchain : Ypv ^ (q'.num.toNat * q.den) ≤ Ypv ^ (q.num.toNat * q'.den) := by
    calc Ypv ^ (q'.num.toNat * q.den) = (Ypv ^ q'.num.toNat) ^ q.den := pow_mul _ _ _
      _ ≤ (X ^ q'.den) ^ q.den :=
        pow_le_pow_left' hKLE q.den
      _ = (X ^ q.den) ^ q'.den := by rw [← pow_mul, mul_comm, pow_mul]
      _ ≤ (Ypv ^ q.num.toNat) ^ q'.den :=
        pow_le_pow_left' hKGE q'.den
      _ = Ypv ^ (q.num.toNat * q'.den) := (pow_mul _ _ _).symm
  have hflip : q.num.toNat * q'.den ≤ q'.num.toNat * q.den :=
    (pow_le_pow_iff_right_of_lt_one₀ hy0 hy1).mp hchain
  have hqlt : q'.num.toNat * q.den < q.num.toNat * q'.den := by
    have h1 : (q'.num : ℚ) / q'.den < (q.num : ℚ) / q.den := by
      rw [Rat.num_div_den, Rat.num_div_den]; exact hlt
    rw [div_lt_div_iff₀ (by exact_mod_cast q'.den_pos) (by exact_mod_cast q.den_pos)] at h1
    have h2 : ((q'.num.toNat : ℤ) : ℚ) = (q'.num : ℚ) := by
      rw [Int.toNat_of_nonneg (Rat.num_pos.mpr hq').le]
    have h3 : ((q.num.toNat : ℤ) : ℚ) = (q.num : ℚ) := by
      rw [Int.toNat_of_nonneg (Rat.num_pos.mpr (hq'.trans hlt)).le]
    exact_mod_cast h2 ▸ h3 ▸ h1
  omega

/-! ### The windows U_n, V_n (Kedlaya, AWS Remark 3.1.9) -/

/-- The constant `c := (p+1)/2 ∈ (1, p) ∩ ℚ` of [Kedlaya-AWS, Rem. 3.1.9] (any rational
in `(1,p)` works; we fix this one). Valid for every prime, including `p = 2`
(`c = 3/2`). Stated with its own explicit binder (independent of the section
variables). -/
def cFF (p : ℕ) : ℚ := ((p : ℚ) + 1) / 2

theorem one_lt_cFF {p : ℕ} (hp : 1 < p) : 1 < cFF p := by
  have : (1 : ℚ) < p := by exact_mod_cast hp
  rw [cFF, lt_div_iff₀ (by norm_num)]
  linarith

theorem cFF_lt_p {p : ℕ} (hp : 1 < p) : cFF p < (p : ℚ) := by
  have : (1 : ℚ) < p := by exact_mod_cast hp
  rw [cFF, div_lt_iff₀ (by norm_num)]
  linarith

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

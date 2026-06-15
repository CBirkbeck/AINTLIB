import HasseWeil.FormalGroup.EvalGroup
import HasseWeil.FormalGroup.Hom
import HasseWeil.FormalGroup.MulByNat
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The associated groups `Ĝ_a(M)` and `Ĝ_m(M)` (Silverman IV.3.1)

For a formal group law `F` over a complete local ring `(R, M)`, we have the abelian
group `F(M)` on the maximal ideal (built in `EvalGroup.lean`).

This file specialises `F(M)` to the two standard formal group laws and records the
content of Silverman's Proposition IV.3.1:

* **`Ĝ_a(M) = (M, +)`** — For the additive formal group `F(X, Y) = X + Y`, the operation
  `evalAdd x y` is the ordinary ring addition, and `evalNeg x` is the ordinary
  negation.

* **`Ĝ_m(M) ≅ (1 + M, ·)`** — For the multiplicative formal group
  `F(X, Y) = X + Y + XY`, the operation `evalAdd x y = x + y + x·y` corresponds,
  via the bijection `x ↦ 1 + x`, to ordinary multiplication on `1 + M`.

## Main results

* `evalAdd_additiveFormalGroup`: `(Ĝ_a).evalAdd x y = x + y`.
* `evalNeg_additiveFormalGroup`: `(Ĝ_a).evalNeg x = -x`.
* `evalAdd_multiplicativeFormalGroup`: `(Ĝ_m).evalAdd x y = x + y + x·y`.
* `evalAdd_multiplicativeFormalGroup_one_add`:
  `(1 + evalAdd (Ĝ_m) x y) = (1 + x)·(1 + y)`, realising the bijection with the
  multiplicative group `1 + M`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.3.1.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

open MvPowerSeries IsLocalRing

section Operations

variable {R : Type*} [CommRing R] [IsLocalRing R] [UniformSpace R]

/-! ### The additive formal group: `Ĝ_a(M) = (M, +)`

The operation lemmas below drop the `IsUniformAddGroup`/`IsTopologicalRing`/
`IsLinearTopology`/`T2Space`/`CompleteSpace` hypotheses that the general `F(M)`
construction needs: the proofs reduce the formal-group law to its underlying
polynomial and apply `MvPolynomial.eval₂_add`, which is unconditional. -/

/-- **`Ĝ_a(M)` has `+_F = +`** (Silverman IV.3.1.1, operation form).

For the additive formal group `F(X, Y) = X + Y` and `x, y ∈ M`, the formal-group
operation `evalAdd x y` coincides with the underlying ring addition. -/
theorem evalAdd_additiveFormalGroup (x y : maximalIdeal R) :
    (additiveFormalGroup R).evalAdd x y = x.1 + y.1 := by
  change MvPowerSeries.eval₂ (RingHom.id R) (![x.1, y.1] : Fin 2 → R)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) = x.1 + y.1
  have hcoe :
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        ((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) :
          MvPowerSeries (Fin 2) R) := by
    push_cast; rfl
  rw [hcoe, MvPowerSeries.eval₂_coe, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  simp

/-! ### The multiplicative formal group: `Ĝ_m(M) ≅ (1 + M, ·)` -/

/-- **`Ĝ_m(M)` has `x +_F y = x + y + x·y`** (Silverman IV.3.1.2, operation form).

For the multiplicative formal group `F(X, Y) = X + Y + XY` and `x, y ∈ M`, the
formal-group operation evaluates to `x + y + x·y`. -/
theorem evalAdd_multiplicativeFormalGroup (x y : maximalIdeal R) :
    (multiplicativeFormalGroup R).evalAdd x y = x.1 + y.1 + x.1 * y.1 := by
  change MvPowerSeries.eval₂ (RingHom.id R) (![x.1, y.1] : Fin 2 → R)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) = _
  have hcoe :
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 +
          MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        ((MvPolynomial.X 0 + MvPolynomial.X 1 +
            MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) :
          MvPowerSeries (Fin 2) R) := by
    push_cast; rfl
  rw [hcoe, MvPowerSeries.eval₂_coe, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  simp

/-- **The bijection `Ĝ_m(M) ↔ (1 + M, ·)`** (Silverman IV.3.1.2).

The map `x ↦ 1 + x` between `M` and `1 + M` sends the formal-group operation
`x +_F y = x + y + x·y` to ordinary multiplication:
`1 + (x +_F y) = (1 + x)·(1 + y)`. -/
theorem evalAdd_multiplicativeFormalGroup_one_add (x y : maximalIdeal R) :
    1 + (multiplicativeFormalGroup R).evalAdd x y = (1 + x.1) * (1 + y.1) := by
  rw [evalAdd_multiplicativeFormalGroup x y]
  ring

end Operations

/-! ### Formal negation for the additive formal group

The negation lemma does need the adic-topology hypotheses, because it is deduced
from `evalAdd_evalNeg`, which is proved by pushing the functional-equation identity
`fAdd F X inverse = 0` through the `MvPowerSeries → R` evaluation map. -/

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
variable [IsLinearTopology R R] [T2Space R] [CompleteSpace R]

/-- **`Ĝ_a(M)` has `-_F = -`** (Silverman IV.3.1.1).

For the additive formal group, the formal-group negation `evalNeg x` coincides
with the underlying ring negation. -/
theorem evalNeg_additiveFormalGroup
    (hAdic : IsAdic (maximalIdeal R))
    (x : maximalIdeal R) :
    (additiveFormalGroup R).evalNeg x = -x.1 := by
  have hinv := (additiveFormalGroup R).evalAdd_evalNeg hAdic x
  rw [evalAdd_additiveFormalGroup x
      ⟨(additiveFormalGroup R).evalNeg x,
        (additiveFormalGroup R).evalNeg_mem hAdic x⟩] at hinv
  exact eq_neg_of_add_eq_zero_right hinv

/-! ### The filtration `F(M^n)` (Silverman IV.3 definition)

For each `n : ℕ`, the set `M^n ⊆ M` is closed under the formal group operation
`+_F` and negation `-_F`, yielding a subgroup of `F(M)`. This gives a decreasing
filtration
  `F(M) = F(M^0) = F(M^1) ⊇ F(M^2) ⊇ F(M^3) ⊇ …`.

(Note: in Silverman's original definition the filtration starts at `n = 1`, but
with the subtype setup here `M^0 = R` and `M^1 = M` both give the whole group, so
we can index from `n = 0` without loss.)

The key mechanism is that `F(X, Y) ≡ X + Y (mod (X, Y)^2)`, so for
`x, y ∈ M^n` each monomial coefficient contributes a term lying in `M^n` (from
linear terms) or in `M^{2n} ⊆ M^n` (from higher-order terms). -/

omit [IsUniformAddGroup R] [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- Each power `(maximalIdeal R)^n` is closed in the `M`-adic topology: it is one
of the basic open neighbourhoods of `0`, hence also closed. -/
lemma maximalIdeal_pow_isClosed
    (hAdic : IsAdic (maximalIdeal R)) (n : ℕ) :
    IsClosed (((maximalIdeal R) ^ n : Ideal R) : Set R) := by
  obtain ⟨hopen, _⟩ := isAdic_iff.mp hAdic
  exact AddSubgroup.isClosed_of_isOpen (G := R)
    (((maximalIdeal R) ^ n).toAddSubgroup) (hopen n)

/-- **Closure of `+_F` on `M^n`**: if `x.1 ∈ M^n` and `y.1 ∈ M^n`, then
`evalAdd F x y ∈ M^n`.

Every term `coeff d F.toSeries * ∏ s, (![x,y] s)^(d s)` of the `hasSum`
decomposition lies in `M^n`:
  * `d = 0`: `coeff 0 F.toSeries = 0` (constant coefficient of a formal group law).
  * `d ≠ 0`: pick any `s` with `d s ≥ 1`, then `(![x,y] s)^(d s) ∈ M^n` by
    `Ideal.pow_mem_of_mem`, so the whole product is in `M^n`. -/
theorem FormalGroup.evalAdd_pow_mem
    (hAdic : IsAdic (maximalIdeal R))
    (F : FormalGroup R) (n : ℕ) {x y : maximalIdeal R}
    (hx : x.1 ∈ (maximalIdeal R) ^ n) (hy : y.1 ∈ (maximalIdeal R) ^ n) :
    F.evalAdd x y ∈ (maximalIdeal R) ^ n := by
  have ha := hasEval_of_mem_maximalIdeal hAdic (a := ![x.1, y.1])
    (by intro i; fin_cases i <;> simp [x.2, y.2])
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid ha F.toSeries
  change MvPowerSeries.eval₂ (RingHom.id R) ![x.1, y.1] F.toSeries ∈ _
  apply (maximalIdeal_pow_isClosed hAdic n).mem_of_tendsto hsum
  filter_upwards with N
  apply ((maximalIdeal R) ^ n).sum_mem
  intro d _hd
  change (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
      (d.prod fun s e => (![x.1, y.1]) s ^ e) ∈ _
  simp only [RingHom.id_apply]
  by_cases hd : d = 0
  · subst hd
    have hc0 : MvPowerSeries.coeff (R := R) (0 : Fin 2 →₀ ℕ) F.toSeries = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact HasseWeil.FG.constantCoeff_FG_toSeries F
    rw [hc0, zero_mul]
    exact ((maximalIdeal R) ^ n).zero_mem
  · apply ((maximalIdeal R) ^ n).mul_mem_left
    have hne : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext (fun s => by simpa using h s))
    obtain ⟨s, hs⟩ := hne
    have hs_mem : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [Finsupp.prod]
    refine ((maximalIdeal R) ^ n).prod_mem (s := d.support) hs_mem ?_
    have hds : 0 < d s := Nat.pos_of_ne_zero hs
    have has : (![x.1, y.1] : Fin 2 → R) s ∈ (maximalIdeal R) ^ n := by
      fin_cases s <;> simp [hx, hy]
    exact Ideal.pow_mem_of_mem _ has _ hds

/-- **Closure of `-_F` on `M^n`**: if `x.1 ∈ M^n`, then `evalNeg F x ∈ M^n`.

Each term `coeff k F.inverse * x.1 ^ k` of the `hasSum` for
`PowerSeries.eval₂ id x.1 F.inverse` lies in `M^n`:
  * `k = 0`: `coeff 0 F.inverse = 0`.
  * `k ≥ 1`: `x.1 ^ k ∈ M^n` by `Ideal.pow_mem_of_mem`. -/
theorem FormalGroup.evalNeg_pow_mem
    (hAdic : IsAdic (maximalIdeal R))
    (F : FormalGroup R) (n : ℕ) {x : maximalIdeal R}
    (hx : x.1 ∈ (maximalIdeal R) ^ n) :
    F.evalNeg x ∈ (maximalIdeal R) ^ n := by
  change PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse ∈ _
  have ha : PowerSeries.HasEval x.1 :=
    isTopologicallyNilpotent_of_mem_maximalIdeal hAdic x.2
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := PowerSeries.hasSum_eval₂ hcid ha F.inverse
  apply (maximalIdeal_pow_isClosed hAdic n).mem_of_tendsto hsum
  filter_upwards with N
  apply ((maximalIdeal R) ^ n).sum_mem
  intro k _hk
  change (RingHom.id R) (PowerSeries.coeff k F.inverse) * x.1 ^ k ∈ _
  simp only [RingHom.id_apply]
  by_cases hk : k = 0
  · subst hk
    rw [F.inverse_coeff_zero, zero_mul]
    exact ((maximalIdeal R) ^ n).zero_mem
  · apply ((maximalIdeal R) ^ n).mul_mem_left
    exact Ideal.pow_mem_of_mem _ hx _ (Nat.pos_of_ne_zero hk)

/-- **`F(M^n)` as a subgroup of `F(M)`** (Silverman IV.3 definition).

The subgroup of `F(M)` whose underlying set is `M^n`. This builds the decreasing
filtration `F(M) ⊇ F(M²) ⊇ F(M³) ⊇ …` on the formal-group associated to a
complete local ring. -/
noncomputable def FormalGroup.evalGroup_powerIdeal
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) (n : ℕ) :
    AddSubgroup (F.EvalGroup hAdic) where
  carrier := {x : F.EvalGroup hAdic | x.val.1 ∈ (maximalIdeal R) ^ n}
  zero_mem' := by
    change (0 : R) ∈ (maximalIdeal R) ^ n
    exact ((maximalIdeal R) ^ n).zero_mem
  add_mem' := fun {x y} hx hy => F.evalAdd_pow_mem hAdic n hx hy
  neg_mem' := fun {x} hx => F.evalNeg_pow_mem hAdic n hx

/-- The `F(M^n)` filtration is monotone: `m ≤ n ⇒ F(M^n) ⊆ F(M^m)`. -/
theorem FormalGroup.evalGroup_powerIdeal_mono
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {m n : ℕ} (hmn : m ≤ n) :
    F.evalGroup_powerIdeal hAdic n ≤ F.evalGroup_powerIdeal hAdic m := by
  intro x hx
  exact (Ideal.pow_le_pow_right hmn : (maximalIdeal R) ^ n ≤ _) hx

/-! ### The nsmul/formal-[n] bridge

The `AddGroup.ofLeftAxioms` construction uses the default `nsmulRec` for
scalar multiplication by naturals. On `F.EvalGroup hAdic`, `n • x` therefore
corresponds (at the underlying ring level) to the formal-group multiplication
series `[n](T) = mulByNatSeries F n` evaluated at `x.val.1`. -/

/-- **nsmul/formal-[n] bridge**. On the wrapper `F.EvalGroup hAdic`, the
`AddGroup` scalar action `n • x` agrees (at the underlying ring level) with
`PowerSeries.eval₂ (RingHom.id R) x.val.1 (F.mulByNatHom n).toSeries`. -/
theorem FormalGroup.EvalGroup.nsmul_val
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
    (n : ℕ) (x : F.EvalGroup hAdic) :
    (n • x).val.1 =
      PowerSeries.eval₂ (RingHom.id R) x.val.1 (F.mulByNatHom n).toSeries := by
  induction n with
  | zero =>
    rw [zero_nsmul, F.mulByNatHom_zero_toSeries]
    -- Goal: (0 : F.EvalGroup hAdic).val.1 = PowerSeries.eval₂ id x.val.1 0.
    change (0 : R) = PowerSeries.eval₂ (RingHom.id R) x.val.1 (0 : PowerSeries R)
    rw [show (0 : PowerSeries R) = ((0 : Polynomial R) : PowerSeries R) from by simp,
        PowerSeries.eval₂_coe]
    simp
  | succ n ih =>
    -- LHS: ((n+1) • x).val.1 = (n • x + x).val.1 = F.evalAdd (n • x).val x.val.
    rw [succ_nsmul, FormalGroup.EvalGroup.val_add]
    -- RHS: unfold mulByNatHom_toSeries, then mulByNatSeries (n+1) = fAdd F (mulByNatSeries F n) X.
    rw [F.mulByNatHom_toSeries]
    change F.evalAdd (n • x).val x.val =
      PowerSeries.eval₂ (RingHom.id R) x.val.1
        (HasseWeil.FG.mulByNatSeries F (n + 1))
    -- mulByNatSeries F (n+1) = fAdd F (mulByNatSeries F n) X
    --                        = subst ![mulByNatSeries F n, X] F.toSeries (by def of fAdd).
    change F.evalAdd (n • x).val x.val =
      PowerSeries.eval₂ (RingHom.id R) x.val.1
        (HasseWeil.FG.fAdd F (HasseWeil.FG.mulByNatSeries F n) PowerSeries.X)
    -- `fAdd F f g = MvPowerSeries.subst ![f, g] F.toSeries` (definitional).
    -- Apply the substitution bridge.
    let a : Fin 2 → MvPowerSeries Unit R :=
      ![HasseWeil.FG.mulByNatSeries F n, PowerSeries.X]
    have ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0 := by
      intro s
      fin_cases s
      · -- a 0 = mulByNatSeries F n.
        change MvPowerSeries.constantCoeff
          (HasseWeil.FG.mulByNatSeries F n : PowerSeries R) = 0
        exact HasseWeil.FG.constantCoeff_mulByNatSeries F n
      · -- a 1 = PowerSeries.X.
        change MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0
        change PowerSeries.constantCoeff (R := R) PowerSeries.X = 0
        simp
    have ha : MvPowerSeries.HasSubst a :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => ha0 s)
    have hb_mem : ∀ _ : Unit, x.val.1 ∈ maximalIdeal R := fun _ => x.val.2
    -- Bridge: eval₂ id (fun _ => x) (subst a F.toSeries) =
    --         eval₂ id (fun s => eval₂ id (fun _ => x) (a s)) F.toSeries.
    have bridge :=
      eval₂_subst_bridge hAdic ha0 ha (b := fun _ : Unit => x.val.1) hb_mem F.toSeries
    -- The RHS of bridge is evaluated at the pair (eval_x (mulByNatSeries F n), x).
    -- Using the induction hypothesis, this becomes (![(n • x).val.1, x.val.1]).
    -- Compute the two functions and match.
    have hfun : (fun s : Fin 2 =>
          MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => x.val.1) (a s)) =
        ![(n • x).val.1, x.val.1] := by
      funext s
      fin_cases s
      · -- s = 0: eval₂ id x (mulByNatSeries F n) = (n • x).val.1 by ih.
        change MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => x.val.1)
            (HasseWeil.FG.mulByNatSeries F n : PowerSeries R) = ((n • x).val.1 : R)
        change PowerSeries.eval₂ (RingHom.id R) x.val.1
            (HasseWeil.FG.mulByNatSeries F n) = _
        have ih' : (n • x).val.1 =
            PowerSeries.eval₂ (RingHom.id R) x.val.1
              (F.mulByNatHom n).toSeries := ih
        rw [F.mulByNatHom_toSeries] at ih'
        exact ih'.symm
      · -- s = 1: eval₂ id x PowerSeries.X = x.val.1.
        change MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => x.val.1)
            (PowerSeries.X : PowerSeries R) = x.val.1
        change PowerSeries.eval₂ (RingHom.id R) x.val.1 PowerSeries.X = _
        rw [PowerSeries.eval₂_X]
    -- Match the bridge RHS to F.evalAdd (n • x).val x.val.
    rw [hfun] at bridge
    -- bridge's LHS is eval_x (subst a F.toSeries) = eval_x (fAdd F ...).
    -- bridge's RHS is eval₂ id ![(n•x), x] F.toSeries = F.evalAdd (n • x).val x.val.
    change _ = PowerSeries.eval₂ (RingHom.id R) x.val.1
      (MvPowerSeries.subst a F.toSeries)
    change _ = MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => x.val.1)
      (MvPowerSeries.subst a F.toSeries)
    rw [bridge]
    rfl

/-! ### The graded-isomorphism congruence (Silverman IV.3.2.a)

The core content of Silverman's Proposition IV.3.2(a) is the congruence
`F(x, y) ≡ x + y  (mod M^(n+1))`  for  `x, y ∈ M^n`,

which underpins the graded isomorphism `F(M^n) / F(M^(n+1)) ≅ M^n / M^(n+1)`.
The proof decomposes the `hasSum` of `eval₂` into its "low-degree" part
(indices with `d 0 + d 1 ≤ 1`) and the remaining higher-order tail (indices
with `d 0 + d 1 ≥ 2`). The low-degree part equals `x + y` by the unit axioms
`coeff_10 F = coeff_01 F = 1` and `constantCoeff F.toSeries = 0`; the tail
sits in `M^(2n) ⊆ M^(n+1)`. -/

/-- The low-degree index finset `{0, single 0 1, single 1 1}` used in the
decomposition of `F(x, y) = x + y + (higher-order terms)`. -/
private noncomputable def lowDegFinset : Finset (Fin 2 →₀ ℕ) :=
  {0, Finsupp.single 0 1, Finsupp.single 1 1}

/-- The three elements of `lowDegFinset` are distinct. -/
private lemma lowDegFinset_mem_iff (d : Fin 2 →₀ ℕ) :
    d ∈ lowDegFinset ↔
      d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
  unfold lowDegFinset
  simp [Finset.mem_insert, Finset.mem_singleton]

private lemma single_zero_one_ne_zero :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

private lemma single_one_one_ne_zero :
    (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private lemma single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

/-- If `d ∉ lowDegFinset`, then `d 0 + d 1 ≥ 2`. -/
private lemma two_le_sum_of_not_mem_lowDeg {d : Fin 2 →₀ ℕ}
    (hd : d ∉ lowDegFinset) : 2 ≤ d 0 + d 1 := by
  by_contra h
  push_neg at h
  -- h : d 0 + d 1 < 2, so d 0 + d 1 ∈ {0, 1}.
  apply hd
  rw [lowDegFinset_mem_iff]
  have hsum : d 0 + d 1 = 0 ∨ d 0 + d 1 = 1 := by omega
  rcases hsum with hsum | hsum
  · -- d 0 + d 1 = 0 ⇒ d = 0.
    have hd0 : d 0 = 0 := by omega
    have hd1 : d 1 = 0 := by omega
    left; ext i; fin_cases i <;> simp [hd0, hd1]
  · -- d 0 + d 1 = 1.
    rcases Nat.eq_zero_or_pos (d 0) with hd0 | hd0
    · have hd1 : d 1 = 1 := by omega
      right; right; ext i; fin_cases i <;> simp [hd0, hd1]
    · have hd0' : d 0 = 1 := by omega
      have hd1 : d 1 = 0 := by omega
      right; left; ext i; fin_cases i <;> simp [hd0', hd1]

/-- **The key congruence for the graded isomorphism** (Silverman IV.3.2.a).

For `x, y ∈ M^n` with `n ≥ 1`, the formal-group operation `F(x, y)` differs
from ordinary addition `x + y` by an element of `M^(n+1)`:
`F(x, y) ≡ x + y  (mod M^(n+1))`.

This is the content underlying the graded isomorphism
`F(M^n) / F(M^(n+1)) ≅ M^n / M^(n+1)`.

**Proof sketch.** Expand `F(x, y) = eval₂ id ![x, y] F.toSeries` as a `hasSum`
over `d : Fin 2 →₀ ℕ`. Split the index set into the "low-degree" finset
`S = {0, single 0 1, single 1 1}` and its complement. The low-degree sum is
`0 + x + y = x + y` (using `constantCoeff F = 0`, `coeff_10 F = coeff_01 F = 1`).
The tail sum lies in `M^(n+1)` because for every `d` with `d 0 + d 1 ≥ 2`,
the monomial `x^(d 0) * y^(d 1)` sits in `M^(n*(d 0 + d 1)) ⊆ M^(2n) ⊆ M^(n+1)`. -/
theorem FormalGroup.evalAdd_sub_add_mem_pow_succ
    (hAdic : IsAdic (maximalIdeal R))
    (F : FormalGroup R) {n : ℕ} (hn : 1 ≤ n)
    {x y : maximalIdeal R}
    (hx : x.1 ∈ (maximalIdeal R) ^ n) (hy : y.1 ∈ (maximalIdeal R) ^ n) :
    F.evalAdd x y - (x.1 + y.1) ∈ (maximalIdeal R) ^ (n + 1) := by
  -- Unfold evalAdd and get the hasSum decomposition.
  have ha := hasEval_of_mem_maximalIdeal hAdic (a := ![x.1, y.1])
    (by intro i; fin_cases i <;> simp [x.2, y.2])
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid ha F.toSeries
  -- Abbreviate the general term.
  set term : (Fin 2 →₀ ℕ) → R := fun d =>
    (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
      (d.prod fun s e => (![x.1, y.1] : Fin 2 → R) s ^ e) with hterm
  change F.evalAdd x y - (x.1 + y.1) ∈ _
  -- Compute ∑ d ∈ lowDegFinset, term d = x + y.
  have hsum_S : ∑ d ∈ lowDegFinset, term d = x.1 + y.1 := by
    have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 :=
      single_zero_ne_single_one
    rw [lowDegFinset, Finset.sum_insert (by
          simp [Finset.mem_insert, Finset.mem_singleton, single_zero_one_ne_zero.symm,
                single_one_one_ne_zero.symm]),
        Finset.sum_insert (by simp [Finset.mem_singleton, h01]),
        Finset.sum_singleton]
    -- Term at d = 0.
    have hterm_zero : term 0 = 0 := by
      simp only [hterm, Finsupp.prod_zero_index, mul_one, RingHom.id_apply]
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact HasseWeil.FG.constantCoeff_FG_toSeries F
    -- Term at d = single 0 1.
    have hterm_10 : term (Finsupp.single (0 : Fin 2) 1) = x.1 := by
      simp only [hterm, RingHom.id_apply, HasseWeil.FG.FormalGroup.coeff_10,
        Finsupp.prod_single_index, pow_zero, pow_one,
        Matrix.cons_val_zero, one_mul]
    -- Term at d = single 1 1.
    have hterm_01 : term (Finsupp.single (1 : Fin 2) 1) = y.1 := by
      simp only [hterm, RingHom.id_apply, HasseWeil.FG.FormalGroup.coeff_01,
        Finsupp.prod_single_index, pow_zero, pow_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
    rw [hterm_zero, hterm_10, hterm_01, zero_add]
  -- Shift the tendsto by -(x + y).
  have hsum_term : HasSum term (F.evalAdd x y) := hsum
  have htendsto :
      Filter.Tendsto (fun N : Finset (Fin 2 →₀ ℕ) => (∑ d ∈ N, term d) - (x.1 + y.1))
        Filter.atTop (nhds (F.evalAdd x y - (x.1 + y.1))) :=
    (hsum_term : Filter.Tendsto _ _ _).sub_const _
  -- Apply IsClosed.mem_of_tendsto on M^(n+1), which is closed.
  apply (maximalIdeal_pow_isClosed hAdic (n + 1)).mem_of_tendsto htendsto
  -- For each N ⊇ lowDegFinset, the partial difference lies in M^(n+1).
  filter_upwards [Filter.eventually_ge_atTop lowDegFinset] with N hN
  -- Rewrite partial sum difference as a sum over N \ S.
  have hrewrite : (∑ d ∈ N, term d) - (x.1 + y.1) = ∑ d ∈ N \ lowDegFinset, term d := by
    rw [← hsum_S, ← Finset.sum_sdiff hN, add_sub_cancel_right]
  rw [hrewrite]
  -- Each term in N \ lowDegFinset lies in M^(n+1).
  apply ((maximalIdeal R) ^ (n + 1)).sum_mem
  intro d hd
  rw [Finset.mem_sdiff] at hd
  obtain ⟨_, hd_not_low⟩ := hd
  have hd_sum : 2 ≤ d 0 + d 1 := two_le_sum_of_not_mem_lowDeg hd_not_low
  simp only [hterm, RingHom.id_apply]
  apply ((maximalIdeal R) ^ (n + 1)).mul_mem_left
  -- Show x^(d 0) * y^(d 1) ∈ M^(n+1).
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  -- x^(d 0) ∈ M^(n * d 0) and y^(d 1) ∈ M^(n * d 1).
  have hxpow : x.1 ^ (d 0) ∈ (maximalIdeal R) ^ (n * d 0) := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow hx (d 0)
  have hypow : y.1 ^ (d 1) ∈ (maximalIdeal R) ^ (n * d 1) := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow hy (d 1)
  -- Product lies in M^(n*(d 0) + n*(d 1)) = M^(n*(d 0 + d 1)).
  have hprod_mem : x.1 ^ (d 0) * y.1 ^ (d 1) ∈
      (maximalIdeal R) ^ (n * d 0 + n * d 1) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hxpow hypow
  -- M^(n*(d 0 + d 1)) ⊆ M^(n+1) since n*(d 0 + d 1) ≥ 2n ≥ n + 1.
  have hbound : n + 1 ≤ n * d 0 + n * d 1 := by
    have : n + n ≤ n * d 0 + n * d 1 := by
      calc n + n = n * 2 := by ring
        _ ≤ n * (d 0 + d 1) := Nat.mul_le_mul_left n hd_sum
        _ = n * d 0 + n * d 1 := by ring
    omega
  exact (Ideal.pow_le_pow_right hbound) hprod_mem

/-- **`evalNeg` inverts `+` modulo `M^(n+1)`** (the additive analogue of the
graded-isomorphism congruence for negation).

For `x ∈ M^n` with `n ≥ 1`, the formal-group negation `evalNeg F x` differs
from ordinary negation `-x` by an element of `M^(n+1)`:
`F.evalNeg x ≡ -x  (mod M^(n+1))`, i.e., `F.evalNeg x + x ∈ M^(n+1)`.

This follows from applying the congruence `F(u, v) ≡ u + v (mod M^(n+1))` to
`u := x` and `v := F.evalNeg x` (which lies in `M^n`), noting that
`F(x, F.evalNeg x) = 0` by the inverse axiom. -/
theorem FormalGroup.evalNeg_add_mem_pow_succ
    (hAdic : IsAdic (maximalIdeal R))
    (F : FormalGroup R) {n : ℕ} (hn : 1 ≤ n)
    {x : maximalIdeal R} (hx : x.1 ∈ (maximalIdeal R) ^ n) :
    F.evalNeg x + x.1 ∈ (maximalIdeal R) ^ (n + 1) := by
  -- Let v = F.evalNeg x ∈ M^n.
  have hux : F.evalNeg x ∈ (maximalIdeal R) ^ n := F.evalNeg_pow_mem hAdic n hx
  -- Apply the congruence F(u, v) ≡ u + v (mod M^(n+1)) with u = x, v = F.evalNeg x.
  have hcong :=
    F.evalAdd_sub_add_mem_pow_succ hAdic hn
      (x := x) (y := ⟨F.evalNeg x, F.evalNeg_mem hAdic x⟩) hx hux
  -- But F.evalAdd x (F.evalNeg x) = 0 by the inverse axiom.
  have hinv := F.evalAdd_evalNeg hAdic x
  simp only at hcong
  rw [hinv, zero_sub] at hcong
  -- hcong : -(x.1 + F.evalNeg x) ∈ M^(n+1). Rewrite the argument using add_comm.
  have hneg : F.evalNeg x + x.1 = -(-(x.1 + F.evalNeg x)) := by ring
  rw [hneg]
  exact ((maximalIdeal R) ^ (n + 1)).neg_mem hcong

/-! ### The graded AddMonoidHom `F(M^n) → R / M^(n+1)` (T-IV-3-006 Part B)

Using the congruence `evalAdd_sub_add_mem_pow_succ`, the natural map
`⟨x, hx⟩ ↦ [x.1]` from `F(M^n)` to `R / M^(n+1)` is a group homomorphism. Its
kernel is exactly `F(M^(n+1))`; its image coincides with `M^n / M^(n+1)` in
`R / M^(n+1)`. -/

/-- **The forward map `F(M^n) →+ R / M^(n+1)`** (Silverman IV.3.2(a), forward
direction). For `n ≥ 1`, sends `⟨x, hx⟩ ↦ Ideal.Quotient.mk _ x.val.1`. This is
a group homomorphism by the congruence `evalAdd x y ≡ x + y (mod M^(n+1))`. -/
noncomputable def FormalGroup.evalGroup_powerIdeal_toQuot
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    F.evalGroup_powerIdeal hAdic n →+ R ⧸ ((maximalIdeal R) ^ (n + 1)) where
  toFun := fun x => (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) x.1.val.1
  map_zero' := by
    change (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) (0 : R) = 0
    exact map_zero _
  map_add' := fun x y => by
    change (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) (F.evalAdd x.1.val y.1.val) =
      (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) x.1.val.1 +
      (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) y.1.val.1
    rw [← map_add]
    exact Ideal.Quotient.eq.mpr (F.evalAdd_sub_add_mem_pow_succ hAdic hn x.2 y.2)

/-- The kernel of `evalGroup_powerIdeal_toQuot` is `F(M^(n+1))` embedded in
`F(M^n)` via `AddSubgroup.addSubgroupOf`. -/
theorem FormalGroup.evalGroup_powerIdeal_toQuot_ker
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    (F.evalGroup_powerIdeal_toQuot hAdic hn).ker =
      (F.evalGroup_powerIdeal hAdic (n + 1)).addSubgroupOf
        (F.evalGroup_powerIdeal hAdic n) := by
  ext x
  constructor
  · intro hx
    change (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) x.1.val.1 = 0 at hx
    change x.1.val.1 ∈ (maximalIdeal R) ^ (n + 1)
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hx
  · intro hx
    change x.1.val.1 ∈ (maximalIdeal R) ^ (n + 1) at hx
    change (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) x.1.val.1 = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hx

/-- The image of `evalGroup_powerIdeal_toQuot` is `Ideal.map (Ideal.Quotient.mk _) M^n`
— i.e., the elements of `R / M^(n+1)` representable by some `m ∈ M^n`. -/
theorem FormalGroup.evalGroup_powerIdeal_toQuot_range
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    (F.evalGroup_powerIdeal_toQuot hAdic hn).range =
      (Ideal.map (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1)))
        ((maximalIdeal R) ^ n)).toAddSubgroup := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact Ideal.mem_map_of_mem _ x.2
  · intro hq
    -- q ∈ Ideal.map _ M^n, so q = mk _ r for some r ∈ M^n.
    rcases (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq with ⟨r, hr, hrq⟩
    refine ⟨⟨⟨⟨r, ((maximalIdeal R).pow_le_self (by omega) : _) hr⟩⟩, hr⟩, ?_⟩
    exact hrq

/-- **The graded isomorphism, intermediate form**: applying the first isomorphism
theorem to `evalGroup_powerIdeal_toQuot` gives
`F(M^n) / ker ≃+ range`, where the kernel and range are characterised by
`evalGroup_powerIdeal_toQuot_ker` and `evalGroup_powerIdeal_toQuot_range`. A
downstream caller can transport these equalities to obtain
`F(M^n) / F(M^(n+1)) ≅ Ideal.map (Quotient.mk M^(n+1)) M^n` (i.e.,
`M^n / M^(n+1)` realised inside `R / M^(n+1)`). -/
noncomputable def FormalGroup.evalGroup_powerIdeal_quotKerEquivRange
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    (F.evalGroup_powerIdeal hAdic n ⧸ (F.evalGroup_powerIdeal_toQuot hAdic hn).ker) ≃+
      (F.evalGroup_powerIdeal_toQuot hAdic hn).range :=
  QuotientAddGroup.quotientKerEquivRange (F.evalGroup_powerIdeal_toQuot hAdic hn)

/-! ### T-IV-3-007: Torsion of `F(M)` has `p`-power order (Silverman IV.3.2(b))

When the residue field of `R` has characteristic `p`, every torsion element
`x : F.EvalGroup hAdic` has `addOrderOf x = p^k` for some `k : ℕ`.

The residue-characteristic hypothesis is packaged as
`hR : ∀ m : ℕ, ¬ p ∣ m → IsUnit ((m : ℕ) : R)` — any `m` not divisible by `p`
becomes a unit in `R`. This is the key consequence of the residue field having
characteristic `p` combined with units lifting in a complete local ring.

The proof strategy is:
* Show `[n]` is injective on `F.EvalGroup hAdic` when `(n : R)` is a unit.
* Split `addOrderOf x = p^k * m` with `gcd(m, p) = 1`; then `(m : R)` is a unit.
* `(p^k) • x` is annihilated by `m`, hence is zero by injectivity of `[m]`.
* So `p^k` already annihilates `x`, forcing `m = 1`.

The injectivity of `[n]` is proved first at the **series level**
(`FormalGroup.mulByNatHom_subst_injective_of_unit` in `Hom.lean`), then
transported to the **evaluation level** on `F.EvalGroup hAdic` here. -/

/-- **Helper**: evaluation at `0 ∈ R` of a power series with zero constant
coefficient is `0`. Used in the evaluation-level injectivity argument. -/
private theorem FormalGroup.eval₂_zero_of_constantCoeff_zero
    (hAdic : IsAdic (maximalIdeal R)) {f : PowerSeries R}
    (hf : @PowerSeries.constantCoeff R _ f = 0) :
    PowerSeries.eval₂ (RingHom.id R) (0 : R) f = 0 := by
  have hzero_mem : (0 : R) ∈ maximalIdeal R := (maximalIdeal R).zero_mem
  have hPE : PowerSeries.HasEval (0 : R) :=
    isTopologicallyNilpotent_of_mem_maximalIdeal hAdic hzero_mem
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := PowerSeries.hasSum_eval₂ hcid hPE f
  -- Every term of the sum is 0.
  have hterms : ∀ d : ℕ, (RingHom.id R) (PowerSeries.coeff d f) *
      (0 : R) ^ d = 0 := by
    intro d
    simp only [RingHom.id_apply]
    by_cases hd : d = 0
    · subst hd
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · rw [zero_pow hd, mul_zero]
  have hsum_zero : HasSum
      (fun d : ℕ => (RingHom.id R) (PowerSeries.coeff d f) * (0 : R) ^ d) 0 := by
    rw [show (fun d : ℕ => (RingHom.id R) (PowerSeries.coeff d f) * (0 : R) ^ d) =
        (fun _ : ℕ => (0 : R)) from funext hterms]
    exact hasSum_zero
  exact hsum.unique hsum_zero

/-- **Evaluation-level injectivity of `[n]`** (when `(n : R)` is a unit).

For `a ∈ M`, if `PowerSeries.eval₂ id a.1 [n].toSeries = 0`, then `a.1 = 0`.

The proof applies `eval₂ id a.1` to the series-level left-inverse identity
`subst [n].toSeries invSeries = X` (from `Hom.lean`), then uses the
substitution bridge `eval₂_subst_bridge` to transport the evaluation through. -/
theorem FormalGroup.eval_mulByNatHom_injective_of_unit
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
    {n : ℕ} (hn : IsUnit ((n : ℕ) : R))
    {a : maximalIdeal R}
    (ha : PowerSeries.eval₂ (RingHom.id R) a.1 (F.mulByNatHom n).toSeries = 0) :
    a.1 = 0 := by
  -- Series-level left inverse: `subst [n].toSeries invSeries = X`.
  have hleft : PowerSeries.subst (F.mulByNatHom n).toSeries
      (F.mulByNatInvSeries n hn) = PowerSeries.X :=
    F.subst_mulByNatHom_mulByNatInvSeries hn
  -- Unit-indexed substitution family `b` so we can apply the MvPowerSeries bridge.
  let b : Unit → MvPowerSeries Unit R := fun _ => (F.mulByNatHom n).toSeries
  have hb0 : ∀ s : Unit, MvPowerSeries.constantCoeff (b s) = 0 := fun _ =>
    (F.mulByNatHom n).zero_const
  have hb : MvPowerSeries.HasSubst b :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => hb0 s)
  have hleft' : MvPowerSeries.subst b (F.mulByNatInvSeries n hn) = PowerSeries.X :=
    hleft
  -- Apply `eval₂ id (fun _ : Unit => a.1)` to both sides and invoke the bridge.
  have hc_mem : ∀ _ : Unit, a.1 ∈ maximalIdeal R := fun _ => a.2
  have bridge := eval₂_subst_bridge hAdic hb0 hb (b := fun _ : Unit => a.1) hc_mem
    (F.mulByNatInvSeries n hn)
  rw [hleft'] at bridge
  have hlhs : MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => a.1)
      (PowerSeries.X : PowerSeries R) = a.1 := by
    change PowerSeries.eval₂ (RingHom.id R) a.1 PowerSeries.X = a.1
    rw [PowerSeries.eval₂_X]
  rw [hlhs] at bridge
  -- Inner function collapses to the constant-zero function by `ha`.
  have hfun : (fun s : Unit =>
        MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => a.1) (b s)) =
      fun _ : Unit => (0 : R) := by
    funext s; cases s
    change PowerSeries.eval₂ (RingHom.id R) a.1 (F.mulByNatHom n).toSeries = 0
    exact ha
  rw [hfun] at bridge
  rw [bridge]
  -- Goal: `eval₂ id 0 invSeries = 0`, using `constantCoeff invSeries = 0`.
  change PowerSeries.eval₂ (RingHom.id R) 0 (F.mulByNatInvSeries n hn) = 0
  exact FormalGroup.eval₂_zero_of_constantCoeff_zero hAdic
    (F.constantCoeff_mulByNatInvSeries n hn)

/-- **nsmul injectivity on `F.EvalGroup hAdic`** (when `(n : R)` is a unit).

For `x : F.EvalGroup hAdic`, if `n • x = 0`, then `x = 0`. -/
theorem FormalGroup.EvalGroup.nsmul_injective_of_unit
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
    {n : ℕ} (hn : IsUnit ((n : ℕ) : R))
    {x : F.EvalGroup hAdic} (hx : n • x = 0) :
    x = 0 := by
  -- From `n • x = 0`, extract `(n • x).val.1 = 0`.
  have hval : (n • x).val.1 = 0 := by rw [hx]; rfl
  -- Via the nsmul bridge, this gives `eval₂ id x.val.1 [n].toSeries = 0`.
  have heval : PowerSeries.eval₂ (RingHom.id R) x.val.1 (F.mulByNatHom n).toSeries = 0 := by
    rw [← FormalGroup.EvalGroup.nsmul_val F hAdic n x]; exact hval
  -- Apply the evaluation-level injectivity.
  have hx_zero : x.val.1 = 0 :=
    FormalGroup.eval_mulByNatHom_injective_of_unit F hAdic hn heval
  -- Conclude x = 0 by the structure's extensionality.
  apply FormalGroup.EvalGroup.ext
  apply Subtype.ext
  exact hx_zero

/-- **T-IV-3-007 (Silverman IV.3.2(b))**: every torsion element of `F.EvalGroup hAdic`
has order a power of `p`, provided the residue field has characteristic `p`.

The residue-characteristic hypothesis is packaged as
`hR : ∀ m : ℕ, ¬ p ∣ m → IsUnit ((m : ℕ) : R)`. -/
theorem FormalGroup.EvalGroup.addOrderOf_isPowOf
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
    (p : ℕ) (hp : p.Prime)
    (hR : ∀ m : ℕ, ¬ p ∣ m → IsUnit ((m : ℕ) : R))
    (x : F.EvalGroup hAdic) (hx : IsOfFinAddOrder x) :
    ∃ k : ℕ, addOrderOf x = p^k := by
  -- Let N := addOrderOf x, positive by hx.
  set N : ℕ := addOrderOf x with hN_def
  have hN_pos : 0 < N := hx.addOrderOf_pos
  have hN_ne : N ≠ 0 := hN_pos.ne'
  -- Decompose N = p^k * m with m = ordCompl[p] N (coprime to p).
  set k : ℕ := N.factorization p with hk_def
  set m : ℕ := ordCompl[p] N with hm_def
  have hfact : p^k * m = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hm_copr : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hN_ne
  -- So (m : R) is a unit.
  have hm_unit : IsUnit ((m : ℕ) : R) := hR m hm_copr
  -- Let y := (p^k) • x. Then m • y = N • x = 0 (by definition of addOrderOf).
  set y : F.EvalGroup hAdic := (p^k) • x with hy_def
  have hmy : m • y = 0 := by
    rw [hy_def, ← mul_smul]
    rw [show m * p^k = N by rw [mul_comm, hfact]]
    exact addOrderOf_nsmul_eq_zero x
  -- By nsmul injectivity (since m is coprime to p), y = 0.
  have hy_zero : y = 0 :=
    FormalGroup.EvalGroup.nsmul_injective_of_unit F hAdic hm_unit hmy
  -- So (p^k) • x = 0, hence N | p^k.
  have hN_dvd : N ∣ p^k := by
    rw [hN_def, addOrderOf_dvd_iff_nsmul_eq_zero]; exact hy_zero
  -- We also have N = p^k * m, so p^k | N (from the factorization).
  have hpk_dvd : p^k ∣ N := ⟨m, hfact.symm⟩
  -- So N = p^k: from hN_dvd (N ∣ p^k) and hpk_dvd (p^k ∣ N).
  refine ⟨k, Nat.dvd_antisymm hN_dvd hpk_dvd⟩

/-! ### T-IV-3-004 Part B: `Ĝ_m(M) ≅ (1 + M)ˣ` as abelian groups

Packages the operation-level identity `1 + evalAdd x y = (1 + x)(1 + y)` for
`Ĝ_m` (proved as `evalAdd_multiplicativeFormalGroup_one_add` above) into a
`MulEquiv` between `Multiplicative (Ĝ_m.EvalGroup hAdic)` and the subgroup of
`Rˣ` consisting of 1-units, i.e. units `u` with `u - 1 ∈ maximalIdeal R`.

Working with `Rˣ` (rather than a raw submonoid of `R`) gives the target a
`Group` structure for free — any `Subgroup Rˣ` is automatically a `Group`.
This sidesteps proving that `1 + M` is closed under inverses inside `R`.

The key ingredient is the local-ring fact
`IsLocalRing.notMem_maximalIdeal : x ∉ maximalIdeal R ↔ IsUnit x`, which we
use to promote each `1 + x` with `x ∈ M` to an element of `Rˣ`. -/

/-- The 1-units of `R`, realised as a subgroup of `Rˣ`: those units `u` with
`(u : R) - 1 ∈ maximalIdeal R`. -/
def oneUnitsSubgroup (R : Type*) [CommRing R] [IsLocalRing R] : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ maximalIdeal R}
  one_mem' := by
    change ((1 : Rˣ) : R) - 1 ∈ maximalIdeal R
    simp
  mul_mem' := fun {u v} hu hv => by
    -- `u*v - 1 = (u-1)*(v-1) + (u-1) + (v-1)` — all three summands are in `M`.
    change ((u * v : Rˣ) : R) - 1 ∈ maximalIdeal R
    have h : ((u * v : Rˣ) : R) - 1 =
        ((u : R) - 1) * ((v : R) - 1) + ((u : R) - 1) + ((v : R) - 1) := by
      push_cast; ring
    rw [h]
    exact (maximalIdeal R).add_mem
      ((maximalIdeal R).add_mem ((maximalIdeal R).mul_mem_right _ hu) hu) hv
  inv_mem' := fun {u} hu => by
    -- `(u⁻¹ : R) - 1 = -(u - 1) * (u⁻¹ : R) ∈ M`.
    change ((u⁻¹ : Rˣ) : R) - 1 ∈ maximalIdeal R
    have hinv : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by
      exact_mod_cast u.mul_inv
    have h : ((u⁻¹ : Rˣ) : R) - 1 = -((u : R) - 1) * ((u⁻¹ : Rˣ) : R) := by
      have heq : ((u⁻¹ : Rˣ) : R) - 1 =
          ((u⁻¹ : Rˣ) : R) - (u : R) * ((u⁻¹ : Rˣ) : R) := by rw [hinv]
      rw [heq]; ring
    rw [h]
    exact (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).neg_mem hu)

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- Helper lemma: `1 + x.1` is a unit when `x.1 ∈ maximalIdeal R`. -/
private theorem oneAdd_isUnit (x : maximalIdeal R) : IsUnit (1 + x.1) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  have h1 : (1 : R) = (1 + x.1) - x.1 := by ring
  have hone : (1 : R) ∈ maximalIdeal R := by
    rw [h1]; exact (maximalIdeal R).sub_mem h x.2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((maximalIdeal R).eq_top_iff_one.mpr hone)

/-- Helper: for `x : maximalIdeal R`, the element `1 + x.1 ∈ R` is a unit.

In a local ring, `1 + x ∉ M` since otherwise `1 = (1 + x) - x ∈ M`,
contradicting `1 ∉ M`. By `IsLocalRing.notMem_maximalIdeal`, this gives a unit. -/
private noncomputable def oneAddUnit (x : maximalIdeal R) : Rˣ :=
  (oneAdd_isUnit x).unit

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- `oneAddUnit x` has underlying element `1 + x.1`. -/
private theorem oneAddUnit_val (x : maximalIdeal R) :
    ((oneAddUnit x : Rˣ) : R) = 1 + x.1 :=
  IsUnit.unit_spec _

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- `oneAddUnit x` belongs to the 1-units subgroup. -/
private theorem oneAddUnit_mem (x : maximalIdeal R) :
    oneAddUnit x ∈ oneUnitsSubgroup R := by
  change ((oneAddUnit x : Rˣ) : R) - 1 ∈ maximalIdeal R
  rw [oneAddUnit_val, add_sub_cancel_left]
  exact x.2

/-- **Silverman IV.3.1.2 packaged**: `Ĝ_m(M) ≃* (1 + M, ·)` as abelian groups,
where the target is the 1-units subgroup of `Rˣ`.

The forward map sends the additive wrapper `x : Ĝ_m.EvalGroup hAdic` (viewed
multiplicatively) to the unit `1 + x.val.1 ∈ Rˣ`. The inverse map sends a
1-unit `u` to the wrapped element `u - 1 ∈ M`. Multiplicativity is the content
of `evalAdd_multiplicativeFormalGroup_one_add`. -/
noncomputable def multiplicativeFormalGroup_EvalGroup_mulEquiv
    (hAdic : IsAdic (maximalIdeal R)) :
    Multiplicative ((multiplicativeFormalGroup R).EvalGroup hAdic) ≃*
      oneUnitsSubgroup R where
  toFun := fun x => ⟨oneAddUnit x.toAdd.val, oneAddUnit_mem x.toAdd.val⟩
  invFun := fun u =>
    Multiplicative.ofAdd ⟨⟨((u : Rˣ) : R) - 1, u.2⟩⟩
  left_inv := fun x => by
    -- `toFun` then `invFun`: reduces to `(1 + x.val.1) - 1 = x.val.1`.
    apply (Multiplicative.toAdd).injective
    apply FormalGroup.EvalGroup.ext
    apply Subtype.ext
    change ((oneAddUnit x.toAdd.val : Rˣ) : R) - 1 = x.toAdd.val.1
    rw [oneAddUnit_val]
    ring
  right_inv := fun u => by
    -- `invFun` then `toFun`: reduces to `1 + (u - 1) = u` in `Rˣ` via `Units.ext`.
    apply Subtype.ext
    apply Units.ext
    change ((oneAddUnit _ : Rˣ) : R) = ((u : Rˣ) : R)
    rw [oneAddUnit_val]
    change (1 : R) + (((u : Rˣ) : R) - 1) = ((u : Rˣ) : R)
    ring
  map_mul' := fun x y => by
    -- Multiplicativity: reduce to equality in `R` via `Subtype.ext`/`Units.ext`.
    apply Subtype.ext
    apply Units.ext
    change ((oneAddUnit _ : Rˣ) : R) =
      ((oneAddUnit _ : Rˣ) : R) * ((oneAddUnit _ : Rˣ) : R)
    rw [oneAddUnit_val, oneAddUnit_val, oneAddUnit_val]
    -- `x * y` in `Multiplicative` unfolds to `ofAdd (x.toAdd + y.toAdd)`, whose
    -- `.val` is `F.evalAdd x.toAdd.val y.toAdd.val`. Apply the operation lemma.
    change 1 + (multiplicativeFormalGroup R).evalAdd x.toAdd.val y.toAdd.val =
      (1 + x.toAdd.val.1) * (1 + y.toAdd.val.1)
    exact evalAdd_multiplicativeFormalGroup_one_add _ _

/-! ### T-IV-6-001: torsion p-power for residue characteristic p (Silverman IV.6.1)

Specialization of `FormalGroup.EvalGroup.addOrderOf_isPowOf`: when `R`'s residue
field has characteristic `p`, the abstract hypothesis `hR` is automatic (any
integer `m` not divisible by `p` becomes a unit in `R`, since it doesn't fall
into the maximal ideal after reducing mod the residue field). -/

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- Helper: in a local ring with residue field of characteristic `p`, any
natural number `m` not divisible by `p` is a unit when cast to `R`. -/
theorem isUnit_natCast_of_not_dvd_residueChar (p : ℕ)
    [CharP (IsLocalRing.ResidueField R) p] {m : ℕ} (hm : ¬ p ∣ m) :
    IsUnit ((m : ℕ) : R) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h_mem
  have h_res_eq_zero : ((m : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    have := map_natCast (IsLocalRing.residue R) m
    rw [← this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
  exact hm ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p m).mp h_res_eq_zero)

/-- **Silverman IV.6.1** (residue-char form of T-IV-3-007).

For a formal group `F` over a complete local ring `R` whose residue field has
characteristic `p`, every torsion element of `F(M)` has order a power of `p`. -/
theorem FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar
    (F : FormalGroup R) (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (x : F.EvalGroup hAdic) (hx : IsOfFinAddOrder x) :
    ∃ k : ℕ, addOrderOf x = p ^ k :=
  FormalGroup.EvalGroup.addOrderOf_isPowOf F hAdic p hp
    (fun _ hm => isUnit_natCast_of_not_dvd_residueChar p hm) x hx

end HasseWeil.FormalGroup

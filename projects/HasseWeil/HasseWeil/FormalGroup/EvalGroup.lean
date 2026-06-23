import HasseWeil.FormalGroup.Definition
import HasseWeil.FormalGroup.Inverse
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.Algebra.UniformRing

/-!
# The group `F(M)` associated to a formal group over a complete local ring
# (Silverman IV.3, ticket T-IV-3-001)

Let `R` be a commutative local ring with maximal ideal `M = IsLocalRing.maximalIdeal R`,
equipped with the `M`-adic topology (so that it is both a topological ring with
a linear topology, a uniform ring, etc.), and assume moreover that it is
`M`-adically complete (so `R` is Hausdorff and complete for this topology).

For a formal group law `F(X, Y) ∈ R[[X, Y]]`, the set `M` acquires a structure of
an abelian group via
  `x +_F y := F(x, y) = MvPowerSeries.eval₂ (RingHom.id R) ![x, y] F.toSeries`.

The convergence of the power series `F(x, y)` is guaranteed by `x, y ∈ M` (they are
topologically nilpotent, as `M^n → 0` in the adic topology) and by completeness.

## Main definitions

* `HasseWeil.FormalGroup.FormalGroup.evalAdd F x y` — the binary operation
  `x +_F y` on `M`, returning an element of `R`.
* `HasseWeil.FormalGroup.FormalGroup.evalAdd_mem F x y` — the operation is closed
  in `M`, i.e. `evalAdd F x y ∈ M`.
* `HasseWeil.FormalGroup.FormalGroup.evalNeg F x` — the formal negation
  `-_F x := i(x)` for `x ∈ M`, where `i = F.inverse` is the formal inverse
  power series.
* `HasseWeil.FormalGroup.FormalGroup.evalNeg_mem F x` — the negation is closed
  in `M`, i.e. `evalNeg F x ∈ M`.

Additional lemmas discharge the unit and commutativity axioms for the operation.

Associativity `evalAdd_assoc`, the inverse-axiom `evalAdd_evalNeg`, and the
bundled `AddCommGroup (IsLocalRing.maximalIdeal R)` instance are deferred to
follow-up work; they would follow from `F.assoc`, `FormalGroup.fAdd_X_inverse_eq_zero`,
and a bridge lemma pushing continuous evaluation through `MvPowerSeries.subst`.
The bridge lemma is technically subtle because mathlib's cleanest `subst ∘ eval₂`
commutation route (`MvPowerSeries.eval₂_subst`) requires the coefficient ring
to carry the discrete uniformity, which our `R` does not have (it has the
`M`-adic uniformity).

## Assumptions on `R`

We require `R` to be a `CommRing`, `IsLocalRing`, equipped with topology and uniform
space structure coming from the `M`-adic topology, and `M`-adically complete.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.3 (Definition of the group
  `F(M)`, p. 122).
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-! ### The binary operation `x +_F y` on `M`

We assume `R` has a topology and uniform space structure such that:
  - `R` is a topological ring, a uniform additive group, with linear topology;
  - `R` is Hausdorff and complete;
  - the topology is the `M`-adic topology (via `IsAdic (maximalIdeal R)`).

Under these hypotheses, every element of `M` is topologically nilpotent
(`M^n → 0`), so `MvPowerSeries.eval₂` at any such element converges.
-/

section EvalGroup

variable [IsLocalRing R]
variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
variable [IsLinearTopology R R] [T2Space R] [CompleteSpace R]

omit [IsUniformAddGroup R] [IsTopologicalRing R] [IsLinearTopology R R] [T2Space R]
  [CompleteSpace R] in
/-- Elements of the maximal ideal are topologically nilpotent under the
`M`-adic topology. -/
lemma isTopologicallyNilpotent_of_mem_maximalIdeal
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsTopologicallyNilpotent x := by
  unfold IsTopologicallyNilpotent
  rw [hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ ?_⟩
  -- Want `x ^ m ∈ M ^ n`. Since `m ≥ n`, we have `M ^ m ≤ M ^ n`, and `x ^ m ∈ M ^ m`.
  exact (Ideal.pow_le_pow_right hm : (IsLocalRing.maximalIdeal R) ^ m ≤ _)
    (Ideal.pow_mem_pow hx m)

/-- Any function `a : Fin 2 → R` taking values in the maximal ideal satisfies
`HasEval` for the `M`-adic topology. -/
lemma hasEval_of_mem_maximalIdeal
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {a : Fin 2 → R} (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R) :
    MvPowerSeries.HasEval a where
  hpow i := isTopologicallyNilpotent_of_mem_maximalIdeal hAdic (ha i)
  tendsto_zero := by
    -- `Fin 2` is a finite type, so the cofinite filter is bot, hence any map converges.
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

/-- **The binary operation `x +_F y` on the maximal ideal** (Silverman IV.3).

For `x, y ∈ M` and `F : FormalGroup R`, this is `F(x, y) = MvPowerSeries.eval₂`
of `F.toSeries` at the pair `(x, y)`. The result is an element of `R`; a separate
lemma `evalAdd_mem` shows it actually lies in `M`. -/
noncomputable def FormalGroup.evalAdd (F : FormalGroup R)
    (x y : IsLocalRing.maximalIdeal R) : R :=
  MvPowerSeries.eval₂ (RingHom.id R) (![x.1, y.1] : Fin 2 → R) F.toSeries

/-! ### Closure under `+_F`: `evalAdd F x y ∈ M` -/

omit [IsUniformAddGroup R] [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- The maximal ideal is closed in the `M`-adic topology.

`M` is open (as the basis of neighborhoods of 0 at level 1, i.e. `M^1 = M`),
hence closed. -/
lemma maximalIdeal_isClosed
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R)) :
    IsClosed (IsLocalRing.maximalIdeal R : Set R) := by
  -- Use `isAdic_iff` to extract `IsOpen (M^n)` for all `n`, in particular `n = 1`.
  obtain ⟨hopen, _⟩ := isAdic_iff.mp hAdic
  have h2 : IsOpen (IsLocalRing.maximalIdeal R : Set R) := by
    have := hopen 1
    rwa [pow_one] at this
  exact AddSubgroup.isClosed_of_isOpen (G := R)
    ((IsLocalRing.maximalIdeal R).toAddSubgroup) h2

/-- `evalAdd F x y ∈ M`. Follows from `constantCoeff F.toSeries = 0` and the
fact that evaluation `eval₂` of a series with vanishing constant coefficient at
a point in `M` lies in `M`. -/
theorem FormalGroup.evalAdd_mem
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (x y : IsLocalRing.maximalIdeal R) :
    F.evalAdd x y ∈ IsLocalRing.maximalIdeal R := by
  have ha := hasEval_of_mem_maximalIdeal hAdic (a := ![x.1, y.1])
    (by intro i; fin_cases i <;> simp [x.2, y.2])
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid ha F.toSeries
  change MvPowerSeries.eval₂ (RingHom.id R) ![x.1, y.1] F.toSeries ∈ _
  have hM_closed : IsClosed (IsLocalRing.maximalIdeal R : Set R) :=
    maximalIdeal_isClosed hAdic
  -- The sum is a `Tendsto` over finite subsets; use `IsClosed.mem_of_tendsto`.
  -- `HasSum f a` unfolds to `Tendsto (fun s : Finset _ ↦ ∑ b ∈ s, f b) atTop (𝓝 a)`.
  apply hM_closed.mem_of_tendsto hsum
  -- Each partial sum is in M.
  filter_upwards with N
  apply (IsLocalRing.maximalIdeal R).sum_mem
  intro d _hd
  change (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![x.1, y.1]) s ^ e) ∈ _
  simp only [RingHom.id_apply]
  by_cases hd : d = 0
  · -- d = 0: coeff 0 F.toSeries = constantCoeff F.toSeries = 0.
    subst hd
    have hc0 : MvPowerSeries.coeff (R := R) (0 : Fin 2 →₀ ℕ) F.toSeries = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact HasseWeil.FG.constantCoeff_FG_toSeries F
    rw [hc0, zero_mul]
    exact (IsLocalRing.maximalIdeal R).zero_mem
  · -- d ≠ 0: the product has some factor of x or y, both in M.
    apply (IsLocalRing.maximalIdeal R).mul_mem_left
    have hne : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext (fun s ↦ by simpa using h s))
    obtain ⟨s, hs⟩ := hne
    have hs_mem : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [Finsupp.prod]
    refine (IsLocalRing.maximalIdeal R).prod_mem (s := d.support) hs_mem ?_
    have hds : 0 < d s := Nat.pos_of_ne_zero hs
    have has : (![x.1, y.1] : Fin 2 → R) s ∈ IsLocalRing.maximalIdeal R := by
      fin_cases s <;> simp [x.2, y.2]
    exact Ideal.pow_mem_of_mem _ has _ hds

/-! ### Basic properties of `evalAdd`

We compute `evalAdd F 0 0 = 0` directly from `constantCoeff F.toSeries = 0`.
-/

/-- `F(0, 0) = 0`: the formal group law evaluated at the origin gives zero,
since `constantCoeff F.toSeries = 0`. -/
theorem FormalGroup.evalAdd_zero_zero
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) :
    F.evalAdd ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩
              ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩ = 0 := by
  -- evalAdd is eval₂ at (0, 0). Only the constant-coefficient term survives,
  -- and `constantCoeff F.toSeries = 0`.
  change MvPowerSeries.eval₂ (RingHom.id R)
      (![(0 : R), (0 : R)] : Fin 2 → R) F.toSeries = 0
  have ha := hasEval_of_mem_maximalIdeal hAdic (a := ![(0 : R), (0 : R)])
    (by intro i; fin_cases i <;> simp)
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid ha F.toSeries
  -- For each d, the term is 0: if d = 0, coeff 0 F = 0; else some factor vanishes.
  have hterm_zero : ∀ d : Fin 2 →₀ ℕ,
      (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![(0 : R), (0 : R)]) s ^ e) = 0 := by
    intro d
    simp only [RingHom.id_apply]
    by_cases hd : d = 0
    · subst hd
      have hc0 : MvPowerSeries.coeff (R := R) (0 : Fin 2 →₀ ℕ) F.toSeries = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
        exact HasseWeil.FG.constantCoeff_FG_toSeries F
      rw [hc0, zero_mul]
    · -- The prod has a zero factor since d s > 0 for some s, and a s = 0.
      have hne : ∃ s, d s ≠ 0 := by
        by_contra h
        push Not at h
        exact hd (Finsupp.ext (fun s ↦ by simpa using h s))
      obtain ⟨s, hs⟩ := hne
      have hs_mem : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
      have : (d.prod fun s' e' ↦ (![(0 : R), (0 : R)]) s' ^ e') = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hs_mem ?_
        have : (![(0 : R), (0 : R)] : Fin 2 → R) s = 0 := by fin_cases s <;> simp
        rw [this, zero_pow hs]
      rw [this, mul_zero]
  -- So the hasSum is hasSum of the zero function, which sums to 0.
  have hzero : HasSum (fun d : Fin 2 →₀ ℕ ↦
      (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![(0 : R), (0 : R)]) s ^ e)) 0 := by
    convert hasSum_zero using 1
    exact funext hterm_zero
  exact (hzero.unique hsum).symm

/-! ### Commutativity of `evalAdd`

We prove `evalAdd F x y = evalAdd F y x` using the coefficient-level swap
symmetry implied by `F.comm`, together with reindexing of the `hasSum`. -/

/-- Swap equivalence on `Fin 2 →₀ ℕ`: sends `d ↦ (d 1, d 0)`. -/
private noncomputable def finsupp_swap : (Fin 2 →₀ ℕ) ≃ (Fin 2 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 1) + Finsupp.single 1 (d 0)
  invFun d := Finsupp.single 0 (d 1) + Finsupp.single 1 (d 0)
  left_inv d := by
    ext i; fin_cases i <;>
      simp [Finsupp.coe_add, Pi.add_apply]
  right_inv d := by
    ext i; fin_cases i <;>
      simp [Finsupp.coe_add, Pi.add_apply]

private lemma finsupp_swap_apply_zero (d : Fin 2 →₀ ℕ) :
    (finsupp_swap d) 0 = d 1 := by
  simp [finsupp_swap]

private lemma finsupp_swap_apply_one (d : Fin 2 →₀ ℕ) :
    (finsupp_swap d) 1 = d 0 := by
  simp [finsupp_swap]

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- The coefficient swap induced by `F.comm`: `coeff d F.toSeries =
coeff (finsupp_swap d) F.toSeries`. This is a consequence of
`subst ![X 1, X 0] F.toSeries = F.toSeries`. -/
theorem FormalGroup.coeff_swap (F : FormalGroup R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d F.toSeries =
      MvPowerSeries.coeff (finsupp_swap d) F.toSeries := by
  have h_swap : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have key := congr_arg (MvPowerSeries.coeff d) F.comm
  rw [MvPowerSeries.coeff_subst h_swap] at key
  -- key : finsum (fun d' ↦ coeff d' F • coeff d (prod (![X 1, X 0] s)^e)) = coeff d F
  -- The only nonzero term in this sum is at d' = finsupp_swap d, where the product
  -- `X 1^(d' 0) * X 0^(d' 1)` has coefficient 1 at `(d' 1, d' 0)`.
  -- When `d' = finsupp_swap d`, i.e., `d' 0 = d 1, d' 1 = d 0`, the product
  -- `X 1^(d 1) * X 0^(d 0)` has coefficient 1 at `(d 0, d 1) = d`.
  rw [finsum_eq_single _ (finsupp_swap d)] at key
  · -- Evaluate the single nonzero term.
    simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at key
    have hcoeff_prod :
        MvPowerSeries.coeff d
          ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ ((finsupp_swap d) 0) *
            (MvPowerSeries.X 0) ^ ((finsupp_swap d) 1)) = 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
          MvPowerSeries.monomial_mul_monomial, mul_one]
      rw [MvPowerSeries.coeff_monomial]
      rw [finsupp_swap_apply_zero, finsupp_swap_apply_one]
      rw [if_pos]
      ext i; fin_cases i <;> simp
    rw [hcoeff_prod, smul_eq_mul, mul_one] at key
    exact key.symm
  · -- Other terms vanish.
    intro d' hd'
    simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    suffices MvPowerSeries.coeff d
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ (d' 0) *
          (MvPowerSeries.X 0) ^ (d' 1)) = 0 by
      rw [this, smul_zero]
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, mul_one]
    rw [MvPowerSeries.coeff_monomial]
    split_ifs with heq
    · exfalso; apply hd'
      -- heq says single 0 (d' 1) + single 1 (d' 0) = d
      have h0' : d' 1 = d 0 := by
        have := DFunLike.congr_fun heq 0
        simpa [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] using this.symm
      have h1' : d' 0 = d 1 := by
        have := DFunLike.congr_fun heq 1
        simpa [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] using this.symm
      ext i
      fin_cases i
      · show d' 0 = finsupp_swap d 0
        rw [finsupp_swap_apply_zero]
        exact h1'
      · show d' 1 = finsupp_swap d 1
        rw [finsupp_swap_apply_one]
        exact h0'
    · rfl

-- The proof uses a reindexed `HasSum` via `finsupp_swap` equivalence; this
-- requires substantial term manipulation and benefits from a higher heartbeat
-- limit.
set_option maxHeartbeats 800000 in
/-- Commutativity: `evalAdd F x y = evalAdd F y x`. -/
theorem FormalGroup.evalAdd_comm
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (x y : IsLocalRing.maximalIdeal R) :
    F.evalAdd x y = F.evalAdd y x := by
  have hax : MvPowerSeries.HasEval (![x.1, y.1] : Fin 2 → R) :=
    hasEval_of_mem_maximalIdeal hAdic (by intro i; fin_cases i <;> simp [x.2, y.2])
  have hay : MvPowerSeries.HasEval (![y.1, x.1] : Fin 2 → R) :=
    hasEval_of_mem_maximalIdeal hAdic (by intro i; fin_cases i <;> simp [x.2, y.2])
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum_xy := MvPowerSeries.hasSum_eval₂ hcid hax F.toSeries
  have hsum_yx := MvPowerSeries.hasSum_eval₂ hcid hay F.toSeries
  change MvPowerSeries.eval₂ (RingHom.id R) (![x.1, y.1] : Fin 2 → R) F.toSeries =
    MvPowerSeries.eval₂ (RingHom.id R) (![y.1, x.1] : Fin 2 → R) F.toSeries
  -- Reindex hsum_yx via σ to match hsum_xy.
  have hsum_yx_reindex :
      HasSum (fun d ↦ (fun d' : Fin 2 →₀ ℕ ↦
        (RingHom.id R) (MvPowerSeries.coeff d' F.toSeries) *
          (d'.prod fun s e ↦ (![y.1, x.1] : Fin 2 → R) s ^ e)) (finsupp_swap d))
        (MvPowerSeries.eval₂ (RingHom.id R) (![y.1, x.1] : Fin 2 → R) F.toSeries) :=
    (finsupp_swap.hasSum_iff).mpr hsum_yx
  -- Show the reindexed sum function equals the xy sum function.
  have hterm_eq : ∀ d : Fin 2 →₀ ℕ,
      (RingHom.id R) (MvPowerSeries.coeff (finsupp_swap d) F.toSeries) *
        ((finsupp_swap d).prod fun s e ↦ (![y.1, x.1] : Fin 2 → R) s ^ e) =
      (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![x.1, y.1] : Fin 2 → R) s ^ e) := by
    intro d
    simp only [RingHom.id_apply]
    -- Key: coeff (finsupp_swap d) F = coeff d F by F.coeff_swap.
    rw [← F.coeff_swap d]
    congr 1
    -- Show product equality.
    rw [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _),
        Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _),
        Fin.prod_univ_two, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [finsupp_swap_apply_zero, finsupp_swap_apply_one]
    simp only [Matrix.cons_val_zero]
    ring
  have hsum_xy_match : HasSum
      (fun d : Fin 2 →₀ ℕ ↦
        (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
          (d.prod fun s e ↦ (![x.1, y.1] : Fin 2 → R) s ^ e))
      (MvPowerSeries.eval₂ (RingHom.id R) (![y.1, x.1] : Fin 2 → R) F.toSeries) := by
    convert hsum_yx_reindex using 1
    ext d
    exact (hterm_eq d).symm
  exact hsum_xy.unique hsum_xy_match

/-! ### Unit axioms: `evalAdd F x 0 = x` and `evalAdd F 0 y = y`

These follow from the coefficient identities in `F.toSeries`:
  - `coeff (j, 0) F = 0` for `j ≠ 1`, and `coeff (1, 0) F = 1` (from `F.lunit`).
  - `coeff (0, j) F = 0` for `j ≠ 1`, and `coeff (0, 1) F = 1` (from `F.runit`).

The first coefficient identity is essentially the contrapositive of
`FormalGroup.coeff_10`. We prove variants we need here. -/

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- The `single i j` coefficient of the variable `X i` vanishes when `j ≠ 1`:
`X i` is the monomial `single i 1`, and `single i j = single i 1` forces `j = 1`.
This is the right-hand-side computation in `coeff_j0_of_ne_one` (and `F.lunit`). -/
private lemma coeff_single_X_self_of_ne_one (i : Fin 2) (j : ℕ) (hj : j ≠ 1) :
    MvPowerSeries.coeff (Finsupp.single i j)
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 := by
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · -- `single i j = single i 1` would give `j = 1`, contradiction.
    exfalso
    apply hj
    have := DFunLike.congr_fun h i
    simpa [Finsupp.single_apply] using this
  · rfl

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- The off-diagonal term in the `coeff_subst` expansion for `F(X, 0)` vanishes:
for any multi-index `d ≠ single 0 j`, the `single 0 j` coefficient of the
substituted monomial `(X 0) ^ (d 0) * 0 ^ (d 1)` is zero. There are two cases:
if `d 1 ≠ 0` the factor `0 ^ (d 1)` is zero; if `d 1 = 0` then `d = single 0 (d 0)`
with `d 0 ≠ j`, so the surviving monomial `single 0 (d 0)` differs from `single 0 j`. -/
private lemma coeff_single_X_pow_mul_zero_pow_of_ne
    {j : ℕ} {d : Fin 2 →₀ ℕ} (hd : d ≠ Finsupp.single (0 : Fin 2) j) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j)
      ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ (d 0)
        * (0 : MvPowerSeries (Fin 2) R) ^ (d 1)) = 0 := by
  by_cases hd1 : d 1 = 0
  · -- d 1 = 0, so d = single 0 (d 0). Since d ≠ single 0 j, d 0 ≠ j.
    have hdeq : d = Finsupp.single (0 : Fin 2) (d 0) := by
      ext i; fin_cases i
      · simp
      · simp [hd1]
    have hdj : d 0 ≠ j := fun heq ↦ hd (by rw [hdeq, heq])
    simp only [hd1, pow_zero, mul_one]
    rw [show ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ (d 0)) =
          MvPowerSeries.monomial (R := R) (Finsupp.single 0 (d 0)) 1 from by
        rw [MvPowerSeries.X_pow_eq]]
    rw [MvPowerSeries.coeff_monomial]
    rw [if_neg]
    intro heq
    apply hdj
    have := DFunLike.congr_fun heq 0
    simpa [Finsupp.single_apply] using this.symm
  · -- d 1 ≠ 0, so 0 ^ (d 1) = 0.
    rw [zero_pow hd1, mul_zero, map_zero]

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- For any `j ≠ 1`, `coeff (j, 0) F.toSeries = 0`. This is the coefficient-level
statement of `F.lunit` saying `F(X, 0) = X`. -/
theorem FormalGroup.coeff_j0_of_ne_one (F : FormalGroup R) (j : ℕ) (hj : j ≠ 1) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j) F.toSeries = 0 := by
  -- Apply F.lunit : subst ![X 0, 0] F = X 0.
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have key := congr_arg
    (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j)) F.lunit
  -- RHS: coeff (single 0 j) (X 0) = 1 if j=1, 0 else. Since j ≠ 1, = 0.
  have hrhs : MvPowerSeries.coeff
      (Finsupp.single (0 : Fin 2) j) (MvPowerSeries.X (0 : Fin 2) :
        MvPowerSeries (Fin 2) R) = 0 :=
    coeff_single_X_self_of_ne_one 0 j hj
  rw [hrhs] at key
  -- LHS: coeff (single 0 j) (subst ![X 0, 0] F) via coeff_subst.
  rw [MvPowerSeries.coeff_subst ha,
      finsum_eq_single _ (Finsupp.single (0 : Fin 2) j)] at key
  · -- Main term: coeff (single 0 j) F * coeff (single 0 j) (X 0^j * 0^0) = coeff (0,j) F * 1
    simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at key
    have hj0 : (Finsupp.single (0 : Fin 2) j) 0 = j := by simp
    have hj1 : (Finsupp.single (0 : Fin 2) j) 1 = 0 := by
      simp
    rw [hj0, hj1] at key
    simp only [pow_zero, mul_one] at key
    rw [show ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ j) =
          MvPowerSeries.monomial (R := R) (Finsupp.single 0 j) 1 from by
        rw [MvPowerSeries.X_pow_eq],
        MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one] at key
    exact key
  · -- Other terms vanish: for d ≠ single 0 j, the monomial coefficient is `0`
    -- (see `coeff_single_X_pow_mul_zero_pow_of_ne`), so the smul term is `0`.
    intro d hd
    simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [coeff_single_X_pow_mul_zero_pow_of_ne hd, smul_zero]

/-- Right-unit: `evalAdd F x ⟨0, _⟩ = x.1`. -/
theorem FormalGroup.evalAdd_zero_right
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) :
    F.evalAdd x ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩ = x.1 := by
  change MvPowerSeries.eval₂ (RingHom.id R) (![x.1, (0 : R)] : Fin 2 → R) F.toSeries = x.1
  have ha := hasEval_of_mem_maximalIdeal hAdic (a := ![x.1, (0 : R)])
    (by intro i; fin_cases i <;> simp [x.2])
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid ha F.toSeries
  -- Each term: coeff d F * x^(d 0) * 0^(d 1).
  -- If d 1 > 0: 0^(d 1) = 0.
  -- If d 1 = 0: term = coeff (d 0, 0) F * x^(d 0).
  --   For d 0 ≠ 1 (and d 1 = 0), coeff (d 0, 0) F = 0 by coeff_j0_of_ne_one.
  --   For (d 0, d 1) = (1, 0), coeff = 1 (by coeff_10), term = x.
  -- So the sum has only one nonzero term: x.
  have hterm_eq : ∀ d : Fin 2 →₀ ℕ,
      (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![x.1, (0 : R)] : Fin 2 → R) s ^ e) =
      (if d = Finsupp.single 0 1 then x.1 else 0) := by
    intro d
    simp only [RingHom.id_apply]
    by_cases hd1 : d 1 = 0
    · -- d 1 = 0. Then d = single 0 (d 0).
      have hdeq : d = Finsupp.single (0 : Fin 2) (d 0) := by
        ext i; fin_cases i
        · simp
        · simp [hd1]
      rw [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero,
          hd1, pow_zero, mul_one]
      by_cases hd0 : d 0 = 1
      · -- coeff F = 1, term = 1 * x^1 = x.
        -- First rewrite the coeff and power using d = single 0 1.
        have hd_single : d = Finsupp.single (0 : Fin 2) 1 := by
          rw [hdeq, hd0]
        rw [hd_single, HasseWeil.FG.FormalGroup.coeff_10]
        rw [show (Finsupp.single (0 : Fin 2) 1) 0 = 1 from by
              simp]
        rw [pow_one, one_mul, if_pos rfl]
      · -- coeff F = 0.
        rw [hdeq, F.coeff_j0_of_ne_one (d 0) hd0, zero_mul, if_neg]
        intro hcontra
        apply hd0
        have := DFunLike.congr_fun hcontra 0
        simpa [Finsupp.single_apply] using this
    · -- d 1 ≠ 0. 0^(d 1) = 0, so product has a zero factor.
      rw [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero,
          zero_pow hd1, mul_zero, mul_zero, if_neg]
      intro hcontra
      -- d = single 0 1 means d 1 = 0, contradicting hd1.
      apply hd1
      have := DFunLike.congr_fun hcontra 1
      simpa [Finsupp.single_apply] using this
  -- So hsum is the sum of x at d = single 0 1 and 0 elsewhere.
  have hsum_x : HasSum (fun d : Fin 2 →₀ ℕ ↦
      (if d = Finsupp.single 0 1 then x.1 else 0)) x.1 :=
    hasSum_ite_eq (Finsupp.single (0 : Fin 2) 1) x.1
  have hsum_rewrite : HasSum (fun d : Fin 2 →₀ ℕ ↦
      (RingHom.id R) (MvPowerSeries.coeff d F.toSeries) *
        (d.prod fun s e ↦ (![x.1, (0 : R)] : Fin 2 → R) s ^ e)) x.1 := by
    convert hsum_x using 1
    ext d; exact hterm_eq d
  exact hsum.unique hsum_rewrite

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- For any `j ≠ 1`, `coeff (0, j) F.toSeries = 0`. Analogue of `coeff_j0_of_ne_one`
via `F.runit`. -/
theorem FormalGroup.coeff_0j_of_ne_one (F : FormalGroup R) (j : ℕ) (hj : j ≠ 1) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) F.toSeries = 0 := by
  have ha : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have key := congr_arg
    (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j)) F.runit
  have hrhs : MvPowerSeries.coeff
      (Finsupp.single (1 : Fin 2) j) (MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) R) = 0 := by
    rw [MvPowerSeries.coeff_X]
    split_ifs with h
    · exfalso
      apply hj
      have := DFunLike.congr_fun h 1
      simpa [Finsupp.single_apply] using this
    · rfl
  rw [hrhs] at key
  rw [MvPowerSeries.coeff_subst ha,
      finsum_eq_single _ (Finsupp.single (1 : Fin 2) j)] at key
  · simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at key
    have hj0 : (Finsupp.single (1 : Fin 2) j) 0 = 0 := by
      simp
    have hj1 : (Finsupp.single (1 : Fin 2) j) 1 = j := by simp
    rw [hj0, hj1] at key
    simp only [pow_zero, one_mul] at key
    rw [show ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ j) =
          MvPowerSeries.monomial (R := R) (Finsupp.single 1 j) 1 from by
        rw [MvPowerSeries.X_pow_eq],
        MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one] at key
    exact key
  · intro d hd
    simp only [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases hd0 : d 0 = 0
    · have hdeq : d = Finsupp.single (1 : Fin 2) (d 1) := by
        ext i; fin_cases i
        · simp [hd0]
        · simp
      have hdj : d 1 ≠ j := fun heq ↦ hd (by rw [hdeq, heq])
      simp only [hd0, pow_zero, one_mul]
      rw [show ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ (d 1)) =
            MvPowerSeries.monomial (R := R) (Finsupp.single 1 (d 1)) 1 from by
          rw [MvPowerSeries.X_pow_eq]]
      rw [MvPowerSeries.coeff_monomial]
      rw [if_neg]
      · rw [smul_zero]
      · intro heq
        apply hdj
        have := DFunLike.congr_fun heq 1
        simpa [Finsupp.single_apply] using this.symm
    · rw [zero_pow hd0, zero_mul, map_zero, smul_zero]

/-- Left-unit: `evalAdd F ⟨0, _⟩ y = y.1`. -/
theorem FormalGroup.evalAdd_zero_left
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (y : IsLocalRing.maximalIdeal R) :
    F.evalAdd ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩ y = y.1 := by
  rw [F.evalAdd_comm hAdic]
  exact F.evalAdd_zero_right hAdic y

/-! ### The formal negation `evalNeg F x = i(x)`

We evaluate the formal inverse power series `F.inverse` at `x ∈ M` using
`PowerSeries.eval₂`. This gives the negation `−_F x` in the group `F(M)`.

The key defining property is `F(x, i(x)) = 0`, which follows from
`FormalGroup.fAdd_X_inverse_eq_zero` (the functional equation of the formal
inverse) by evaluating both sides at `x`. -/

/-- `PowerSeries.HasEval` holds for any `x ∈ M`: `x` is topologically nilpotent. -/
private lemma powerSeries_hasEval_of_mem
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    PowerSeries.HasEval x :=
  isTopologicallyNilpotent_of_mem_maximalIdeal hAdic hx

/-- **The formal negation `-_F x` on the maximal ideal** (Silverman IV.3).

For `x ∈ M` and `F : FormalGroup R`, this is `i(x)` where `i = F.inverse` is
the formal inverse power series. The result is an element of `R`; a separate
lemma `evalNeg_mem` shows it actually lies in `M`. -/
noncomputable def FormalGroup.evalNeg (F : FormalGroup R)
    (x : IsLocalRing.maximalIdeal R) : R :=
  PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse

/-- `evalNeg F x ∈ M`: the formal negation lies in the maximal ideal.

Follows from `constantCoeff F.inverse = 0` and the fact that univariate
evaluation of a power series with vanishing constant coefficient at a point
in `M` lies in `M`. -/
theorem FormalGroup.evalNeg_mem
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) :
    F.evalNeg x ∈ IsLocalRing.maximalIdeal R := by
  change PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse ∈ _
  have ha : PowerSeries.HasEval x.1 := powerSeries_hasEval_of_mem hAdic x.2
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := PowerSeries.hasSum_eval₂ hcid ha F.inverse
  have hM_closed : IsClosed (IsLocalRing.maximalIdeal R : Set R) :=
    maximalIdeal_isClosed hAdic
  apply hM_closed.mem_of_tendsto hsum
  filter_upwards with N
  apply (IsLocalRing.maximalIdeal R).sum_mem
  intro n _hn
  simp only [RingHom.id_apply]
  by_cases hn : n = 0
  · subst hn
    have h0 : PowerSeries.coeff 0 F.inverse = 0 := F.inverse_coeff_zero
    rw [h0, zero_mul]; exact (IsLocalRing.maximalIdeal R).zero_mem
  · apply (IsLocalRing.maximalIdeal R).mul_mem_left
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    exact Ideal.pow_mem_of_mem _ x.2 _ hn_pos

/-! ### The bridge: `eval_x ∘ fAdd F u v = evalAdd F (eval_x u) (eval_x v)`

The following technical lemma is the bridge from univariate evaluation to
two-variable evaluation. It lets us derive `evalAdd_evalNeg` from
`fAdd_X_inverse_eq_zero`.

**Proof strategy**: both sides are HasSums over `d : Fin 2 →₀ ℕ` of terms
`coeff d F.toSeries * (eval_x u)^(d 0) * (eval_x v)^(d 1)`. We identify the
LHS HasSum using `coeff_subst` + Fubini-style exchange, and the RHS HasSum
directly via `MvPowerSeries.hasSum_eval₂`. -/

/-- Auxiliary: for `u : PowerSeries R` with zero constant coefficient and
`x ∈ M`, `PowerSeries.eval₂ id x u ∈ M`. -/
private theorem powerSeries_eval_mem
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (x : IsLocalRing.maximalIdeal R) (u : PowerSeries R)
    (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.eval₂ (RingHom.id R) x.1 u ∈ IsLocalRing.maximalIdeal R := by
  have ha : PowerSeries.HasEval x.1 := powerSeries_hasEval_of_mem hAdic x.2
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := PowerSeries.hasSum_eval₂ hcid ha u
  have hM_closed : IsClosed (IsLocalRing.maximalIdeal R : Set R) :=
    maximalIdeal_isClosed hAdic
  apply hM_closed.mem_of_tendsto hsum
  filter_upwards with N
  apply (IsLocalRing.maximalIdeal R).sum_mem
  intro n _hn
  simp only [RingHom.id_apply]
  by_cases hn : n = 0
  · subst hn
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, zero_mul]
    exact (IsLocalRing.maximalIdeal R).zero_mem
  · apply (IsLocalRing.maximalIdeal R).mul_mem_left
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    exact Ideal.pow_mem_of_mem _ x.2 _ hn_pos


/-! ### The substitution bridge

The bridge lemma says that evaluating a substitution commutes with evaluation:

  `eval₂ id b (subst a F) = eval₂ id (eval₂ id b ∘ a) F`

This is exactly `MvPowerSeries.eval₂_subst` in mathlib, but that lemma
requires the coefficient ring `R` to carry the **discrete** uniformity. In
our adic setting, we work around this by using the Pi topology on
intermediate power series rings (the "formal" topology), which gives us
continuity of `subst` and of `eval₂`, together with density of polynomials.

We open the `WithPiTopology` scope to activate Pi topologies on MvPowerSeries
rings. The adic topology on our base `R` is unaffected. -/

open scoped MvPowerSeries.WithPiTopology

/-! ### Continuity of substitution in the Pi topology

We prove that `MvPowerSeries.subst a` is continuous in the Pi topology when each
`a s` has zero constant coefficient. This is topology-independent and valid for
any topology on `R`. -/

omit [IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R] in
/-- For `a : σ → MvPowerSeries τ R` with zero constant coefficient at each `s`,
and for each multi-index `e : τ →₀ ℕ`, the set
`{d : σ →₀ ℕ | coeff e (∏ (a s)^(d s)) ≠ 0}` is finite. -/
private theorem coeff_prod_pow_support_finite
    {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ R}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (e : τ →₀ ℕ) :
    Set.Finite {d : σ →₀ ℕ | MvPowerSeries.coeff e
      (d.prod fun s e' ↦ (a s) ^ e') ≠ 0} := by
  classical
  apply (Finsupp.finite_of_degree_le e.degree).subset
  intro d hd
  simp only [Set.mem_setOf_eq] at hd ⊢
  by_contra hdeg
  push Not at hdeg
  apply hd
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.prod]
  have hord : ((Finsupp.degree d : ℕ) : ℕ∞) ≤
      MvPowerSeries.order (∏ s ∈ d.support, (a s) ^ (d s)) := by
    simp only [Finsupp.degree_apply]
    push_cast
    calc (∑ s ∈ d.support, (d s : ℕ∞))
        ≤ ∑ s ∈ d.support, MvPowerSeries.order ((a s) ^ (d s)) := by
          apply Finset.sum_le_sum
          intros s _
          have := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (d s) (ha0 s)
          exact_mod_cast this
      _ ≤ _ := MvPowerSeries.le_order_prod _ _
  have hlt : (((Finsupp.degree e : ℕ) : ℕ∞) < ((Finsupp.degree d : ℕ) : ℕ∞)) :=
    ENat.coe_lt_coe.mpr hdeg
  exact hlt.trans_le hord

/-- Continuity of `MvPowerSeries.subst a` in the Pi topology for `a` with zero
constant coefficient. -/
private theorem continuous_subst_of_constantCoeff_zero
    {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ R}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.subst a : MvPowerSeries σ R → MvPowerSeries τ R) := by
  classical
  apply continuous_pi_iff.mpr
  intro e
  have hS_fin := coeff_prod_pow_support_finite (R := R) ha0 e
  obtain ⟨T, hTS⟩ : ∃ T : Finset (σ →₀ ℕ),
      {d : σ →₀ ℕ | MvPowerSeries.coeff e
        (d.prod fun s e' ↦ (a s) ^ e') ≠ 0} ⊆ ↑T :=
    ⟨hS_fin.toFinset, by simp [Set.Finite.coe_toFinset]⟩
  have heq : (fun f : MvPowerSeries σ R ↦ (MvPowerSeries.subst a f) e) =
      (fun f ↦ ∑ d ∈ T, MvPowerSeries.coeff d f *
        MvPowerSeries.coeff e (d.prod fun s e' ↦ (a s) ^ e')) := by
    funext f
    change MvPowerSeries.coeff e (MvPowerSeries.subst a f) = _
    rw [MvPowerSeries.coeff_subst ha]
    rw [finsum_eq_sum_of_support_subset _ (by
      intro d hd
      rw [Function.mem_support] at hd
      apply hTS
      simp only [Set.mem_setOf_eq]
      intro heq
      apply hd
      rw [heq, smul_zero])]
    refine Finset.sum_congr rfl ?_
    intros d _
    rw [smul_eq_mul]
  rw [heq]
  exact continuous_finsetSum T fun d _ ↦
    (continuous_mul_const _).comp (MvPowerSeries.WithPiTopology.continuous_coeff R d)

/-! ### Membership and HasEval lemmas for general finite-type MvPowerSeries -/

/-- The evaluation `eval₂ id b u` of a power series `u` with zero constant coefficient
at `b : σ → M` lies in `M`. -/
private theorem mvPowerSeries_eval_mem_maximalIdeal {σ : Type*} [Finite σ]
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {b : σ → R} (hb_mem : ∀ s, b s ∈ IsLocalRing.maximalIdeal R)
    (u : MvPowerSeries σ R) (hu : MvPowerSeries.constantCoeff u = 0) :
    MvPowerSeries.eval₂ (RingHom.id R) b u ∈ IsLocalRing.maximalIdeal R := by
  have hb : MvPowerSeries.HasEval b := by
    cases nonempty_fintype σ
    refine ⟨fun s ↦ ?_, ?_⟩
    · exact isTopologicallyNilpotent_of_mem_maximalIdeal hAdic (hb_mem s)
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have hcid : Continuous (RingHom.id R) := continuous_id
  have hsum := MvPowerSeries.hasSum_eval₂ hcid hb u
  have hM_closed : IsClosed (IsLocalRing.maximalIdeal R : Set R) :=
    maximalIdeal_isClosed hAdic
  apply hM_closed.mem_of_tendsto hsum
  filter_upwards with N
  apply (IsLocalRing.maximalIdeal R).sum_mem
  intro d _hd
  simp only [RingHom.id_apply]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hu, zero_mul]
    exact (IsLocalRing.maximalIdeal R).zero_mem
  · apply (IsLocalRing.maximalIdeal R).mul_mem_left
    have hne : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    obtain ⟨s, hs⟩ := hne
    have hs_mem : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [Finsupp.prod]
    refine (IsLocalRing.maximalIdeal R).prod_mem (s := d.support) hs_mem ?_
    have hds : 0 < d s := Nat.pos_of_ne_zero hs
    exact Ideal.pow_mem_of_mem _ (hb_mem s) _ hds

/-- HasEval for a general finite-type family of elements of `M`. -/
private lemma hasEval_of_mem_maximalIdeal_general {σ : Type*} [Finite σ]
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {b : σ → R} (hb_mem : ∀ s, b s ∈ IsLocalRing.maximalIdeal R) :
    MvPowerSeries.HasEval b := by
  cases nonempty_fintype σ
  refine ⟨fun s ↦ ?_, ?_⟩
  · exact isTopologicallyNilpotent_of_mem_maximalIdeal hAdic (hb_mem s)
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

/-! ### The substitution bridge theorem

The bridge lemma says that evaluating a substitution equals the iterated
evaluation, for values of `b` in `M`. -/

/-- The substitution bridge: `eval₂ id b (subst a F) = eval₂ id (eval₂ id b ∘ a) F`. -/
theorem eval₂_subst_bridge {σ τ : Type*} [Finite σ] [Finite τ]
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    {a : σ → MvPowerSeries τ R}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (ha : MvPowerSeries.HasSubst a)
    {b : τ → R} (hb_mem : ∀ i, b i ∈ IsLocalRing.maximalIdeal R)
    (F : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ (RingHom.id R) b (MvPowerSeries.subst a F) =
      MvPowerSeries.eval₂ (RingHom.id R)
        (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)) F := by
  have hb := hasEval_of_mem_maximalIdeal_general hAdic hb_mem
  have hbcomp : MvPowerSeries.HasEval
      (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)) := by
    cases nonempty_fintype σ
    refine ⟨fun s ↦ ?_, ?_⟩
    · apply isTopologicallyNilpotent_of_mem_maximalIdeal hAdic
      exact mvPowerSeries_eval_mem_maximalIdeal hAdic hb_mem (a s) (ha0 s)
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have hcid : Continuous (RingHom.id R) := continuous_id
  -- Use eval₂_unique to identify (f ↦ eval₂ id b (subst a f)) with eval₂ id (eval₂ id b ∘ a).
  have key := MvPowerSeries.eval₂_unique (σ := σ) (R := R) (S := R)
    (φ := RingHom.id R) (a := fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s))
    hcid hbcomp (ε := fun f ↦
      MvPowerSeries.eval₂ (RingHom.id R) b (MvPowerSeries.subst a f))
    (hε := (MvPowerSeries.continuous_eval₂ hcid hb).comp
      (continuous_subst_of_constantCoeff_zero ha0 ha))
    (h := ?_)
  · exact congrFun key F
  · -- Polynomial agreement.
    intro p
    rw [MvPowerSeries.subst_coe (a := a) (R := R) (τ := τ) (S := R) p,
        MvPolynomial.aeval_def]
    -- Apply MvPolynomial.eval₂_comp_left with k = eval₂Hom hcid hb.
    rw [show MvPowerSeries.eval₂ (RingHom.id R) b =
        (MvPowerSeries.eval₂Hom hcid hb : MvPowerSeries τ R →+* R) from
        (MvPowerSeries.coe_eval₂Hom hcid hb).symm]
    rw [MvPolynomial.eval₂_comp_left (MvPowerSeries.eval₂Hom hcid hb)
          (algebraMap R (MvPowerSeries τ R)) a p]
    -- Now match the two sides.
    have hcomp : ((MvPowerSeries.eval₂Hom hcid hb).comp
        (algebraMap R (MvPowerSeries τ R)) : R →+* R) = RingHom.id R := by
      ext r
      simp only [RingHom.comp_apply, MvPowerSeries.coe_eval₂Hom, RingHom.id_apply]
      rw [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul, mul_one]
      rw [show (MvPowerSeries.C (σ := τ) (R := R) r : MvPowerSeries τ R) =
            ((MvPolynomial.C r : MvPolynomial τ R) : MvPowerSeries τ R) from
            (MvPolynomial.coe_C r).symm]
      rw [MvPowerSeries.eval₂_coe]
      simp [MvPolynomial.eval₂_C]
    rw [hcomp]
    -- Goal: MvPolynomial.eval₂ (RingHom.id R) ((eval₂Hom hcid hb) ∘ a) p =
    --       MvPolynomial.eval₂ (RingHom.id R) (fun s ↦ eval₂ id b (a s)) p
    -- The functions are equal (∘ = fun s =>).
    rfl

/-! ### Bridge: univariate version

Bridging the univariate evaluation `PowerSeries.eval₂ id x` (on `PowerSeries R`,
viewed as `MvPowerSeries Unit R`) with `MvPowerSeries.eval₂`. -/

omit [IsLocalRing R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsLinearTopology R R]
  [T2Space R] [CompleteSpace R] in
/-- The univariate version: for `u : PowerSeries R` with zero const coeff and `x ∈ M`,
`PowerSeries.eval₂ id x u = MvPowerSeries.eval₂ id (fun _ => x) u`. -/
private theorem powerSeries_eval₂_eq_mvEval₂
    (u : PowerSeries R) (x : R) :
    PowerSeries.eval₂ (RingHom.id R) x u =
      MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit ↦ x) u := rfl

/-! ### The inverse axiom: `F(x, -_F x) = 0` -/

/-- **The inverse axiom** (Silverman IV.3): `F(x, i(x)) = 0`, i.e.,
`evalAdd F x (evalNeg F x) = 0`. -/
theorem FormalGroup.evalAdd_evalNeg
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) :
    F.evalAdd x ⟨F.evalNeg x, F.evalNeg_mem hAdic x⟩ = 0 := by
  -- `fAdd F X (inverse F) = 0` ⇒ after applying `PowerSeries.eval₂ id x`, we get
  -- `eval₂ id x (subst ![X, inverse F] F.toSeries) = eval₂ id x 0 = 0`.
  -- By the bridge, LHS = `eval₂ id ![eval₂ id x X, eval₂ id x (inverse F)] F.toSeries`
  --                   = `eval₂ id ![x, evalNeg F x] F.toSeries`
  --                   = `evalAdd F x ⟨evalNeg F x, _⟩`.
  -- So evalAdd F x (evalNeg F x) = 0.
  have hfg_zero : HasseWeil.FG.fAdd F PowerSeries.X F.inverse = 0 :=
    F.fAdd_X_inverse_eq_zero
  -- `fAdd F X inverse = subst ![X, inverse] F.toSeries` (unfolding).
  change MvPowerSeries.eval₂ (RingHom.id R) (![x.1, F.evalNeg x] : Fin 2 → R) F.toSeries = 0
  -- Apply the bridge with a := ![PowerSeries.X, F.inverse], b := fun _ ↦ x,
  -- or equivalently treat everything in MvPowerSeries.
  -- Set up: a : Fin 2 → PowerSeries R = MvPowerSeries Unit R
  let a : Fin 2 → MvPowerSeries Unit R := ![PowerSeries.X, F.inverse]
  have ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0 := by
    intro s
    fin_cases s
    · -- a 0 = PowerSeries.X: constantCoeff = 0.
      show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0
      change PowerSeries.constantCoeff (R := R) PowerSeries.X = 0
      simp
    · -- a 1 = F.inverse: constantCoeff = 0 by F.inverse_constantCoeff.
      show MvPowerSeries.constantCoeff (F.inverse : PowerSeries R) = 0
      exact F.inverse_constantCoeff
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s ↦ ha0 s)
  -- The substitution gives us `subst a F.toSeries` ∈ MvPowerSeries Unit R = PowerSeries R.
  -- By hfg_zero, `subst a F.toSeries = fAdd F X inverse = 0`.
  have hsubst_zero : MvPowerSeries.subst a F.toSeries = 0 := by
    have : MvPowerSeries.subst a F.toSeries = HasseWeil.FG.fAdd F PowerSeries.X F.inverse := rfl
    rw [this, hfg_zero]
  -- Apply eval₂ id (fun _ ↦ x.1) to both sides. RHS = 0.
  have hb_mem : ∀ _ : Unit, x.1 ∈ IsLocalRing.maximalIdeal R := fun _ ↦ x.2
  have bridge := eval₂_subst_bridge hAdic ha0 ha (b := fun _ : Unit ↦ x.1) hb_mem F.toSeries
  -- bridge: eval₂ id (fun _ ↦ x.1) (subst a F.toSeries) =
  --         eval₂ id (fun s ↦ eval₂ id (fun _ ↦ x.1) (a s)) F.toSeries
  rw [hsubst_zero] at bridge
  have heval_zero : MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit ↦ x.1)
      (0 : MvPowerSeries Unit R) = 0 := by
    change PowerSeries.eval₂ (RingHom.id R) x.1 (0 : PowerSeries R) = 0
    rw [show (0 : PowerSeries R) = ((0 : Polynomial R) : PowerSeries R) from by simp,
        PowerSeries.eval₂_coe]
    simp
  rw [heval_zero] at bridge
  -- Now LHS of bridge is 0. RHS: eval₂ id (fun s ↦ eval_x (a s)) F.toSeries.
  -- The function `fun s ↦ eval_x (a s)` is `fun s ↦ eval_x (![X, inverse] s)`:
  --   s = 0: eval_x X = x.1.
  --   s = 1: eval_x inverse = F.evalNeg x.
  have hfun : (fun s : Fin 2 ↦
        MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit ↦ x.1) (a s)) =
      ![x.1, F.evalNeg x] := by
    funext s
    fin_cases s
    · -- s = 0: a 0 = PowerSeries.X, eval_x X = x.1.
      show MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit ↦ x.1) (PowerSeries.X : PowerSeries R)
          = x.1
      change PowerSeries.eval₂ (RingHom.id R) x.1 PowerSeries.X = x.1
      rw [PowerSeries.eval₂_X]
    · -- s = 1: a 1 = F.inverse, eval_x inverse = F.evalNeg x (definitionally).
      show MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit ↦ x.1) F.inverse = F.evalNeg x
      change PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse = F.evalNeg x
      rfl
  rw [hfun] at bridge
  exact bridge.symm

/-! ### Associativity of `evalAdd` -/

set_option maxHeartbeats 800000 in
/-- **Associativity of `evalAdd`** (Silverman IV.3):
`F.evalAdd (F.evalAdd x y) z = F.evalAdd x (F.evalAdd y z)`. -/
theorem FormalGroup.evalAdd_assoc
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (F : FormalGroup R)
    (x y z : IsLocalRing.maximalIdeal R) :
    F.evalAdd ⟨F.evalAdd x y, F.evalAdd_mem hAdic x y⟩ z =
    F.evalAdd x ⟨F.evalAdd y z, F.evalAdd_mem hAdic y z⟩ := by
  -- Strategy: apply `eval₂ id ![x,y,z]` to both sides of `F.assoc`.
  -- F.assoc : subst ![F_XY, X 2] F.toSeries = subst ![X 0, F_YZ] F.toSeries,
  -- where F_XY = subst ![X 0, X 1] F.toSeries, F_YZ = subst ![X 1, X 2] F.toSeries.
  -- Taking eval_xyz of both sides: eval_xyz (LHS) = eval_xyz (RHS).
  -- Bridge identifies these with F.evalAdd (F.evalAdd x y) z resp. F.evalAdd x (F.evalAdd y z).
  change MvPowerSeries.eval₂ (RingHom.id R) (![F.evalAdd x y, z.1] : Fin 2 → R) F.toSeries =
         MvPowerSeries.eval₂ (RingHom.id R) (![x.1, F.evalAdd y z] : Fin 2 → R) F.toSeries
  -- Define xyz := ![x.1, y.1, z.1] : Fin 3 → R.
  set xyz : Fin 3 → R := ![x.1, y.1, z.1]
  have hxyz_mem : ∀ i : Fin 3, xyz i ∈ IsLocalRing.maximalIdeal R := by
    intro i; fin_cases i <;> simp [xyz, x.2, y.2, z.2]
  -- Inner substitutions a_L = ![F_XY, X 2] and a_R = ![X 0, F_YZ] (all in MvPowerSeries (Fin 3) R).
  -- Inner XY / YZ: ![X 0, X 1] / ![X 1, X 2] as maps Fin 2 → MvPS (Fin 3) R.
  set XY : Fin 2 → MvPowerSeries (Fin 3) R := ![MvPowerSeries.X 0, MvPowerSeries.X 1]
  set YZ : Fin 2 → MvPowerSeries (Fin 3) R := ![MvPowerSeries.X 1, MvPowerSeries.X 2]
  have hXY0 : ∀ s, MvPowerSeries.constantCoeff (XY s) = 0 := by
    intro s; fin_cases s <;> simp [XY]
  have hYZ0 : ∀ s, MvPowerSeries.constantCoeff (YZ s) = 0 := by
    intro s; fin_cases s <;> simp [YZ]
  have hXY : MvPowerSeries.HasSubst XY :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXY0
  have hYZ : MvPowerSeries.HasSubst YZ :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hYZ0
  -- Outer substitutions: ![subst_XY F, X 2] and ![X 0, subst_YZ F].
  let F_XY : MvPowerSeries (Fin 3) R := MvPowerSeries.subst XY F.toSeries
  let F_YZ : MvPowerSeries (Fin 3) R := MvPowerSeries.subst YZ F.toSeries
  set aL : Fin 2 → MvPowerSeries (Fin 3) R := ![F_XY, MvPowerSeries.X 2]
  set aR : Fin 2 → MvPowerSeries (Fin 3) R := ![MvPowerSeries.X 0, F_YZ]
  have hF_XY_cc : MvPowerSeries.constantCoeff F_XY = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst XY F.toSeries) = 0
    rw [HasseWeil.FG.constantCoeff_subst_vanishing hXY hXY0]
    exact HasseWeil.FG.constantCoeff_FG_toSeries F
  have hF_YZ_cc : MvPowerSeries.constantCoeff F_YZ = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst YZ F.toSeries) = 0
    rw [HasseWeil.FG.constantCoeff_subst_vanishing hYZ hYZ0]
    exact HasseWeil.FG.constantCoeff_FG_toSeries F
  have haL0 : ∀ s, MvPowerSeries.constantCoeff (aL s) = 0 := by
    intro s; fin_cases s
    · exact hF_XY_cc
    · simp [aL]
  have haR0 : ∀ s, MvPowerSeries.constantCoeff (aR s) = 0 := by
    intro s; fin_cases s
    · simp [aR]
    · exact hF_YZ_cc
  have haL : MvPowerSeries.HasSubst aL :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero haL0
  have haR : MvPowerSeries.HasSubst aR :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero haR0
  -- F.assoc: subst aL F.toSeries = subst aR F.toSeries
  have h_assoc : MvPowerSeries.subst aL F.toSeries =
      MvPowerSeries.subst aR F.toSeries := F.assoc
  -- Apply eval₂ id xyz (a ring hom).
  have h_step : MvPowerSeries.eval₂ (RingHom.id R) xyz
      (MvPowerSeries.subst aL F.toSeries) =
      MvPowerSeries.eval₂ (RingHom.id R) xyz
      (MvPowerSeries.subst aR F.toSeries) := by
    rw [h_assoc]
  -- Apply the bridge to both sides.
  have hbridge_L := eval₂_subst_bridge hAdic haL0 haL (b := xyz) hxyz_mem F.toSeries
  have hbridge_R := eval₂_subst_bridge hAdic haR0 haR (b := xyz) hxyz_mem F.toSeries
  rw [hbridge_L, hbridge_R] at h_step
  -- h_step: eval₂ id (eval_xyz ∘ aL) F.toSeries = eval₂ id (eval_xyz ∘ aR) F.toSeries.
  -- Compute eval_xyz ∘ aL and eval_xyz ∘ aR.
  -- For s = 0: eval_xyz (aL 0) = eval_xyz F_XY = ? (needs inner bridge).
  -- For s = 1: eval_xyz (aL 1) = eval_xyz (X 2) = z.1.
  -- Inner bridge for eval_xyz F_XY:
  have hbridge_XY := eval₂_subst_bridge hAdic hXY0 hXY (b := xyz) hxyz_mem F.toSeries
  have hbridge_YZ := eval₂_subst_bridge hAdic hYZ0 hYZ (b := xyz) hxyz_mem F.toSeries
  -- eval_xyz F_XY = eval₂ id (eval_xyz ∘ XY) F.toSeries = eval₂ id ![x,y] F.toSeries = evalAdd F x y.
  have hxy_fn : (fun s : Fin 2 ↦ MvPowerSeries.eval₂ (RingHom.id R) xyz (XY s)) =
      ![x.1, y.1] := by
    funext s
    fin_cases s
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (0 : Fin 3)) = x.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (1 : Fin 3)) = y.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
  have hyz_fn : (fun s : Fin 2 ↦ MvPowerSeries.eval₂ (RingHom.id R) xyz (YZ s)) =
      ![y.1, z.1] := by
    funext s
    fin_cases s
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (1 : Fin 3)) = y.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (2 : Fin 3)) = z.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
  rw [hxy_fn] at hbridge_XY
  rw [hyz_fn] at hbridge_YZ
  -- hbridge_XY: eval_xyz F_XY = eval₂ id ![x,y] F.toSeries = evalAdd F x y
  -- hbridge_YZ: eval_xyz F_YZ = eval₂ id ![y,z] F.toSeries = evalAdd F y z
  -- Now compute eval_xyz ∘ aL and eval_xyz ∘ aR:
  have hL_fn : (fun s : Fin 2 ↦ MvPowerSeries.eval₂ (RingHom.id R) xyz (aL s)) =
      ![F.evalAdd x y, z.1] := by
    funext s
    fin_cases s
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz F_XY = F.evalAdd x y
      rw [hbridge_XY]; rfl
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (2 : Fin 3)) = z.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
  have hR_fn : (fun s : Fin 2 ↦ MvPowerSeries.eval₂ (RingHom.id R) xyz (aR s)) =
      ![x.1, F.evalAdd y z] := by
    funext s
    fin_cases s
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz (MvPowerSeries.X (0 : Fin 3)) = x.1
      rw [MvPowerSeries.eval₂_X]; simp [xyz]
    · show MvPowerSeries.eval₂ (RingHom.id R) xyz F_YZ = F.evalAdd y z
      rw [hbridge_YZ]; rfl
  rw [hL_fn, hR_fn] at h_step
  exact h_step

/-! ### The `AddCommGroup` instance on `F.EvalGroup hAdic`

With `evalAdd_assoc`, the unit and commutativity laws, and the inverse axiom
`evalAdd_evalNeg` all proven, we can bundle `M` into an `AddCommGroup`.

To avoid a typeclass diamond with the native `AddCommGroup (maximalIdeal R)`
coming from the `Submodule R R` structure, we use a one-field wrapper
`F.EvalGroup hAdic` carrying the formal-group `AddCommGroup` structure. -/

/-- Wrapper type carrying the formal-group `AddCommGroup` structure on the
maximal ideal `M`, to avoid a typeclass diamond with the native
`AddCommGroup (maximalIdeal R)` from the `Submodule` structure. -/
@[ext]
structure FormalGroup.EvalGroup (_ : FormalGroup R)
    (_ : IsAdic (IsLocalRing.maximalIdeal R)) where
  /-- The underlying element of `M`. -/
  val : IsLocalRing.maximalIdeal R

namespace FormalGroup.EvalGroup

variable {F : FormalGroup R} {hAdic : IsAdic (IsLocalRing.maximalIdeal R)}

/-- The zero element of `F.EvalGroup hAdic`. -/
instance : Zero (F.EvalGroup hAdic) :=
  ⟨⟨⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩⟩⟩

/-- The formal-group addition on `F.EvalGroup hAdic`. -/
noncomputable instance : Add (F.EvalGroup hAdic) :=
  ⟨fun x y ↦ ⟨⟨F.evalAdd x.val y.val, F.evalAdd_mem hAdic x.val y.val⟩⟩⟩

/-- The formal-group negation on `F.EvalGroup hAdic`. -/
noncomputable instance : Neg (F.EvalGroup hAdic) :=
  ⟨fun x ↦ ⟨⟨F.evalNeg x.val, F.evalNeg_mem hAdic x.val⟩⟩⟩

omit [IsUniformAddGroup R] [IsTopologicalRing R] [IsLinearTopology R R]
  [T2Space R] [CompleteSpace R] in
@[simp]
theorem val_zero : (0 : F.EvalGroup hAdic).val = ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩ :=
  rfl

@[simp]
theorem val_add (x y : F.EvalGroup hAdic) :
    (x + y).val = ⟨F.evalAdd x.val y.val, F.evalAdd_mem hAdic x.val y.val⟩ :=
  rfl

@[simp]
theorem val_neg (x : F.EvalGroup hAdic) :
    (-x).val = ⟨F.evalNeg x.val, F.evalNeg_mem hAdic x.val⟩ :=
  rfl

end FormalGroup.EvalGroup

/-- **The `AddCommGroup` structure on `F(M)`** (Silverman IV.3, closing T-IV-3-001).

For a complete local ring `(R, M)` and a formal group law `F`, the maximal
ideal `M` becomes an abelian group under `+_F := F(x, y)`, `0`, and
`-_F := inverse F`, with the carrier `F.EvalGroup hAdic`.

We construct it as a plain `AddCommGroup` record, supplying the default
`nsmul`/`zsmul`/`sub` fields via the standard recursors. -/
noncomputable instance FormalGroup.EvalGroup.instAddCommGroup
    (F : FormalGroup R) (hAdic : IsAdic (IsLocalRing.maximalIdeal R)) :
    AddCommGroup (F.EvalGroup hAdic) :=
  letI addGroup : AddGroup (F.EvalGroup hAdic) :=
    AddGroup.ofLeftAxioms
      (fun x y z ↦
        FormalGroup.EvalGroup.ext
          (Subtype.ext (F.evalAdd_assoc hAdic x.val y.val z.val)))
      (fun x ↦
        FormalGroup.EvalGroup.ext
          (Subtype.ext (F.evalAdd_zero_left hAdic x.val)))
      (fun x ↦
        FormalGroup.EvalGroup.ext
          (Subtype.ext (by
            change F.evalAdd ⟨F.evalNeg x.val, F.evalNeg_mem hAdic x.val⟩ x.val = 0
            rw [F.evalAdd_comm hAdic]
            exact F.evalAdd_evalNeg hAdic x.val)))
  { addGroup with
    add_comm := fun x y ↦
      FormalGroup.EvalGroup.ext
        (Subtype.ext (F.evalAdd_comm hAdic x.val y.val)) }

end EvalGroup

end HasseWeil.FormalGroup

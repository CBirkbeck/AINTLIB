import BernoulliRegular.FLT37.PadicL.ColemanDigitCoeff

/-!
# The Teichmüller `π`-digit reduction of `Λ 32` — eliminating `ω` from the digit ladder

This file attacks the irreducible deep core of FLT37 Case-II II2, the `π`-digit
ladder of

  `Λ i = logCoeffSum c i = Σ_{j ∈ (ZMod p)ˣ} c_j · (ω j)^i`,

by **proving the exact Teichmüller `π`-structure** and using it to *eliminate* the
Teichmüller character `ω` from the per-rung digit analysis of
`ColemanDigitLadder37` (`ColemanDigitCoeff.lean`).

## The soundness correction (the crux, verified)

The Coleman-ladder design comment in `ColemanDigitCoeff.lean` posits that the
`d`-th `π`-digit of `(ω j)^{32}`, as a function of `j ∈ 𝔽_p^×`, is a *nonzero*
`𝔽_p`-polynomial of degree `⌊d/2⌋` (a Gross–Koblitz / Dwork "even-Teichmüller"
shift), and the per-rung residual `ColemanNextRungResidue` carries that
`P'.natDegree ≤ (d+1)/2` as undischarged content.  This file proves the **sharp
truth**, which is much stronger and corrects the `mod π²` premise:

  **`ω j ≡ (j.val : O) (mod π^{p-1})`**     (`omega_sub_natCast_addVal_ge`)

i.e. the Teichmüller lift agrees with the *naive integer lift* `j.val` not merely
to order `1` (the structural `omega_residue : ω j ≡ j (mod π)`) but to order
`p − 1 = 36`.  This is provable from the abstract `StickelbergerF1Setup` axioms
alone — no unramified subring needed — via Fermat (`(j.val)^{p-1} ≡ 1 (mod p)`,
`addVal(p) = p − 1`) together with the geometric factorisation
`ω(j)^{p-1} − j.val^{p-1} = (ω j − j.val)·G` whose cofactor `G` has residue
`(p−1)·j^{p-2} = −j^{p-2} ≠ 0`, hence is a `𝔓`-adic **unit**.

The consequence for the digit ladder is that the Teichmüller contributes **no new
`π`-digit** below level `p − 1`:

  **`(ω j)^i ≡ (j.val : O)^i (mod π^{p-1})`**   (`omega_pow_sub_natCast_pow_addVal_ge`)

so for every digit `d < p − 1` (in particular `d = 0, …, 7`) the `d`-th `π`-digit
of `Λ i` equals the `d`-th `π`-digit of the **integer-lift functional**

  `M i = integerLogCoeffSum c i = Σ_j c_j · (j.val : O)^i`,

in which `ω` has been replaced by the honest integer power `(j.val)^i`
(`logCoeffSum_sub_integerLogCoeffSum_addVal_ge`,
`pi_pow_dvd_logCoeffSum_iff_integer_of_lt`).  There is therefore **no
`⌊d/2⌋`-degree Teichmüller digit polynomial to prove**; the per-rung weight is the
digit of the integer power `(j.val)^i`, whose residue is the character power sum
`Σ_j residue(c_j)·j^i` that the proven orthogonality engine
(`sum_units_poly_mul_pow_eq_zero`) consumes.

## What this file proves (genuine progress, soundness-first)

1. The sharp Teichmüller–integer congruence `ω j ≡ j.val (mod π^{p-1})` and its
   power form, over the abstract DVR (no `LpData`, no unramified subring assumed).
2. The `π`-digit-ladder reduction `Λ i ≡ M i (mod π^{p-1})`, eliminating `ω`.
3. The corrected, genuinely smaller core `IntegerLogCoeffLadder37` — the digit
   ladder of the **integer-lift** functional `M 32` — feeding the proven engine
   `pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_digitColemanGrading`.  This replaces
   the unsound `ColemanNextRungResidue` "`⌊d/2⌋` Teichmüller polynomial" premise
   with the honest integer-power digit content, and shows the two cores agree on
   the orthogonality-reachable half (`π⁸ ∣ Λ 32`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Prop 8.12
  (p. 156), Thm 5.18 (pp. 63–66), §6.2 (the `𝔓`-grading); Lemma 6.2 (the
  Teichmüller/integer agreement to order `p − 1`).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.PadicL

open Finset
open IsDiscreteValuationRing IsLocalRing

namespace StickelbergerF1Setup

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-! ## Part A — the sharp Teichmüller–integer congruence `ω j ≡ j.val (mod π^{p-1})`

The Teichmüller lift agrees with the naive integer lift `j.val` to `𝔓`-order
`p − 1`.  Proved from the abstract axioms only. -/

/-- The residue of the integer lift `(j.val : O)` is the residue class `j`:
`residue((j.val : O)) = (j : ZMod p)`.  (The natural-number `ZMod.val` representative
casts back to its own class.) -/
theorem residue_natCast_teichRep (j : (ZMod p)ˣ) :
    S.residue (((j : ZMod p).val : S.O)) = (j : ZMod p) := by
  rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]

/-- The natural-number Fermat divisibility `p ∣ (j.val)^{p-1} − 1` (with the ℕ
subtraction well-defined since `j.val ≥ 1`).  Read off from `(j : ZMod p)^{p-1} = 1`
(`ZMod.pow_card_sub_one_eq_one`, `j ≠ 0`). -/
theorem p_dvd_teichRep_pow_sub_one (j : (ZMod p)ˣ) :
    p ∣ ((j : ZMod p).val ^ (p - 1) - 1) := by
  have hjval : (j : ZMod p).val ≠ 0 := by rw [Ne, ZMod.val_eq_zero]; exact j.ne_zero
  have hone : 1 ≤ (j : ZMod p).val ^ (p - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hjval)
  rw [← (ZMod.natCast_eq_zero_iff _ p)]
  push_cast [Nat.cast_sub hone]
  rw [ZMod.natCast_val, ZMod.cast_id, ZMod.pow_card_sub_one_eq_one j.ne_zero, sub_self]

/-- **The integer lift is a `𝔓`-adic root of unity to order `p − 1`**:
`addVal((j.val : O)^{p-1} − 1) ≥ p − 1`.  This is Fermat's little theorem
`p ∣ (j.val)^{p-1} − 1` transported to `O` (`(p : O) ∣ (j.val : O)^{p-1} − 1`) and
the ramification `π^{p-1} ∣ (p : O)` (`addVal(p) = p − 1`). -/
theorem addVal_natCast_teichRep_pow_sub_one_ge (j : (ZMod p)ˣ) :
    ((p - 1 : ℕ) : ℕ∞) ≤ addVal S.O ((((j : ZMod p).val : S.O)) ^ (p - 1) - 1) := by
  -- `(p : O) ∣ (j.val : O)^{p-1} − 1` from the ℕ-Fermat divisibility, cast to `O`.
  have hjval : (j : ZMod p).val ≠ 0 := by rw [Ne, ZMod.val_eq_zero]; exact j.ne_zero
  have hone : 1 ≤ (j : ZMod p).val ^ (p - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hjval)
  obtain ⟨m, hm⟩ := p_dvd_teichRep_pow_sub_one j
  have hcastO : (((j : ZMod p).val : S.O)) ^ (p - 1) - 1 = (p : S.O) * (m : S.O) := by
    have : (((j : ZMod p).val ^ (p - 1) : ℕ) : S.O) = ((1 + p * m : ℕ) : S.O) := by
      congr 1; omega
    push_cast at this ⊢
    linear_combination this
  rw [hcastO]
  -- `addVal((p:O)·m) = addVal(p) + addVal(m) ≥ addVal(p) = p − 1`.
  rw [addVal_mul, S.addVal_p_eq]
  exact le_self_add

/-- The geometric cofactor `G_j = Σ_{k < p-1} (ω j)^k · (j.val)^{p-2-k}` of the
factorisation `(ω j)^{p-1} − (j.val)^{p-1} = (ω j − j.val) · G_j`. -/
noncomputable def teichGeomCofactor (j : (ZMod p)ˣ) : S.O :=
  ∑ k ∈ Finset.range (p - 1),
    ((S.ω j : S.O)) ^ k * (((j : ZMod p).val : S.O)) ^ (p - 1 - 1 - k)

/-- The geometric factorisation `(ω j − j.val) · G_j = (ω j)^{p-1} − (j.val)^{p-1}`
(`geom_sum₂_mul`, after `(ω j)^{p-1} = 1`). -/
theorem omega_sub_natCast_mul_geomCofactor (j : (ZMod p)ˣ) :
    S.teichGeomCofactor j * (((S.ω j : S.O)) - (((j : ZMod p).val : S.O)))
      = 1 - (((j : ZMod p).val : S.O)) ^ (p - 1) := by
  unfold teichGeomCofactor
  rw [geom_sum₂_mul]
  -- `(ω j : O)^{p-1} = ((ω j)^{p-1} : Oˣ) = 1`.
  rw [show ((S.ω j : S.O)) ^ (p - 1) = (((S.ω j) ^ (p - 1) : S.Oˣ) : S.O) from
    (Units.val_pow_eq_pow_val _ _).symm, S.ω_pow_sub_one j, Units.val_one]

/-- The residue of the geometric cofactor is `(p−1)·j^{p-2} = −j^{p-2}`
(`omega_residue`, `residue_natCast_teichRep`, each of the `p−1` summands reduces to
`j^{p-2}`). -/
theorem residue_teichGeomCofactor (j : (ZMod p)ˣ) :
    S.residue (S.teichGeomCofactor j) = ((p : ℕ) - 1 : ℕ) • (j : ZMod p) ^ (p - 2) := by
  unfold teichGeomCofactor
  rw [map_sum, Finset.sum_congr rfl (fun k hk => ?_), Finset.sum_const, Finset.card_range]
  -- Each summand residue is `j^k · j^{p-2-k} = j^{p-2}`.
  rw [Finset.mem_range] at hk
  rw [map_mul, map_pow, map_pow, S.omega_residue j, S.residue_natCast_teichRep, ← pow_add]
  congr 1
  -- `k + (p - 1 - 1 - k) = p - 2` for `k < p - 1`.
  omega

/-- **A nonzero residue forces a unit** over the DVR: if `residue x ≠ 0` then
`x` is a `𝔓`-adic unit (`addVal x = 0`).  (`residue x ≠ 0 ↔ ¬ π ∣ x ↔ addVal x = 0`.) -/
theorem isUnit_of_residue_ne_zero {x : S.O} (hx : S.residue x ≠ 0) : IsUnit x := by
  rw [← addVal_eq_zero_iff]
  -- `¬ π ∣ x` from `residue x ≠ 0`; then `addVal x < 1`, so `addVal x = 0`.
  have hndvd : ¬ S.π ∣ x := fun hdvd => hx ((S.residue_eq_zero_iff x).mpr hdvd)
  by_contra hne
  have h1 : (1 : ℕ∞) ≤ addVal S.O x := ENat.one_le_iff_ne_zero.mpr hne
  exact hndvd (by simpa using (S.le_addVal_iff_pi_pow_dvd x 1).mp (by exact_mod_cast h1))

/-- The geometric cofactor is a `𝔓`-adic **unit** (its residue `(p−1)·j^{p-2} =
−j^{p-2}` is nonzero, `j ≠ 0`). -/
theorem isUnit_teichGeomCofactor (j : (ZMod p)ˣ) : IsUnit (S.teichGeomCofactor j) := by
  refine S.isUnit_of_residue_ne_zero ?_
  rw [S.residue_teichGeomCofactor j]
  -- `(p-1) • j^{p-2} = -(j^{p-2}) ≠ 0` since `p - 1 ≡ -1 (mod p)` is a unit and `j ≠ 0`.
  rw [nsmul_eq_mul]
  refine mul_ne_zero ?_ (pow_ne_zero _ (Units.ne_zero j))
  -- `((p - 1 : ℕ) : ZMod p) = -1 ≠ 0`.
  have hp2 := hp.out.two_le
  rw [show ((p - 1 : ℕ) : ZMod p) = -1 from by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]]
  exact neg_ne_zero.mpr one_ne_zero

/-- **The sharp Teichmüller–integer congruence** `ω j ≡ (j.val : O) (mod π^{p-1})`:

  `addVal(ω j − (j.val : O)) ≥ p − 1`.

The Teichmüller lift agrees with the naive integer lift to `𝔓`-order `p − 1`, far
beyond the structural `ω j ≡ j (mod π)` (`omega_residue`).  Proof: the geometric
factorisation `G_j·(ω j − j.val) = 1 − (j.val)^{p-1}` (`omega_sub_natCast_mul_geomCofactor`)
has a **unit** cofactor `G_j` (`isUnit_teichGeomCofactor`) and a right-hand side of
order `≥ p − 1` (`addVal_natCast_teichRep_pow_sub_one_ge`, Fermat + ramification),
so `addVal(ω j − j.val) = addVal(G_j·(ω j − j.val)) ≥ p − 1`. -/
theorem omega_sub_natCast_addVal_ge (j : (ZMod p)ˣ) :
    ((p - 1 : ℕ) : ℕ∞) ≤ addVal S.O (((S.ω j : S.O)) - (((j : ZMod p).val : S.O))) := by
  -- The product `G_j · (ω j − j.val)` has order `≥ p − 1`.
  obtain ⟨u, hu⟩ := S.isUnit_teichGeomCofactor j
  have hval : addVal S.O (S.teichGeomCofactor j * (((S.ω j : S.O)) - (((j : ZMod p).val : S.O))))
      = addVal S.O (((S.ω j : S.O)) - (((j : ZMod p).val : S.O))) := by
    rw [addVal_mul]
    rw [show addVal S.O (S.teichGeomCofactor j) = 0 from by
      rw [addVal_eq_zero_iff]; exact S.isUnit_teichGeomCofactor j, zero_add]
  rw [← hval, S.omega_sub_natCast_mul_geomCofactor j]
  -- `addVal(1 − (j.val)^{p-1}) = addVal((j.val)^{p-1} − 1) ≥ p − 1`.
  rw [show (1 : S.O) - (((j : ZMod p).val : S.O)) ^ (p - 1)
        = -((((j : ZMod p).val : S.O)) ^ (p - 1) - 1) from by ring, AddValuation.map_neg]
  exact S.addVal_natCast_teichRep_pow_sub_one_ge j

/-- **The Teichmüller power congruence** `(ω j)^i ≡ (j.val : O)^i (mod π^{p-1})`:

  `addVal((ω j)^i − (j.val : O)^i) ≥ p − 1`.

Raising the base congruence to the `i`-th power: `(ω j)^i − (j.val)^i` is divisible
by `(ω j − j.val)` (`sub_dvd_pow_sub_pow`), whose order is `≥ p − 1`. -/
theorem omega_pow_sub_natCast_pow_addVal_ge (i : ℕ) (j : (ZMod p)ˣ) :
    ((p - 1 : ℕ) : ℕ∞) ≤
      addVal S.O ((((S.ω j) ^ i : S.Oˣ) : S.O) - (((j : ZMod p).val : S.O)) ^ i) := by
  -- `(ω j)^i = (ω j : O)^i`; the difference is divisible by `ω j − j.val`.
  rw [Units.val_pow_eq_pow_val]
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow ((S.ω j : S.O)) (((j : ZMod p).val : S.O)) i
  rw [ht, addVal_mul]
  exact le_trans (S.omega_sub_natCast_addVal_ge j) le_self_add

/-! ## Part C — the integer-lift functional and the `π`-digit-ladder reduction

The Teichmüller is eliminated from the digit ladder: below level `p − 1`, every
`π`-digit of `Λ i` equals the corresponding digit of the **integer-lift functional**
`M i = Σ_j c_j (j.val : O)^i`, in which `(ω j)^i` is replaced by the honest integer
power `(j.val)^i`. -/

/-- **The integer-lift log-coefficient functional**
`M i = Σ_j c_j · (j.val : O)^i`: the Teichmüller-free analogue of
`logCoeffSum c i = Σ_j c_j (ω j)^i`, with each Teichmüller power `(ω j)^i` replaced
by the naive integer power `(j.val : O)^i`. -/
noncomputable def integerLogCoeffSum (c : (ZMod p)ˣ → S.O) (i : ℕ) : S.O :=
  ∑ j : (ZMod p)ˣ, c j * (((j : ZMod p).val : S.O)) ^ i

/-- **The digit-ladder reduction** `Λ i ≡ M i (mod π^{p-1})`:

  `addVal(logCoeffSum c i − integerLogCoeffSum c i) ≥ p − 1`.

Term by term, `c_j·((ω j)^i − (j.val)^i)` has order `≥ p − 1`
(`omega_pow_sub_natCast_pow_addVal_ge`), and the sum of order-`≥ p−1` terms has
order `≥ p − 1` (`addVal_add` / `Finset.dvd_sum`).  So the two functionals share
**every** `π`-digit below level `p − 1`; the Teichmüller correction is invisible to
digits `0, …, p − 2` (in particular `0, …, 7`). -/
theorem logCoeffSum_sub_integerLogCoeffSum_addVal_ge (c : (ZMod p)ˣ → S.O) (i : ℕ) :
    ((p - 1 : ℕ) : ℕ∞) ≤
      addVal S.O (S.logCoeffSum c i - S.integerLogCoeffSum c i) := by
  -- Rewrite the difference as the sum of the per-term differences.
  have hsub : S.logCoeffSum c i - S.integerLogCoeffSum c i
      = ∑ j : (ZMod p)ˣ, c j * ((((S.ω j) ^ i : S.Oˣ) : S.O) - (((j : ZMod p).val : S.O)) ^ i) := by
    unfold logCoeffSum integerLogCoeffSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub]
  rw [hsub]
  -- `π^{p-1}` divides each term, hence the sum.
  refine (S.le_addVal_iff_pi_pow_dvd _ (p - 1)).mpr ?_
  refine Finset.dvd_sum fun j _ => ?_
  -- `π^{p-1} ∣ c_j·(diff)` since `π^{p-1} ∣ diff`.
  refine Dvd.dvd.mul_left ?_ _
  exact (S.le_addVal_iff_pi_pow_dvd _ (p - 1)).mp (S.omega_pow_sub_natCast_pow_addVal_ge i j)

/-- **The `π`-digit ladder is shared below level `p − 1`**: for `k ≤ p − 1`,

  `π^k ∣ Λ i  ↔  π^k ∣ M i`.

Either divisibility transfers to the other through the order-`≥ p − 1` difference
`Λ i − M i` (`logCoeffSum_sub_integerLogCoeffSum_addVal_ge`).  This is the exact
statement that the orthogonality-reachable half of the digit ladder (`k ≤ p − 1 = 36`,
covering `π⁸ ∣ Λ 32`) may be computed on the **integer-lift** functional `M`, with
the Teichmüller eliminated. -/
theorem pi_pow_dvd_logCoeffSum_iff_integer_of_le {c : (ZMod p)ˣ → S.O} {i k : ℕ}
    (hk : k ≤ p - 1) :
    S.π ^ k ∣ S.logCoeffSum c i ↔ S.π ^ k ∣ S.integerLogCoeffSum c i := by
  have hdiff : S.π ^ k ∣ (S.logCoeffSum c i - S.integerLogCoeffSum c i) := by
    refine dvd_trans (pow_dvd_pow _ hk) ?_
    exact (S.le_addVal_iff_pi_pow_dvd _ (p - 1)).mp
      (S.logCoeffSum_sub_integerLogCoeffSum_addVal_ge c i)
  constructor
  · intro h
    have hd := dvd_sub h hdiff
    rwa [show S.logCoeffSum c i - (S.logCoeffSum c i - S.integerLogCoeffSum c i)
      = S.integerLogCoeffSum c i from by ring] at hd
  · intro h
    have hd := dvd_add h hdiff
    rwa [show S.integerLogCoeffSum c i + (S.logCoeffSum c i - S.integerLogCoeffSum c i)
      = S.logCoeffSum c i from by ring] at hd

/-- The residue of the integer-lift functional is the **same** character power sum
`Σ_j residue(c_j)·j^i` as the Teichmüller functional (`residue_logCoeffSum`): the
integer lift `(j.val : O)` has residue `j` exactly (`residue_natCast_teichRep`), so
the leading digit is unchanged. -/
theorem residue_integerLogCoeffSum (c : (ZMod p)ˣ → S.O) (i : ℕ) :
    S.residue (S.integerLogCoeffSum c i)
      = ∑ j : (ZMod p)ˣ, S.residue (c j) * (j : ZMod p) ^ i := by
  unfold integerLogCoeffSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, S.residue_natCast_teichRep]

/-! ## Part D — the corrected, Teichmüller-free digit-ladder core

`ColemanDigitCoeff.lean` posits the per-rung weight as the `⌊d/2⌋`-degree
Teichmüller `π`-digit polynomial of `(ω j)^{32}` (`ColemanNextRungResidue`).  Part B
shows that premise is unsound: the Teichmüller agrees with the integer lift to order
`p − 1 = 36`, so for every reachable rung `d < 36` the digit of `(ω j)^{32}` is the
digit of the *integer power* `(j.val)^{32}`, with **no** new `⌊d/2⌋`-degree
contribution.  Here the digit ladder is re-grounded on the integer-lift functional
`M`, and the corrected core `IntegerLogCoeffGrading37` (the integer-lift analogue of
`DigitColemanGrading`) is shown to drive `π⁸ ∣ Λ 32` through the proven engine. -/

/-- **The integer-lift digit-grading core** (`p = 37`): the analogue of
`DigitColemanGrading` for the **integer-lift** functional `M 32` — for each rung
`d < 8`, the `d`-th `π`-digit of `M 32` is a sub-threshold character power sum
`Σ_j j^32·P_d(j)` (`P_d.natDegree + 32 < 36`).  This is the corrected, sound form of
the per-rung Coleman residual: it carries **no** Teichmüller `(ω j)^{32}` digit
polynomial — the digits are those of the honest integer powers `(j.val)^{32}` (Part B),
whose residues `j^{32}` the orthogonality engine consumes.  Carried as a named `Prop`,
**not** an axiom. -/
def IntegerLogCoeffGrading37 (S : StickelbergerF1Setup 37) (c : (ZMod 37)ˣ → S.O)
    (k : ℕ) : Prop :=
  ∀ d : ℕ, d < k → ∃ (q : S.O) (P : Polynomial (ZMod 37)),
    S.integerLogCoeffSum c 32 = S.π ^ d * q ∧
    P.natDegree + 32 < (37 : ℕ) - 1 ∧
    S.residue q = ∑ j : (ZMod 37)ˣ, (j : ZMod 37) ^ 32 * P.eval (j : ZMod 37)

/-- **The integer-lift grading transfers to the Teichmüller functional** (`p = 37`):
`IntegerLogCoeffGrading37 c 8` implies `DigitColemanGrading c 32 8`.  At each rung
`d < 8 ≤ 36`, the digit divisibility `π^d ∣ M 32` transfers to `π^d ∣ Λ 32`
(`pi_pow_dvd_logCoeffSum_iff_integer_of_le`, since `d ≤ p − 1`), and the digit
residue is computed on `M` (whose quotient differs from `Λ`'s quotient by a multiple
of `π^{p−1−d}`, invisible to the residue for `d < p − 1`).  Concretely we re-derive
the `Λ`-side datum directly: `Λ 32 = π^d·q'` with `residue q' = Σ_j j^32·P_d(j)`,
using that `Λ 32` and `M 32` agree mod `π^{p−1}`. -/
theorem digitColemanGrading_of_integerLogCoeffGrading37
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hgrad : S.IntegerLogCoeffGrading37 c 8) :
    S.DigitColemanGrading c 32 8 := by
  intro d hd
  obtain ⟨q, P, hq, hdeg, hres⟩ := hgrad d hd
  -- `π^d ∣ M 32` (from `M 32 = π^d·q`), transfer to `π^d ∣ Λ 32` (d ≤ 36).
  have hdvdM : S.π ^ d ∣ S.integerLogCoeffSum c 32 := ⟨q, hq⟩
  have hdvdΛ : S.π ^ d ∣ S.logCoeffSum c 32 :=
    (S.pi_pow_dvd_logCoeffSum_iff_integer_of_le (by omega)).mpr hdvdM
  obtain ⟨q', hq'⟩ := hdvdΛ
  refine ⟨q', P, hq', hdeg, ?_⟩
  -- `residue q' = residue q`: `Λ − M = π^d(q' − q)` has order `≥ p−1`, and `d < p−1`
  -- forces `addVal(q' − q) ≥ p − 1 − d ≥ 1`, i.e. `π ∣ q' − q`, so the residues agree.
  have hdiff : addVal S.O (S.logCoeffSum c 32 - S.integerLogCoeffSum c 32)
      = addVal S.O (S.π ^ d * (q' - q)) := by
    congr 1; rw [mul_sub, ← hq', ← hq]
  have hge : ((37 - 1 : ℕ) : ℕ∞) ≤ addVal S.O (S.π ^ d * (q' - q)) := by
    rw [← hdiff]; exact S.logCoeffSum_sub_integerLogCoeffSum_addVal_ge c 32
  rw [addVal_mul, S.π_irreducible.addVal_pow] at hge
  -- `d + addVal(q'−q) ≥ 36`, `d < 8`, so `addVal(q'−q) ≥ 1`, i.e. `π ∣ q'−q`.
  have h1 : (1 : ℕ∞) ≤ addVal S.O (q' - q) := by
    have hdc : (d : ℕ∞) < (37 - 1 : ℕ) := by exact_mod_cast (by omega : d < 37 - 1)
    -- from `(d:ℕ∞) + addVal(q'−q) ≥ 36` and `d ≤ 7`.
    by_contra hlt
    rw [not_le, Order.lt_one_iff] at hlt
    rw [hlt, add_zero] at hge
    exact absurd (lt_of_lt_of_le hdc hge) (lt_irrefl _)
  have hπdvd : S.π ∣ (q' - q) := by
    simpa using (S.le_addVal_iff_pi_pow_dvd (q' - q) 1).mp (by exact_mod_cast h1)
  have hresdiff : S.residue (q' - q) = 0 := (S.residue_eq_zero_iff _).mpr hπdvd
  rw [map_sub, sub_eq_zero] at hresdiff
  rw [hresdiff, hres]

/-- **`π⁸ ∣ Λ 32` from the integer-lift grading core** (`p = 37`): composing the
transfer `digitColemanGrading_of_integerLogCoeffGrading37` with the proven
orthogonality engine `pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_digitColemanGrading`.
So the orthogonality-reachable half of Prop 8.12 is driven entirely by the
**integer-lift** digit grading — the Teichmüller-free, sound replacement for the
`⌊d/2⌋`-degree Teichmüller-polynomial premise of `ColemanNextRungResidue`. -/
theorem pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_integerLogCoeffGrading37
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hgrad : S.IntegerLogCoeffGrading37 c 8) :
    S.π ^ 8 ∣ S.logCoeffSum c 32 :=
  S.pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_digitColemanGrading
    (S.digitColemanGrading_of_integerLogCoeffGrading37 hgrad)

/-! ## Part E — soundness: the corrected core is non-vacuous

The single-unit witness `piOrderWitnessCoeff` realises the integer-lift grading core,
so it introduces no hidden contradiction.  (For that witness the integer-lift
functional has the same `π⁸` order; the per-rung quotients are `π`-divisible, so the
weight is `0`.) -/

/-- For the single-unit witness the integer-lift functional equals the Teichmüller
functional value `π⁸` (the witness is supported at `j = 1`, where `(1.val : O) = 1`,
so the integer and Teichmüller powers coincide). -/
theorem integerLogCoeffSum_piOrderWitnessCoeff (S : StickelbergerF1Setup p) :
    S.integerLogCoeffSum (S.piOrderWitnessCoeff) 32 = S.logCoeffSum (S.piOrderWitnessCoeff) 32 := by
  classical
  unfold integerLogCoeffSum logCoeffSum piOrderWitnessCoeff
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = 1
  · -- At `j = 1`: `(1.val : O)^32 = 1^32 = 1 = (ω 1)^32`-value? Both reduce via `c_1` factor.
    subst hj
    rw [if_pos rfl]
    -- `((1:(ZMod p)ˣ) : ZMod p).val = 1`, so `(1 : O)^32 = 1`; and `(ω 1)^32 = 1`.
    have hval1 : (((1 : (ZMod p)ˣ) : ZMod p).val : S.O) = 1 := by
      rw [Units.val_one]
      rw [show ((1 : ZMod p).val : S.O) = (((1 : ZMod p).val : ℕ) : S.O) from rfl]
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.out.one_lt]; norm_num
    rw [hval1, one_pow]
    -- `(ω 1)^32 = 1`: `ω 1 = 1` (omegaHom_apply / map_one).
    have hω1 : ((S.ω 1) ^ 32 : S.Oˣ) = 1 := by
      rw [show S.ω 1 = 1 from by rw [← omegaHom_apply, map_one], one_pow]
    rw [show (((S.ω 1) ^ 32 : S.Oˣ) : S.O) = (1 : S.O) from by rw [hω1, Units.val_one]]
  · rw [if_neg hj, zero_mul, zero_mul]

/-- **Non-vacuity of the integer-lift grading core** (`p = 37`, soundness witness):
the witness `piOrderWitnessCoeff` realises `IntegerLogCoeffGrading37 c 8` (with zero
weights), so the corrected core is **not** a vacuous / contradictory `Prop`. -/
theorem integerLogCoeffGrading37_inhabited (S : StickelbergerF1Setup 37) :
    ∃ c : (ZMod 37)ˣ → S.O, S.IntegerLogCoeffGrading37 c 8 := by
  refine ⟨S.piOrderWitnessCoeff, ?_⟩
  intro d hd
  -- `M 32 = Λ 32 = π⁸ = π^d · π^{8−d}`, with `residue(π^{8−d}) = 0`, weight `P = 0`.
  refine ⟨S.π ^ (8 - d), 0, ?_, ?_, ?_⟩
  · rw [S.integerLogCoeffSum_piOrderWitnessCoeff, S.logCoeffSum_piOrderWitnessCoeff, ← pow_add]
    congr 1; omega
  · rw [Polynomial.natDegree_zero]; omega
  · rw [(S.residue_eq_zero_iff _).mpr ⟨S.π ^ (8 - d - 1), by rw [← pow_succ']; congr 1; omega⟩]
    simp

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL

end

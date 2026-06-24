import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.FermatLastTheoremClosure

/-!
# [FLT37-CASEII-R2] The free-content descent step on `37`-content data, and the parity obstruction

This file attacks `FreeContentCaseIIDescentStep37` (the single remaining FLT37 Case-II residual,
`CaseIIFreeContentDatum.lean`) by reconnecting the **free-content** frame to the proven
`RealCaseIIData37` descent machinery at the `(ζ−1)`-contents `n ≡ 0 (mod 37)` where the two frames
coincide; and it **machine-verifies** the content-parity obstruction that blocks the *full* step.

## The promotion (FULLY PROVEN here)

A free-content datum at content `37·(m+1)` is *exactly* a `RealCaseIIData37 m`: its equation
`x³⁷ + y³⁷ = ε·(ζ−1)^{37(m+1)}·z³⁷ = ε·((ζ−1)^{m+1}·z)³⁷` is the real-datum equation, and reality /
`𝔭`-coprimality / `(ζ−1)∤z` all transfer verbatim — the converse of the proven embedding
`FreeContentCaseIIData37.ofRealCaseIIData37`.  We prove `freeContentCaseIIData37_toReal` and that
the **corrected radical** at the adjacent root `η = ζ` agrees in the two frames
(`caseIIFree_correctedRadical_eq_real`), so the non-terminal hypothesis transfers.

## The conjugate-norm strict factor drop on `37`-content free data (FULLY PROVEN here)

Composing the promotion with the proven `caseII_conjNorm_factorCount_strict`
(`CaseIIConjNormFactorDrop.lean`) yields, for a free-content datum at content `37·(m+1)` in the
non-terminal regime, the conjugate norm `ξ₁ = ρ₀σρ₀` (real, `𝔭`-coprime) with **strictly fewer**
distinct prime factors than `D.z` (`caseIIFree_conjNorm_factorCount_strict`).  This is the genuine
descent *measure* drop, in the free frame, at the contents where the root-ideal machinery runs.

## The content-parity obstruction (FULLY PROVEN here — the structural heart of R2)

`freeContentCaseIIData37_even_content`: **every `FreeContentCaseIIData37 n` has even content `n`.**
(`x³⁷ + y³⁷` is real, so it lies in `algebraMap(𝓞 K⁺)`; `𝔭 = (ζ−1)` is ramified of index `2` in
`K/K⁺`, so `v_𝔭` of a real element is even — `multiplicity_zetaPrime_even_of_map_eq_span` — and
that `v_𝔭` equals `n`.)  Washington's conjugate-norm descent output has content `2m−37`, which is
**odd**, so it does **not** fit the free frame; the repo's σ-stable Case-I form has content `0`
(violating `hn : 1 ≤ n`).  So the descent step's conclusion is parity/content-obstructed in the
`FreeContentCaseIIData37` frame as defined — `FreeContentCaseIIDescentStep37` is **not** discharged
by either available construction, and is **not** closed here.

## What is reduced, and the honest gaps

The `37`-content descent step is reduced to a *sound* datum-packaging residual
`FreeContentCaseIIAnchorDatumAssembly37` (a **true implication**,
`freeContentCaseIIDescentStep37_of_assembly_on_p_content`; the residual's own truth is open and
faces the proven parity obstruction).  This does **not** prove `FreeContentCaseIIDescentStep37` (nor
FLT37): the full step also needs contents `n ≢ 0 (mod 37)` — where the flt-regular root-ideal
extraction (`span{x³⁷+y³⁷} = (𝔭^{m+1}·z)³⁷`, a *perfect* `37`-th power) does not apply — and a
packaging that the parity obstruction shows neither known construction supplies.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173.
* flt-regular, `FltRegular/CaseII/InductionStep.lean` (the content-`(m+1)·p` root-ideal chain).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The promotion `FreeContentCaseIIData37 (37·(m+1)) ↦ RealCaseIIData37 m` (PROVEN) -/

/-- **[FREE-CONTENT-TO-REAL] A free-content datum at content `37·(m+1)` is a `RealCaseIIData37 m`.**

The converse of `FreeContentCaseIIData37.ofRealCaseIIData37`: from a free-content datum `D` at
content `n = 37·(m+1)` (whose equation `x³⁷+y³⁷ = ε·(ζ−1)^{37(m+1)}·z³⁷` is `ε·((ζ−1)^{m+1}·z)³⁷`,
the real datum equation), read off a `RealCaseIIData37 m` with the *same* `ζ, x, y, z, ε` and the
reality / `𝔭`-coprimality fields.  The descended `ξ₁` machinery
(`caseII_conjNorm_factorCount_strict`) runs on this promotion. -/
def freeContentCaseIIData37_toReal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    RealCaseIIData37 (CyclotomicField 37 ℚ) m where
  ζ := D.ζ
  hζ := D.hζ
  x := D.x
  y := D.y
  z := D.z
  ε := D.ε
  equation := by
    -- `x³⁷+y³⁷ = ε·(ζ−1)^{37(m+1)}·z³⁷ = ε·((ζ−1)^{m+1}·z)³⁷`.
    rw [D.equation, mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 37, mul_assoc]
  hy := D.hy
  hz := D.hz
  x_real := D.x_real
  y_real := D.y_real

@[simp] theorem freeContentCaseIIData37_toReal_hζ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    (freeContentCaseIIData37_toReal D).hζ = D.hζ := rfl

@[simp] theorem freeContentCaseIIData37_toReal_x
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    (freeContentCaseIIData37_toReal D).x = D.x := rfl

@[simp] theorem freeContentCaseIIData37_toReal_y
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    (freeContentCaseIIData37_toReal D).y = D.y := rfl

@[simp] theorem freeContentCaseIIData37_toReal_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    (freeContentCaseIIData37_toReal D).z = D.z := rfl

/-- The promotion preserves the descent measure: the free factor count of `D` equals the real factor
count of its promotion (both count distinct primes of `(z)`, `z` unchanged). -/
theorem caseIIFreeFactorCount_toReal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    caseIIFreeFactorCount D =
      caseIIZFactorCount (freeContentCaseIIData37_toReal D).toCaseIIData37 := rfl

/-! ## 2. The corrected radical agrees in the two frames (PROVEN)

The free-content corrected radical at `η = ζ` (built from `x, y` directly) and the
`RealCaseIIData37` corrected radical at the adjacent root `etaOne` (built via the root-ratio +
Washington `−ζ^a` correction) are the *same* element of `K`, because on the promotion `etaOne` coe
is `ζ` (`caseII_etaOne_coe_eq_zeta`) and the correction unit at `etaOne` is `−ζ`.  Hence the
non-terminal hypothesis (the radical is *not* a unit) transfers between the frames verbatim. -/

/-- **[FREE-CONTENT-RADICAL-COMPAT] The free corrected radical = the real one on the promotion.**

`caseIIFree_correctedRadical D = caseII_correctedRadical (toReal D) etaOne (correctionUnit etaOne)`.
Both unfold to `(−ζ)⁻¹·algebraMap(x+yζ)/algebraMap(x+yζ³⁶)`. -/
theorem caseIIFree_correctedRadical_eq_real
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1))) :
    D.caseIIFree_correctedRadical =
      caseII_correctedRadical (freeContentCaseIIData37_toReal D)
        (freeContentCaseIIData37_toReal D).etaOne
        (caseII_correctionUnit (freeContentCaseIIData37_toReal D).etaOne) := by
  have hp : (37 : ℕ) ≠ 2 := by decide
  set D' := freeContentCaseIIData37_toReal D
  -- `etaOne` coe is `ζ` (anchor `η₀ = 1`).
  have hη : (D'.etaOne : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger := by
    rw [caseII_etaOne_coe_eq_zeta D' hp]
    rfl
  rw [FreeContentCaseIIData37.caseIIFree_correctedRadical, caseII_correctedRadical,
    caseII_rootRatioK, caseII_correctionUnit_val, hη]
  -- both sides are now `(−ζ)⁻¹·algebraMap(x+yζ)/algebraMap(x+yζ³⁶)` (the promotion copies `x, y`).
  congr 1

/-! ## 3. The conjugate-norm strict factor drop on `37`-content free data (PROVEN) -/

/-- **[FREE-CONTENT-CONJ-NORM-DROP] Washington's `ξ₁ = ρ₀σρ₀` strict drop, free-content frame.**

For a free-content datum `D` at content `37·(m+1)` whose corrected radical at `η = ζ` is **not** a
unit, there is a real, `𝔭`-coprime `ξ₁` with strictly fewer distinct prime factors than `D.z`:
`count(ξ₁) < caseIIFreeFactorCount D`.  Proof: promote `D` to `RealCaseIIData37 m`, transfer the
non-terminal hypothesis via `caseIIFree_correctedRadical_eq_real`, and apply the proven
`caseII_conjNorm_factorCount_strict`. -/
theorem caseIIFree_conjNorm_factorCount_strict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1)))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ ξ₁ : 𝓞 (CyclotomicField 37 ℚ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ξ₁ = ξ₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ ξ₁ ∧
      (normalizedFactors (Ideal.span ({ξ₁} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset.card <
        caseIIFreeFactorCount D := by
  set D' := freeContentCaseIIData37_toReal D
  -- Transfer the non-terminal hypothesis to the real datum `D'`.
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D' D'.etaOne (caseII_correctionUnit D'.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rwa [← caseIIFree_correctedRadical_eq_real D]
  -- The proven strict drop on `D'` (note `D'.hζ = D.hζ`, `caseIIZFactorCount D' = free count D`).
  exact caseII_conjNorm_factorCount_strict D' hnonterm'

/-! ## 3'. The content-parity lemma: every `FreeContentCaseIIData37 n` has **even** content (PROVEN)

The decisive structural fact behind the R2 doubled-measure obstruction, *machine-verified* here.
Because `x, y` are real (`x_real`, `y_real`), the Fermat sum `x³⁷ + y³⁷` is real, hence lies in the
image of `algebraMap (𝓞 K⁺) (𝓞 K)` (`ringOfIntegersComplexConj_eq_self_iff`); and `𝔭 = (ζ−1)` is
ramified of index `2` in `K/K⁺`, so the multiplicity `v_𝔭` of any such real element is **even**
(`multiplicity_zetaPrime_even_of_map_eq_span`).  Since `x³⁷ + y³⁷ = ε·(ζ−1)ⁿ·z³⁷` with `(ζ−1) ∤ z`,
that multiplicity is exactly `n`.  Hence **`n` is even**: `FreeContentCaseIIData37 n` is *vacuous*
for odd `n`.

This is precisely why Washington's conjugate-norm descent output (content `2m−37`, **odd**) does not
fit the free-content frame, and the descent step's conclusion is content-obstructed (see §4). -/

/-- **[FREE-CONTENT-EVEN-CONTENT] The `(ζ−1)`-content of a `FreeContentCaseIIData37` is even.**

Every `FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n` has `Even n`.  Proof: `x³⁷ + y³⁷` is real
(from `x_real`, `y_real`), so `x³⁷ + y³⁷ = algebraMap s` for some `s : 𝓞 K⁺`, whence
`span{x³⁷+y³⁷} = (span{s}).map algebraMap` and `multiplicity_zetaPrime_even_of_map_eq_span` gives
`Even (multiplicity (ζ−1) (x³⁷+y³⁷))`.  The equation `x³⁷+y³⁷ = ε·(ζ−1)ⁿ·z³⁷` with `(ζ−1)∤z`
(`hz`) and `ε` a unit gives `multiplicity (ζ−1) (x³⁷+y³⁷) = n` exactly.  So `Even n`. -/
theorem freeContentCaseIIData37_even_content
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {n : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n) : Even n := by
  set K := CyclotomicField 37 ℚ
  set πD : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K) with hπD
  set π : 𝓞 K := (zeta_spec 37 ℚ K).toInteger - 1 with hπ
  have hπD_prime : Prime πD := D.hζ.zeta_sub_one_prime'
  -- `πD = D.hζ.toInteger − 1` is associate to `π = zeta_spec.toInteger − 1` (both `(root) − 1`).
  have hassoc : Associated πD π := by
    -- pairwise-associated differences: `Associated ((zeta_spec) − 1) (ζ_D − 1)`.
    have hmem_dζ : D.hζ.toInteger ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
      D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
    have hmem_one : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) := by
      rw [mem_nthRootsFinset (by norm_num)]; ring
    have hne : D.hζ.toInteger ≠ (1 : 𝓞 K) :=
      fun h ↦ D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) h
    have hpair := (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot
      |>.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        (by decide : Nat.Prime 37) hmem_dζ hmem_one hne
    -- `hpair : Associated ((zeta_spec).toInteger − 1) (ζ_D − 1)`.
    simpa [hπD, hπ] using hpair.symm
  -- `x³⁷ + y³⁷` is real.
  have hsum_real : ringOfIntegersComplexConj K (D.x ^ 37 + D.y ^ 37) =
      D.x ^ 37 + D.y ^ 37 := by
    rw [map_add, map_pow, map_pow, D.x_real, D.y_real]
  -- so it descends: `x³⁷ + y³⁷ = algebraMap s`.
  obtain ⟨s, hs⟩ := (ringOfIntegersComplexConj_eq_self_iff K _).mp hsum_real
  -- `x³⁷ + y³⁷ ≠ 0` (else `z = 0`, contradicting `hz`).
  have hsum_ne : D.x ^ 37 + D.y ^ 37 ≠ 0 := by
    rw [D.equation]
    refine mul_ne_zero (mul_ne_zero D.ε.ne_zero (pow_ne_zero _ ?_)) (pow_ne_zero _ ?_)
    · exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
    · exact D.caseIIFree_z_ne_zero
  -- `span{x³⁷+y³⁷} = (span{s}).map algebraMap`.
  have hspan : (Ideal.span ({s} : Set (𝓞 (NumberField.maximalRealSubfield K)))).map
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span ({D.x ^ 37 + D.y ^ 37} : Set (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton, hs]
  -- Even multiplicity of `π = ζ−1` in `x³⁷+y³⁷`.
  have heven := multiplicity_zetaPrime_even_of_map_eq_span (p := 37) (by decide : (37 : ℕ) ≠ 2)
    K (Ideal.span ({s} : Set (𝓞 (NumberField.maximalRealSubfield K))))
    (D.x ^ 37 + D.y ^ 37) hsum_ne hspan
  -- `multiplicity π (x³⁷+y³⁷) = n` (via the equation and the associate `πD ~ π`).
  have hmult_n : multiplicity π (D.x ^ 37 + D.y ^ 37) = n := by
    have hz_not : ¬ πD ∣ D.z := by rw [hπD]; exact D.hz
    -- `πD^n ∣ x³⁷+y³⁷` and `¬ πD^{n+1} ∣ x³⁷+y³⁷`.
    have hdvd : πD ^ n ∣ D.x ^ 37 + D.y ^ 37 := by
      rw [D.equation, hπD]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_refl _) _) _
    have hnotdvd : ¬ πD ^ (n + 1) ∣ D.x ^ 37 + D.y ^ 37 := by
      rw [D.equation, hπD]
      intro hd
      -- `(ζ_D−1)^{n+1} ∣ ε·(ζ_D−1)ⁿ·z³⁷` ⟹ `(ζ_D−1) ∣ ε·z³⁷` ⟹ `(ζ_D−1) ∣ z`.
      have hd2 : (D.hζ.toInteger - 1 : 𝓞 K) ^ n * (D.hζ.toInteger - 1 : 𝓞 K) ∣
          (D.hζ.toInteger - 1 : 𝓞 K) ^ n * ((D.ε : 𝓞 K) * D.z ^ 37) := by
        refine dvd_trans (by rw [pow_succ]) (dvd_trans hd ?_)
        exact ⟨1, by ring⟩
      have hd' : (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.ε : 𝓞 K) * D.z ^ 37 :=
        (mul_dvd_mul_iff_left (pow_ne_zero n hπD_prime.ne_zero)).mp hd2
      rcases hπD_prime.dvd_mul.mp hd' with hε | hz37
      · exact hπD_prime.not_unit (isUnit_of_dvd_unit hε D.ε.isUnit)
      · exact hz_not (hπD_prime.dvd_of_dvd_pow hz37)
    -- so `multiplicity πD (x³⁷+y³⁷) = n`; transfer to `π` via the associate.
    have hmultD : multiplicity πD (D.x ^ 37 + D.y ^ 37) = n :=
      multiplicity_eq_of_dvd_of_not_dvd hdvd hnotdvd
    exact (multiplicity_eq_of_associated_left hassoc).trans hmultD
  rwa [hmult_n] at heven

/-- **A `RealCaseIIData37 m` forces `m` odd** (corollary of the content-parity lemma).  Its
embedding `ofRealCaseIIData37` is a `FreeContentCaseIIData37` at content `37·(m+1)`, even by
`freeContentCaseIIData37_even_content`; `37·(m+1)` even forces `m+1` even, i.e. `m` odd.  (So
`RealCaseIIData37 m` is vacuous for even `m`.) -/
theorem realCaseIIData37_odd_m
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) : Odd m := by
  have heven : Even (37 * (m + 1)) :=
    freeContentCaseIIData37_even_content (FreeContentCaseIIData37.ofRealCaseIIData37 D)
  -- `37·(m+1)` even ⟹ `m+1` even ⟹ `m` odd.
  rcases Nat.even_mul.mp heven with h37 | hm1
  · exact absurd h37 (by decide)
  · rw [Nat.odd_iff, ← Nat.not_even_iff]
    intro hm
    exact (Nat.even_add_one.mp hm1) hm

/-! ## 4. The `37`-content descent step, reduced to a datum-packaging residual

The strict drop above hands the new Fermat variable `ξ₁` (real, `𝔭`-coprime, strictly smaller
distinct prime count, `(ξ₁) = 𝔞₀^{2k'}`) with all of its `𝓞 K`-data.  The descent step's
*conclusion* is a free-content datum `D'` with `D'.z` having that smaller count.  The one thing not
supplied is the **equation** exhibiting `ξ₁` as the Fermat variable of a free-content datum.

We isolate **exactly** that as `FreeContentCaseIIAnchorDatumAssembly37`: from a real Case-II datum
`D` and a real, `𝔭`-coprime element `w` whose principal ideal is a power `𝔞₀ᵏ` of `D`'s `𝔭`-free
anchor `𝔞₀` — *precisely* the conjugate norm `ξ₁ = ρ₀σρ₀` (which the proven
`caseII_anchorPow_conjNorm_real_span` constructs with these exact properties) — produce a
free-content datum whose Fermat variable **is** `w`.  Its hypothesis pins `w` to `𝔞₀ᵏ` (Washington's
`ξ₁`), *never* an arbitrary real `𝔭`-coprime element (which would be the false "every real
`𝔭`-coprime element is a Fermat variable"); the reduction
`freeContentCaseIIDescentStep37_of_assembly_on_p_content` below is a **true implication**
(assembly → `37`-content step).

### ⚠ Truth of the residual is OPEN, with a MACHINE-VERIFIED content-parity obstruction

`FreeContentCaseIIAnchorDatumAssembly37` is **not** asserted true here; its truth is open, and the
following obstruction shows it is **not** discharged by Washington's literal construction:

* **PROVEN** (`freeContentCaseIIData37_even_content`, §3'): every `FreeContentCaseIIData37 n` has
  **even** content `n`.  (Mechanism: `x³⁷ + y³⁷` is real, so it lies in `algebraMap(𝓞 K⁺)`, and `𝔭`
  is ramified of index `2` in `K/K⁺` — `ramificationIdx_zetaPrimePlus_eq_two` — so `v_𝔭` of a real
  element is even — `multiplicity_zetaPrime_even_of_map_eq_span` — and that `v_𝔭` equals `n`.)  So
  `FreeContentCaseIIData37 n` is **vacuous for odd `n`**.
* Washington's conjugate-norm equation `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷` has content `2m−37`, which
  is **odd** (`(w+θ)² = η₀²·λ^{2m−p+1}·ρ₀^{2p}` with `v_𝔭(ρ₀) = 0` gives `2m−p = 2·v_𝔭(w+θ) − 1`).
* So Washington's descended datum at content `2m−37` (odd) **cannot** be a
  `FreeContentCaseIIData37` (proven to require even content).  The repo's *other* descent output —
  the σ-stable Case-I form
  `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷` (`caseII_pair_real_caseI_form_of_realCaseIIData37`) — has content `0`
  (even, but violating `hn : 1 ≤ n`), with the doubled measure absorbed into `ε₁, ε₂` and the
  valuations of `X, Y, Z` (the documented measure-doubling, b2 `R2-zeta-twist`).

Hence neither available construction packages `ξ₁` as a `FreeContentCaseIIData37 n'` with `n' ≥ 1`:
the descent step's conclusion is parity/content-obstructed in the `FreeContentCaseIIData37` frame as
defined (the even-content half now machine-verified).  This is the genuine structural heart of R2,
and it is **not** closed here. -/

/-- **[FREE-CONTENT-ANCHOR-DATUM-ASSEMBLY] The conjugate-norm Fermat-equation assembly**,
free-content frame.  **A structural reduction target whose truth is OPEN** (see the §4 docstring's
content-parity obstruction); *not* asserted true.

From a real Case-II datum `D` and a **real**, `𝔭`-coprime element `w : 𝓞 K` whose principal ideal is
a power `𝔞₀ᵏ` (`k ≥ 1`) of `D`'s `𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow` — *exactly* the
conjugate norm `ξ₁ = ρ₀σρ₀` produced by `caseII_anchorPow_conjNorm_real_span` — there exist `n'` and
a free-content Case-II datum `D' : FreeContentCaseIIData37 K n'` whose Fermat variable **is** `w`
(`D'.z = w`).

A `def … : Prop` (**not** an axiom).  Its hypothesis is `caseII_anchorPow_conjNorm_real_span`'s
proven output, so it consumes inhabited input; its conclusion asserts only the datum packaging
`D'.z = w`.  Its truth is open and faces the content-parity obstruction documented above (the
free-content frame forces even content, while Washington's equation gives odd content). -/
def FreeContentCaseIIAnchorDatumAssembly37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (w : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k →
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w = w →
    ¬ (D.hζ.toInteger - 1) ∣ w →
    Ideal.span ({w} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k →
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n'), D'.z = w

/-- **The `37`-content descent step from the conjugate-norm assembly residual** (a **true
implication**: assembly → step; the assembly's own truth is open, see §4).

For a free-content datum `D` **at content `37·(m+1)`** in the non-terminal regime, the descent
step's conclusion holds: there is a free-content datum `D'` with `caseIIFreeFactorCount D' <
caseIIFreeFactorCount D`.  Proof: promote `D` to a `RealCaseIIData37 m`; the **proven**
`caseII_anchorPow_conjNorm_real_span` supplies the conjugate norm `ξ₁ = ρ₀σρ₀` (real, `𝔭`-coprime,
`(ξ₁) = 𝔞₀^{2k'}`); the assembly residual `FreeContentCaseIIAnchorDatumAssembly37` realises `ξ₁` as
a free-content datum `D'` with `D'.z = ξ₁`; and the **proven** anchor-support strict drop
`caseIIZFactorCount_strict_of_anchor_supported` gives `count(ξ₁) < caseIIFreeFactorCount D`, so
`caseIIFreeFactorCount D' = count(ξ₁) < caseIIFreeFactorCount D`.

This reduces the descent step *on the `37`-content data* (the contents reachable by the promotion,
where the flt-regular root-ideal extraction runs) to the assembly residual.  It does **not** cover
the contents `n ≢ 0 (mod 37)`, nor does it discharge the assembly residual (open; content-parity
obstructed, §4). -/
theorem freeContentCaseIIDescentStep37_of_assembly_on_p_content
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_assembly : FreeContentCaseIIAnchorDatumAssembly37)
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1)))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n'),
      caseIIFreeFactorCount D' < caseIIFreeFactorCount D := by
  set D' := freeContentCaseIIData37_toReal D
  -- Transfer the non-terminal hypothesis to the real datum `D'`.
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D' D'.etaOne (caseII_correctionUnit D'.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rwa [← caseIIFree_correctedRadical_eq_real D]
  -- Washington's conjugate norm `ξ₁ = ρ₀σρ₀` (PROVEN): real, `𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}`.
  obtain ⟨w, k, hk, hw_real, hw_p, hw_span⟩ := caseII_anchorPow_conjNorm_real_span D'
  -- The assembly residual realises `ξ₁ = w` as a free-content datum `Dnew` (note `Dnew.z = w`).
  obtain ⟨n', Dnew, hDnewz⟩ := h_assembly D' w k hk hw_real hw_p hw_span
  refine ⟨n', Dnew, ?_⟩
  -- `count(Dnew.z) = count(w) < caseIIFreeFactorCount D = caseIIZFactorCount D'`: the PROVEN
  -- anchor-support strict drop on `w` (whose span is `𝔞₀^{2k'}`, support ⊆ support 𝔞₀).
  rw [caseIIFreeFactorCount, hDnewz]
  have hsupp := caseII_anchorSupported_of_span_eq_anchorPow D' hk hw_span
  exact caseIIZFactorCount_strict_of_anchor_supported D' (by decide : (37 : ℕ) ≠ 2)
    hnonterm' hsupp

/-- **Non-vacuity (hypothesis satisfiable) of the assembly residual.**  The hypothesis bundle of
`FreeContentCaseIIAnchorDatumAssembly37` — a real, `𝔭`-coprime `w` with `(w) = 𝔞₀ᵏ`, `k ≥ 1` — is
*not* vacuous: it is realised, for every real datum `D`, by the proven conjugate norm `ξ₁ = ρ₀σρ₀`
(`caseII_anchorPow_conjNorm_real_span`).  So the residual genuinely consumes inhabited input (it is
not vacuously true for the wrong reason).  This does **not** assert the residual's *conclusion* (the
existence of the packaged free-content datum), which is open and content-parity obstructed (§4). -/
theorem freeContentCaseIIAnchorDatumAssembly37_hyp_satisfiable
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (w : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w = w ∧
      ¬ (D.hζ.toInteger - 1) ∣ w ∧
      Ideal.span ({w} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k :=
  caseII_anchorPow_conjNorm_real_span D

end BernoulliRegular.FLT37.Eichler

end

end

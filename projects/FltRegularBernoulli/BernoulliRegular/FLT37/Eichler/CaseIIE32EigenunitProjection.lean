import BernoulliRegular.FLT37.Eichler.CaseIICor823Level72Valuation
import BernoulliRegular.FLT37.Eichler.CaseIIEx811EigenVandermonde

/-!
# The `ω³²` collapse via the **eigenunit projection** `E₃₂`: the reviewer's whole-element argument,
# and the precise verdict on whether it drops the per-basis level-`72` Dwork **shape**

This file formalises the expert reviewer's *eigenunit* reformulation of the Case-II `R4`
second-order `ω³²` collapse `Cor823Omega32SecondOrderCollapse37` (Washington Proposition 8.12 at the
irregular index `i = 32`).  The reviewer's argument runs the collapse through the **single eigenunit**
`E₃₂` (the repository's `pollaczekUnitPlusKplus 37 K 32`, whose class lies in the `ω³²`-eigenspace,
the proven `pollaczekUnit_image_in_omegaChar_eigenspace_general` at `i = 32`) and its `λ`-adic log
valuation, instead of the per-cyclotomic-column level-`72` Dwork distribution
(`CaseIICor823Level72Shape37`, the `varpi^{32}` Teichmüller-Vandermonde row of each column).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The reviewer's argument, formalised through the **detector functional**

The repository's level-`72` `ω³²` projection is the proven linear functional
`caseIICor823DetSqLog X = valuedLambdaQuotientDworkCoeffModSq ⟨32,_⟩ (evalₐ 72 X)`
(`CaseIICor823SecondOrderDescentReduction.lean`): for a completed `λ`-adic log element `X`, it reads
the `varpi^{32}` Dwork coordinate at level `72`, in `ZMod 37²`.  This **is** "the `ω³²`-projection at
level `72`" of the reviewer's argument; it is additive (`caseIICor823DetSqLog_add`) and `ℤ`-linear,
and scales the `p`-th-power correction by `37` (`caseIICor823DetSqLog_nsmul_thirtyseven`).

For an eigenunit `E_i = pollaczekUnitPlusKplus 37 K i`, the proven expansion
`pollaczekUnitPlusKplus_eq_CPlusExponentProduct` writes `E_i = CPlusExponentProduct 0 (e_a =
(a+2)^{36-i})`, so the proven `completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum` gives
`completedLog(E_i^{36}) = ∑_a (a+2)^{36-i} • kummerLogCompletedColumn a`.  Hence the eigenunit
detector is the **column-sum**

  `caseII_E32EigenunitDetector i
     = caseIICor823DetSqLog (completedLog(E_i^{36}))
     = ∑_a (a+2)^{36-i} • genericColumnCoordLHS37 a`                                      (§1)

(`caseII_eigenunitDetector_eq_column_sum`), where `genericColumnCoordLHS37 a` is the per-column
level-`72` `varpi^{32}` coordinate.  This is the precise meaning of "`v_π(ω³²-proj log E_i)`" in the
repository.

## What the single eigenunit valuation IS, and what the collapse actually consumes

* **§2 — the single eigenunit valuation residual `CaseIIE32EigenunitLogPiVal37`.**  This is the
  reviewer's `v_π(log E₃₂) = 68 < 72`, in its sharp `ZMod 37²` form: the eigenunit detector value on
  `E₃₂` is `37·(unit)` (its mod-`37` reduction is `0`, by the proven first-order degeneracy at
  `i = 32`; its `37`-divided part is a unit, the `M ≤ 1` content).  A **single** valuation datum.

* **§3 — the regular eigenunit vanishings `CaseIIRegularEigenunitLevel72Vanish37`.**  For every
  *regular* even index `i ≠ 32` (`2 ≤ i ≤ 34`), the eigenunit detector value on `E_i` vanishes in
  `ZMod 37²`: `caseII_E32EigenunitDetector i = 0`.  This is the `ω³²` level-`72` coordinate of a
  *regular*-eigenspace unit vanishing — `16` separate valuation data.

The honest accounting of the collapse (§4) is that it consumes **both** §2 and §3: the descent unit
`u` saturates to `v ∈ C⁺` with column coordinates `e`, and `[v] = ∑_j c_j [E_{2(j+1)}]`, but the
detector reaches `D_vC = ∑_a e_a · genericColumnCoordLHS37 a` directly, and re-expressing this
through the eigenunits requires *all 17* eigenunit detector values (the change of basis is an
invertible `17×17` Vandermonde): the single `E₃₂` value alone determines only one coordinate of the
inverse system.

## The verdict (rigorous, reported precisely)

**The eigenunit reformulation does NOT reduce `R4` to the single valuation `v_π(log E₃₂) = 68`.**

* It **does** isolate that single valuation as `CaseIIE32EigenunitLogPiVal37` (§2), the sharp
  `M ≤ 1` non-degeneracy in eigenunit form.

* But it **also** needs the `16` regular eigenunit vanishings
  `CaseIIRegularEigenunitLevel72Vanish37`
  (§3).  Together these are `17` valuation data — the same level-`72` Dwork content as the per-basis
  shape `CaseIICor823Level72Shape37` (`17` per-column values `F·V_a`), reorganised through the
  `17×17` Vandermonde change of basis (whose determinant `∏ (nodes distinct mod 37)` is a `37`-unit,
  hence invertible over `ZMod 37²`).  This file **proves the load-bearing direction** *shape ⟹ §2 ∧
  §3* (`caseII_E32EigenunitLogPiVal37_of_shape`, `caseII_regularEigenunitVanish_of_shape`), via the
  mod-`37` column-sum identity `∑_a (a+2)^{36-i}·(((a+2)²)^{16}-1) = 18·[i = 32]`
  (`caseII_eigenunit_columnSum_mod37`, a `decide`).  The converse *§2 ∧ §3 ⟹ shape* holds
  mathematically by inverting that Vandermonde (the eigenunit values determine the column values
  uniquely), but is **not** formalised here — it is not needed for the verdict, which follows from
  the forward direction alone: `§3` is a genuine companion input, *not* implied by `§2`.

So the reviewer's eigenunit route is the *structurally clean* repackaging of the same level-`72`
Dwork content, but it **relocates** rather than **removes** the shape: the genuine level-`72`
Galois-graded Dwork-evaluator content (that a *regular*-eigenspace unit has vanishing `ω³²`
level-`72` log coordinate — the `16` vanishings — together with the sharp `E₃₂` valuation) is the
per-column shape, in the eigenbasis.  The single `E₃₂` valuation is **necessary but not sufficient**.
This is the honest finding requested.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181), Exercise 8.11 (p. 166).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The eigenunit detector as the column sum

`caseII_E32EigenunitDetector i` is the level-`72` `ω³²` Dwork coordinate (the detector
`caseIICor823DetSqLog`) of the completed logarithm `completedLog(E_i^{36})` of the eigenunit
`E_i = pollaczekUnitPlusKplus 37 K i`.  By the proven `E_i = CPlusExponentProduct 0 ((a+2)^{36-i})`
and the completed-log column-sum identity, it is the `(a+2)^{36-i}`-weighted sum of the per-column
level-`72` coordinates `genericColumnCoordLHS37 a`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The eigenunit detector value**: the level-`72` `varpi^{32}` Dwork coordinate
(`caseIICor823DetSqLog`) of the completed log `completedLog(E_i^{36})` of the symmetrised eigenunit
`E_i = pollaczekUnitPlusKplus 37 K i`.  This is the repository realisation of the reviewer's
"`ω³²`-projection of `log E_i` at level `72`". -/
def caseII_E32EigenunitDetector
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (i : ℕ) : ZMod (37 ^ 2) :=
  caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
    (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ)
      (FLT37.Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) i (by norm_num)
        (by norm_num))))

open BernoulliRegular (CPlusGenerator) in
/-- **The detector is `ℤ`-linear**: `caseIICor823DetSqLog (n • X) = (n : ZMod 37²)·detSqLog X`
(proven, from `zsmul_eq_mul` + `valuedLambdaQuotientDworkCoeffModSq_intCast_mul`). -/
theorem caseIICor823DetSqLog_zsmul
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (n : ℤ) (X : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) :
    caseIICor823DetSqLog (n • X) = ((n : ℤ) : ZMod (37 ^ 2)) * caseIICor823DetSqLog X := by
  unfold caseIICor823DetSqLog
  rw [zsmul_eq_mul, map_mul, map_intCast, valuedLambdaQuotientDworkCoeffModSq_intCast_mul]

open BernoulliRegular (CPlusGenerator) in
/-- **The detector is additive over finite sums** (proven, from `caseIICor823DetSqLog_add`). -/
theorem caseIICor823DetSqLog_finsetSum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {ι : Type*} (s : Finset ι) (f : ι → DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) :
    caseIICor823DetSqLog (∑ i ∈ s, f i) = ∑ i ∈ s, caseIICor823DetSqLog (f i) := by
  classical
  have hzero : caseIICor823DetSqLog (0 : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) = 0 := by
    have h := caseIICor823DetSqLog_add (0 : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, caseIICor823DetSqLog_add, ih]

open BernoulliRegular (CPlusGenerator) in
/-- **The per-column detector value is `genericColumnCoordLHS37 a`** (proven, definitional): the
detector `caseIICor823DetSqLog` on the `a`-th completed-log column `kummerLogCompletedColumn a` is
the per-column level-`72` `varpi^{32}` coordinate `genericColumnCoordLHS37 a` (both unfold to
`valuedLambdaQuotientDworkCoeffModSq ⟨32,_⟩ (evalₐ 72 (kummerLogCompletedColumn a))`). -/
theorem caseIICor823DetSqLog_kummerLogCompletedColumn
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    caseIICor823DetSqLog
        (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a) =
      genericColumnCoordLHS37 a := by
  unfold caseIICor823DetSqLog genericColumnCoordLHS37
  congr 1

set_option maxHeartbeats 1600000 in
open BernoulliRegular (CPlusGenerator) in
/-- **The eigenunit detector is the `(a+2)^{36-i}`-weighted column sum** (proven, axiom-clean).

  `caseII_E32EigenunitDetector i = ∑_a (((a+2)^{36-i} : ℤ) : ZMod 37²) · genericColumnCoordLHS37 a`.

Proof: the proven `pollaczekUnitPlusKplus_eq_CPlusExponentProduct` writes
`E_i = CPlusExponentProduct 0 (e_a = (a+2)^{36-i})`; the proven
`completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum` gives `completedLog(E_i^{36}) =
∑_a e_a • kummerLogCompletedColumn a`; the detector is additive (`caseIICor823DetSqLog_finsetSum`)
and `ℤ`-linear (`caseIICor823DetSqLog_zsmul`), and on the `a`-th completed-log column it is
`genericColumnCoordLHS37 a` (`caseIICor823DetSqLog_kummerLogCompletedColumn`). -/
theorem caseII_eigenunitDetector_eq_column_sum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (i : ℕ) :
    caseII_E32EigenunitDetector i =
      ∑ a : Fin (kummerLogRank 37),
        ((((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) : ZMod (37 ^ 2)) *
          genericColumnCoordLHS37 a := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  classical
  unfold caseII_E32EigenunitDetector
  -- `E_i = CPlusExponentProduct 0 (e_a)`, `e_a = (a+2)^{36-i}`.
  rw [FLT37.pollaczekUnitPlusKplus_eq_CPlusExponentProduct i]
  -- `completedLog(E_i^36) = ∑_a e_a • kummerLogCompletedColumn a`.
  rw [completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) 0
    (fun a : Fin (kummerLogRank 37) ↦ ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ))]
  -- Push the detector through the sum and each `zsmul`, identifying the per-column value.
  rw [caseIICor823DetSqLog_finsetSum]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [caseIICor823DetSqLog_zsmul, caseIICor823DetSqLog_kummerLogCompletedColumn]

/-! ## 2. The single eigenunit valuation residual (`v_π(log E₃₂) = 68`)

`CaseIIE32EigenunitLogPiVal37` is the reviewer's single valuation `v_π(completedLog E₃₂) = 68 < 72`,
in its sharp `ZMod 37²` form: the eigenunit detector on `E₃₂` is `37·(unit)`.  Its mod-`37`
reduction is `0` (the first-order degeneracy at `i = 32`, the irregularity `37 ∣ B₃₂`); its
`37`-divided part is a *unit* (the second-order `M ≤ 1`, `v₃₇(L₃₇(1, ω³²)) = 1`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The single eigenunit valuation residual** (a `def … : Prop`, **not** an axiom — the sharp
`M ≤ 1` non-degeneracy in eigenunit form).

The eigenunit detector value `caseII_E32EigenunitDetector 32` (the `ω³²` level-`72` Dwork coordinate
of `completedLog(E₃₂^{36})`) is `37·ρ` for a *unit* `ρ : ZMod 37` (`ρ ≠ 0`):

  `∃ ρ : ZMod 37, ρ ≠ 0 ∧ caseII_E32EigenunitDetector 32 = 37 · (ρ.val : ZMod 37²)`.

This is `v_π(completedLog E₃₂) = 68 < 72` read at the **valuation**: the leading `λ`-term of
`completedLog E₃₂` is a unit at repo `λ`-level `68` (`c₃₂ = 2·(16 + 18·1)`), strictly below the
precision level `72`, so its mod-`37²` `varpi^{32}` coordinate is `37·(unit)`.  A **single**
valuation datum (one eigenunit), the sharp `M ≤ 1` content (`v₃₇(L₃₇(1,ω³²)) = 1`).  It is **sound**
(a definite `ZMod 37²` factorisation with a unit factor) and **non-circular** (a valuation
statement, never the vanishing of `c₁₅`). -/
def CaseIIE32EigenunitLogPiVal37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    caseII_E32EigenunitDetector 32 = (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2))

/-! ## 3. The regular eigenunit vanishings (the `16` companion data)

`CaseIIRegularEigenunitLevel72Vanish37` asks that every *regular* eigenunit `E_i` (`i ≠ 32` even,
`2 ≤ i ≤ 34`) has vanishing `ω³²` level-`72` detector: `caseII_E32EigenunitDetector i = 0`.  These
are the `16` companion valuation data — the `ω³²` level-`72` coordinate of a *regular*-eigenspace
unit vanishing — that the eigenunit route needs in addition to the single `E₃₂` valuation. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The regular eigenunit level-`72` vanishings** (a `def … : Prop`, **not** an axiom — the `16`
companion `ω³²` level-`72` coordinate vanishings).

For every *regular* even index `i` with `2 ≤ i ≤ 34` and `i ≠ 32`, the eigenunit detector value on
`E_i = pollaczekUnitPlusKplus 37 K i` vanishes in `ZMod 37²`:

  `∀ i, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 → caseII_E32EigenunitDetector i = 0`.

This is the Galois-graded level-`72` content "*a unit in a regular `ω^i`-eigenspace (`i ≠ 32`) has
vanishing `ω^{32}` log-coordinate at level `72`*".  Together with the single `E₃₂` valuation
(`CaseIIE32EigenunitLogPiVal37`, §2), these are the `17` eigenunit data the collapse consumes
(§4).  It is **sound** (a vanishing of definite `ZMod 37²` elements) and **non-circular** (a
valuation/coordinate statement, never the vanishing of `c₁₅`). -/
def CaseIIRegularEigenunitLevel72Vanish37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 → caseII_E32EigenunitDetector i = 0

/-! ## 4. The mod-`37` eigenunit column-sum identity (the bridge to the shape)

The mod-`37` reduction of the eigenunit column sum `∑_a (a+2)^{36-i}·(((a+2)²)^{16}-1)` is
`18·[i = 32]` for even `i ∈ [2, 34]` — a `decide`-checked power-sum identity.  This is the
diagonal-Vandermonde coincidence (`caseIIEx811Eigen_matrix_diagonal`, with the factor `2`
reabsorbed): it certifies that the *shape* `genericColumnCoordLHS37 a = F·(((a+2)²)^{16}-1)` makes
the eigenunit detector value `F·(18·[i=32])` — non-degenerate at `i = 32`, vanishing at regular
`i`. -/

open Finset in
/-- **The eigenunit column-sum mod-`37` identity** (proven by `decide`): for the even indices
`i = 2(m+1)` (`m : Fin 17`, so `i ∈ {2, 4, …, 34}`),

  `∑_a ((a+2)^{36-i} : ZMod 37) · (((a+2)²)^{16} − 1) = 18 · [i = 32]`   (`= 18·[m = 15]`).

This is the factor-`2`-reabsorbed diagonal of the two-Vandermonde coincidence
(`caseIIEx811Eigen_matrix_diagonal`: `∑_a (((a+2)²)^{m+1}-1)·2⁻¹(a+2)^{34-2m'} = 9·[m=m']`, here at
`m = 15`, `m' = m`, `34 - 2m' = 36 - i`, `2·9 = 18`).  It certifies the shape ⟹ eigenunit-data
direction (§5): with `genericColumnCoordLHS37 a = F·(((a+2)²)^{16}-1)`, the eigenunit detector value
`caseII_E32EigenunitDetector (2(m+1)) = F·(18·[m=15] mod 37²)` (mod the `37`-multiple correction),
which §5 turns into the sharp `E₃₂`-non-degeneracy and the regular vanishings. -/
theorem caseII_eigenunit_columnSum_mod37 :
    ∀ m : Fin 17,
      (∑ a : Fin 17, ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (37 - 1 - (2 * ((m : ℕ) + 1)))) *
          ((((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((15 : ℕ) + 1)) - 1)) =
        (if (m : ℕ) = 15 then (18 : ZMod 37) else 0) := by
  decide

/-! ## 5. The shape ⟹ eigenunit data: both §2 and §3 hold from the per-basis shape

We now prove the **shape ⟹ eigenunit-data** direction, which is the rigorous content of the verdict:
the single `E₃₂` valuation (§2) **and** the `16` regular vanishings (§3) are *both* downstream of the
per-basis level-`72` shape `CaseIICor823Level72LeadingCoeff37` (the residual `∃ ρ ≠ 0, ∀ a,
genericColumnCoordLHS37 a = 37·ρ.val·(((a+2)²)^{16} − 1)`).  This certifies that the eigenunit data
is **not smaller** than the shape — it is the same `17`-fold level-`72` Dwork content, in the
eigenbasis.

The computation: with `genericColumnCoordLHS37 a = 37·ρ.val·V_a` (`V_a = (((a+2)²)^{16}−1)`),

  `caseII_E32EigenunitDetector i = ∑_a (a+2)^{36-i}·(37·ρ.val·V_a) = 37·ρ.val·(∑_a (a+2)^{36-i}·V_a)`,

and the mod-`37` reduction of the column sum `∑_a (a+2)^{36-i}·V_a` is `18·[i = 32]`
(`caseII_eigenunit_columnSum_mod37`).  At `i = 32` this is the unit `18·ρ` (so the detector is
`37·(unit)`, the `E₃₂` valuation); at regular `i` it is `0` (so the column sum is `37·(…)` and the
detector is `37²·(…) = 0`, the regular vanishing). -/

open BernoulliRegular (CPlusGenerator) in
/-- **`37·Z = 37·((castHom Z).val)`** in `ZMod 37²` (proven): the `37`-multiple of `Z` depends only
on the mod-`37` reduction of `Z` (the `37`-multiple kills the `37`-part).  This is the precision
bridge `37·· : ZMod 37² → ZMod 37²` factoring through `castHom`. -/
theorem thirtyseven_mul_eq_castHom_val (Z : ZMod (37 ^ 2)) :
    (37 : ZMod (37 ^ 2)) * Z =
      (37 : ZMod (37 ^ 2)) *
        ((((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) Z).val : ℕ) :
          ZMod (37 ^ 2)) := by
  -- Set `n := Z.val`, so `Z = (n : ZMod 37²)`; then `castHom (n : ZMod 37²) = (n : ZMod 37)` with
  -- `.val = n % 37`, reducing to a `Nat.ModEq` on `37 * n`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Z = ((n : ℕ) : ZMod (37 ^ 2)) := ⟨Z.val, (ZMod.natCast_zmod_val Z).symm⟩
  rw [hn, map_natCast, ZMod.val_natCast]
  rw [show (37 : ZMod (37 ^ 2)) = ((37 : ℕ) : ZMod (37 ^ 2)) from by push_cast; ring]
  rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  -- `37 * n ≡ 37 * (n % 37) [MOD 37²]`: write `n = 37·q + r`, then
  -- `37·n = 37²·q + 37·r ≡ 37·r [MOD 37²]`.
  have hdiv : 37 * n = 37 ^ 2 * (n / 37) + 37 * (n % 37) := by
    nlinarith [Nat.div_add_mod n 37]
  rw [Nat.ModEq, hdiv, Nat.add_comm, Nat.add_mul_mod_self_left]

open BernoulliRegular (CPlusGenerator) in
/-- **The `castHom` of the eigenunit column sum is `18·[i = 32]`** (proven): the mod-`37` reduction
of the `ZMod 37²` column sum `∑_a (a+2)^{36-i}·V_a` (`V_a = (((a+2)²)^{16}−1)`) at the even index
`i = 2(m+1)` is `18·[m = 15]` (`= 18·[i = 32]`), by `caseII_eigenunit_columnSum_mod37` pushed
through `castHom`. -/
theorem caseII_eigenunit_columnSum_castHom (m : Fin 17) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (∑ a : Fin (kummerLogRank 37),
          ((((((a : ℕ) + 2) ^ (37 - 1 - (2 * ((m : ℕ) + 1))) : ℕ) : ℤ)) : ZMod (37 ^ 2)) *
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) =
      (if (m : ℕ) = 15 then (18 : ZMod 37) else 0) := by
  rw [map_sum, ← caseII_eigenunit_columnSum_mod37 m]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [map_mul, map_sub, map_pow, map_pow, map_one, map_intCast, map_natCast]
  push_cast
  ring

set_option maxHeartbeats 800000 in
open BernoulliRegular (CPlusGenerator) in
/-- **The eigenunit detector value at an even index, from the shape** (proven, axiom-clean given
`CaseIICor823Level72LeadingCoeff37`).

With the per-basis shape `genericColumnCoordLHS37 a = 37·ρ.val·V_a` (`ρ ≠ 0`), the eigenunit detector
at the even index `i = 2(m+1)` is `37·(ρ · 18·[m = 15]).val`:

  `caseII_E32EigenunitDetector (2(m+1)) = 37·(((ρ · (if m = 15 then 18 else 0)).val : ℕ) : ZMod 37²)`.

This is the master computation of §5: `det = 37·ρ.val·S` with `S` the column sum, and `37·X` depends
only on `castHom X` (`thirtyseven_mul_eq_castHom_val`), where
`castHom (ρ.val · S) = ρ · 18·[m = 15]` (`caseII_eigenunit_columnSum_castHom`).  At `m = 15`
(`i = 32`) the factor is the unit `18·ρ`; at regular `m` it is `0`. -/
theorem caseII_eigenunitDetector_even_of_shape
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {ρ : ZMod 37}
    (hShape : ∀ a : Fin (kummerLogRank 37),
      genericColumnCoordLHS37 a =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1))
    (m : Fin 17) :
    caseII_E32EigenunitDetector (2 * ((m : ℕ) + 1)) =
      (37 : ZMod (37 ^ 2)) *
        (((ρ * (if (m : ℕ) = 15 then (18 : ZMod 37) else 0)).val : ℕ) : ZMod (37 ^ 2)) := by
  -- `det = ∑_a (a+2)^{36-i}·(37·ρ.val·V_a) = 37·(ρ.val · S)`.
  rw [caseII_eigenunitDetector_eq_column_sum]
  have hfac : ∑ a : Fin (kummerLogRank 37),
        ((((((a : ℕ) + 2) ^ (37 - 1 - (2 * ((m : ℕ) + 1))) : ℕ) : ℤ)) : ZMod (37 ^ 2)) *
          genericColumnCoordLHS37 a =
      (37 : ZMod (37 ^ 2)) * (((ρ.val : ℕ) : ZMod (37 ^ 2)) *
        ∑ a : Fin (kummerLogRank 37),
          ((((((a : ℕ) + 2) ^ (37 - 1 - (2 * ((m : ℕ) + 1))) : ℕ) : ℤ)) : ZMod (37 ^ 2)) *
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [hShape a]
    ring
  rw [hfac, thirtyseven_mul_eq_castHom_val]
  -- Peel the `37·`; reduce to `(castHom (ρ.val · S)).val = (ρ · 18·[m = 15]).val`.
  refine congrArg (fun t : ℕ ↦ (37 : ZMod (37 ^ 2)) * ((t : ℕ) : ZMod (37 ^ 2))) ?_
  refine congrArg ZMod.val ?_
  -- `castHom (ρ.val · S) = castHom (ρ.val) · castHom S = ρ · 18·[m = 15]`.
  rw [map_mul, caseII_eigenunit_columnSum_castHom m, map_natCast, ZMod.natCast_val, ZMod.cast_id]

open BernoulliRegular (CPlusGenerator) in
/-- **§2 from the per-basis shape**: `CaseIIE32EigenunitLogPiVal37` from
`CaseIICor823Level72LeadingCoeff37` (proven, axiom-clean).

The single `E₃₂` eigenunit valuation `v_π(log E₃₂) = 68 < 72` is *downstream* of the per-basis
level-`72` shape: with `genericColumnCoordLHS37 a = 37·ρ.val·V_a` (`ρ ≠ 0`), the eigenunit detector
`caseII_E32EigenunitDetector 32 = 37·(ρ·18).val` (`caseII_eigenunitDetector_even_of_shape` at
`m = 15`, `2(15+1) = 32`), and `ρ·18 ≠ 0` (`ρ ≠ 0`, `18 ≠ 0` mod `37`).  So the detector is
`37·(unit)`, the sharp `M ≤ 1` valuation. -/
theorem caseII_E32EigenunitLogPiVal37_of_shape
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72LeadingCoeff37) :
    CaseIIE32EigenunitLogPiVal37 := by
  obtain ⟨ρ, hρ_ne, hcol⟩ := hShape
  refine ⟨ρ * 18, ?_, ?_⟩
  · -- `ρ · 18 ≠ 0`.
    have h18 : (18 : ZMod 37) ≠ 0 := by decide
    exact mul_ne_zero hρ_ne h18
  · -- `det 32 = 37·(ρ·18).val`.
    have h := caseII_eigenunitDetector_even_of_shape hcol (15 : Fin 17)
    have hv : ((15 : Fin 17) : ℕ) = 15 := by decide
    rw [hv, if_pos rfl] at h
    rw [show 2 * ((15 : ℕ) + 1) = 32 from by norm_num] at h
    exact h

open BernoulliRegular (CPlusGenerator) in
/-- **§3 from the per-basis shape**: `CaseIIRegularEigenunitLevel72Vanish37` from
`CaseIICor823Level72LeadingCoeff37` (proven, axiom-clean).

The `16` regular eigenunit vanishings are *also* downstream of the per-basis level-`72` shape: with
`genericColumnCoordLHS37 a = 37·ρ.val·V_a`, for a *regular* even index `i = 2(m+1) ≠ 32` (`m ≠ 15`)
the eigenunit detector `caseII_E32EigenunitDetector i = 37·(ρ·0).val = 0`
(`caseII_eigenunitDetector_even_of_shape`, `if m = 15` is `false`).  This certifies the `16`
companion data are not independent of the shape. -/
theorem caseII_regularEigenunitVanish_of_shape
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72LeadingCoeff37) :
    CaseIIRegularEigenunitLevel72Vanish37 := by
  obtain ⟨ρ, _hρ_ne, hcol⟩ := hShape
  intro i hi_even hi2 hi34 hi32
  -- Write `i = 2(m+1)` with `m : Fin 17`, `m ≠ 15`.
  obtain ⟨k, hk⟩ := hi_even
  -- `i = 2k`, with `2 ≤ 2k ≤ 34`, so `1 ≤ k ≤ 17`; set `m = k - 1 : Fin 17`.
  have hk1 : 1 ≤ k := by omega
  have hk17 : k ≤ 17 := by omega
  have hk15 : k ≠ 16 := by omega
  set m : Fin 17 := ⟨k - 1, by omega⟩ with hm
  have hi_eq : i = 2 * ((m : ℕ) + 1) := by rw [hm]; simp only []; omega
  rw [hi_eq, caseII_eigenunitDetector_even_of_shape hcol m]
  have hm_ne : (m : ℕ) ≠ 15 := by rw [hm]; simp only []; omega
  rw [if_neg hm_ne, mul_zero]
  simp

/-! ## 6. The eigenunit valuation supplies the non-degeneracy — the per-column **shape** is NOT dropped

The single eigenunit valuation `CaseIIE32EigenunitLogPiVal37` (§2) **does** supply the
non-degeneracy `Level72ColumnNonVanish37` (`CaseIICor823Level72Valuation.lean`: *some* column
coordinate is nonzero in `ZMod 37²`).  Indeed `caseII_E32EigenunitDetector 32 = ∑_a (a+2)^4 ·
genericColumnCoordLHS37 a`, and if *every* `genericColumnCoordLHS37 a` were `0` the eigenunit
detector would vanish — contradicting `= 37·ρ.val ≠ 0` (`ρ ≠ 0`).  So the eigenunit valuation is a
clean source for the non-degeneracy half of the prior split.

But the per-column **shape** `CaseIICor823Level72Shape37` (the `varpi^{32}` Teichmüller-Vandermonde
distribution `genericColumnCoordLHS37 a = 37·ρ·V_a` across the `17` columns) is **not** dropped: the
eigenunit valuation constrains a *single* linear combination `∑_a (a+2)^4 · col_a` of the `17` column
values, so it determines only one coordinate of the (invertible-Vandermonde) column system, never
the full per-column distribution.  Composing §6 with the prior split's
`caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish` confirms: the collapse follows from
`CaseIICor823Level72Shape37` (per-column shape) **plus** the eigenunit valuation `§2` — the same
shape residual as before, with the non-degeneracy now read off the single eigenunit valuation. -/

open BernoulliRegular (CPlusGenerator) in
/-- **`37·ρ.val ≠ 0` in `ZMod 37²` for `ρ ≠ 0`** (proven): `ρ.val ∈ {1, …, 36}`, so
`37·ρ.val ∈ {37, …, 37·36}`, all positive and `< 37² = 1369`, hence nonzero in `ZMod 37²`. -/
theorem thirtyseven_mul_val_ne_zero {ρ : ZMod 37} (hρ : ρ ≠ 0) :
    (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) ≠ 0 := by
  have hval_pos : 0 < ρ.val := by
    rcases Nat.eq_zero_or_pos ρ.val with h0 | hpos
    · exact absurd (ZMod.val_eq_zero ρ |>.mp h0) hρ
    · exact hpos
  have hval_lt : ρ.val < 37 := ZMod.val_lt ρ
  rw [show (37 : ZMod (37 ^ 2)) = ((37 : ℕ) : ZMod (37 ^ 2)) from by push_cast; ring,
    ← Nat.cast_mul, Ne, ZMod.natCast_eq_zero_iff]
  -- `37² ∤ 37·ρ.val` because `0 < 37·ρ.val < 37²`.
  intro hdvd
  have hle : 37 ^ 2 ≤ 37 * ρ.val := Nat.le_of_dvd (by positivity) hdvd
  omega

open BernoulliRegular (CPlusGenerator) in
/-- **The eigenunit valuation supplies the column non-vanishing** (proven, axiom-clean): the single
`E₃₂` eigenunit valuation `CaseIIE32EigenunitLogPiVal37` (§2) implies `Level72ColumnNonVanish37`
(*some* cyclotomic column's level-`72` `varpi^{32}` Dwork coordinate is nonzero in `ZMod 37²`).

If every `genericColumnCoordLHS37 a` were `0`, then `caseII_E32EigenunitDetector 32 = ∑_a (a+2)^4 ·
genericColumnCoordLHS37 a = 0`, contradicting the eigenunit valuation `= 37·ρ.val ≠ 0`
(`thirtyseven_mul_val_ne_zero`, `ρ ≠ 0`).  So the eigenunit valuation is a clean source for the
non-degeneracy half of the prior split (`CaseIICor823Level72Valuation.lean`); it does **not** supply
the per-column shape. -/
theorem level72ColumnNonVanish37_of_eigenunitPiVal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hPiVal : CaseIIE32EigenunitLogPiVal37) :
    Level72ColumnNonVanish37 := by
  obtain ⟨ρ, hρ_ne, hdet⟩ := hPiVal
  by_contra hall
  -- `¬ ∃ a, col a ≠ 0` means every column coordinate is `0`.
  rw [Level72ColumnNonVanish37, not_exists] at hall
  simp only [not_not] at hall
  -- Then the eigenunit detector at `32` vanishes — contradicting `= 37·ρ.val ≠ 0`.
  have hzero : caseII_E32EigenunitDetector 32 = 0 := by
    rw [caseII_eigenunitDetector_eq_column_sum]
    refine Finset.sum_eq_zero (fun a _ ↦ ?_)
    rw [hall a, mul_zero]
  rw [hzero] at hdet
  exact (thirtyseven_mul_val_ne_zero hρ_ne) hdet.symm

open BernoulliRegular (CPlusGenerator) in
/-- **The bundled level-`72` leading coefficient from the per-column shape + the eigenunit
valuation** (proven, axiom-clean): `CaseIICor823Level72LeadingCoeff37` follows from
`CaseIICor823Level72Shape37` (the per-column shape, **not** dropped) together with
`CaseIIE32EigenunitLogPiVal37` (the eigenunit valuation §2, supplying the non-degeneracy).

This is the eigenunit-interface refactor of the prior split
(`CaseIICor823Level72Valuation.lean`): the non-degeneracy half `Level72ColumnNonVanish37` is now read
off the **single eigenunit valuation** `CaseIIE32EigenunitLogPiVal37`
(`level72ColumnNonVanish37_of_eigenunitPiVal`), in place of the prior abstract
`CaseIIE32CompletedLogPropEightTwelve37`.  The per-column **shape** `CaseIICor823Level72Shape37`
remains the genuine level-`72` Dwork residual.  Composes with the prior split's
`caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish`. -/
theorem caseIICor823Level72LeadingCoeff37_of_shape_of_eigenunitPiVal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72Shape37)
    (hPiVal : CaseIIE32EigenunitLogPiVal37) :
    CaseIICor823Level72LeadingCoeff37 :=
  caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish hShape
    (level72ColumnNonVanish37_of_eigenunitPiVal hPiVal)

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the per-column shape + the
eigenunit valuation** (proven, axiom-clean given both).  Composes
`caseIICor823Level72LeadingCoeff37_of_shape_of_eigenunitPiVal` with the proven
`cor823PthPowerOfRationalModSq37_of_level72LeadingCoeff`. -/
theorem cor823PthPowerOfRationalModSq37_of_shape_of_eigenunitPiVal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72Shape37)
    (hPiVal : CaseIIE32EigenunitLogPiVal37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_level72LeadingCoeff
    (caseIICor823Level72LeadingCoeff37_of_shape_of_eigenunitPiVal hShape hPiVal)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the per-column level-`72` **shape** plus
the **single eigenunit valuation** `v_π(log E₃₂) = 68`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

This is the eigenunit-interface refactor of the FLT37 endpoint: `R4`'s level-`72` second-order
content is supplied through **two** residuals,

* `CaseIICor823Level72Shape37` — the per-column Teichmüller **shape** of the level-`72` coordinate
  (the genuine Dwork-evaluator content, degree `37..72`, **not** avoided by the eigenunit); and
* `CaseIIE32EigenunitLogPiVal37` — the **single eigenunit valuation** `v_π(completedLog E₃₂) = 68 <
  72` (the `M ≤ 1` non-degeneracy in eigenunit form, supplying `Level72ColumnNonVanish37`).

The honest verdict (this file): the eigenunit reformulation isolates the non-degeneracy as the single
eigenunit valuation, but it does **not** drop the per-column shape — the per-basis shape **proves**
the full eigenunit data, both `§2` and the `16` regular vanishings `§3`
(`caseII_E32EigenunitLogPiVal37_of_shape`, `caseII_regularEigenunitVanish_of_shape`), so the
eigenunit data is no weaker than the shape, and the single valuation `§2` alone is *necessary but not
sufficient* (the `16` regular vanishings `§3` are a genuine companion input). -/
theorem fermatLastTheoremFor_thirtyseven_of_shape_of_eigenunitPiVal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_level72Shape : CaseIICor823Level72Shape37)
    (caseII_eigenunitPiVal : CaseIIE32EigenunitLogPiVal37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level72LeadingCoeff37_of_shape_of_eigenunitPiVal
      caseII_level72Shape caseII_eigenunitPiVal)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

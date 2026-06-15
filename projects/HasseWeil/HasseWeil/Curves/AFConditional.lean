import HasseWeil.Curves.EffectiveSumReduce
import HasseWeil.Curves.PoleOrderParity
import HasseWeil.EC.IsogenyAG.HomProperty

/-!
# AF unified package: conditional witnesses

Wires together the shipped infrastructure into the witnesses needed by
`AddHomProperty_of_picZero_witnesses` (the universal Silverman III.4.8
theorem). Each witness is parametrized over the remaining outstanding
hypotheses, making the dependency chain explicit:

| Witness needed | Conditional hypothesis |
|---|---|
| `h_inj` (`κ ∘ σ̄ = id`) | `DivZeroReduce W` (= reduction lemma) |
| `h_van` (`σ` vanishes on principal) | `DivZeroReduce W` AND a `point_minus_O_principal_eq_zero` over arbitrary functions (= the no-finite-poles bridge) |

Once `DivZeroReduce W` lands (which itself decomposes into the
list-induction `effective_sum_reduce` + Finsupp-to-list bridge for
multiplicities) and the no-finite-poles bridge, the AF unified package
fully closes B-4-003 conditionally on Miller (the geometric chord/tangent
construction, the only remaining genuinely-new mathematical piece).

## References

* `T-PIC-AF-UNIFIED.md` for the full plan.
-/

open WeierstrassCurve

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- The full divisor reduction property: every degree-zero divisor is
linearly equivalent to `(σD) − (O)`. The proof requires Miller (via
`effective_sum_reduce`) plus a Finsupp-to-list bridge for handling
multiplicities. Both are outstanding tickets. -/
def DivZeroReduce : Prop :=
  ∀ D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F),
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      D.val (kappaDivisor W (projectiveDivisorSum W D.val))

/-- The unconditional `point_minus_O` property: if `(P) − (O)` is
principal, then `P = 0`. The proof requires the parity lemma (shipped
as `point_minus_O_principal_eq_zero_of_coord`) plus the no-finite-poles
→ CR-image bridge (outstanding ticket: `T-PIC-AF-UNIFIED.md` piece (a)). -/
def PointMinusOPrincipalEqZero : Prop :=
  ∀ P : W.Point,
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W P) → P = 0

/-! ### Witness 1: `h_inj` from the divisor reduction -/

/-- The h_inj witness for `AddHomProperty_of_picZero_witnesses`,
derived from the divisor reduction.

Mathematical content: if every D ∈ Div⁰ satisfies `D ~ (σD) − (O)`, then
the Pic⁰ classes of D and `(σD) − (O)` are equal, which is exactly
`κ ∘ σ̄ = id`. -/
theorem h_inj_of_divZeroReduce
    (h_reduce : DivZeroReduce W)
    (h_van : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      projectiveDivisorSum W D = 0)
    (D : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F)) :
    picZeroOfPoint W
        (HasseWeil.EC.Isogeny.picZeroSumOfWitness W h_van D) = D := by
  refine QuotientAddGroup.induction_on D fun D' => ?_
  rw [HasseWeil.EC.Isogeny.picZeroSumOfWitness_apply_mk]
  -- Goal: picZeroOfPoint W (σ D'.val) = QuotientAddGroup.mk D'
  unfold picZeroOfPoint
  -- Use Quot.sound to convert mk-equality to relation membership.
  apply Quot.sound
  rw [QuotientAddGroup.leftRel_apply]
  -- Goal: -⟨kappaDivisor⟩ + D' ∈ subgroup.addSubgroupOf
  show (-kappaDivisor W (projectiveDivisorSum W D'.val) + D'.val) ∈
    (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup
  rw [show (-kappaDivisor W (projectiveDivisorSum W D'.val) + D'.val) =
      D'.val - kappaDivisor W (projectiveDivisorSum W D'.val) by abel]
  exact h_reduce D'

/-! ### Witness 2: `h_van` from divisor reduction + point_minus_O -/

/-- The h_van witness for `AddHomProperty_of_picZero_witnesses`, derived
from the divisor reduction + the unconditional point_minus_O.

Mathematical content: if D is principal then D ~ 0. By the reduction,
D ~ (σD) − (O). Combining: (σD) − (O) ~ 0, i.e., (σD) − (O) is principal.
By point_minus_O: σD = 0. -/
theorem h_van_degZero_of_divZeroReduce_and_pointMinusO
    (h_reduce : DivZeroReduce W)
    (h_pmO : PointMinusOPrincipalEqZero W)
    (D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F))
    (hD : D.val ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    projectiveDivisorSum W D.val = 0 := by
  -- D ~ (σD) − (O) from h_reduce.
  have h_lin := h_reduce D
  -- ProjLinearlyEquiv = principalness of difference.
  have h_diff_principal :
      D.val - kappaDivisor W (projectiveDivisorSum W D.val) ∈
        (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup := h_lin
  -- kappaDivisor (σD.val) = D.val − (D.val − kappaDivisor (σD.val))
  -- both summands principal (the second by negation of h_diff_principal).
  have h_kappa_principal :
      kappaDivisor W (projectiveDivisorSum W D.val) ∈
        (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup := by
    have h_neg : kappaDivisor W (projectiveDivisorSum W D.val) =
        D.val - (D.val - kappaDivisor W (projectiveDivisorSum W D.val)) := by
      abel
    rw [h_neg]
    exact (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.sub_mem
      hD h_diff_principal
  -- Apply h_pmO.
  exact h_pmO _ h_kappa_principal

/-! ### `PointMinusOPrincipalEqZero` from the no-finite-poles bridge -/

/-- The no-finite-poles → CR-image bridge: any nonzero function with all
local orders nonneg lies in the coordinate-ring image. The proof composes
worker-I's `pointValuation_algebraMap_le_one`, `smoothPointEquivMaxIdeal`
(under `[IsAlgClosed F] [IsElliptic]`), and mathlib's
`mem_coordinateRing_of_valuation_le_one`. ~80-150 LOC follow-up ticket. -/
def NoFinitePolesBridge : Prop :=
  ∀ (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField), f ≠ 0 →
    (∀ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint,
      0 ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f) →
    ∃ u : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing,
      algebraMap _ (⟨W⟩ : SmoothPlaneCurve F).FunctionField u = f

/-- Given the no-finite-poles bridge, the unconditional point_minus_O
property holds: if `(P) − (O)` is principal, then `P = 0`.

The proof: extract the witness function `f` for principalness; apply the
bridge to conclude `f ∈ image of CR` (since `(P) − (O)` has no finite
poles); then apply the intermediate `point_minus_O_principal_eq_zero_of_coord`. -/
theorem pointMinusO_of_bridge
    (h_bridge : NoFinitePolesBridge W) :
    PointMinusOPrincipalEqZero W := by
  intro P h_principal
  obtain ⟨f, hf_ne, hf_div⟩ := h_principal
  -- hf_div: projectiveDivisorOf f = kappaDivisor W P
  -- Show f has no finite poles, then apply the intermediate lemma.
  apply point_minus_O_principal_eq_zero_of_coord W P f hf_ne hf_div
  apply h_bridge f hf_ne
  intro Q
  -- (projDiv f) at affine Q = (ord_Q f).untopD 0. Per project lemma.
  -- (kappaDivisor W P) at affine Q ∈ {0, 1}.
  -- So (ord_Q f).untopD 0 ∈ {0, 1}.
  -- If ⊤: f = 0, contradicts hf_ne. Else ord_Q f = 0 or 1, both ≥ 0.
  have h_eq := SmoothPlaneCurve.projectiveDivisorOf_apply_affine
    (C := (⟨W⟩ : SmoothPlaneCurve F)) f Q
  rw [hf_div] at h_eq
  -- h_eq: kappaDivisor W P (affine Q) = (ord_P Q f).untopD 0
  -- The LHS: kappaDivisor at affine Q ∈ {0, 1, -1, ...} via Finsupp.single semantics.
  -- Specifically: Finsupp.single P.toProj 1 - Finsupp.single ∞ 1 evaluated at
  -- (affine Q). Since affine Q ≠ ∞, the second term contributes 0.
  -- The first term contributes 1 if affine Q = P.toProj, else 0.
  unfold kappaDivisor at h_eq
  rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply] at h_eq
  -- h_eq: (if P.toProj = affine Q then 1 else 0) - (if ∞ = affine Q then 1 else 0)
  --     = (ord_P Q f).untopD 0
  -- ∞ ≠ affine Q (different constructors), so RHS-second = 0.
  have h_inf_ne :
      ((ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint
        (⟨W⟩ : SmoothPlaneCurve F))) ≠ ProjectiveSmoothPoint.affine Q := by
    intro h; nomatch h
  rw [if_neg h_inf_ne, sub_zero] at h_eq
  -- h_eq: (if P.toProj = affine Q then 1 else 0) = (ord_P Q f).untopD 0
  -- Case split on whether P.toProj = affine Q.
  by_cases h_eq_pt : P.toProjectiveSmoothPoint = ProjectiveSmoothPoint.affine Q
  · rw [if_pos h_eq_pt] at h_eq
    -- h_eq: 1 = (ord_P Q f).untopD 0; so ord_P Q f = 1 (not ⊤, not 0).
    cases h_top : (⟨W⟩ : SmoothPlaneCurve F).ord_P Q f with
    | top =>
      rw [h_top, WithTop.untopD_top] at h_eq
      exact absurd h_eq (by decide)
    | coe n =>
      rw [h_top, WithTop.untopD_coe] at h_eq
      -- h_eq : 1 = n; goal: 0 ≤ ↑n (after cases substitution)
      have hn : n = 1 := h_eq.symm
      subst hn
      exact_mod_cast (by decide : (0 : ℤ) ≤ 1)
  · rw [if_neg h_eq_pt] at h_eq
    cases h_top : (⟨W⟩ : SmoothPlaneCurve F).ord_P Q f with
    | top =>
      exfalso; apply hf_ne
      exact ((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := Q) f).mp h_top
    | coe n =>
      rw [h_top, WithTop.untopD_coe] at h_eq
      have hn : n = 0 := h_eq.symm
      subst hn; rfl

/-! ### Bundled AFInputs structure -/

/-- The three input Props needed for the AF unified package on a single
elliptic curve `W`:

* `miller`: chord/tangent geometric identity at the divisor level.
* `divZeroReduce`: combinatorial reduction `D ~ (σD) − (O)` for D ∈ Div⁰.
* `noFinitePolesBridge`: the algebraic bridge from "no finite poles" to
  "in coordinate-ring image".

Each is its own outstanding ticket; once all three are discharged for a
specific `W`, both witnesses needed by `AddHomProperty_of_picZero_witnesses`
(restricted to that curve's side of the isogeny) follow immediately. -/
structure AFInputs (W : Affine F) [W.IsElliptic] where
  miller : MillerHypothesis W
  divZeroReduce : DivZeroReduce W
  noFinitePolesBridge : NoFinitePolesBridge W

namespace AFInputs

/-- Derived: the unconditional point_minus_O property. -/
theorem pointMinusO {W : Affine F} [W.IsElliptic] (a : AFInputs W) :
    PointMinusOPrincipalEqZero W :=
  pointMinusO_of_bridge W a.noFinitePolesBridge

/-- Derived: the h_inj witness for `AddHomProperty_of_picZero_witnesses`. -/
theorem h_inj {W : Affine F} [W.IsElliptic] (a : AFInputs W)
    (h_van : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      projectiveDivisorSum W D = 0)
    (D : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F)) :
    picZeroOfPoint W
        (HasseWeil.EC.Isogeny.picZeroSumOfWitness W h_van D) = D :=
  h_inj_of_divZeroReduce W a.divZeroReduce h_van D

/-- Derived: the h_van witness restricted to the degZero subgroup. -/
theorem h_van_degZero {W : Affine F} [W.IsElliptic] (a : AFInputs W)
    (D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F))
    (hD : D.val ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    projectiveDivisorSum W D.val = 0 :=
  h_van_degZero_of_divZeroReduce_and_pointMinusO W a.divZeroReduce
    a.pointMinusO D hD

end AFInputs

/-! ### Final B-4-003 wrapper -/

/-- The "principal divisors lie in degZero" predicate. Proved by
worker-K's T-II-3-009 (`projectiveDivisorOf_degree_zero`) under
`[IsAlgClosed F]`. We take it as a hypothesis here to keep the wrapper
conditional. -/
def PrincipalImpliesDegZero (W : Affine F) [W.IsElliptic] : Prop :=
  ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
    D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
    D ∈ ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)

namespace AFInputs

/-- The full h_van witness, given `AFInputs` + the principal-implies-degZero
bridge (worker-K's T-II-3-009). -/
theorem h_van {W : Affine F} [W.IsElliptic] (a : AFInputs W)
    (h_pdz : PrincipalImpliesDegZero W)
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F))
    (hD : D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    projectiveDivisorSum W D = 0 := by
  have h_dz := h_pdz D hD
  -- Construct the degZero subtype element
  have := a.h_van_degZero ⟨D, h_dz⟩ hD
  exact this

end AFInputs

/-- **Final conditional B-4-003** for an isogeny: given `AFInputs` for
both curves, the principal-degZero bridge for both curves, and the
pushforward-preserves-principal hypothesis (T-PIC-C-003), the universal
hom property holds.

This closes B-4-003 over `[IsAlgClosed F]` modulo:
- `MillerHypothesis` for both W₁ and W₂ (geometric chord/tangent — the BIG remaining piece)
- `DivZeroReduce` for both W₁ and W₂ (Finsupp decomposition + miller corollaries)
- `NoFinitePolesBridge` for both W₁ and W₂ (valuation bridge)
- `PrincipalImpliesDegZero` for both W₁ and W₂ (worker-K's T-II-3-009)
- `h_pres` (T-PIC-C-003 = norm-divisor identity)

All the structural plumbing is here; the remaining work is to prove
each of these Props for elliptic curves. -/
theorem AddHomProperty_of_AFInputs
    {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : HasseWeil.EC.Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (a₁ : AFInputs W₁) (a₂ : AFInputs W₂)
    (h_pdz₁ : PrincipalImpliesDegZero W₁)
    (h_pdz₂ : PrincipalImpliesDegZero W₂)
    (h_pres : ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    φ.AddHomProperty cd :=
  HasseWeil.EC.Isogeny.AddHomProperty_of_picZero_witnesses φ cd
    (a₁.h_van h_pdz₁) (a₂.h_van h_pdz₂) h_pres
    (a₁.h_inj (a₁.h_van h_pdz₁))

end HasseWeil.Curves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.AdjointTransfer
import HasseWeil.WeilPairing.GenericCovarianceGeneral
import HasseWeil.EC.IsogenyAG.CanonicalDual

/-!
# Dual additivity `(φ+ψ)^ = φ̂ + ψ̂` in arbitrary characteristic (Silverman III.6.2(c))

Silverman proves III.6.2(c) in characteristic `0` only and punts arbitrary characteristic to
Exercise 3.31.  This file executes the **Weil-pairing route**, available here because the
pairing layer of the Hasse-bound development is fully built: bilinearity in both slots,
nondegeneracy, and the separable adjoint.

## The route

1. **The separation engine** (`Isogeny.pullback_eq_of_pointMap_eqOn_infinite`): two
   `Basic.Isogeny`s whose stored point maps agree on an *infinite* set of points and whose
   stored data is coherent (the cofinite `PullbackEvaluation` witness of
   `GenericCovarianceGeneral`) have **equal pullbacks**.  At every common good point the two
   pulled-back generators take the same value (the agreeing image point's coordinates), and
   two functions agreeing at infinitely many points are equal — a nonzero difference has
   finitely many zeros (Silverman II.1.2, `finite_setOf_ord_P_nonzero`); conclude with the
   generator extensionality `algHom_ext_x_y_gen`.  This is the missing
   values-determine-functions principle for the whole isogeny theory.

2. **The per-`ℓ` adjoint calculus** (`WeilPairing/AdjointTransfer.lean`): on each `E[ℓ]`,
   adjoints are unique, transfer along `[m]`-composition identities, and satisfy
   `δ_{φ+ψ} = δ_φ + δ_ψ` (the additivity computation).

3. **Assembly** (`dual_add_pullback`): the dual candidates agree on
   `⋃_{ℓ ∈ L} E[ℓ]` for an infinite set `L` of good primes — an infinite set of points,
   since each `E[ℓ]` contributes a nonzero point (`#E[ℓ] = ℓ² > 1`, `card_torsion_ell`) and
   distinct primes give disjoint nonzero torsion (`torsionSubgroup_inf`).  The separation
   engine then upgrades torsion-level agreement of the point maps to **pullback equality**
   of the dual isogenies.

## Honest scoping

* The theorems are at the **endomorphism** level (`Isogeny W.toAffine W.toAffine`), the
  level at which the pairing layer is built.
* The sum isogeny is taken **witness-style**: `χ` with
  `χ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom` (the `addIsog` machinery of
  `AdditionPullback.lean` *builds* such a `χ` from `AddNonInversePair` witnesses —
  `addIsog_toAddMonoidHom` — so the hypothesis is non-vacuous), and similarly `σ` for
  `φ̂ + ψ̂`.
* The adjoint identities for `φ, ψ, χ` at each good `ℓ` are carried as
  `IsWeilAdjointOn` hypotheses; they are dischargeable per isogeny from the III.8.2
  geometric witnesses (`IsWeilAdjointOn.of_adjointWitnesses`) or transferred from a
  `picDual`-style adjoint along the canonical-dual composition identities
  (`IsWeilAdjointOn.of_comp`).
* The conclusion is **pullback equality** plus point-map agreement on the torsion union —
  the two stored fields of a `Basic.Isogeny` are independent data, and the point maps of
  the two sides are only forced to agree where the pairing sees them.  Full structure
  equality needs point-map agreement everywhere (`Isogeny.ext`).

## Main results

* `WeilPairing.eq_of_evaluatesTo_infinite` — functions agreeing (in the `EvaluatesTo`
  sense) at infinitely many points are equal.  No algebraic closure needed.
* `Isogeny.ext` — extensionality for `Basic.Isogeny` (both stored fields).
* `Isogeny.pullback_eq_of_pointMap_eqOn_infinite` (+ `_points` and full-`ext` variants) —
  **the separation engine**.
* `exists_torsion_ne_zero`, `torsionUnionSet_infinite` — the infinitude source.
* `WeilPairing.dual_add_pointMap_eqOn_torsionUnion` — `δ_χ = δ_φ + δ_ψ` on `⋃ E[ℓ]`.
* `WeilPairing.dual_add_pullback` — **dual additivity**: any dual candidate `D_χ` for
  `χ = φ + ψ` has the same pullback as any sum candidate `σ` for `φ̂ + ψ̂`.
* `EC.Isogeny.canonicalDual_pullback_eq_of_dual_add` — the statement at the canonical dual
  (`CanonicalDual.lean`), for an `EC`-isogeny realisation of `χ̂`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.2(c), Exercise 3.31, III.8,
  II.1.2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-! ### Separation: functions agreeing at infinitely many points are equal

The infinite-agreement variant of `eq_of_evaluatesTo_cofinite`: here the *agreement set*
carries the infinitude, so no algebraic closure is needed. -/

/-- **Infinite-agreement separation** (Silverman II.1.2): two rational functions sharing a
value at every point of an *infinite* set are equal.  A nonzero difference would vanish at
every agreement point, but it has only finitely many zeros
(`finite_setOf_ord_P_nonzero`). -/
theorem eq_of_evaluatesTo_infinite {f g : KE}
    {S : Set (W_smooth W).SmoothPoint} (hS : S.Infinite)
    (h : ∀ P ∈ S, ∃ c : F, EvaluatesTo W P f c ∧ EvaluatesTo W P g c) : f = g := by
  by_contra hne
  have hD : f - g ≠ 0 := sub_ne_zero_of_ne hne
  -- every agreement point is a zero of `f − g`
  have hzero : ∀ P ∈ S, (W_smooth W).ord_P P (f - g) ≠ 0 := by
    intro P hP
    obtain ⟨c, hf, hg⟩ := h P hP
    have hval : (W_smooth W).pointValuation P (f - g) < 1 := by
      have hrw : f - g = (f - algebraMap F KE c) - (g - algebraMap F KE c) := by abel
      rw [hrw]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hf hg)
    have h1 : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P (f - g) :=
      (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one (P := P) hD).mpr hval
    intro h0
    rw [h0] at h1
    have h1' : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast h1
    exact absurd (WithTop.coe_le_coe.mp h1') (by norm_num)
  -- so the infinite agreement set sits inside the finite zero set
  exact ((W_smooth W).finite_setOf_ord_P_nonzero hD).not_infinite
    (hS.mono fun P hP ↦ hzero P hP)

end HasseWeil.WeilPairing

namespace HasseWeil

open WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Extensionality for `Basic.Isogeny` -/

/-- **Extensionality for `Basic.Isogeny`**: the structure is exactly its two stored fields,
so isogenies with equal pullbacks and equal point maps are equal. -/
@[ext] theorem Isogeny.ext {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Isogeny W₁ W₂} (hpb : α.pullback = β.pullback)
    (hhom : α.toAddMonoidHom = β.toAddMonoidHom) : α = β := by
  cases α; cases β; subst hpb; subst hhom; rfl

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-! ### The separation engine (Part C)

Two coherent isogenies whose stored point maps agree on an infinite set of points have equal
pullbacks: the pulled-back generators agree (as values) at cofinitely many of the agreement
points, and infinitely many agreement values force function equality. -/

variable {W} in
/-- **The separation engine**: two endo-isogenies `α, β` with cofinite pullback-evaluation
witnesses (`PullbackEvaluation`, the stored-fields coherence of `GenericCovarianceGeneral`)
whose stored point maps agree on an **infinite** set `S` of smooth points have equal
pullbacks.

At every `P ∈ S` outside the two bad sets, the witnesses evaluate `α^* x_gen` and
`β^* x_gen` to the `x`-coordinate of the *common* image point (and likewise for `y_gen`);
the infinite-agreement separation `eq_of_evaluatesTo_infinite` gives
`α^* x_gen = β^* x_gen` and `α^* y_gen = β^* y_gen`, and the generator extensionality
`algHom_ext_x_y_gen` finishes. -/
theorem Isogeny.pullback_eq_of_pointMap_eqOn_infinite
    {α β : Isogeny W.toAffine W.toAffine}
    {badα badβ : Set (W_smooth W).SmoothPoint}
    (hbadα : badα.Finite) (hbadβ : badβ.Finite)
    (hwα : PullbackEvaluation W α badα) (hwβ : PullbackEvaluation W β badβ)
    {S : Set (W_smooth W).SmoothPoint} (hS : S.Infinite)
    (h : ∀ P ∈ S, α.toAddMonoidHom P.toAffinePoint = β.toAddMonoidHom P.toAffinePoint) :
    α.pullback = β.pullback := by
  have hS' : (S \ (badα ∪ badβ)).Infinite := hS.diff (hbadα.union hbadβ)
  -- at every common good point the pulled-back generators take the same value
  have key : ∀ P ∈ S \ (badα ∪ badβ),
      (∃ c : F, EvaluatesTo W P (α.pullback (x_gen W)) c ∧
        EvaluatesTo W P (β.pullback (x_gen W)) c) ∧
      (∃ c : F, EvaluatesTo W P (α.pullback (y_gen W)) c ∧
        EvaluatesTo W P (β.pullback (y_gen W)) c) := by
    rintro P ⟨hPS, hPbad⟩
    obtain ⟨xa, ya, hnsa, heqa, hxa, hya⟩ :=
      hwα P (fun hc ↦ hPbad (Set.mem_union_left _ hc))
    obtain ⟨xb, yb, hnsb, heqb, hxb, hyb⟩ :=
      hwβ P (fun hc ↦ hPbad (Set.mem_union_right _ hc))
    have heq : (WeierstrassCurve.Affine.Point.some xa ya hnsa : W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some xb yb hnsb :=
      heqa.symm.trans ((h P hPS).trans heqb)
    obtain ⟨hxx, hyy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp heq
    exact ⟨⟨xa, hxa, by rw [hxx]; exact hxb⟩, ⟨ya, hya, by rw [hyy]; exact hyb⟩⟩
  have hx : α.pullback (x_gen W) = β.pullback (x_gen W) :=
    eq_of_evaluatesTo_infinite W hS' fun P hP ↦ (key P hP).1
  have hy : α.pullback (y_gen W) = β.pullback (y_gen W) :=
    eq_of_evaluatesTo_infinite W hS' fun P hP ↦ (key P hP).2
  exact algHom_ext_x_y_gen W hx hy

variable {W} in
/-- **The separation engine, point-set form**: agreement of the stored point maps on an
infinite set of `Affine.Point`s (e.g. a torsion union) gives pullback equality.  All nonzero
points are affine, so the infinite agreement transfers to smooth points. -/
theorem Isogeny.pullback_eq_of_pointMap_eqOn_infinite_points
    {α β : Isogeny W.toAffine W.toAffine}
    {badα badβ : Set (W_smooth W).SmoothPoint}
    (hbadα : badα.Finite) (hbadβ : badβ.Finite)
    (hwα : PullbackEvaluation W α badα) (hwβ : PullbackEvaluation W β badβ)
    {T : Set W.toAffine.Point} (hT : T.Infinite)
    (h : ∀ P ∈ T, α.toAddMonoidHom P = β.toAddMonoidHom P) :
    α.pullback = β.pullback := by
  -- every nonzero point is affine, so `T \ {0}` lifts to smooth points
  have hsub : T \ {0} ⊆
      Set.range (fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint) := by
    rintro P ⟨hPT, hP0⟩
    cases P with
    | zero =>
      exact absurd (Set.mem_singleton_iff.mpr WeierstrassCurve.Affine.Point.zero_def) hP0
    | some x y hns => exact ⟨⟨x, y, hns⟩, rfl⟩
  have hpre : ((fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint) ⁻¹'
      (T \ {0})).Infinite :=
    (hT.diff (Set.finite_singleton 0)).preimage hsub
  exact Isogeny.pullback_eq_of_pointMap_eqOn_infinite hbadα hbadβ hwα hwβ hpre
    fun P hP ↦ h P.toAffinePoint hP.1

variable {W} in
/-- **Full extensionality from point-map agreement** (over `K̄`): two coherent
endo-isogenies with the *same* stored point map are equal — the pullbacks agree by the
separation engine on the (infinite) full point set, and the structure has no further
fields. -/
theorem Isogeny.ext_of_pointMap_eq [IsAlgClosed F]
    {α β : Isogeny W.toAffine W.toAffine}
    {badα badβ : Set (W_smooth W).SmoothPoint}
    (hbadα : badα.Finite) (hbadβ : badβ.Finite)
    (hwα : PullbackEvaluation W α badα) (hwβ : PullbackEvaluation W β badβ)
    (h : ∀ P : W.toAffine.Point, α.toAddMonoidHom P = β.toAddMonoidHom P) :
    α = β := by
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI : Infinite (W_smooth W).SmoothPoint := (W_smooth W).smoothPoint_infinite
  refine Isogeny.ext ?_ (AddMonoidHom.ext h)
  exact Isogeny.pullback_eq_of_pointMap_eqOn_infinite hbadα hbadβ hwα hwβ
    Set.infinite_univ fun P _ ↦ h P.toAffinePoint

/-! ### The infinitude source: nonzero torsion across infinitely many primes -/

/-- **`E[ℓ]` has a nonzero point** over `K̄` for `|ℓ| > 1`, `(ℓ : F) ≠ 0`:
`#E[ℓ] = ℓ² > 1` (`card_torsion_ell`). -/
theorem exists_torsion_ne_zero [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (hℓ1 : 1 < ℓ.natAbs) :
    ∃ P : W.toAffine.Point, ℓ • P = 0 ∧ P ≠ 0 := by
  have hcard : Nat.card W.toAffine[ℓ] = ℓ.natAbs ^ 2 := by
    have hZ := WeilPairing.TorsionGeometric.card_torsion_ell W ℓ hℓ
    have h' : (Nat.card W.toAffine[ℓ] : ℤ) = ((ℓ.natAbs ^ 2 : ℕ) : ℤ) := by
      rw [hZ]; push_cast; rw [sq_abs]
    exact_mod_cast h'
  by_contra hno
  push Not at hno
  have hbot : W.toAffine[ℓ] = ⊥ := by
    ext P
    simp only [mem_torsionSubgroup, AddSubgroup.mem_bot]
    exact ⟨fun hP ↦ hno P hP, fun hP ↦ by rw [hP, smul_zero]⟩
  rw [hbot, AddSubgroup.card_bot] at hcard
  exact absurd hcard.symm (Nat.one_lt_pow two_ne_zero hℓ1).ne'

/-- The union of the `ℓ`-torsion subgroups over `ℓ ∈ L` — the agreement set of the
dual-additivity argument. -/
def torsionUnionSet (L : Set ℕ) : Set W.toAffine.Point :=
  {P : W.toAffine.Point | ∃ ℓ ∈ L, ((ℓ : ℤ)) • P = 0}

@[simp] theorem mem_torsionUnionSet {L : Set ℕ} {P : W.toAffine.Point} :
    P ∈ torsionUnionSet W L ↔ ∃ ℓ ∈ L, ((ℓ : ℤ)) • P = 0 := Iff.rfl

/-- **The torsion union over infinitely many good primes is infinite**: each `E[ℓ]`
contributes a nonzero point (`exists_torsion_ne_zero`), and the contributions are pairwise
distinct since nonzero torsion at coprime orders is disjoint
(`torsionSubgroup_inf` + `Nat.coprime_primes`). -/
theorem torsionUnionSet_infinite [IsAlgClosed F] {L : Set ℕ}
    (hL : L.Infinite) (hLp : ∀ ℓ ∈ L, Nat.Prime ℓ)
    (hLchar : ∀ ℓ ∈ L, ((ℓ : ℤ) : F) ≠ 0) :
    (torsionUnionSet W L).Infinite := by
  haveI : Infinite ↥L := hL.to_subtype
  -- choose a nonzero `ℓ`-torsion point for each `ℓ ∈ L`
  have hchoice : ∀ ℓ : ↥L,
      ∃ P : W.toAffine.Point, ((ℓ : ℕ) : ℤ) • P = 0 ∧ P ≠ 0 := by
    rintro ⟨ℓ, hℓ⟩
    refine exists_torsion_ne_zero W ((ℓ : ℕ) : ℤ) (hLchar ℓ hℓ) ?_
    rw [Int.natAbs_natCast]
    exact (hLp ℓ hℓ).one_lt
  set f : ↥L → W.toAffine.Point := fun ℓ ↦ (hchoice ℓ).choose with hf
  have hf_spec : ∀ ℓ : ↥L, ((ℓ : ℕ) : ℤ) • f ℓ = 0 ∧ f ℓ ≠ 0 :=
    fun ℓ ↦ (hchoice ℓ).choose_spec
  -- distinct primes give distinct points: nonzero torsion at coprime orders is disjoint
  have hinj : Function.Injective f := by
    rintro ⟨ℓ₁, h₁⟩ ⟨ℓ₂, h₂⟩ heq
    by_contra hne
    have hℓne : ℓ₁ ≠ ℓ₂ := fun hc ↦ hne (Subtype.ext hc)
    have h1 : ((ℓ₁ : ℕ) : ℤ) • f ⟨ℓ₁, h₁⟩ = 0 := (hf_spec ⟨ℓ₁, h₁⟩).1
    have h2 : ((ℓ₂ : ℕ) : ℤ) • f ⟨ℓ₁, h₁⟩ = 0 := by
      rw [heq]; exact (hf_spec ⟨ℓ₂, h₂⟩).1
    have hcop : IsCoprime ((ℓ₁ : ℕ) : ℤ) ((ℓ₂ : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes (hLp ℓ₁ h₁) (hLp ℓ₂ h₂)).mpr hℓne
    obtain ⟨a, b, hab⟩ := hcop
    refine (hf_spec ⟨ℓ₁, h₁⟩).2 ?_
    calc f ⟨ℓ₁, h₁⟩ = (1 : ℤ) • f ⟨ℓ₁, h₁⟩ := (one_smul ℤ _).symm
      _ = (a * ((ℓ₁ : ℕ) : ℤ) + b * ((ℓ₂ : ℕ) : ℤ)) • f ⟨ℓ₁, h₁⟩ := by rw [hab]
      _ = a • (((ℓ₁ : ℕ) : ℤ) • f ⟨ℓ₁, h₁⟩) + b • (((ℓ₂ : ℕ) : ℤ) • f ⟨ℓ₁, h₁⟩) := by
          rw [add_smul, mul_smul, mul_smul]
      _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro P ⟨ℓ, rfl⟩
  exact ⟨ℓ.val, ℓ.prop, (hf_spec ℓ).1⟩

end HasseWeil

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

/-! ### Assembly: dual additivity (Part B) -/

section DualAdd

variable [IsAlgClosed F]

variable {W} in
/-- **Dual additivity on the torsion union** (Silverman III.6.2(c), per-`ℓ` form unioned):
if `χ` is a sum isogeny for `φ + ψ` (stored point maps) and `δφ, δψ, δχ` are `ℓ`-level Weil
adjoints of the respective point maps for every `ℓ ∈ L`, then `δχ = δφ + δψ` on
`⋃_{ℓ ∈ L} E[ℓ]`.  Pure `IsWeilAdjointOn.add` at the witnessing prime. -/
theorem dual_add_pointMap_eqOn_torsionUnion
    {φ ψ χ : Isogeny W.toAffine W.toAffine}
    {δφ δψ δχ : W.toAffine.Point →+ W.toAffine.Point}
    {L : Set ℕ} (hLchar : ∀ ℓ ∈ L, ((ℓ : ℤ) : F) ≠ 0)
    (hχ : χ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom)
    (hadjφ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ φ.toAddMonoidHom δφ)
    (hadjψ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ ψ.toAddMonoidHom δψ)
    (hadjχ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ χ.toAddMonoidHom δχ) :
    ∀ P ∈ torsionUnionSet W L, δχ P = δφ P + δψ P := by
  rintro P ⟨ℓ, hmem, hP⟩
  have hℓ : ((ℓ : ℤ) : F) ≠ 0 := hLchar ℓ hmem
  have hsum : ∀ Q : W.toAffine.Point,
      χ.toAddMonoidHom Q = φ.toAddMonoidHom Q + ψ.toAddMonoidHom Q := by
    intro Q; rw [hχ]; rfl
  exact IsWeilAdjointOn.add (hadjφ ℓ hmem hℓ) (hadjψ ℓ hmem hℓ) (hadjχ ℓ hmem hℓ) hsum hP

variable {W} in
/-- **DUAL ADDITIVITY** `(φ+ψ)^ = φ̂ + ψ̂` (Silverman III.6.2(c), arbitrary characteristic,
pullback form).  Given

* a sum-isogeny witness `χ` for `φ + ψ` and a sum-isogeny witness `σ` for `φ̂ + ψ̂`
  (stored point maps; `addIsog` builds such isogenies),
* a dual candidate `Dχ` for `χ`, where "dual" enters *only* through the per-`ℓ` adjoint
  identities: `δφ, δψ, Dχ.toAddMonoidHom` are `ℓ`-level Weil adjoints of `φ, ψ, χ` for
  every `ℓ` in an infinite set `L` of primes invertible in `F`,
* the stored-fields coherence witnesses (`PullbackEvaluation`) for `Dχ` and `σ`,

the two candidate duals have **equal pullbacks**: `Dχ.pullback = σ.pullback`.

The point maps agree on the infinite torsion union (`dual_add_pointMap_eqOn_torsionUnion`),
and the separation engine upgrades this to pullback equality. -/
theorem dual_add_pullback
    {φ ψ χ Dχ σ : Isogeny W.toAffine W.toAffine}
    {δφ δψ : W.toAffine.Point →+ W.toAffine.Point}
    {L : Set ℕ} (hL : L.Infinite) (hLp : ∀ ℓ ∈ L, Nat.Prime ℓ)
    (hLchar : ∀ ℓ ∈ L, ((ℓ : ℤ) : F) ≠ 0)
    (hχ : χ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom)
    (hσ : σ.toAddMonoidHom = δφ + δψ)
    (hadjφ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ φ.toAddMonoidHom δφ)
    (hadjψ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ ψ.toAddMonoidHom δψ)
    (hadjχ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ χ.toAddMonoidHom Dχ.toAddMonoidHom)
    {badχ badσ : Set (W_smooth W).SmoothPoint}
    (hbχ : badχ.Finite) (hbσ : badσ.Finite)
    (hwχ : PullbackEvaluation W Dχ badχ) (hwσ : PullbackEvaluation W σ badσ) :
    Dχ.pullback = σ.pullback := by
  have htor := dual_add_pointMap_eqOn_torsionUnion hLchar hχ hadjφ hadjψ hadjχ
  refine Isogeny.pullback_eq_of_pointMap_eqOn_infinite_points hbχ hbσ hwχ hwσ
    (torsionUnionSet_infinite W hL hLp hLchar) fun P hP ↦ ?_
  rw [hσ]
  exact htor P hP

end DualAdd

end HasseWeil.WeilPairing

namespace HasseWeil.EC

open HasseWeil HasseWeil.WeilPairing HasseWeil.Curves

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

section CanonicalDualForm

variable [IsAlgClosed F]

variable {W} in
/-- **Dual additivity at the canonical dual** (Silverman III.6.2(c), the headline form):
if the canonical dual `χ̂ = χE.canonicalDual w` (`CanonicalDual.lean`) is realised by the
Basic dual candidate `Dχ` (`hreal`, pullback agreement), then under the hypotheses of
`dual_add_pullback` the canonical dual's pullback **is** the pullback of the sum
`σ = φ̂ + ψ̂`:

`(χE.canonicalDual w).pullback = σ.pullback`. -/
theorem Isogeny.canonicalDual_pullback_eq_of_dual_add
    (χE : EC.Isogeny W.toAffine W.toAffine) (w : χE.HasCanonicalDualWitness)
    {φ ψ χ Dχ σ : HasseWeil.Isogeny W.toAffine W.toAffine}
    (hreal : (χE.canonicalDual w).toCurveMap.pullback = Dχ.pullback)
    {δφ δψ : W.toAffine.Point →+ W.toAffine.Point}
    {L : Set ℕ} (hL : L.Infinite) (hLp : ∀ ℓ ∈ L, Nat.Prime ℓ)
    (hLchar : ∀ ℓ ∈ L, ((ℓ : ℤ) : F) ≠ 0)
    (hχ : χ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom)
    (hσ : σ.toAddMonoidHom = δφ + δψ)
    (hadjφ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ φ.toAddMonoidHom δφ)
    (hadjψ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ ψ.toAddMonoidHom δψ)
    (hadjχ : ∀ ℓ ∈ L, ∀ hℓ : ((ℓ : ℤ) : F) ≠ 0,
      IsWeilAdjointOn W (ℓ : ℤ) hℓ χ.toAddMonoidHom Dχ.toAddMonoidHom)
    {badχ badσ : Set (W_smooth W).SmoothPoint}
    (hbχ : badχ.Finite) (hbσ : badσ.Finite)
    (hwχ : PullbackEvaluation W Dχ badχ) (hwσ : PullbackEvaluation W σ badσ) :
    (χE.canonicalDual w).toCurveMap.pullback = σ.pullback :=
  hreal.trans (dual_add_pullback hL hLp hLchar hχ hσ hadjφ hadjψ hadjχ hbχ hbσ hwχ hwσ)

end CanonicalDualForm

end HasseWeil.EC

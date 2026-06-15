/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.KernelOfDifferential
import HasseWeil.EC.IsogenyAG.FrobeniusTwist
import HasseWeil.EC.IsogenyAG.FrobeniusDual
import HasseWeil.Hasse.Separability

/-!
# G3: the general twisted Frobenius factorization (Silverman II.2.12) and the relative Verschiebung

Silverman II.2.12 over **every** field of characteristic `p > 0` (perfect base): every
isogeny `φ : E → E'` factors as `φ = φ_sep ∘ Frob_{p^k}` where `Frob_{p^k} : E → E^{(p^k)}`
is the *relative* `p^k`-power Frobenius (the cross-curve twist of `FrobeniusTwist.lean`)
and `φ_sep : E^{(p^k)} → E'` is separable.

This is the **twisted, cross-curve** form. The same-curve statement "every inseparable `φ`
has `Im(φ*) ⊆ Im(π_q*)`" is FALSE over composite `q = pˢ` (e.g. `[p]` over `𝔽_{p²}` has
`deg_i = p`, not a `q`-power), which is why the factorization must pass through the twist
`E^{(p)} ≠ E`; cf. the "general `p^k` twist gap" of `DualReduction.lean`, now closed.

## Layer 0 — the G1 corollary generalized to two curves

`Curves/KernelOfDifferential.lean`'s `Im(φ*) ⊆ K(E)^p` for inseparable `φ` was
endomorphism-only. The proof route is curve-pair-agnostic (T-II-4-004 reverse direction +
`ker d = K^p` on the **source** function field), so we generalize to `EC.Isogeny W₁ W₂`:

* `Isogeny.finiteDimensional_toAlgebra` / `Isogeny.degree_pos'` — `[K(E₁) : φ*K(E₂)] < ∞`
  and `0 < deg φ`, two-curve, unconditional (transcendence-degree argument via
  `CurveMap.isAlgebraic_toAlgebra` + `EssFiniteType`).
* `Isogeny.isSeparable_iff_algebra_isSeparable` — `deg_i φ = 1 ↔ Algebra.IsSeparable`
  (both directions; the endomorphism file had only `Algebra → EC`).
* `Isogeny.isSeparable_of_pullback_kaehlerD_ne_zero` — a single separating image element
  forces separability (cotangent sequence + `FormallyUnramified.iff_isSeparable`).
* `Isogeny.pullback_mem_pth_powers_of_not_isSeparable'` — **the two-curve G1 corollary**:
  `¬φ.IsSeparable → Im(φ*) ⊆ K(E₁)^p`.

## Layer 1 — the single twisted step (a)

For inseparable `φ : E → E'`: `Im(φ*) ⊆ K(E)^p = Im(Frob_p*)`, so the algebraic factoring
`CurveMap.factorThrough` produces `φ₁ : E^{(p)} → E'` with `φ = φ₁ ∘ Frob_p` and
`deg φ = p · deg φ₁`. The basepoint condition of `φ₁` is **derived** (not carried) from the
unconditional `Isogeny.reflects_ordAtInfty` of the relative Frobenius — packaged once as the
fully general cross-curve `Isogeny.factorThrough` (the `EC`-level lift of the algebraic
factoring, mirroring `Isogeny.separablePart`'s basepoint derivation).

## Layer 2 — the full factorization (b): `twistedFrobeniusFactorization`

Strong induction on the degree (mirror of `frobeniusFactorization_of_qStep`): peel one
twisted step while inseparable; the degree strictly drops (`deg φ₁ = deg φ / p`, `p ≥ 2`,
`deg φ₁ ≥ 1`). The **bundled** compose equality `φ = φs.compose (relativeFrobenius p E k)`
is achieved (not just the pullback-level identity): the cast bookkeeping across the source
twists is handled by `Isogeny.congrSource` (term-level `cast`, the `congrTarget` mirror)
and the single `subst`-lemma `congrSource_compose_congrTarget`, with
`relativeFrobenius_add` supplying the iteration law.

## Layer 3 — the `q`-power corollary (c)

Over `𝔽_q` (`q = pˢ`), when the twisted exponent `k` is a multiple of `s` the twist
trivializes (`iterateFrobeniusTwist_card_mul_eq_self`) and the relative Frobenius is the
same-curve `frobeniusPower` (`relativeFrobenius_card_mul_eq_frobeniusPower`); the twisted
factorization then **recovers the `DualReduction` inputs**: the `hincl` inseparability data
and the separability of `Isogeny.separablePart`, hence the `FrobeniusFactorization`
predicate. This is stated *conditionally* on `s ∣ k` — honest: for `s ∤ k` (e.g. `[p]` over
`𝔽_{p²}`) the same-curve factorization genuinely does not exist. Over a prime field
(`s = 1`) the divisibility is automatic and `FrobeniusFactorization` follows outright —
an independent re-derivation of `frobeniusFactorization_of_card_eq_prime`.

## Layer 4 — the relative Verschiebung (d, stretch)

`hasDualWitness_relativeFrobenius`: the relative Frobenius `Frob_{p^e} : E → E^{(p^e)}`
carries a `HasDualWitness` with **every field a theorem** — `ν = [p^e]`, the range
inclusion `Im([p^e]*) ⊆ Im(Frob_{p^e}*)` from iterating the layer-0 step on `[p]`
(`[p]` is inseparable in every characteristic-`p`, `mulByInt_p_not_isSeparable`), the
basepoint from `mulByIntBasepoint_holds`, the reflection from `reflects_ordAtInfty`.
`dualOfWitness` then yields the **relative Verschiebung**
`V̂_{p^e} : E^{(p^e)} → E` with `V̂ ∘ Frob = [p^e]`
(`relativeVerschiebung_compose_relativeFrobenius`, fully bundled). Finale:
`nonempty_hasDualWitness_of_twisted_separable_witnesses` — every isogeny out of `E`
carries a dual witness, modulo only the separable side's witnesses on the twists
(via `HasDualWitness.compose` + the layer-2 factorization).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.11–2.12, III.4.10a, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil.EC

open Curves

/-! ### Layer 0 — the two-curve G1 corollary (`Im(φ*) ⊆ K^p` for inseparable `φ`) -/

section TwoCurveSeparability

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Two-curve finite-dimensionality**: `K(E₁)` is finite-dimensional over `φ*K(E₂)` for
any isogeny `φ : E₁ → E₂`, unconditionally. The transcendence-degree argument
(`CurveMap.isAlgebraic_toAlgebra`) gives algebraicity; `EssFiniteType` descends from
`F → K(E₁)` along the scalar tower; mathlib's
`Algebra.finite_of_essFiniteType_of_isAlgebraic` concludes. Two-curve generalization of
`HasseWeil.isogeny_finiteDimensional`. -/
theorem Isogeny.finiteDimensional_toAlgebra (φ : Isogeny W₁ W₂) :
    @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toCurveMap.toAlgebra.toModule := by
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.toCurveMap.toAlgebra
  haveI : IsScalarTower F W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.toCurveMap.pullback.commutes x).symm
  haveI : Algebra.EssFiniteType W₂.FunctionField W₁.FunctionField :=
    Algebra.EssFiniteType.of_comp F W₂.FunctionField W₁.FunctionField
  haveI : Algebra.IsAlgebraic W₂.FunctionField W₁.FunctionField :=
    ⟨fun z => CurveMap.isAlgebraic_toAlgebra φ.toCurveMap z⟩
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **Two-curve degree positivity**: `0 < deg φ` for any isogeny `φ : E₁ → E₂`,
unconditionally. Generalizes `EC.Isogeny.degree_pos` (which is endomorphism-only). -/
theorem Isogeny.degree_pos' (φ : Isogeny W₁ W₂) : 0 < φ.degree := by
  change 0 < φ.toCurveMap.degree
  unfold CurveMap.degree
  exact @Module.finrank_pos W₂.FunctionField W₁.FunctionField _ _
    φ.toCurveMap.toAlgebra.toModule _ φ.finiteDimensional_toAlgebra _ _ _

/-- **The two-curve separability bridge, iff form**: `φ` is separable in the EC sense
(`deg_i φ = 1`) iff the function-field extension `K(E₁)/φ*K(E₂)` is separable in the
`Algebra.IsSeparable` sense. Both directions (the endomorphism file
`KernelOfDifferential.lean` had only `Algebra → EC`); uses the unconditional two-curve
finite-dimensionality and `Field.finSepDegree_eq_finrank_iff`. -/
theorem Isogeny.isSeparable_iff_algebra_isSeparable (φ : Isogeny W₁ W₂) :
    φ.IsSeparable ↔
      @Algebra.IsSeparable W₂.FunctionField W₁.FunctionField _ _ φ.toCurveMap.toAlgebra := by
  have hfin := φ.finiteDimensional_toAlgebra
  have hiff := @Field.finSepDegree_eq_finrank_iff W₂.FunctionField W₁.FunctionField _ _
    φ.toCurveMap.toAlgebra hfin
  have h_mul : φ.toCurveMap.separableDegree *
      @Field.finInsepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toCurveMap.toAlgebra =
      φ.toCurveMap.degree :=
    @Field.finSepDegree_mul_finInsepDegree W₂.FunctionField W₁.FunctionField _ _
      φ.toCurveMap.toAlgebra
  have h_sep_pos : 0 < φ.toCurveMap.separableDegree :=
    Nat.pos_of_ne_zero (@NeZero.ne _ _ _
      (@Field.instNeZeroFinSepDegree _ _ _ _ φ.toCurveMap.toAlgebra hfin))
  rw [← hiff]
  change φ.toCurveMap.degree / φ.toCurveMap.separableDegree = 1 ↔ _
  constructor
  · intro h1
    have h_dvd : φ.toCurveMap.separableDegree ∣ φ.toCurveMap.degree := ⟨_, h_mul.symm⟩
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk, Nat.mul_div_cancel_left _ h_sep_pos] at h1
    change φ.toCurveMap.separableDegree = φ.toCurveMap.degree
    rw [hk, h1, mul_one]
  · intro h2
    have h2' : φ.toCurveMap.separableDegree = φ.toCurveMap.degree := h2
    change φ.toCurveMap.degree / φ.toCurveMap.separableDegree = 1
    rw [h2']
    exact Nat.div_self (h2' ▸ h_sep_pos)

/-- **A separating image element forces separability** (T-II-4-004 reverse direction,
two-curve): if some pullback `φ* f` has nonvanishing differential in `Ω[K(E₁)/F]`, then
`φ` is separable. Cotangent sequence: `D(φ* f) ≠ 0` makes
`K(E₁) ⊗ Ω[K(E₂)/F] → Ω[K(E₁)/F]` surjective (the target is one-dimensional,
`kaehler_rank_one`), so `Ω[K(E₁)/K(E₂)] = 0`, i.e. the extension is formally unramified,
hence separable (`Algebra.FormallyUnramified.iff_isSeparable`, with `EssFiniteType` from
the tower). -/
theorem Isogeny.isSeparable_of_pullback_kaehlerD_ne_zero (φ : Isogeny W₁ W₂)
    (f : W₂.FunctionField)
    (hne : KaehlerDifferential.D F W₁.FunctionField (φ.toCurveMap.pullback f) ≠ 0) :
    φ.IsSeparable := by
  letI : DecidableEq F := Classical.decEq F
  rw [φ.isSeparable_iff_algebra_isSeparable]
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.toCurveMap.toAlgebra
  haveI : IsScalarTower F W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.toCurveMap.pullback.commutes x).symm
  haveI : Algebra.EssFiniteType W₂.FunctionField W₁.FunctionField :=
    Algebra.EssFiniteType.of_comp F W₂.FunctionField W₁.FunctionField
  have hsurj : Function.Surjective
      (KaehlerDifferential.mapBaseChange F W₂.FunctionField W₁.FunctionField) := by
    intro y
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (kaehler_rank_one W₁) hne y
    refine ⟨a • ((1 : W₁.FunctionField) ⊗ₜ KaehlerDifferential.D F W₂.FunctionField f), ?_⟩
    rw [map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D]
    exact ha
  haveI hsub : Subsingleton (KaehlerDifferential W₂.FunctionField W₁.FunctionField) :=
    subsingleton_relativeKaehler_of_mapBaseChange_surjective F _ _ hsurj
  haveI : Algebra.FormallyUnramified W₂.FunctionField W₁.FunctionField := ⟨hsub⟩
  exact (Algebra.FormallyUnramified.iff_isSeparable _ _).mp inferInstance

/-- **The two-curve G1 corollary** (Silverman II.2.12's existence input, single `p`-step,
cross-curve): the pullback image of an inseparable isogeny `φ : E₁ → E₂` consists of
`p`-th powers in the **source** function field — `Im(φ*) ⊆ K(E₁)^p`. Generalizes
`EC.Isogeny.pullback_mem_pth_powers_of_not_isSeparable` (endomorphism-only) to two
curves: contrapositive of `isSeparable_of_pullback_kaehlerD_ne_zero` through
`ker d = K(E₁)^p` (`kaehlerD_eq_zero_iff_mem_pth_powers`). -/
theorem Isogeny.pullback_mem_pth_powers_of_not_isSeparable' (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectField F] (φ : Isogeny W₁ W₂) (h : ¬φ.IsSeparable)
    (f : W₂.FunctionField) :
    ∃ g : W₁.FunctionField, g ^ p = φ.toCurveMap.pullback f := by
  letI : DecidableEq F := Classical.decEq F
  rw [← kaehlerD_eq_zero_iff_mem_pth_powers W₁ p]
  by_contra hne
  exact h (φ.isSeparable_of_pullback_kaehlerD_ne_zero f hne)

end TwoCurveSeparability

/-! ### Cast transport: `congrSource` and the composition laws -/

section CastTransport

variable {F : Type*} [Field F]

/-- Transport an `EC.Isogeny` along an equality of **source** curves. Term-level `cast`
(the type equality is closed by `subst` + proof-irrelevance of `IsElliptic`), the mirror
of `EC.Isogeny.congrTarget`. -/
noncomputable def Isogeny.congrSource {W₂ : Affine F} [W₂.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : Isogeny V.toAffine W₂) : Isogeny V'.toAffine W₂ :=
  cast (by subst h; rfl) φ

@[simp] theorem Isogeny.congrSource_rfl {W₂ : Affine F} [W₂.IsElliptic]
    {V : WeierstrassCurve F} [V.toAffine.IsElliptic] (φ : Isogeny V.toAffine W₂) :
    Isogeny.congrSource rfl φ = φ := rfl

/-- Separability is invariant under source transport. -/
theorem Isogeny.congrSource_isSeparable {W₂ : Affine F} [W₂.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : Isogeny V.toAffine W₂) :
    (Isogeny.congrSource h φ).IsSeparable ↔ φ.IsSeparable := by
  subst h; exact Iff.rfl

/-- The degree is invariant under source transport. -/
theorem Isogeny.congrSource_degree {W₂ : Affine F} [W₂.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : Isogeny V.toAffine W₂) :
    (Isogeny.congrSource h φ).degree = φ.degree := by
  subst h; rfl

/-- `congrTarget` along `h.symm` cancels `congrTarget` along `h`. -/
theorem Isogeny.congrTarget_symm_congrTarget {W₁ : Affine F} [W₁.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : Isogeny W₁ V.toAffine) :
    Isogeny.congrTarget h.symm (Isogeny.congrTarget h φ) = φ := by
  subst h; rfl

/-- **The cast-composition law**: transporting the outer factor's source and the inner
factor's target along the *same* curve equality leaves the composite unchanged. The single
`subst` lemma through which all the bundled factorization identities flow. -/
theorem Isogeny.congrSource_compose_congrTarget {W₀ W₂ : Affine F} [W₀.IsElliptic]
    [W₂.IsElliptic] {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic]
    [V'.toAffine.IsElliptic] (h : V = V') (ψ : Isogeny V.toAffine W₂)
    (ρ : Isogeny W₀ V.toAffine) :
    (Isogeny.congrSource h ψ).compose (Isogeny.congrTarget h ρ) = ψ.compose ρ := by
  subst h; rfl

/-- Composition of `EC.Isogeny`s is associative. -/
theorem Isogeny.compose_assoc {W₁ W₂ W₃ W₄ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    [W₃.IsElliptic] [W₄.IsElliptic] (χ : Isogeny W₃ W₄) (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) :
    (χ.compose ψ).compose φ = χ.compose (ψ.compose φ) :=
  Isogeny.ext_toCurveMap (CurveMap.comp_assoc _ _ _)

/-- Right identity for composition of `EC.Isogeny`s. -/
@[simp] theorem Isogeny.compose_id {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) : φ.compose (Isogeny.id W₁) = φ :=
  Isogeny.ext_toCurveMap (CurveMap.comp_id _)

end CastTransport

/-! ### The general cross-curve factoring (`EC`-level lift of `CurveMap.factorThrough`) -/

section FactorThrough

variable {F : Type*} [Field F] {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  [W₃.IsElliptic]

/-- **The cross-curve factor as an `EC.Isogeny`** (Silverman II.4.11 / II.2.12 pattern):
given isogenies `ρ : E₁ → E₃` (the map factored *through*) and `φ : E₁ → E₂` with the
range inclusion `Im(φ*) ⊆ Im(ρ*)`, the algebraic factoring `CurveMap.factorThrough`
produces the factor `χ : E₃ → E₂` with `φ = χ ∘ ρ`; its basepoint condition is **derived**
(mirroring `Isogeny.separablePart`): `φ` preserves `∞`-regularity and `ρ` reflects it
(`Isogeny.reflects_ordAtInfty`, unconditional), so `χ` preserves it. -/
noncomputable def Isogeny.factorThrough (ρ : Isogeny W₁ W₃) (φ : Isogeny W₁ W₂)
    (hincl : φ.toCurveMap.pullback.range ≤ ρ.toCurveMap.pullback.range) :
    Isogeny W₃ W₂ where
  toCurveMap := CurveMap.factorThrough ρ.toCurveMap φ.toCurveMap hincl
  pullback_ordAtInfty_nonneg f hf := by
    refine ρ.reflects_ordAtInfty _ ?_
    rw [show ρ.toCurveMap.pullback
          ((CurveMap.factorThrough ρ.toCurveMap φ.toCurveMap hincl).pullback f) =
        φ.toCurveMap.pullback f from
      CurveMap.factorThroughPullback_spec _ _ hincl f]
    exact φ.pullback_ordAtInfty_nonneg f hf

/-- **The factoring identity, pullback form**: `ρ* (χ* z) = φ* z` for the factor
`χ = ρ.factorThrough φ hincl`. -/
theorem Isogeny.factorThrough_pullback_spec (ρ : Isogeny W₁ W₃) (φ : Isogeny W₁ W₂)
    (hincl : φ.toCurveMap.pullback.range ≤ ρ.toCurveMap.pullback.range)
    (z : W₂.FunctionField) :
    ρ.toCurveMap.pullback ((ρ.factorThrough φ hincl).toCurveMap.pullback z) =
      φ.toCurveMap.pullback z :=
  CurveMap.factorThroughPullback_spec _ _ hincl z

/-- **The factoring identity, bundled form**: `χ ∘ ρ = φ` as `EC.Isogeny`s. -/
theorem Isogeny.factorThrough_compose (ρ : Isogeny W₁ W₃) (φ : Isogeny W₁ W₂)
    (hincl : φ.toCurveMap.pullback.range ≤ ρ.toCurveMap.pullback.range) :
    (ρ.factorThrough φ hincl).compose ρ = φ :=
  Isogeny.ext_toCurveMap (CurveMap.factorThrough_comp _ _ hincl).symm

/-- **Degree bookkeeping of the factoring**: `deg φ = deg ρ · deg χ`. -/
theorem Isogeny.degree_eq_mul_factorThrough_degree (ρ : Isogeny W₁ W₃)
    (φ : Isogeny W₁ W₂)
    (hincl : φ.toCurveMap.pullback.range ≤ ρ.toCurveMap.pullback.range) :
    φ.degree = ρ.degree * (ρ.factorThrough φ hincl).degree := by
  conv_lhs => rw [← ρ.factorThrough_compose φ hincl]
  rw [Isogeny.compose_degree]

end FactorThrough

/-! ### Layer 1 (deliverable a) — the single twisted step -/

section TwistedStep

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
  [PerfectField F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
variable {V : Affine F} [V.IsElliptic]

/-- **The single-step inseparability data, twisted** (Silverman II.2.12, one `p`-step over
an arbitrary perfect base): an inseparable isogeny `φ : E → E'` has
`Im(φ*) ⊆ K(E)^p = Im(Frob_p*)` — the range-inclusion input of the cross-curve factoring
through the relative Frobenius at `e = 1`. -/
theorem Isogeny.pullback_range_le_relativeFrobenius_one_of_not_isSeparable
    (φ : Isogeny E.toAffine V) (h : ¬φ.IsSeparable) :
    φ.toCurveMap.pullback.range ≤
      (Isogeny.relativeFrobenius p E 1).toCurveMap.pullback.range := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨g, hg⟩ := φ.pullback_mem_pth_powers_of_not_isSeparable' p h z
  obtain ⟨w, hw⟩ := AlgHom.mem_fieldRange.mp (relativeFrobenius_pow_mem_fieldRange p E 1 g)
  refine ⟨w, ?_⟩
  change (Isogeny.relativeFrobenius p E 1).toCurveMap.pullback w = φ.toCurveMap.pullback z
  rw [hw, pow_one, hg]

/-- **The single twisted step** (deliverable a): the factor `φ₁ : E^{(p)} → E'` of an
inseparable `φ : E → E'` through the relative `p`-Frobenius, with `φ = φ₁ ∘ Frob_p`
(`twistedStep_compose`) and `deg φ = p · deg φ₁` (`degree_eq_p_mul_twistedStep_degree`).
The basepoint condition is derived, not carried. -/
noncomputable def Isogeny.twistedStep (φ : Isogeny E.toAffine V)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.relativeFrobenius p E 1).toCurveMap.pullback.range) :
    Isogeny (E.iterateFrobeniusTwist p 1).toAffine V :=
  (Isogeny.relativeFrobenius p E 1).factorThrough φ hincl

omit [PerfectField F] in
/-- **The twisted-step factorization identity**: `φ₁ ∘ Frob_p = φ` as `EC.Isogeny`s. -/
theorem Isogeny.twistedStep_compose (φ : Isogeny E.toAffine V)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.relativeFrobenius p E 1).toCurveMap.pullback.range) :
    (φ.twistedStep p E hincl).compose (Isogeny.relativeFrobenius p E 1) = φ :=
  (Isogeny.relativeFrobenius p E 1).factorThrough_compose φ hincl

/-- **Degree bookkeeping of the twisted step**: `deg φ = p · deg φ₁`. -/
theorem Isogeny.degree_eq_p_mul_twistedStep_degree (φ : Isogeny E.toAffine V)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.relativeFrobenius p E 1).toCurveMap.pullback.range) :
    φ.degree = p * (φ.twistedStep p E hincl).degree := by
  have h := (Isogeny.relativeFrobenius p E 1).degree_eq_mul_factorThrough_degree φ hincl
  rw [relativeFrobenius_degree p E 1, pow_one] at h
  exact h

end TwistedStep

/-! ### The `e = 0` identification and the rearranged iteration law -/

section RelFrobIteration

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [ExpChar F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- **The relative `p⁰`-Frobenius is the identity**, transported along the twist-`0`
trivialization `E^{(p⁰)} = E`. -/
theorem Isogeny.relativeFrobenius_zero :
    Isogeny.relativeFrobenius p E 0 =
      Isogeny.congrTarget (iterateFrobeniusTwist_zero p E).symm (Isogeny.id E.toAffine) := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext ?_)
  refine functionField_algHom_ext (V := E.iterateFrobeniusTwist p 0) ?_ ?_
  · rw [show (Isogeny.relativeFrobenius p E 0).toCurveMap.pullback
        (x_gen (E.iterateFrobeniusTwist p 0)) = x_gen E ^ p ^ 0 from
      relativeFrobenius_pullback_x_gen p E 0,
      Isogeny.congrTarget_pullback_x_gen (iterateFrobeniusTwist_zero p E).symm
        (Isogeny.id E.toAffine), pow_zero, pow_one]
    rfl
  · rw [show (Isogeny.relativeFrobenius p E 0).toCurveMap.pullback
        (y_gen (E.iterateFrobeniusTwist p 0)) = y_gen E ^ p ^ 0 from
      relativeFrobenius_pullback_y_gen p E 0,
      Isogeny.congrTarget_pullback_y_gen (iterateFrobeniusTwist_zero p E).symm
        (Isogeny.id E.toAffine), pow_zero, pow_one]
    rfl

/-- **The iteration law, composition-resolved form**: the composite
`Frob_{p^b}^{twist} ∘ Frob_{p^a}` *is* `Frob_{p^{a+b}}` transported onto the iterated-twist
source — `relativeFrobenius_add` with the `congrTarget` moved to the right-hand side. -/
theorem Isogeny.relativeFrobenius_compose_relativeFrobenius (a b : ℕ) :
    (Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).compose
        (Isogeny.relativeFrobenius p E a) =
      Isogeny.congrTarget (iterateFrobeniusTwist_iterateFrobeniusTwist p E a b).symm
        (Isogeny.relativeFrobenius p E (a + b)) := by
  rw [← relativeFrobenius_add p E a b]
  exact (Isogeny.congrTarget_symm_congrTarget _ _).symm

end RelFrobIteration

/-! ### Layer 2 (deliverable b) — the full twisted factorization -/

section TwistedFactorization

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
  [PerfectField F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
variable {V : Affine F} [V.IsElliptic]

/-- **Silverman II.2.12, general twisted form** (deliverable b): over a perfect field of
characteristic `p`, every isogeny `φ : E → E'` factors as `φ = φs ∘ Frob_{p^k}` with
`Frob_{p^k} : E → E^{(p^k)}` the relative Frobenius and `φs : E^{(p^k)} → E'`
**separable** — the bundled compose equality, not merely the pullback-level identity.
Strong induction on the degree, peeling single twisted steps. -/
theorem twistedFrobeniusFactorization (φ : Isogeny E.toAffine V) :
    ∃ (k : ℕ) (φs : Isogeny (E.iterateFrobeniusTwist p k).toAffine V),
      φs.IsSeparable ∧ φ = φs.compose (Isogeny.relativeFrobenius p E k) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have main : ∀ n : ℕ, ∀ (E' : WeierstrassCurve F) [E'.toAffine.IsElliptic]
      (φ' : Isogeny E'.toAffine V), φ'.degree ≤ n →
      ∃ (k : ℕ) (φs : Isogeny (E'.iterateFrobeniusTwist p k).toAffine V),
        φs.IsSeparable ∧ φ' = φs.compose (Isogeny.relativeFrobenius p E' k) := by
    intro n
    induction n with
    | zero =>
      intro E' instE' φ' hdeg
      have := φ'.degree_pos'
      omega
    | succ n ih =>
      intro E' instE' φ' hdeg
      by_cases hsep : φ'.IsSeparable
      · -- Separable: `k = 0`, transport along the twist-`0` trivialization.
        refine ⟨0, Isogeny.congrSource (iterateFrobeniusTwist_zero p E').symm φ',
          (Isogeny.congrSource_isSeparable _ _).mpr hsep, ?_⟩
        rw [Isogeny.relativeFrobenius_zero, Isogeny.congrSource_compose_congrTarget,
          Isogeny.compose_id]
      · -- Inseparable: peel one twisted step and recurse on the smaller degree.
        have hincl :=
          φ'.pullback_range_le_relativeFrobenius_one_of_not_isSeparable p E' hsep
        have hd1 : (φ'.twistedStep p E' hincl).degree ≤ n := by
          have h1 := φ'.degree_eq_p_mul_twistedStep_degree p E' hincl
          have h2 : 2 * (φ'.twistedStep p E' hincl).degree ≤
              p * (φ'.twistedStep p E' hincl).degree :=
            Nat.mul_le_mul_right _ hp2
          have h3 := (φ'.twistedStep p E' hincl).degree_pos'
          omega
        obtain ⟨k', φs', hsep', hfact'⟩ :=
          ih (E'.iterateFrobeniusTwist p 1) (φ'.twistedStep p E' hincl) hd1
        refine ⟨1 + k',
          Isogeny.congrSource (iterateFrobeniusTwist_iterateFrobeniusTwist p E' 1 k') φs',
          (Isogeny.congrSource_isSeparable _ _).mpr hsep', ?_⟩
        rw [← relativeFrobenius_add p E' 1 k', Isogeny.congrSource_compose_congrTarget,
          ← Isogeny.compose_assoc, ← hfact', φ'.twistedStep_compose p E' hincl]
  exact main φ.degree E φ le_rfl

-- `[DecidableEq F]` enters through `twistedFrobeniusFactorization` (whose statement names
-- `relativeFrobenius`) in the proof; the linter only inspects the surface type.
set_option linter.unusedDecidableInType false in
/-- **The pullback-level corollary of II.2.12**: every pullback of `φ` is a `p^k`-th
power in `K(E)`, `k` the twisted exponent — `φ* z = (g_z)^{p^k}`. -/
theorem twistedFrobeniusFactorization_pow_root (φ : Isogeny E.toAffine V) :
    ∃ k : ℕ, ∀ z : V.FunctionField,
      ∃ g : E.toAffine.FunctionField, g ^ p ^ k = φ.toCurveMap.pullback z := by
  obtain ⟨k, φs, _, hfact⟩ := twistedFrobeniusFactorization p E φ
  refine ⟨k, fun z => ?_⟩
  have hz : φ.toCurveMap.pullback z =
      (Isogeny.relativeFrobenius p E k).toCurveMap.pullback
        (φs.toCurveMap.pullback z) := by
    conv_lhs => rw [hfact]
    rfl
  rw [hz]
  have hmem : (Isogeny.relativeFrobenius p E k).toCurveMap.pullback
      (φs.toCurveMap.pullback z) ∈
      ((Isogeny.relativeFrobenius p E k).toCurveMap.pullback.fieldRange).toSubfield :=
    (IntermediateField.mem_toSubfield _ _).mpr ⟨φs.toCurveMap.pullback z, rfl⟩
  rw [relativeFrobenius_fieldRange_toSubfield p E k] at hmem
  obtain ⟨g, hg⟩ := RingHom.mem_fieldRange.mp hmem
  exact ⟨g, hg⟩

end TwistedFactorization

/-! ### Layer 3 (deliverable c) — the `q`-power corollary over `𝔽_q` -/

section QPowerCorollary

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (p s : ℕ) [Fact p.Prime] [CharP K p] [ExpChar K p]
variable [Fact (Fintype.card K = p ^ s)]
variable (E : WeierstrassCurve K) [E.toAffine.IsElliptic]

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- **Twist trivialization of the factorization** (`s ∣ k` case): over `𝔽_q` (`q = pˢ`),
a twisted factorization with exponent `s·m` *is* a same-curve factorization through the
`q`-power Frobenius iterate `π^m` — the `q`-identification
`relativeFrobenius_card_mul_eq_frobeniusPower` resolved through the cast-composition law. -/
theorem twistedFactorization_card_mul_eq (φ : Isogeny E.toAffine E.toAffine) (m : ℕ)
    (φs : Isogeny (E.iterateFrobeniusTwist p (s * m)).toAffine E.toAffine)
    (hfact : φ = φs.compose (Isogeny.relativeFrobenius p E (s * m))) :
    φ = (Isogeny.congrSource (iterateFrobeniusTwist_card_mul_eq_self p s E m) φs).compose
      (Isogeny.frobeniusPower E.toAffine m) := by
  rw [← relativeFrobenius_card_mul_eq_frobeniusPower p s E m,
    Isogeny.congrSource_compose_congrTarget]
  exact hfact

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- **The `hincl` input of `DualReduction` recovered** (deliverable c): a twisted
factorization with exponent `s·m` yields the same-curve inseparability data
`Im(φ*) ⊆ Im((π^m)*)` consumed by `Isogeny.separablePart`. -/
theorem rangeIncl_frobeniusPower_of_twistedFactorization
    (φ : Isogeny E.toAffine E.toAffine) (m : ℕ)
    (φs : Isogeny (E.iterateFrobeniusTwist p (s * m)).toAffine E.toAffine)
    (hfact : φ = φs.compose (Isogeny.relativeFrobenius p E (s * m))) :
    φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower E.toAffine m).toCurveMap.pullback.range := by
  rw [twistedFactorization_card_mul_eq p s E φ m φs hfact]
  rintro _ ⟨z, rfl⟩
  exact ⟨(Isogeny.congrSource (iterateFrobeniusTwist_card_mul_eq_self p s E m)
    φs).toCurveMap.pullback z, rfl⟩

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- **The separable part is the trivialized twisted factor**: under `s ∣ k`, the
`DualReduction` separable part `φ.separablePart` coincides with the transported twisted
factor `φs` (pullback-injectivity of `π^m`), hence inherits its separability. -/
theorem separablePart_eq_of_twistedFactorization
    (φ : Isogeny E.toAffine E.toAffine) (m : ℕ)
    (φs : Isogeny (E.iterateFrobeniusTwist p (s * m)).toAffine E.toAffine)
    (hfact : φ = φs.compose (Isogeny.relativeFrobenius p E (s * m))) :
    φ.separablePart m
        (rangeIncl_frobeniusPower_of_twistedFactorization p s E φ m φs hfact) =
      Isogeny.congrSource (iterateFrobeniusTwist_card_mul_eq_self p s E m) φs := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z => ?_))
  apply (Isogeny.frobeniusPower E.toAffine m).pullback_injective
  rw [φ.frobeniusPower_pullback_separablePart_pullback m
    (rangeIncl_frobeniusPower_of_twistedFactorization p s E φ m φs hfact) z]
  conv_lhs => rw [twistedFactorization_card_mul_eq p s E φ m φs hfact]
  rfl

omit [Fact (Nat.Prime p)] [CharP K p] in
/-- **`FrobeniusFactorization` from divisible twisted exponents** (deliverable c,
capstone): if every endomorphism of `E/𝔽_q` admits a twisted factorization whose exponent
is a multiple of `s` (`q = pˢ`), then the same-curve `FrobeniusFactorization` predicate of
`DualReduction.lean` holds. Honest scope: the divisibility is genuinely needed — for
`s ∤ k` (e.g. `[p]` over `𝔽_{p²}`) the same-curve factorization does not exist. -/
theorem frobeniusFactorization_of_twisted_sdvd
    (h : ∀ φ : Isogeny E.toAffine E.toAffine,
      ∃ (k : ℕ) (φs : Isogeny (E.iterateFrobeniusTwist p k).toAffine E.toAffine),
        s ∣ k ∧ φs.IsSeparable ∧ φ = φs.compose (Isogeny.relativeFrobenius p E k)) :
    FrobeniusFactorization E.toAffine := by
  intro φ
  obtain ⟨k, φs, ⟨m, rfl⟩, hsep, hfact⟩ := h φ
  refine ⟨m, rangeIncl_frobeniusPower_of_twistedFactorization p s E φ m φs hfact, ?_⟩
  rw [separablePart_eq_of_twistedFactorization p s E φ m φs hfact]
  exact (Isogeny.congrSource_isSeparable _ _).mpr hsep

end QPowerCorollary

section PrimeFieldCorollary

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

-- `[DecidableEq K]` enters through the twisted factorization in the proof; the linter
-- only inspects the surface type.
set_option linter.unusedDecidableInType false in
/-- **II.2.12 same-curve existence over a prime field, re-derived through the twist**
(`s = 1`, divisibility automatic): an independent confirmation of
`frobeniusFactorization_of_card_eq_prime` via `twistedFrobeniusFactorization` +
the `q`-power corollary. -/
theorem frobeniusFactorization_of_card_eq_prime_via_twist
    (hcard : Fintype.card K = p) (E : WeierstrassCurve K) [E.toAffine.IsElliptic] :
    FrobeniusFactorization E.toAffine := by
  haveI : Fact (Fintype.card K = p ^ 1) := ⟨by rw [pow_one]; exact hcard⟩
  refine frobeniusFactorization_of_twisted_sdvd p 1 E fun φ => ?_
  obtain ⟨k, φs, hsep, hfact⟩ := twistedFrobeniusFactorization p E φ
  exact ⟨k, φs, one_dvd k, hsep, hfact⟩

end PrimeFieldCorollary

/-! ### Layer 4 (deliverable d, stretch) — the relative Verschiebung

The single non-formal input of the relative Verschiebung witness is the **inseparability
of `[p]`** (`a_{[p]} = p = 0`, Silverman III.5.3/III.5.6(b)). The project has it
**axiom-clean over an arbitrary base**: the field-general Route-B chord induction
`omegaCoeff_mulByInt` (`RouteBGeneral.lean`, no EDS Wronskian, no `Fintype`) feeds
`mulByInt_p_omega_pullback_eq_zero` (`Hasse/Separability.lean`). The historical finite-base
twin (`omegaPullbackCoeff_mulByInt_p_eq_zero_routeB`, the `[Fintype K]`-scoped chord
recursion of `RouteBInduction.lean`) is retained for compatibility.

We thread the chain on the single hypothesis
`hinsep : ¬([p] : EC.Isogeny E E).IsSeparable` (every link axiom-clean), and provide both
dischargers: `mulByInt_p_not_isSeparable` (general base, axiom-clean) and
`mulByInt_p_not_isSeparable_finite` (finite base, axiom-clean). -/

section RelativeVerschiebung

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
  [PerfectField F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

omit [CharP F p] [PerfectField F] in
/-- `p^e ≠ 0` as an integer — the `ν`-index of the relative Frobenius dual witness. -/
theorem intPPow_ne_zero (e : ℕ) : ((p ^ e : ℕ) : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr (pow_ne_zero e (Fact.out : p.Prime).pos.ne')

omit [CharP F p] [PerfectField F] in
/-- `p ≠ 0` as an integer. -/
theorem intP_ne_zero : ((p : ℕ) : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'

omit [CharP F p] [PerfectField F] in
/-- **`[p]` is inseparable, EC form, from `a_{[p]} = 0`** (Silverman III.5.6(b)): the
two-curve separability bridge transports `EC`-separability of `[p]` to
`Algebra.IsSeparable` of the Basic-world `[p]`, which forces `a_{[p]} ≠ 0`
(`isogeny_omegaCoeff_ne_zero_of_isSeparable`, T-II-4-004 forward) — contradicting the
supplied vanishing `hcoeff : a_{[p]} = 0`. Axiom-clean; the two dischargers of `hcoeff`
are below. -/
theorem Isogeny.mulByInt_p_not_isSeparable_of_coeff_eq_zero
    (hcoeff : omegaPullbackCoeff E (HasseWeil.mulByInt E.toAffine ((p : ℕ) : ℤ)) = 0) :
    ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable := by
  intro hsep
  have halg := (Isogeny.isSeparable_iff_algebra_isSeparable _).mp hsep
  have hbasic : (HasseWeil.mulByInt E.toAffine ((p : ℕ) : ℤ)).IsSeparable := by
    change @Algebra.IsSeparable E.toAffine.FunctionField E.toAffine.FunctionField _ _
      ((HasseWeil.mulByInt E.toAffine ((p : ℕ) : ℤ)).pullback.toRingHom.toAlgebra)
    rw [show (HasseWeil.mulByInt E.toAffine ((p : ℕ) : ℤ)).pullback =
        HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p : ℕ) : ℤ) (intP_ne_zero p) from
      dif_neg (intP_ne_zero p)]
    exact halg
  exact isogeny_omegaCoeff_ne_zero_of_isSeparable E
    (HasseWeil.mulByInt E.toAffine ((p : ℕ) : ℤ)) hbasic hcoeff

-- `[DecidableEq F]` enters through `omegaPullbackCoeff` in the proof; the linter only
-- inspects the surface type.
set_option linter.unusedDecidableInType false in
omit [PerfectField F] in
/-- **`[p]` is inseparable over a general characteristic-`p` base — axiom-clean**
(Silverman III.5.6(b)). Discharges `a_{[p]} = 0` through
`mulByInt_p_omega_pullback_eq_zero` (`Hasse/Separability.lean`), which routes through
the axiom-clean field-general Route-B chain `omegaCoeff_mulByInt`
(`RouteBGeneral.lean`) — no EDS-Wronskian `sorryAx`. -/
theorem Isogeny.mulByInt_p_not_isSeparable :
    ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable :=
  Isogeny.mulByInt_p_not_isSeparable_of_coeff_eq_zero p E
    (mulByInt_p_omega_pullback_eq_zero p E)

-- `[DecidableEq F]`/`[Fintype F]` enter through the Route B coefficient computation in
-- the proof; the linter only inspects the surface type.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
omit [PerfectField F] in
/-- **`[p]` is inseparable over a finite base — axiom-clean** (Silverman III.5.6(b)):
`a_{[p]} = p = 0` by the `[Fintype K]`-scoped chord-recursion Route B
(`omegaPullbackCoeff_mulByInt_p_eq_zero_routeB`, no EDS Wronskian). Retained for
compatibility — the general-base `mulByInt_p_not_isSeparable` is now equally
axiom-clean (via `RouteBGeneral.lean`). -/
theorem Isogeny.mulByInt_p_not_isSeparable_finite [Fintype F] :
    ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable :=
  Isogeny.mulByInt_p_not_isSeparable_of_coeff_eq_zero p E
    (omegaPullbackCoeff_mulByInt_p_eq_zero_routeB E p (Fact.out : p.Prime).pos.ne')

omit [DecidableEq F] in
/-- **`Im([p^e]*) ⊆ K(E)^{p^e}`, element form**: every `[p^e]`-pullback is a `p^e`-th
power — the layer-0 step iterated `e` times along the multiplicativity
`[p^e · p]* = [p]* ∘ [p^e]*`, from the single inseparability input `hinsep`. -/
theorem mulByInt_p_pow_pullback_exists_pow_root
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ)
    (f : E.toAffine.FunctionField) :
    ∃ g : E.toAffine.FunctionField,
      g ^ p ^ e = HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ)
        (intPPow_ne_zero p e) f := by
  induction e with
  | zero =>
    exact ⟨HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ 0 : ℕ) : ℤ)
      (intPPow_ne_zero p 0) f, pow_one _⟩
  | succ e ih =>
    have hcast : ((p ^ (e + 1) : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) * ((p : ℕ) : ℤ) := by
      push_cast
      ring
    rw [HasseWeil.mulByInt_pullbackAlgHom_congr E.toAffine hcast (intPPow_ne_zero p (e + 1)),
      HasseWeil.mulByInt_pullbackAlgHom_mul E.toAffine ((p ^ e : ℕ) : ℤ) ((p : ℕ) : ℤ)
        (intPPow_ne_zero p e) (intP_ne_zero p),
      AlgHom.comp_apply]
    obtain ⟨g, hg⟩ := ih
    obtain ⟨h', hh⟩ :=
      (Isogeny.mulByInt E.toAffine
        (intP_ne_zero p)).pullback_mem_pth_powers_of_not_isSeparable' p hinsep g
    have hh' : h' ^ p = HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p : ℕ) : ℤ)
        (intP_ne_zero p) g := hh
    refine ⟨h', ?_⟩
    rw [← hg, map_pow, ← hh', ← pow_mul, pow_succ']

/-- **The deep field of the relative Verschiebung witness**:
`Im([p^e]*) ⊆ Im(Frob_{p^e}*)` — through `Im([p^e]*) ⊆ K(E)^{p^e}` and the pure
inseparability of the relative Frobenius range
(`relativeFrobenius_pow_mem_fieldRange`). -/
theorem mulByInt_p_pow_range_le_relativeFrobenius
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ)
        (intPPow_ne_zero p e)).range ≤
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback.range := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨g, hg⟩ := mulByInt_p_pow_pullback_exists_pow_root p E hinsep e z
  obtain ⟨w, hw⟩ := AlgHom.mem_fieldRange.mp (relativeFrobenius_pow_mem_fieldRange p E e g)
  refine ⟨w, ?_⟩
  change (Isogeny.relativeFrobenius p E e).toCurveMap.pullback w =
    HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ) (intPPow_ne_zero p e) z
  rw [hw, hg]

/-- **The relative Frobenius carries a dual witness** (deliverable d), from the single
`[p]`-inseparability input: `ν = [p^e]` (basepoint: `mulByIntBasepoint_holds`), the range
inclusion `mulByInt_p_pow_range_le_relativeFrobenius`, reflection: the unconditional
`Isogeny.reflects_ordAtInfty`. The cross-curve counterpart of `hasDualWitness_frobenius`;
every other field a theorem. -/
noncomputable def hasDualWitnessRelativeFrobeniusOf
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (Isogeny.relativeFrobenius p E e).HasDualWitness :=
  Isogeny.hasDualWitness_of_reflects _
    (HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ) (intPPow_ne_zero p e))
    (mulByInt_p_pow_range_le_relativeFrobenius p E hinsep e)
    (mulByIntBasepoint_holds E.toAffine (intPPow_ne_zero p e))
    (fun g hg => (Isogeny.relativeFrobenius p E e).reflects_ordAtInfty g hg)

/-- **The relative Verschiebung** `V̂_{p^e} : E^{(p^e)} → E` (deliverable d): the dual of
the relative `p^e`-Frobenius, as an `EC.Isogeny`, from the single `[p]`-inseparability
input. Satisfies `V̂ ∘ Frob = [p^e]`
(`relativeVerschiebungOf_compose_relativeFrobenius`). -/
noncomputable def relativeVerschiebungOf
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    Isogeny (E.iterateFrobeniusTwist p e).toAffine E.toAffine :=
  (Isogeny.relativeFrobenius p E e).dual (hasDualWitnessRelativeFrobeniusOf p E hinsep e)

/-- **The defining identity of the relative Verschiebung, pullback form**:
`Frob* (V̂* z) = [p^e]* z`. -/
theorem relativeFrobenius_pullback_relativeVerschiebungOf_pullback
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ)
    (z : E.toAffine.FunctionField) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        ((relativeVerschiebungOf p E hinsep e).toCurveMap.pullback z) =
      HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ)
        (intPPow_ne_zero p e) z :=
  Isogeny.dualOfWitness_comp_pullback _ _ _ _ z

/-- **`V̂ ∘ Frob = [p^e]` as `EC.Isogeny`s** (Silverman III.6.1's defining identity for
the relative Frobenius): the composite of the relative Verschiebung with the relative
Frobenius **is** the multiplication-by-`p^e` isogeny. -/
theorem relativeVerschiebungOf_compose_relativeFrobenius
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (relativeVerschiebungOf p E hinsep e).compose (Isogeny.relativeFrobenius p E e) =
      Isogeny.mulByInt E.toAffine (intPPow_ne_zero p e) := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z => ?_))
  exact relativeFrobenius_pullback_relativeVerschiebungOf_pullback p E hinsep e z

/-! #### Headline instantiations of the Verschiebung

General base and finite base — both axiom-clean (the III.5.3 input `a_{[p]} = 0` is the
field-general Route-B `omegaCoeff_mulByInt` of `RouteBGeneral.lean`). -/

/-- **The relative Verschiebung over a general perfect base — axiom-clean** (deliverable
d headline): `V̂_{p^e} : E^{(p^e)} → E` with `V̂ ∘ Frob = [p^e]`
(`relativeVerschiebung_compose_relativeFrobenius`). The III.5.3 input is the axiom-clean
`mulByInt_p_not_isSeparable` (field-general Route B, `RouteBGeneral.lean`). -/
noncomputable def relativeVerschiebung (e : ℕ) :
    Isogeny (E.iterateFrobeniusTwist p e).toAffine E.toAffine :=
  relativeVerschiebungOf p E (Isogeny.mulByInt_p_not_isSeparable p E) e

/-- `V̂ ∘ Frob = [p^e]` for the general-base Verschiebung. -/
theorem relativeVerschiebung_compose_relativeFrobenius (e : ℕ) :
    (relativeVerschiebung p E e).compose (Isogeny.relativeFrobenius p E e) =
      Isogeny.mulByInt E.toAffine (intPPow_ne_zero p e) :=
  relativeVerschiebungOf_compose_relativeFrobenius p E
    (Isogeny.mulByInt_p_not_isSeparable p E) e

/-- **The relative Verschiebung over a finite base — axiom-clean** (deliverable d
headline): every witness field a theorem, the `[p]`-inseparability by Route B. -/
noncomputable def relativeVerschiebungFinite [Fintype F] (e : ℕ) :
    Isogeny (E.iterateFrobeniusTwist p e).toAffine E.toAffine :=
  relativeVerschiebungOf p E (Isogeny.mulByInt_p_not_isSeparable_finite p E) e

/-- `V̂ ∘ Frob = [p^e]` for the finite-base Verschiebung — axiom-clean. -/
theorem relativeVerschiebungFinite_compose_relativeFrobenius [Fintype F] (e : ℕ) :
    (relativeVerschiebungFinite p E e).compose (Isogeny.relativeFrobenius p E e) =
      Isogeny.mulByInt E.toAffine (intPPow_ne_zero p e) :=
  relativeVerschiebungOf_compose_relativeFrobenius p E
    (Isogeny.mulByInt_p_not_isSeparable_finite p E) e

/-! #### The finale: dual witnesses for arbitrary isogenies, modulo the separable side -/

variable {V : Affine F} [V.IsElliptic]

omit [Fact p.Prime] [CharP F p] [PerfectField F] in
/-- **Dual witness through the twisted factorization** (deliverable d, finale step): a
dual witness for the separable factor of `φ = φs ∘ Frob_{p^k}` and one for the relative
Frobenius itself (e.g. `hasDualWitnessRelativeFrobeniusOf`) compose — by
`HasDualWitness.compose` (conjugation form) — to a dual witness for `φ`. Pure glue,
axiom-clean. -/
noncomputable def Isogeny.hasDualWitness_of_twistedFactorization {k : ℕ} [ExpChar F p]
    (φ : Isogeny E.toAffine V)
    (φs : Isogeny (E.iterateFrobeniusTwist p k).toAffine V)
    (hfact : φ = φs.compose (Isogeny.relativeFrobenius p E k))
    (ws : φs.HasDualWitness)
    (wF : (Isogeny.relativeFrobenius p E k).HasDualWitness) : φ.HasDualWitness :=
  (ws.compose wF).congrIsog hfact.symm

-- `[DecidableEq F]` enters through the twisted factorization and the Verschiebung
-- witness in the proof; the linter only inspects the surface type.
set_option linter.unusedDecidableInType false in
/-- **THE FULLY GENERAL dual existence, modulo the separable side** (deliverable d,
finale, hypothesis-threaded form): over a perfect field of characteristic `p`, *every*
isogeny `φ : E → E'` carries a dual witness, given the `[p]`-inseparability input and
dual witnesses for the **separable** isogenies out of the Frobenius twists of `E`.
Combines the unconditional twisted factorization (II.2.12) with the relative Verschiebung
witness and witness composition. Axiom-clean. -/
theorem nonempty_hasDualWitness_of_twisted_separable_witnessesOf
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable)
    (hsepw : ∀ (k : ℕ) (ψ : Isogeny (E.iterateFrobeniusTwist p k).toAffine V),
      ψ.IsSeparable → Nonempty ψ.HasDualWitness)
    (φ : Isogeny E.toAffine V) : Nonempty φ.HasDualWitness := by
  obtain ⟨k, φs, hsep, hfact⟩ := twistedFrobeniusFactorization p E φ
  obtain ⟨ws⟩ := hsepw k φs hsep
  exact ⟨φ.hasDualWitness_of_twistedFactorization p E φs hfact ws
    (hasDualWitnessRelativeFrobeniusOf p E hinsep k)⟩

set_option linter.unusedDecidableInType false in
/-- The finale over a general perfect base (inherits the standing III.5.3 `sorryAx`
through the `[p]`-inseparability input; no new sorries). -/
theorem nonempty_hasDualWitness_of_twisted_separable_witnesses
    (hsepw : ∀ (k : ℕ) (ψ : Isogeny (E.iterateFrobeniusTwist p k).toAffine V),
      ψ.IsSeparable → Nonempty ψ.HasDualWitness)
    (φ : Isogeny E.toAffine V) : Nonempty φ.HasDualWitness :=
  nonempty_hasDualWitness_of_twisted_separable_witnessesOf p E
    (Isogeny.mulByInt_p_not_isSeparable p E) hsepw φ

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The finale over a finite base — axiom-clean**: every isogeny out of `E/𝔽_q` (to any
target curve) carries a dual witness, modulo only the separable side's witnesses on the
Frobenius twists. -/
theorem nonempty_hasDualWitness_of_twisted_separable_witnesses_finite [Fintype F]
    (hsepw : ∀ (k : ℕ) (ψ : Isogeny (E.iterateFrobeniusTwist p k).toAffine V),
      ψ.IsSeparable → Nonempty ψ.HasDualWitness)
    (φ : Isogeny E.toAffine V) : Nonempty φ.HasDualWitness :=
  nonempty_hasDualWitness_of_twisted_separable_witnessesOf p E
    (Isogeny.mulByInt_p_not_isSeparable_finite p E) hsepw φ

end RelativeVerschiebung

end HasseWeil.EC

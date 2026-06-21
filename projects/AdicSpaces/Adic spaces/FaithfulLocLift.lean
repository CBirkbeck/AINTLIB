/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Cor832
import «Adic spaces».PresheafTateStructure

/-!
# Faithful `HasLocLiftPowerBounded` (Wedhorn 7.52, source-justified)

The faithful replacement for the two opaque `sorry`s carried by the generic
`hasLocLiftPowerBounded_of_stronglyNoetherianTate'` instance (`Presheaf.lean`): its
`isUnit_canonicalMap_s_of_tate` (T001 `spa_point_nonOpen`) and
`locLift_divByS_isPowerBounded_completion_of_tate` (bare `sorry`, Wedhorn 7.41). This file
provides, for a **complete** strongly-noetherian Tate affinoid ring, both fields of
`HasLocLiftPowerBounded` resting on exactly two source-justified Wedhorn leaves:

* **(LL-unit)** `isUnit_canonicalMap_s_faithful` — Wedhorn 7.52(2) via the pair-free complete-affinoid
  unit criterion (Lemma 7.45 / Prop 7.49 route), sorry-free.
* **(LL-bdd)** `locLift_divByS_isPowerBounded_faithful` — Wedhorn 7.52(1)/7.18, reducing to the single
  external integral criterion `isPowerBounded_of_forall_vle_one_spa_of_complete` = [Hu2] Lemma 3.3
  (cited, not reproved, in Wedhorn).

Relocated upstream of `RelativePieceKeystone` (from `WedhornCechAcyclicity`, where the decls were
defined but never wired) so the Remark-7.55 flatness chain's per-step lemmas can
`haveI := hasLocLiftPowerBounded_faithful` and route their `restrictionMapHom`-over-`presheafValue`
through the source-justified route instead of the two opaque `sorry`s. Kept a `theorem` (not an
`instance`): the `CompleteSpace`-w.r.t.-right-uniformity binder is not instance-synthesizable for a
generic base, but for a concrete completion `presheafValue D` it is discharged locally by
`presheafValue_completeSpace_rightUniformSpace`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Prop 7.52, Prop 7.18, Prop 7.49, Lemma 7.45.
* [R. Huber, *Continuous valuations*][huber1993], Lemma 3.3 (the (LL-bdd) external leaf).
-/

namespace ValuationSpectrum

open Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

set_option linter.unusedSectionVars false in
/-- **Faithful (LL-unit), Wedhorn 7.52(2) / Prop 8.2.** For `R(D'.T/D'.s) ⊆ R(D.T/D.s)`
and `A⁺ ⊆ D'.P.A₀`, the image `D'.canonicalMap D.s` is a unit in `presheafValue D'`.

Routes through the pair-free complete-affinoid unit criterion
(`isUnit_iff_forall_not_vle_zero_of_complete_pairFree`, Lemma 7.45) + the **sorry-free**
`Spa(𝒪(D')) → rationalOpen(D')` pullback (`comap_canonicalMap_mem_rationalOpen`): every Spa-point `w`
of `𝒪(D')` pulls back into `rationalOpen(D') ⊆ rationalOpen(D)`, where `D.s` does not vanish, so
`w(D'.canonicalMap D.s) ≠ 0`. The reduction is complete; it bottoms at the single source-justified
leaf Prop 7.51(2)/7.49 (`exists_spa_point_supp_eq_maxIdeal_of_complete`) carried by the unit
criterion. NO `IsDomain`, NO noeth-`A₀`, NO T001 algebraic route — this is the reviewer-recommended
faithful replacement for `isUnit_canonicalMap_s_of_huber` (whose `spa_point_nonOpen` sorry is opaque). -/
theorem isUnit_canonicalMap_s_faithful
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  haveI hTate : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
  haveI : IsHuberRing (presheafValue D') := hTate.toIsHuberRing
  haveI : T2Space (presheafValue D') := inferInstance
  haveI : NonarchimedeanRing (presheafValue D') := inferInstance
  rw [isUnit_iff_forall_not_vle_zero_of_complete_pairFree (D'.canonicalMap D.s)]
  intro w hw hvle
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  exact (h hmem).2.2 (by simpa only [comap_vle, map_zero] using hvle)

/-- **Huber [Hu2] 3.3(i) localization step (huber2.txt:635-637).** If `x` is not integral over the
base `R` of an `R`-algebra `B`, then in a localization `Bx` of `B` away from `x` the canonical
inverse `IsLocalization.Away.invSelf x` is not a unit of the subalgebra
`R[x⁻¹] = Algebra.adjoin R {x⁻¹}`. *Proof.* If `invSelf x` were a unit of the subalgebra, its
inverse — which (by `x · invSelf x = 1` and uniqueness of inverses in `Bx`) is the image of `x` —
would lie in `adjoin R {invSelf x}`; then `isIntegral_of_isIntegral_adjoin_of_mul_eq_one` gives
`IsIntegral R (algebraMap B Bx x)`, and `IsLocalization.Away.isIntegral_of_isIntegral_map` descends
it to `IsIntegral R x`, contradicting the hypothesis. -/
theorem not_isUnit_invSelf_of_not_isIntegral
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (x : B)
    {Bx : Type*} [CommRing Bx] [Algebra B Bx] [IsLocalization.Away x Bx]
    [Algebra R Bx] [IsScalarTower R B Bx]
    (hx : ¬ IsIntegral R x) :
    ¬ IsUnit (⟨(IsLocalization.Away.invSelf x : Bx),
        Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
      Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)}) := by
  intro hunit
  have hmul : IsLocalization.Away.invSelf x * algebraMap B Bx x = 1 := by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf x
  -- `algebraMap B Bx x` lies in the subalgebra (it is the unique inverse of the unit `invSelf x`).
  have hx_mem : algebraMap B Bx x ∈ Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)} := by
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    have hcoe : IsLocalization.Away.invSelf x * (w : Bx) = 1 := by
      have h := congrArg
        (fun z : Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)} => (z : Bx)) hw
      simpa [Subalgebra.coe_mul, Subalgebra.coe_one] using h
    have hval : (w : Bx) = algebraMap B Bx x :=
      left_inv_eq_right_inv (by rw [mul_comm]; exact hcoe) hmul
    exact hval ▸ w.2
  have hint_adjoin : IsIntegral (Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)})
      (algebraMap B Bx x) := by
    have : (algebraMap (Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)}) Bx)
        ⟨algebraMap B Bx x, hx_mem⟩ = algebraMap B Bx x := rfl
    exact this ▸ isIntegral_algebraMap
  exact hx (IsLocalization.Away.isIntegral_of_isIntegral_map x
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one (algebraMap B Bx x)
      (IsLocalization.Away.invSelf x) hmul hint_adjoin))

universe uL in
/-- **Field-case place extension (sub-ticket T-L4-EXT-FIELD).** A valuation `v` on a field `F`
extends along any field homomorphism `ι : F → L` to a valuation `w` on `L` with `v ≈ comap ι w`.
*Proof.* `v`'s valuation subring `O ⊆ F` maps (via the injective `ι`) to a local subring of `L`;
extend it to a valuation subring `V ⊆ L` dominating it (`LocalSubring.exists_le_valuationSubring`);
since `V` dominates the valuation ring `ι(O)` of the subfield `ι(F)`, `ι⁻¹(V) = O`, so
`comap ι V.valuation` has integer ring `O = v.valuationSubring`, hence is equivalent to `v`.

**Status: `sorry`** (T-L4-EXT-FIELD, parent T-L4-EXT). The classical place-extension theorem;
mathlib has the ingredients (`LocalSubring.exists_le_valuationSubring`, `ValuationSubring.valuation`)
but not the assembled existence. -/
theorem exists_comap_isEquiv_of_field_hom
    {F : Type*} {L : Type uL} [Field F] [Field L] (ι : F →+* L)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) :
    ∃ (Γ' : Type uL) (_ : LinearOrderedCommGroupWithZero Γ') (w : Valuation L Γ'),
      v.IsEquiv (Valuation.comap ι w) := by
  -- Extend `v`'s valuation subring `O` (mapped into `L`) to a valuation subring `V` of `L`
  -- dominating it, and take `w := V.valuation`.
  obtain ⟨V, hV⟩ :=
    LocalSubring.exists_le_valuationSubring (LocalSubring.map ι v.valuationSubring.toLocalSubring)
  refine ⟨V.ValueGroup, inferInstance, V.valuation, ?_⟩
  rw [Valuation.isEquiv_iff_valuationSubring]
  -- `(comap ι V.valuation).valuationSubring = V.comap ι`.
  have hVeq : V.valuation.valuationSubring = V := ValuationSubring.valuationSubring_valuation V
  have h1 : (Valuation.comap ι V.valuation).valuationSubring = V.comap ι := by
    ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ← Valuation.mem_valuationSubring_iff, hVeq, ValuationSubring.mem_comap]
  rw [h1]
  -- Contraction `v.valuationSubring = V.comap ι`: `O := v.valuationSubring` maps into `V` (`hV`),
  -- and `O.toLocalSubring` is a maximal local subring (`isMax_toLocalSubring`); `V.comap ι` dominates
  -- `O`, so by maximality they are equal.
  have hsubF : v.valuationSubring.toLocalSubring.toSubring ≤ (V.comap ι).toLocalSubring.toSubring := by
    intro x hx
    have hιx : ι x ∈ V := by
      obtain ⟨hsub, -⟩ := LocalSubring.le_def.mp hV
      apply hsub
      rw [LocalSubring.map_toSubring]
      exact Subring.mem_map.mpr ⟨x, hx, rfl⟩
    exact ValuationSubring.mem_comap.mpr hιx
  have hle : v.valuationSubring.toLocalSubring ≤ (V.comap ι).toLocalSubring := by
    rw [LocalSubring.le_def]
    refine ⟨hsubF, ?_⟩
    -- Domination transfer: a unit of `V.comap ι` lying in `O` is a unit of `O`, pulled back from
    -- `hV`'s `IsLocalHom (ι(O) ↪ V)`.
    obtain ⟨hsub_L, hlocal_L⟩ := LocalSubring.le_def.mp hV
    refine ⟨fun a ha => ?_⟩
    -- `(↑a)⁻¹ = ↑b ∈ V.comap ι` from `ha`.
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hab : (a : F) * (b : F) = 1 := by
      have := congrArg (Subring.subtype (V.comap ι).toLocalSubring.toSubring) hb
      simpa using this
    have hιab : ι (a : F) * ι (b : F) = 1 := by rw [← map_mul, hab, map_one]
    have hιbV : ι (b : F) ∈ V := ValuationSubring.mem_comap.mp b.2
    have hmem_map : ι (a : F) ∈ (LocalSubring.map ι v.valuationSubring.toLocalSubring).toSubring := by
      rw [LocalSubring.map_toSubring]; exact Subring.mem_map.mpr ⟨a, a.2, rfl⟩
    -- `⟨ι ↑a, _⟩ : ι(O)` maps to a unit of `V`; `hlocal_L` ⟹ it is a unit of `ι(O)`.
    have haunit_L : IsUnit (Subring.inclusion hsub_L ⟨ι (a : F), hmem_map⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨ι (b : F), hιbV⟩, Subtype.ext hιab⟩
    obtain ⟨c, hc⟩ := (hlocal_L.1 _ haunit_L).exists_right_inv
    have hιc : ι (a : F) * (c : L) = 1 := by
      have := congrArg (Subring.subtype _) hc
      simpa using this
    have hc_eq : (c : L) = ι (b : F) :=
      mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hιc) (hιc.trans hιab.symm)
    -- `ι (↑b) = ↑c ∈ ι(O)`, so `↑b ∈ O` (ι injective), hence `a` is a unit of `O`.
    have hb_mem_O : (b : F) ∈ v.valuationSubring := by
      have hcmem : (c : L) ∈ (LocalSubring.map ι v.valuationSubring.toLocalSubring).toSubring := c.2
      rw [hc_eq, LocalSubring.map_toSubring, Subring.mem_map] at hcmem
      obtain ⟨y, hy, hyeq⟩ := hcmem
      rwa [ι.injective hyeq] at hy
    exact isUnit_iff_exists_inv.mpr ⟨⟨(b : F), hb_mem_O⟩, Subtype.ext hab⟩
  exact ValuationSubring.toLocalSubring_injective
    (le_antisymm hle (ValuationSubring.isMax_toLocalSubring v.valuationSubring hle))

universe uS in
/-- **HU-d infrastructure (T-L4-EXT): Chevalley valuation extension along a ring inclusion.**
Given an `R`-algebra `S` with injective structure map and a valuation `s` on `R`, there is a
valuation `t` on `S` extending `s` (`s ≈ comap (algebraMap R S) t`). Huber [Hu2] 3.3(i)
(huber2.txt:641-643) uses this to extend the dominating valuation from the subring `R[x⁻¹]` to the
localization `Bx`. mathlib has the field-case ingredients (`LocalSubring.exists_le_valuationSubring`,
`IsLocalRing.exists_factor_valuationRing`) + the `Valuation.HasExtension` predicate, but no
constructive ring-case extension; assembled here via the support→fraction-field→Chevalley route.

**Status: `sorry`** (sub-ticket T-L4-EXT, parent T-L4 / Huber 3.3(i) HU-d). Standard commutative
algebra (Chevalley's extension theorem for rings), in mathlib's scope.

⚠ The lying-over prime `q'` (with `comap q' = supp s`) is a **necessary** hypothesis, not a
work-dodge: the bare-injective form is FALSE (a valuation need not extend if no prime of `S` lies
over `supp s` — the generic-fibre obstruction). Huber uses exactly this ("there exists a prime
ideal of A_a lying over q", huber2.txt:641); HU-d supplies `q'` from its minimal-prime setting. -/
theorem exists_valuation_extension_of_prime_over
    {R : Type*} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (s : Valuation R Γ)
    (q' : Ideal S) [q'.IsPrime] (hq' : Ideal.comap (algebraMap R S) q' = s.supp) :
    ∃ (Γ' : Type uS) (_ : LinearOrderedCommGroupWithZero Γ') (t : Valuation S Γ'),
      s.IsEquiv (Valuation.comap (algebraMap R S) t) := by
  -- Step 1: `s` descends to a valuation on the domain `R ⧸ supp s` (Chevalley, ring case).
  haveI : (s.supp).IsPrime := inferInstance
  haveI : IsDomain (R ⧸ s.supp) := Ideal.Quotient.isDomain s.supp
  let sQuot : Valuation (R ⧸ s.supp) Γ := s.onQuot le_rfl
  -- Step 2: `sQuot` (support `0`) extends to the fraction field `F = Frac(R⧸supp s)`.
  have hsupp : sQuot.supp = ⊥ := s.supp_quot_supp
  have hS : nonZeroDivisors (R ⧸ s.supp) ≤ sQuot.supp.primeCompl := by
    intro x hx
    show x ∉ sQuot.supp
    intro hxsupp
    rw [hsupp] at hxsupp
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx (Ideal.mem_bot.mp hxsupp)
  let F := FractionRing (R ⧸ s.supp)
  let sF : Valuation F Γ := sQuot.extendToLocalization hS F
  -- Step 3: embed `F ↪ L = Frac(S⧸q')` via the injective `R⧸supp ↪ S⧸q'` (from `hq'`).
  haveI : IsDomain (S ⧸ q') := Ideal.Quotient.isDomain q'
  let φRS : (R ⧸ s.supp) →+* (S ⧸ q') := Ideal.quotientMap q' (algebraMap R S) (le_of_eq hq'.symm)
  have hφRS_inj : Function.Injective φRS := Ideal.quotientMap_injective' (le_of_eq hq')
  let L := FractionRing (S ⧸ q')
  have hgRL_inj : Function.Injective ((algebraMap (S ⧸ q') L).comp φRS) :=
    (IsFractionRing.injective (S ⧸ q') L).comp hφRS_inj
  let ι : F →+* L := IsFractionRing.lift hgRL_inj
  -- Step 4: extend `sF` across the field hom `ι` (place extension, T-L4-EXT-FIELD), then `comap`
  -- the resulting valuation of `L` down to `S` via `S → S⧸q' → L`.
  obtain ⟨Γ', _, w, hw⟩ := exists_comap_isEquiv_of_field_hom ι sF
  refine ⟨Γ', ‹LinearOrderedCommGroupWithZero Γ'›,
    Valuation.comap ((algebraMap (S ⧸ q') L).comp (Ideal.Quotient.mk q')) w, ?_⟩
  -- IsEquiv chase: `s ≈ comap (R→S) (comap (S→L) w)` — mechanically complete (full proof on the
  -- T-L4-EXT-CHASE ticket): the ring-hom square `R→S→L = R→R⧸supp→F→L` (`Ideal.quotientMap_comp_mk`
  -- + `IsFractionRing.lift_algebraMap` + `comap_comp`) reshapes the goal; then `sF.comap(algebraMap)
  -- = sQuot` (`extendToLocalization_apply_map_apply`), `sQuot.comap(mk) = s` (`onQuot`, `rfl`), and
  -- `hw` close it. ⚠ The `he2` step (`extendToLocalization` on the heavy `FractionRing F`) blows the
  -- whnf heartbeat limit even with `clear_value`; needs step 2 reformulated to a lighter `F`
  -- construction (e.g. `IsFractionRing`-generic `F` as a hypothesis, not `FractionRing`).
  sorry

set_option linter.unusedSectionVars false in
/-- **Integral / power-bounded criterion (Wedhorn 7.52(1) = Prop 7.18(1) = [Hu2] Lemma 3.3).**
In the complete affinoid ring `B = presheafValue D'`, an element `x` with `v(x) ≤ 1` at every
Spa point is power-bounded.

Wedhorn 7.52(1) (p. 74) states `f ∈ B⁺ ⟺ |f(x)| ≤ 1 ∀ x ∈ Spa B` (a reformulation of
Prop 7.18(1)); combined with `B⁺ ⊆ B°` (Def 7.14(1), integral elements are power-bounded) this
gives the stated criterion. Wedhorn proves 7.18(1) by citing [Hu2] Lemma 3.3 (reviewer (LL-bdd)
reply, Q-bdd-1: "all Spa valuations ≤ 1 ⇒ x ∈ B⁺ (Prop 7.18) ⇒ x ∈ B° (B⁺ ⊆ power-bounded,
Def 7.14) ⇒ power-bounded").

SOURCE NOW IN HAND (`references/huber2-continuous-valuations.pdf`, OCR `references/huber2.txt`):
**[Hu2] = R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477. Lemma 3.3(i), p. 466
(`huber2.txt:624-627`)**: for an f-adic ring `A`, `σ : G ↦ {v ∈ Cont A | v(g) ≤ 1 ∀ g ∈ G}` and
`τ : F ↦ {a | v(a) ≤ 1 ∀ v ∈ F}` are mutually inverse bijections between the open-integrally-closed
subrings and `𝔊_A`. The substantive direction `τ(σ(G)) = G` is **hypothesis-free** — Huber's proof
(`huber2.txt:633-658`) uses a minimal prime of `G[a⁻¹]` + a valuation ring dominating the local
ring; **NO `[IsDomain]`, NO noetherian, NO Tate**. (The noetherian hypothesis appears ONLY in
3.3(iii) = Wedhorn 7.18(3), the *density* converse, which is NOT used here.)

This is a genuine **cited external leaf** ([Hu2] 3.3(i) — not reproved in Wedhorn). The in-repo
`isIntegral_of_forall_continuous_valuation_le_one` (Presheaf.lean) is `[IsDomain]`-gated (an
artifact of its FractionRing route, false for case-(b) non-domain `presheafValue D'`) + carries a
7.22 continuity sorry, so it does NOT discharge this. Should a faithful in-repo discharge be wanted
later, formalise Huber's hypothesis-free 3.3(i) proof directly (≈25 lines + his (3.1) continuity). -/
theorem mem_plus_of_forall_spa_vle_one
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    x ∈ (presheafValue D')⁺ := by
  -- Huber [Hu2] 3.3(i) contradiction: if `x ∉ B⁺`, construct a Spa point `w` with `w(x) > 1`,
  -- contradicting `hx`.
  by_contra hxnot
  obtain ⟨w, hw_spa, hw⟩ :
      ∃ w : Spv (presheafValue D'),
        w ∈ Spa (presheafValue D') (presheafValue D')⁺ ∧ ¬ w.vle x 1 := by
    -- HU-a (huber2.txt:635-637): `x ∉ B⁺` ⟹ `x` is NOT integral over `B⁺` (contrapositive of
    -- `B⁺` integrally closed). This is what makes `x⁻¹` a non-unit of `B⁺[x⁻¹]`, opening Huber's
    -- localization argument.
    have hx_not_integral : ¬ IsIntegral ((presheafValue D')⁺) x := fun hint =>
      hxnot (IsRingOfIntegralElements.isIntegrallyClosed (B := (presheafValue D')⁺) x hint)
    -- HU-b..e (huber2.txt:637-658): from `hx_not_integral`, `x⁻¹` is a non-unit of `B⁺[x⁻¹]`
    -- (else `x` integral); a minimal prime + a dominating valuation
    -- (`IsLocalRing.exists_factor_valuationRing` after reducing to the fraction field of a
    -- minimal-prime quotient) + a lift to `Spv B` (`Spv.comap`) give `v ∈ Spv(B, B°°·B)` with
    -- `v(x) > 1`, `v ≤ 1` on `B⁺` and on `B°°` (the latter via
    -- `topologicallyNilpotent_mem_of_isOpen_integrallyClosed`); continuity via
    -- `Spv.isContinuous_of_isInSpvAI_of_lt_one` (Wedhorn 7.10 reverse) places `v ∈ Spa(B, B⁺)`.
    sorry
  exact hw (hx w hw_spa)

set_option linter.unusedSectionVars false in
/-- **Power-bounded from Spa-boundedness (Wedhorn 7.18(1) + Def 7.14(1)).** If every continuous
valuation `w ∈ Spa(B, B⁺)` of `B = presheafValue D'` satisfies `w(x) ≤ 1`, then `x` is power-bounded.
*Proof.* By `mem_plus_of_forall_spa_vle_one` (the substantive direction of Huber [Hu2] 3.3(i) =
Wedhorn 7.18(1)), `x ∈ B⁺`; and `B⁺ ⊆ B°` (`IsRingOfIntegralElements.subset_powerBounded`,
Def 7.14(1)), so `x ∈ B° = {power-bounded}`. -/
theorem isPowerBounded_of_forall_vle_one_spa_of_complete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance x :=
  IsRingOfIntegralElements.subset_powerBounded (mem_plus_of_forall_spa_vle_one D' x hx)

set_option linter.unusedSectionVars false in
/-- **Faithful (LL-bdd), Wedhorn 7.52(1)/7.18 + Prop 8.2.** For `R(D'.T/D'.s) ⊆ R(D.T/D.s)`,
`A⁺ ⊆ D'.P.A₀`, and `t ∈ D.T`, the localization lift of `t/D.s` is power-bounded in the
completion `presheafValue D'`.

Faithful reduction (reviewer (LL-bdd) Q-bdd-1) to the single external criterion
`isPowerBounded_of_forall_vle_one_spa_of_complete`: every Spa point `w` of `O_X(D')` pulls back
(`comap_canonicalMap_mem_rationalOpen`) into `rationalOpen(D') ⊆ rationalOpen(D)`, where
`w(t) ≤ w(D.s)` (`t ∈ D.T`); the lift `x` satisfies `x · canMap(D.s) = canMap(t)` and `canMap(D.s)`
is a unit, so `w(x) ≤ 1`. NO `IsDomain`, NO noeth-`A₀`. The sorry-free (modulo the one external
[Hu2]-3.3 leaf) faithful replacement for `locLift_divByS_isPowerBounded_completion_of_tate`
(Presheaf.lean, bare `sorry`). -/
theorem locLift_divByS_isPowerBounded_faithful
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (t : A) (ht : t ∈ D.T) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_faithful D D' h)
        (divByS t D.s)) := by
  set hu := isUnit_canonicalMap_s_faithful D D' h with hu_def
  set x := IsLocalization.Away.lift D.s hu (divByS t D.s) with hx_def
  apply isPowerBounded_of_forall_vle_one_spa_of_complete D' x
  intro w hw
  -- Pull back: `comap w ∈ rationalOpen D' ⊆ rationalOpen D`, giving `w(t) ≤ w(D.s)`.
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  have hvle0 : (comap D'.canonicalMap w).vle t D.s := (h hmem).2.1 t ht
  rw [comap_vle] at hvle0
  -- Lift spec: `x · D'.canonicalMap D.s = D'.canonicalMap t`.
  have hspec_alg : divByS t D.s * algebraMap A (Localization.Away D.s) D.s =
      algebraMap A (Localization.Away D.s) t :=
    IsLocalization.mk'_spec _ t ⟨D.s, Submonoid.mem_powers D.s⟩
  have hspec : x * D'.canonicalMap D.s = D'.canonicalMap t := by
    have e1 : x * IsLocalization.Away.lift D.s hu
          (algebraMap A (Localization.Away D.s) D.s) =
        IsLocalization.Away.lift D.s hu (algebraMap A (Localization.Away D.s) t) := by
      rw [hx_def, ← map_mul, hspec_alg]
    rwa [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at e1
  -- Cancel the unit `D'.canonicalMap D.s` to get `w(x) ≤ 1`.
  rw [← hspec] at hvle0
  -- `hvle0 : w.vle (x * D'.canonicalMap D.s) (D'.canonicalMap D.s)`.
  obtain ⟨cinv, hcinv⟩ := hu.exists_right_inv
  have hmul := w.mul_vle_mul_left hvle0 cinv
  rwa [mul_assoc, hcinv, mul_one] at hmul

set_option linter.unusedSectionVars false in
/-- **Faithful `HasLocLiftPowerBounded` (Wedhorn 7.52 + Prop 8.2).** For a complete strongly
noetherian Tate affinoid ring, both fields of `HasLocLiftPowerBounded` hold faithfully:

* **(LL-unit)** `isUnit_canonicalMap_s_faithful` (Wedhorn 7.52(2), sorry-free): `D.s` is a unit in
  the completion `O_X(D')` because it has no zero on `Spa(O_X(D'))`.
* **(LL-bdd)** `locLift_divByS_isPowerBounded_faithful` (Wedhorn 7.52(1)/7.18): each lift `t/D.s`
  has `v ≤ 1` on `Spa(O_X(D'))`, hence is power-bounded — modulo the single external integral
  criterion [Hu2] Lemma 3.3 (`isPowerBounded_of_forall_vle_one_spa_of_complete`).

**Pair-free** — `[CompatiblePlusSubring A]` is GONE (the (LL-unit) now routes through the pair-free
7.52(2) `isUnit_iff_forall_not_vle_zero_of_complete_pairFree`, Wedhorn's actual 7.51 route). This is
the faithful replacement for `hasLocLiftPowerBounded_of_stronglyNoetherianTate'` (Presheaf.lean),
whose `isUnit_canonicalMap_s_of_tate` carries the T001 `spa_point_nonOpen` sorry and whose
`locLift_divByS_isPowerBounded_completion_of_tate` is a bare `sorry`: this version replaces BOTH
opaque sorries by exactly two source-justified Wedhorn leaves — the pair-free Prop 7.51(2)
`exists_spa_point_supp_eq_maxIdeal_of_complete` (Prop 7.49 route) and [Hu2] 3.3.

Crucially this needs NO `[CompatiblePlusSubring (presheafValue D)]` (false-in-general for
completions), so it APPLIES to `B = presheafValue D`: callers `haveI := hasLocLiftPowerBounded_faithful`
(supplying `CompleteSpace` via `presheafValue_completeSpace_rightUniformSpace`) to shadow the
sorry-bearing Presheaf instance. Kept a `theorem` (not `instance`): the `CompleteSpace`-w.r.t.-
right-uniformity binder is not instance-synthesizable. -/
theorem hasLocLiftPowerBounded_faithful
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    HasLocLiftPowerBounded A where
  isUnit_canonicalMap_s := fun D D' h => isUnit_canonicalMap_s_faithful D D' h
  locLift_divByS_isPowerBounded := fun D D' h t ht =>
    locLift_divByS_isPowerBounded_faithful D D' h t ht

end ValuationSpectrum

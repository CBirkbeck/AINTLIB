/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.WeierstrassInvariant
import ModularCurves.ForMathlib.InvariantLocalization

/-!
# a5-P-loc: localized descent + spread of the invariant Weierstrass model

Given a finite group `G` acting freely on a commutative ring `R`, a Weierstrass curve
`W₀ : WeierstrassCurve R` with a `VariableChange`-cocycle action `C`, and a prime `p` of the
fixed subring `Rᴳ`, we produce an invariant `a ∉ p` and a Weierstrass curve `W₁` over
`(Rᴳ)_a = Localization.Away a` that base-changes to `E⁻¹ • W₀` over `R_a`, together with the
coboundary identity `C g = E * (g • E)⁻¹` over `R_a`.

Strategy:
1. Localize `R` at the invariant submonoid `S = image of (Rᴳ \ p)`; the `G`-action extends
   (`MulSemiringAction.localizationInvariant`), the fixed points of `Localization S` are the
   localization `(Rᴳ)_p` (`exists_fixed_smul_mk'_eq`), which is local, and freeness localizes.
2. Apply the coboundary theorem `exists_coboundary` over `Localization S`.
3. Spread: all the finitely many numerators/denominators involved live over a single basic
   localization `Away a`, `a ∉ p`, and the equations descend by `IsLocalization` uniqueness.
-/


/-!
# Localized descent and spread of the invariant Weierstrass model ([a5-P-loc])

The bridge from the H¹-vanishing descent (`exists_invariant_descent`, which needs a LOCAL fixed
ring) to the Zariski-local statement the engine needs: at every prime `p` of the fixed subring
`Rᴳ` there is an invariant basic open `D(a) ∋ p` over which the model descends.

Route: localize `R` at the invariant multiplicative set `S = (Rᴳ \ p)·R`
(`MulSemiringAction.localizationInvariant` — the generalization of `MulSemiringAction.away`);
fixed points commute with the localization (`exists_fixed_smul_mk'_eq` and
`isLocalRing_fixedPoints_of_isLocalization`, so `(Localization S)ᴳ` is local); freeness localizes
(`isFreeAlgebraAction_of_isLocalization`); base-change the cocycle; run `exists_coboundary` +
`descendFixed` over the localization; then SPREAD: the finitely many coefficients of the model,
the variable change `E`, and the coboundary identities all have finitely many denominators —
clear them into a single invariant `a ∉ p` (`exists_away_invariant_descent`).

The output exposes the **coboundary identity** `C g = E · (g•E)⁻¹` over `R_a` — required by the
`G`-invariance of the `[a5]` fppf-comparison (not derivable downstream: Weierstrass curves have
nontrivial `VariableChange` stabilizers).
-/
open WeierstrassCurve

open scoped Pointwise

universe u v

namespace ModularCurves

/-! ## Generic helpers -/

section Helpers

variable {A : Type v} [CommRing A]

/-- If `x ∣ y`, then `x` becomes a unit in `Localization.Away y`. -/
theorem isUnit_algebraMap_away {x y : A} (h : x ∣ y) :
    IsUnit (algebraMap A (Localization.Away y) x) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.map_units _ ⟨y, Submonoid.mem_powers y⟩)

/-- Mapping a fraction `x * d⁻¹` into a localization in which `x ↦ algebraMap b` and
`d ↦ algebraMap s` yields the fraction `mk' b s`. -/
theorem map_mul_isUnit_inv_eq_mk' {L T : Type*} [CommRing L] [CommRing T]
    {M : Submonoid A} [Algebra A L] [IsLocalization M L]
    (f : T →+* L) {x d : T} (hd : IsUnit d) {b : A} {s : M}
    (hx : f x = algebraMap A L b) (hds : f d = algebraMap A L (s : A)) :
    f (x * (↑hd.unit⁻¹ : T)) = IsLocalization.mk' L b s := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hds, map_mul, mul_assoc, ← map_mul,
    hd.val_inv_mul, map_one, mul_one, hx]

/-- Cancellation transported along a divisor: if `a ∣ b` and `a * x = a * y`, then also
`b * x = b * y`. (No cancellativity is needed — multiply the hypothesis through by the cofactor.) -/
theorem mul_right_cancel_of_dvd {M : Type*} [CommMonoid M] {a b x y : M}
    (hab : a ∣ b) (h : a * x = a * y) : b * x = b * y := by
  obtain ⟨e, rfl⟩ := hab
  rw [mul_right_comm, h, mul_right_comm]

end Helpers

/-! ## The `G`-action on the localization at a pointwise-invariant submonoid

This generalizes AINTLIB's `MulSemiringAction.away` (localization away from a single invariant
element) to an arbitrary submonoid `S` all of whose elements are fixed by the action. -/

section LocalizationAction

variable {G : Type*} [Group G] {R : Type u} [CommRing R] [MulSemiringAction G R]
variable {S : Submonoid R}

namespace MulSemiringAction

theorem le_comap_toRingHom_of_forall_smul_eq (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (g : G) :
    S ≤ S.comap (MulSemiringAction.toRingHom G R g) := fun s hs =>
  Submonoid.mem_comap.mpr (by
    show g • s ∈ S
    rw [hS g s hs]; exact hs)

/-- The ring endomorphism of `Localization S` induced by `g • ·`, for a pointwise-fixed
submonoid `S`. -/
noncomputable def locHom (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (g : G) :
    Localization S →+* Localization S :=
  IsLocalization.map (Localization S) (MulSemiringAction.toRingHom G R g)
    (le_comap_toRingHom_of_forall_smul_eq hS g)

theorem locHom_algebraMap (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (g : G) (b : R) :
    locHom hS g (algebraMap R (Localization S) b) = algebraMap R (Localization S) (g • b) :=
  IsLocalization.map_eq _ b

theorem locHom_one (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (x : Localization S) :
    locHom hS (1 : G) x = x := by
  have h : locHom hS (1 : G) = RingHom.id (Localization S) := by
    apply IsLocalization.ringHom_ext S
    ext b
    simp [locHom_algebraMap]
  rw [h, RingHom.id_apply]

theorem locHom_mul (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (g g' : G) (x : Localization S) :
    locHom hS (g * g') x = locHom hS g (locHom hS g' x) := by
  have h : locHom hS (g * g') = (locHom hS g).comp (locHom hS g') := by
    apply IsLocalization.ringHom_ext S
    ext b
    simp [locHom_algebraMap, mul_smul]
  rw [h, RingHom.comp_apply]

/-- The action of `G` on `Localization S` for a pointwise-fixed submonoid `S`. Not an
instance (it depends on the hypothesis `hS`); bring it into scope with `letI`. -/
@[implicit_reducible]
noncomputable def localizationInvariant (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) :
    MulSemiringAction G (Localization S) where
  smul g x := locHom hS g x
  one_smul := locHom_one hS
  mul_smul := locHom_mul hS
  smul_zero g := map_zero (locHom hS g)
  smul_add g := map_add (locHom hS g)
  smul_one g := map_one (locHom hS g)
  smul_mul g := map_mul (locHom hS g)

end MulSemiringAction

end LocalizationAction

/-! ## Abstract compatible actions on a localization

We work with an abstract `L` with `[IsLocalization S L]` carrying a `MulSemiringAction G L`
that is compatible with the action on `R` along `algebraMap R L`.  All lemmas below are then
applicable to `Localization S` with the action `MulSemiringAction.localizationInvariant`. -/

section CompatibleAction

variable {G : Type*} [Group G] {R : Type u} [CommRing R] [MulSemiringAction G R]
variable {S : Submonoid R} {L : Type u} [CommRing L] [Algebra R L] [IsLocalization S L]
variable [MulSemiringAction G L]

theorem smul_mk'_of_compatible
    (hcomp : ∀ (g : G) (r : R), g • (algebraMap R L r) = algebraMap R L (g • r))
    (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (g : G) (b : R) (s : S) :
    g • (IsLocalization.mk' L b s) = IsLocalization.mk' L (g • b) s := by
  have h1 : (g • IsLocalization.mk' L b s) * (g • algebraMap R L ((s : R)))
      = g • algebraMap R L b := by
    rw [← smul_mul', IsLocalization.mk'_spec]
  rw [hcomp g, hcomp g, hS g _ s.2] at h1
  exact IsLocalization.eq_mk'_iff_mul_eq.mpr h1

/-- **Fixed points of an invariant localization are fractions with invariant numerator**:
for a finite group, every fixed element of `L` is `mk' b s` with `b` invariant and `s ∈ S`.
No averaging over `G`: the numerator is corrected by an element of `S` instead, so there is
no invertibility hypothesis on `|G|`. -/
theorem exists_fixed_smul_mk'_eq [Finite G]
    (hcomp : ∀ (g : G) (r : R), g • (algebraMap R L r) = algebraMap R L (g • r))
    (hS : ∀ (g : G), ∀ s ∈ S, g • s = s) (x : L) (hx : ∀ g : G, g • x = x) :
    ∃ (b : R) (s : S), (∀ g : G, g • b = b) ∧ IsLocalization.mk' L b s = x := by
  classical
  cases nonempty_fintype G
  obtain ⟨b₀, s₀, rfl⟩ := IsLocalization.exists_mk'_eq S x
  have key : ∀ g : G, ∃ c : S, (c : R) * ((s₀ : R) * (g • b₀)) = (c : R) * ((s₀ : R) * b₀) := by
    intro g
    have hg : IsLocalization.mk' L (g • b₀) s₀ = IsLocalization.mk' L b₀ s₀ := by
      rw [← smul_mk'_of_compatible hcomp hS g b₀ s₀]
      exact hx g
    rw [IsLocalization.mk'_eq_iff_eq] at hg
    exact (IsLocalization.eq_iff_exists S L).mp hg
  choose c hc using key
  set d : R := ∏ g : G, (c g : R) with hd
  have hdS : d ∈ S := Submonoid.prod_mem S fun g _ => (c g).2
  have hdfix : ∀ g : G, g • d = d := by
    intro g
    show MulSemiringAction.toRingHom G R g d = d
    rw [hd, map_prod]
    exact Finset.prod_congr rfl fun h _ => hS g _ (c h).2
  refine ⟨b₀ * ((s₀ : R) * d), s₀ * (⟨(s₀ : R) * d, Submonoid.mul_mem S s₀.2 hdS⟩ : S),
    fun g => ?_, ?_⟩
  · have hsplit : d = (c g : R) * ∏ h ∈ Finset.univ.erase g, (c h : R) := by
      rw [hd]
      exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ g)).symm
    rw [smul_mul', smul_mul', hS g _ s₀.2, hdfix g]
    calc (g • b₀) * ((s₀ : R) * d)
        = (∏ h ∈ Finset.univ.erase g, (c h : R)) * ((c g : R) * ((s₀ : R) * (g • b₀))) := by
          rw [hsplit]; ring
      _ = (∏ h ∈ Finset.univ.erase g, (c h : R)) * ((c g : R) * ((s₀ : R) * b₀)) := by
          rw [hc g]
      _ = b₀ * ((s₀ : R) * d) := by rw [hsplit]; ring
  · exact IsLocalization.mk'_cancel (S := L) b₀ s₀
      ⟨(s₀ : R) * d, Submonoid.mul_mem S s₀.2 hdS⟩

/-- Freeness of the action localizes: if `G` acts freely on `R` (in the Katz–Mazur sense),
it acts freely on any compatible localization `L` of `R`. -/
theorem isFreeAlgebraAction_of_isLocalization
    (hcomp : ∀ (g : G) (r : R), g • (algebraMap R L r) = algebraMap R L (g • r))
    (hfree : IsFreeAlgebraAction G ℤ R) : IsFreeAlgebraAction G ℤ L := by
  refine fun g hg R' _ _ _ φ => ?_
  have ψcommutes : ∀ n : ℤ, ((φ : L →+* R').comp (algebraMap R L)) (algebraMap ℤ R n)
      = algebraMap ℤ R' n := fun n => by
    rw [eq_intCast (algebraMap ℤ R) n, eq_intCast (algebraMap ℤ R') n]
    exact map_intCast _ n
  obtain ⟨a, ha⟩ := hfree g hg R' ⟨(φ : L →+* R').comp (algebraMap R L), ψcommutes⟩
  refine ⟨algebraMap R L a, fun h => ha ?_⟩
  rw [hcomp g a] at h
  exact h

end CompatibleAction

/-! ## The invariant submonoid attached to a prime of the fixed subring

For a prime `p` of `Rᴳ = FixedPoints.subring R G`, the image `S` of `p.primeCompl` in `R` is a
pointwise-fixed submonoid; `Localization S` is nontrivial, carries the localized `G`-action,
and its fixed subalgebra is (the isomorphic image of) `Localization.AtPrime p` — in particular
a local ring. -/

section PrimeSetup

variable {G : Type*} [Group G] {R : Type u} [CommRing R] [MulSemiringAction G R]

/-- Elements of the image of `p.primeCompl` in `R` are pointwise fixed. -/
theorem primeComplImage_fixed (p : Ideal (FixedPoints.subring R G)) [p.IsPrime] :
    ∀ (g : G), ∀ s ∈ p.primeCompl.map (algebraMap (FixedPoints.subring R G) R), g • s = s := by
  rintro g s hs
  obtain ⟨k, -, rfl⟩ := Submonoid.mem_map.mp hs
  exact k.2 g

theorem nontrivial_localization_primeComplImage (p : Ideal (FixedPoints.subring R G))
    [p.IsPrime] :
    Nontrivial (Localization (p.primeCompl.map (algebraMap (FixedPoints.subring R G) R))) := by
  set S := p.primeCompl.map (algebraMap (FixedPoints.subring R G) R) with hSdef
  have h0 : (0 : R) ∉ S := by
    intro h0
    obtain ⟨k, hk, hk0⟩ := Submonoid.mem_map.mp h0
    refine hk ?_
    have hk' : k = 0 := Subtype.ext hk0
    rw [hk']
    exact p.zero_mem
  refine nontrivial_of_ne 1 0 fun h => h0 ?_
  have h1 : algebraMap R (Localization S) 1 = algebraMap R (Localization S) 0 := by
    rw [map_one, map_zero]; exact h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S _).mp h1
  have hc0 : (c : R) = 0 := by rwa [mul_one, mul_zero] at hc
  rw [← hc0]
  exact c.2

/-- The fixed subalgebra of a compatible localization at (the image of) `p.primeCompl` is a
**local ring**: it is the surjective image of `Localization.AtPrime p` under the localized
inclusion of the fixed subring. -/
theorem isLocalRing_fixedPoints_of_isLocalization [Finite G]
    (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
    {L : Type u} [CommRing L] [Algebra R L]
    [IsLocalization (p.primeCompl.map (algebraMap (FixedPoints.subring R G) R)) L]
    [MulSemiringAction G L] [Nontrivial L]
    (hcomp : ∀ (g : G) (r : R), g • (algebraMap R L r) = algebraMap R L (g • r)) :
    IsLocalRing (FixedPoints.subalgebra ℤ L G) := by
  classical
  set S := p.primeCompl.map (algebraMap (FixedPoints.subring R G) R) with hSdef
  have hS : ∀ (g : G), ∀ s ∈ S, g • s = s := primeComplImage_fixed p
  have hle : p.primeCompl ≤ S.comap (algebraMap (FixedPoints.subring R G) R) :=
    fun k hk => Submonoid.mem_comap.mpr (Submonoid.mem_map_of_mem _ hk)
  set θ : Localization.AtPrime p →+* L :=
    IsLocalization.map L (algebraMap (FixedPoints.subring R G) R) hle with hθdef
  have hmk'_congr : ∀ (b₁ b₂ : R) (s₁ s₂ : S), b₁ = b₂ → (s₁ : R) = (s₂ : R) →
      IsLocalization.mk' L b₁ s₁ = IsLocalization.mk' L b₂ s₂ := by
    rintro b₁ b₂ s₁ s₂ rfl hs
    exact congrArg _ (Subtype.ext hs)
  have hrange : ∀ z : Localization.AtPrime p, θ z ∈ FixedPoints.subalgebra ℤ L G := by
    intro z
    show ∀ g : G, g • θ z = θ z
    intro g
    obtain ⟨β, σ, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    rw [hθdef, IsLocalization.map_mk', smul_mk'_of_compatible hcomp hS]
    exact hmk'_congr _ _ _ _ (β.2 g) rfl
  have hsurj : Function.Surjective
      (θ.codRestrict (FixedPoints.subalgebra ℤ L G) hrange) := by
    rintro ⟨x, hx⟩
    obtain ⟨b, s, hb, hmk⟩ := exists_fixed_smul_mk'_eq hcomp hS x (fun g => hx g)
    obtain ⟨σ, hσ, hσeq⟩ := Submonoid.mem_map.mp s.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) (⟨b, hb⟩ : FixedPoints.subring R G)
      (⟨σ, hσ⟩ : p.primeCompl), ?_⟩
    apply Subtype.ext
    show θ (IsLocalization.mk' (Localization.AtPrime p) _ _) = x
    rw [hθdef, IsLocalization.map_mk']
    exact (hmk'_congr _ _ _ _ rfl hσeq).trans hmk
  haveI : Nontrivial (FixedPoints.subalgebra ℤ L G) :=
    ⟨0, 1, fun h => zero_ne_one (α := L) (congrArg Subtype.val h)⟩
  exact IsLocalRing.of_surjective' _ hsurj

end PrimeSetup

/-! ## Base change of cocycle data along a compatible ring map

The cocycle datum `(C, W₀)` on `R` transports along any `G`-equivariant ring map `f : R →+* L`
(one with `g • f r = f (g • r)`): the mapped family `g ↦ (C g).map f` is again a cocycle, and the
action-compatibility of `C` is preserved.  Applied to `f = algebraMap R (Localization S)` this
base-changes the whole descent problem to the invariant localization. -/

section BaseChange

/-- Base change of a `VariableChange` cocycle along a `G`-equivariant ring map: if `C` is a cocycle
on `R` and `f : R →+* L` intertwines the actions, then `g ↦ (C g).map f` is a cocycle on `L`. -/
theorem isVCocycle_map {G : Type*} [Group G] {R : Type*} [CommRing R] [MulSemiringAction G R]
    {L : Type*} [CommRing L] [MulSemiringAction G L] (f : R →+* L)
    (hf : ∀ (g : G) (r : R), g • f r = f (g • r)) {C : G → VariableChange R} (hC : IsVCocycle C) :
    IsVCocycle (fun g => (C g).map f) := by
  have hequiv : ∀ g : G, (MulSemiringAction.toRingHom G L g).comp f
      = f.comp (MulSemiringAction.toRingHom G R g) := fun g => RingHom.ext fun r => hf g r
  intro g h
  show (C (g * h)).map f = (C g).map f * g • ((C h).map f)
  rw [vcSMul_smul_def, vcSMul_eq_map, VariableChange.map_map, hequiv g,
    ← VariableChange.map_map, hC g h, ← vcSMul_eq_map, ← vcSMul_smul_def]
  exact map_mul (VariableChange.mapHom _) _ _

/-- Base change of the action-compatibility `C g • (g • W₀) = W₀` along a `G`-equivariant ring map
`f`: the mapped curve `W₀.map f` is carried back to itself by `(C g).map f` after the `g`-twist. -/
theorem map_variableChange_action {G : Type*} [Group G] {R : Type*} [CommRing R]
    [MulSemiringAction G R] {L : Type*} [CommRing L] [MulSemiringAction G L] (f : R →+* L)
    (hf : ∀ (g : G) (r : R), g • f r = f (g • r)) {W₀ : WeierstrassCurve R}
    {C : G → VariableChange R}
    (haction : ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀) (g : G) :
    ((C g).map f) • ((W₀.map f).map (MulSemiringAction.toRingHom G L g)) = W₀.map f := by
  have hequiv : (MulSemiringAction.toRingHom G L g).comp f
      = f.comp (MulSemiringAction.toRingHom G R g) := RingHom.ext fun r => hf g r
  rw [WeierstrassCurve.map_map, hequiv, ← WeierstrassCurve.map_map,
    WeierstrassCurve.map_variableChange, haction g]

/-- If a constant change of variables `D` turns the twisted cocycle into a coboundary
(`D * C g = g • D`) and `C` carries `g • W` back to `W`, then `D • W` is `G`-invariant:
`(D • W).map g = D • W` for every `g`. -/
theorem map_smul_variableChange_eq_of_coboundary {G : Type*} [Group G] {L : Type*} [CommRing L]
    [MulSemiringAction G L] {W : WeierstrassCurve L} {D : VariableChange L}
    {C : G → VariableChange L}
    (haction : ∀ g, C g • (W.map (MulSemiringAction.toRingHom G L g)) = W)
    (hcob : ∀ g, D * C g = g • D) (g : G) :
    (D • W).map (MulSemiringAction.toRingHom G L g) = D • W := by
  rw [← WeierstrassCurve.map_variableChange, ← vcSMul_eq_map, ← vcSMul_smul_def,
    ← hcob g, mul_smul, haction g]

end BaseChange

/-! ## Clearing denominators in an equality of variable changes -/

section Clearing

/-- Clear denominators in an equality of variable changes.  Given a ring map `φ` for which any
equality `φ x = φ y` can be cleared against a submonoid `S` by a common multiplier `c : S`
(`hclear`), an equality `A.map φ = B.map φ` of variable changes is cleared by a **single** `c : S`
simultaneously in all four coordinates `(u, r, s, t)`. -/
theorem exists_common_clear_variableChange {R T U : Type*} [CommRing R] [CommRing T] [CommRing U]
    {S : Submonoid R} (alg : R →+* T) (φ : T →+* U)
    (hclear : ∀ x y : T, φ x = φ y → ∃ c : S, alg (c : R) * x = alg (c : R) * y)
    {A B : VariableChange T} (h : A.map φ = B.map φ) :
    ∃ c : S, (alg (c : R) * (A.u : T) = alg (c : R) * (B.u : T)) ∧
      (alg (c : R) * A.r = alg (c : R) * B.r) ∧
      (alg (c : R) * A.s = alg (c : R) * B.s) ∧
      (alg (c : R) * A.t = alg (c : R) * B.t) := by
  have hu : φ (A.u : T) = φ (B.u : T) := by
    have := congrArg (fun z : VariableChange U => (z.u : U)) h
    simpa using this
  have hr : φ A.r = φ B.r := by have := congrArg VariableChange.r h; simpa using this
  have hs : φ A.s = φ B.s := by have := congrArg VariableChange.s h; simpa using this
  have ht : φ A.t = φ B.t := by have := congrArg VariableChange.t h; simpa using this
  obtain ⟨cu, hcu⟩ := hclear _ _ hu
  obtain ⟨cr, hcr⟩ := hclear _ _ hr
  obtain ⟨cs, hcs⟩ := hclear _ _ hs
  obtain ⟨ct, hct⟩ := hclear _ _ ht
  refine ⟨((cu * cr) * cs) * ct, ?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel_of_dvd (map_dvd _ (map_dvd (Submonoid.subtype S)
      (((dvd_mul_right cu cr).mul_right cs).mul_right ct))) hcu
  · exact mul_right_cancel_of_dvd (map_dvd _ (map_dvd (Submonoid.subtype S)
      (((dvd_mul_left cr cu).mul_right cs).mul_right ct))) hcr
  · exact mul_right_cancel_of_dvd (map_dvd _ (map_dvd (Submonoid.subtype S)
      ((dvd_mul_left cs (cu * cr)).mul_right ct))) hcs
  · exact mul_right_cancel_of_dvd (map_dvd _ (map_dvd (Submonoid.subtype S)
      (dvd_mul_left ct ((cu * cr) * cs)))) hct

end Clearing

/-! ## The main theorem: localized descent + spread -/

section Main

variable {G : Type*} [Group G] {R : Type u} [CommRing R] [MulSemiringAction G R]

/-- Bridge: under the localized action `MulSemiringAction.away hfix` on
`Localization.Away h`, the ring-hom form `E.map (awayHom hfix g)` appearing in
`exists_away_invariant_descent` is literally the action `g • E` on variable changes. -/
theorem variableChange_map_awayHom {B : Type v} [CommRing B] [MulSemiringAction G B]
    {h : B} (hfix : ∀ g : G, g • h = h) (g : G)
    (E : VariableChange (Localization.Away h)) :
    letI := MulSemiringAction.away hfix
    E.map (MulSemiringAction.awayHom hfix g) = g • E := by
  letI := MulSemiringAction.away hfix
  show E.map (MulSemiringAction.awayHom hfix g) = vcSMul g E
  exact (vcSMul_eq_map g E).symm

theorem powers_le_comap_fixedAway (a : FixedPoints.subring R G) :
    Submonoid.powers a ≤ (Submonoid.powers ((a : R))).comap
      (algebraMap (FixedPoints.subring R G) R) := by
  rintro x ⟨n, rfl⟩
  refine Submonoid.mem_comap.mpr ⟨n, ?_⟩
  show ((a : R)) ^ n = algebraMap (FixedPoints.subring R G) R (a ^ n)
  exact (map_pow (algebraMap (FixedPoints.subring R G) R) a n).symm

/-- The canonical map `(Rᴳ)_a → R_a` between basic localizations, for `a` in the fixed
subring. -/
noncomputable def fixedAwayMap (a : FixedPoints.subring R G) :
    Localization.Away a →+* Localization.Away ((a : R)) :=
  IsLocalization.map (Localization.Away ((a : R))) (algebraMap (FixedPoints.subring R G) R)
    (powers_le_comap_fixedAway a)

theorem fixedAwayMap_algebraMap (a : FixedPoints.subring R G) (v : FixedPoints.subring R G) :
    fixedAwayMap a (algebraMap _ (Localization.Away a) v)
      = algebraMap R (Localization.Away ((a : R))) ((v : R)) :=
  IsLocalization.map_eq (powers_le_comap_fixedAway a) v

/-- **Localized descent and spread of a `G`-invariant Weierstrass model** (a5-P-loc).

Let a finite group `G` act freely on `R`, let `W₀` be a Weierstrass curve over `R` carrying a
`VariableChange`-cocycle action (`C` a cocycle with `C g • (g • W₀) = W₀`), and let `p` be a
prime of the fixed subring `Rᴳ`.  Then there is an invariant `a ∉ p`, a Weierstrass curve
`W₁` over `(Rᴳ)_a` and a variable change `E` over `R_a` such that `W₁` base-changes to
`E⁻¹ • W₀` over `R_a` **and** the localized cocycle is the coboundary of `E`:
`C g = E * (g • E)⁻¹` over `R_a` (with `g • E = E.map (awayHom … g)` the localized action). -/
theorem exists_away_invariant_descent [Fintype G] [DecidableEq G]
    (hfree : IsFreeAlgebraAction G ℤ R) (W₀ : WeierstrassCurve R)
    {C : G → VariableChange R} (hC : IsVCocycle C)
    (haction : ∀ g : G, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀)
    (p : Ideal (FixedPoints.subring R G)) [p.IsPrime] :
    ∃ (a : FixedPoints.subring R G) (_ : a ∉ p)
      (W₁ : WeierstrassCurve (Localization.Away a))
      (E : VariableChange (Localization.Away ((a : R)))),
      W₁.map (fixedAwayMap a)
          = E⁻¹ • (W₀.map (algebraMap R (Localization.Away ((a : R))))) ∧
        ∀ g : G, (C g).map (algebraMap R (Localization.Away ((a : R))))
          = E * (E.map (MulSemiringAction.awayHom (fun g' => a.2 g') g))⁻¹ := by
  classical
  -- ### Part 1: the invariant multiplicative set and the localized action
  set S : Submonoid R := p.primeCompl.map (algebraMap (FixedPoints.subring R G) R) with hSdef
  have hS : ∀ (g : G), ∀ s ∈ S, g • s = s := primeComplImage_fixed p
  letI : MulSemiringAction G (Localization S) := MulSemiringAction.localizationInvariant hS
  have hcomp : ∀ (g : G) (r : R),
      g • (algebraMap R (Localization S) r) = algebraMap R (Localization S) (g • r) :=
    fun g r => MulSemiringAction.locHom_algebraMap hS g r
  haveI : Nontrivial (Localization S) := nontrivial_localization_primeComplImage p
  haveI := isLocalRing_fixedPoints_of_isLocalization p hcomp
  have hfreeL := isFreeAlgebraAction_of_isLocalization hcomp hfree
  -- ### base change of the cocycle data to `Localization S`
  set C' : G → VariableChange (Localization S) :=
    fun g => (C g).map (algebraMap R (Localization S)) with hC'def
  have hC' : IsVCocycle C' := by
    rw [hC'def]; exact isVCocycle_map (algebraMap R (Localization S)) hcomp hC
  have haction' : ∀ g : G,
      C' g • ((W₀.map (algebraMap R (Localization S))).map
          (MulSemiringAction.toRingHom G (Localization S) g))
        = W₀.map (algebraMap R (Localization S)) := by
    intro g
    rw [hC'def]
    exact map_variableChange_action (algebraMap R (Localization S)) hcomp haction g
  -- ### the coboundary over `Localization S`
  obtain ⟨E', hE'⟩ := exists_coboundary hfreeL hC'
  set D' : VariableChange (Localization S) := E'⁻¹ with hD'def
  have hDcob : ∀ g : G, D' * C' g = g • D' := by
    intro g
    rw [hD'def, hE' g, smul_inv', inv_mul_cancel_left]
  have hinv : ∀ g : G,
      (D' • (W₀.map (algebraMap R (Localization S)))).map
          (MulSemiringAction.toRingHom G (Localization S) g)
        = D' • (W₀.map (algebraMap R (Localization S))) :=
    map_smul_variableChange_eq_of_coboundary haction' hDcob
  -- ### fraction forms of all the data over `Localization S`
  have hcoef : ∀ x : Localization S, (∀ g : G, g • x = x) →
      ∃ (b : R) (s : S), (∀ g : G, g • b = b) ∧ IsLocalization.mk' (Localization S) b s = x :=
    fun x hx => exists_fixed_smul_mk'_eq hcomp hS x hx
  obtain ⟨b₁, s₁, hb₁, hmk₁⟩ := hcoef ((D' • (W₀.map (algebraMap R (Localization S)))).a₁)
    (fun g => congrArg WeierstrassCurve.a₁ (hinv g))
  obtain ⟨b₂, s₂, hb₂, hmk₂⟩ := hcoef ((D' • (W₀.map (algebraMap R (Localization S)))).a₂)
    (fun g => congrArg WeierstrassCurve.a₂ (hinv g))
  obtain ⟨b₃, s₃, hb₃, hmk₃⟩ := hcoef ((D' • (W₀.map (algebraMap R (Localization S)))).a₃)
    (fun g => congrArg WeierstrassCurve.a₃ (hinv g))
  obtain ⟨b₄, s₄, hb₄, hmk₄⟩ := hcoef ((D' • (W₀.map (algebraMap R (Localization S)))).a₄)
    (fun g => congrArg WeierstrassCurve.a₄ (hinv g))
  obtain ⟨b₆, s₆, hb₆, hmk₆⟩ := hcoef ((D' • (W₀.map (algebraMap R (Localization S)))).a₆)
    (fun g => congrArg WeierstrassCurve.a₆ (hinv g))
  obtain ⟨pu, du, hpu⟩ := IsLocalization.exists_mk'_eq S ((D'.u : Localization S))
  obtain ⟨pv, dv, hpv⟩ := IsLocalization.exists_mk'_eq S ((↑(D'.u⁻¹) : Localization S))
  obtain ⟨pr, dr, hpr⟩ := IsLocalization.exists_mk'_eq S D'.r
  obtain ⟨ps, ds, hps⟩ := IsLocalization.exists_mk'_eq S D'.s
  obtain ⟨pt, dt, hpt⟩ := IsLocalization.exists_mk'_eq S D'.t
  -- the unit relation, cleared of denominators
  have hunit_rel : ∃ c : S, (c : R) * (pu * pv) = (c : R) * ((du : R) * (dv : R)) := by
    have huv1 : IsLocalization.mk' (Localization S) (pu * pv) (du * dv) = 1 := by
      rw [IsLocalization.mk'_mul, hpu, hpv]
      exact D'.u.mul_inv
    have h3 := IsLocalization.mk'_spec (Localization S) (pu * pv) (du * dv)
    rw [huv1, one_mul] at h3
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S _).mp h3.symm
    exact ⟨c, hc⟩
  obtain ⟨cuv, hcuv⟩ := hunit_rel
  -- ### preimages in the fixed subring
  have hpre' : ∀ s : S, ∃ k : FixedPoints.subring R G,
      k ∉ p ∧ algebraMap (FixedPoints.subring R G) R k = (s : R) := by
    intro s
    obtain ⟨k, hk, hke⟩ := Submonoid.mem_map.mp s.2
    exact ⟨k, hk, hke⟩
  choose pre hpre_mem hpre_eq using hpre'
  -- ### Part 2 (spread): the preliminary invariant element `a₀`
  have hmulmem : ∀ {x y : FixedPoints.subring R G}, x ∉ p → y ∉ p → x * y ∉ p :=
    fun hx hy => p.primeCompl.mul_mem hx hy
  set a₀ : FixedPoints.subring R G :=
    pre s₁ * (pre s₂ * (pre s₃ * (pre s₄ * (pre s₆ *
      (pre du * (pre dv * (pre dr * (pre ds * (pre dt * pre cuv))))))))) with ha₀def
  have ha₀ : a₀ ∉ p :=
    hmulmem (hpre_mem _) (hmulmem (hpre_mem _) (hmulmem (hpre_mem _)
      (hmulmem (hpre_mem _) (hmulmem (hpre_mem _) (hmulmem (hpre_mem _)
      (hmulmem (hpre_mem _) (hmulmem (hpre_mem _) (hmulmem (hpre_mem _)
      (hmulmem (hpre_mem _) (hpre_mem _))))))))))
  have hdvd₁ : pre s₁ ∣ a₀ := dvd_mul_right _ _
  have hdvd₂ : pre s₂ ∣ a₀ := (dvd_mul_right _ _).mul_left _
  have hdvd₃ : pre s₃ ∣ a₀ := ((dvd_mul_right _ _).mul_left _).mul_left _
  have hdvd₄ : pre s₄ ∣ a₀ := (((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _
  have hdvd₆ : pre s₆ ∣ a₀ :=
    ((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _
  have hdvdu : pre du ∣ a₀ :=
    (((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _
  have hdvdv : pre dv ∣ a₀ :=
    ((((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
      _).mul_left _
  have hdvdr : pre dr ∣ a₀ :=
    (((((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
      _).mul_left _).mul_left _
  have hdvds : pre ds ∣ a₀ :=
    ((((((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
      _).mul_left _).mul_left _).mul_left _
  have hdvdt : pre dt ∣ a₀ :=
    (((((((((dvd_mul_right _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
      _).mul_left _).mul_left _).mul_left _).mul_left _
  have hdvdc : pre cuv ∣ a₀ :=
    (((((((((dvd_mul_left _ _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
      _).mul_left _).mul_left _).mul_left _).mul_left _
  -- ### rings and maps at level `a₀`
  have ha₀S : ((a₀ : R)) ∈ S := by
    rw [hSdef]
    exact Submonoid.mem_map_of_mem _ (show a₀ ∈ p.primeCompl from ha₀)
  have hj₀le : Submonoid.powers ((a₀ : R)) ≤ S.comap (RingHom.id R) := by
    rintro x ⟨n, rfl⟩
    exact Submonoid.mem_comap.mpr (Submonoid.pow_mem S ha₀S n)
  set j₀ : Localization.Away ((a₀ : R)) →+* Localization S :=
    IsLocalization.map (Localization S) (RingHom.id R) hj₀le with hj₀def
  have hj₀_alg : ∀ x : R,
      j₀ (algebraMap R (Localization.Away ((a₀ : R))) x) = algebraMap R (Localization S) x :=
    fun x => IsLocalization.map_eq hj₀le x
  set k₀ : Localization.Away a₀ →+* Localization.Away ((a₀ : R)) := fixedAwayMap a₀ with hk₀def
  have hk₀_alg : ∀ v : FixedPoints.subring R G,
      k₀ (algebraMap _ (Localization.Away a₀) v)
        = algebraMap R (Localization.Away ((a₀ : R))) ((v : R)) :=
    fun v => fixedAwayMap_algebraMap a₀ v
  have hcompalg : j₀.comp (algebraMap R (Localization.Away ((a₀ : R))))
      = algebraMap R (Localization S) := by
    rw [hj₀def]
    exact (IsLocalization.map_comp hj₀le).trans (RingHom.comp_id _)
  set F : Localization.Away a₀ →+* Localization S := j₀.comp k₀ with hFdef
  have hFb_alg : ∀ v : FixedPoints.subring R G,
      F (algebraMap _ (Localization.Away a₀) v) = algebraMap R (Localization S) ((v : R)) :=
    fun v => by rw [hFdef, RingHom.comp_apply, hk₀_alg, hj₀_alg]
  -- ### units at level `a₀` and the curves/changes of variables over the basic localizations
  have hu₁ : IsUnit (algebraMap _ (Localization.Away a₀) (pre s₁)) := isUnit_algebraMap_away hdvd₁
  have hu₂ : IsUnit (algebraMap _ (Localization.Away a₀) (pre s₂)) := isUnit_algebraMap_away hdvd₂
  have hu₃ : IsUnit (algebraMap _ (Localization.Away a₀) (pre s₃)) := isUnit_algebraMap_away hdvd₃
  have hu₄ : IsUnit (algebraMap _ (Localization.Away a₀) (pre s₄)) := isUnit_algebraMap_away hdvd₄
  have hu₆ : IsUnit (algebraMap _ (Localization.Away a₀) (pre s₆)) := isUnit_algebraMap_away hdvd₆
  have hdvdR : ∀ s : S, pre s ∣ a₀ → ((s : R)) ∣ ((a₀ : R)) := fun s hd => by
    rw [← hpre_eq s]
    exact map_dvd (algebraMap (FixedPoints.subring R G) R) hd
  have hUdu : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((du : R))) :=
    isUnit_algebraMap_away (hdvdR du hdvdu)
  have hUdv : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((dv : R))) :=
    isUnit_algebraMap_away (hdvdR dv hdvdv)
  have hUdr : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((dr : R))) :=
    isUnit_algebraMap_away (hdvdR dr hdvdr)
  have hUds : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((ds : R))) :=
    isUnit_algebraMap_away (hdvdR ds hdvds)
  have hUdt : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((dt : R))) :=
    isUnit_algebraMap_away (hdvdR dt hdvdt)
  have hUc : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) ((cuv : R))) :=
    isUnit_algebraMap_away (hdvdR cuv hdvdc)
  have hUpu : IsUnit (algebraMap R (Localization.Away ((a₀ : R))) pu) := by
    have h1 : IsUnit (algebraMap R (Localization.Away ((a₀ : R)))
        ((cuv : R) * ((du : R) * (dv : R)))) := by
      rw [map_mul, map_mul]
      exact hUc.mul (hUdu.mul hUdv)
    rw [← hcuv] at h1
    exact isUnit_of_dvd_unit (map_dvd _ ⟨(cuv : R) * pv, by ring⟩) h1
  set W₁ₗ : WeierstrassCurve (Localization.Away a₀) :=
    ⟨algebraMap _ _ (⟨b₁, hb₁⟩ : FixedPoints.subring R G) * ↑hu₁.unit⁻¹,
     algebraMap _ _ (⟨b₂, hb₂⟩ : FixedPoints.subring R G) * ↑hu₂.unit⁻¹,
     algebraMap _ _ (⟨b₃, hb₃⟩ : FixedPoints.subring R G) * ↑hu₃.unit⁻¹,
     algebraMap _ _ (⟨b₄, hb₄⟩ : FixedPoints.subring R G) * ↑hu₄.unit⁻¹,
     algebraMap _ _ (⟨b₆, hb₆⟩ : FixedPoints.subring R G) * ↑hu₆.unit⁻¹⟩ with hW₁ₗdef
  set Dₗ : VariableChange (Localization.Away ((a₀ : R))) :=
    ⟨hUpu.unit * hUdu.unit⁻¹,
     algebraMap R _ pr * ↑hUdr.unit⁻¹,
     algebraMap R _ ps * ↑hUds.unit⁻¹,
     algebraMap R _ pt * ↑hUdt.unit⁻¹⟩ with hDₗdef
  -- ### the `j₀`-images recover the data over `Localization S`
  have hW₁ₗF : W₁ₗ.map F = D' • (W₀.map (algebraMap R (Localization S))) := by
    have hds : ∀ s : S, F (algebraMap _ (Localization.Away a₀) (pre s))
        = algebraMap R (Localization S) ((s : R)) := fun s => by
      rw [hFb_alg]
      exact congrArg (algebraMap R (Localization S)) (hpre_eq s)
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show F (algebraMap _ _ (⟨b₁, hb₁⟩ : FixedPoints.subring R G) * ↑hu₁.unit⁻¹) = _
      rw [map_mul_isUnit_inv_eq_mk' F hu₁ (hFb_alg _) (hds s₁)]
      exact hmk₁
    · show F (algebraMap _ _ (⟨b₂, hb₂⟩ : FixedPoints.subring R G) * ↑hu₂.unit⁻¹) = _
      rw [map_mul_isUnit_inv_eq_mk' F hu₂ (hFb_alg _) (hds s₂)]
      exact hmk₂
    · show F (algebraMap _ _ (⟨b₃, hb₃⟩ : FixedPoints.subring R G) * ↑hu₃.unit⁻¹) = _
      rw [map_mul_isUnit_inv_eq_mk' F hu₃ (hFb_alg _) (hds s₃)]
      exact hmk₃
    · show F (algebraMap _ _ (⟨b₄, hb₄⟩ : FixedPoints.subring R G) * ↑hu₄.unit⁻¹) = _
      rw [map_mul_isUnit_inv_eq_mk' F hu₄ (hFb_alg _) (hds s₄)]
      exact hmk₄
    · show F (algebraMap _ _ (⟨b₆, hb₆⟩ : FixedPoints.subring R G) * ↑hu₆.unit⁻¹) = _
      rw [map_mul_isUnit_inv_eq_mk' F hu₆ (hFb_alg _) (hds s₆)]
      exact hmk₆
  have hDₗj : Dₗ.map j₀ = D' := by
    refine VariableChange.ext ?_ ?_ ?_ ?_
    · apply Units.ext
      show j₀ (↑hUpu.unit * (↑hUdu.unit⁻¹ : Localization.Away ((a₀ : R))))
        = ((D'.u : Localization S))
      rw [hUpu.unit_spec, map_mul_isUnit_inv_eq_mk' j₀ hUdu (hj₀_alg pu) (hj₀_alg _)]
      exact hpu
    · show j₀ (algebraMap R _ pr * ↑hUdr.unit⁻¹) = D'.r
      rw [map_mul_isUnit_inv_eq_mk' j₀ hUdr (hj₀_alg pr) (hj₀_alg _)]
      exact hpr
    · show j₀ (algebraMap R _ ps * ↑hUds.unit⁻¹) = D'.s
      rw [map_mul_isUnit_inv_eq_mk' j₀ hUds (hj₀_alg ps) (hj₀_alg _)]
      exact hps
    · show j₀ (algebraMap R _ pt * ↑hUdt.unit⁻¹) = D'.t
      rw [map_mul_isUnit_inv_eq_mk' j₀ hUdt (hj₀_alg pt) (hj₀_alg _)]
      exact hpt
  have hXY : (W₁ₗ.map k₀).map j₀
      = (Dₗ • (W₀.map (algebraMap R (Localization.Away ((a₀ : R)))))).map j₀ := by
    rw [WeierstrassCurve.map_map, ← hFdef, hW₁ₗF, ← WeierstrassCurve.map_variableChange,
      hDₗj, WeierstrassCurve.map_map, hcompalg]
  -- ### `Localization S` is a localization of `Localization.Away (a₀ : R)`; clearing lemma
  letI : Algebra (Localization.Away ((a₀ : R))) (Localization S) := j₀.toAlgebra
  haveI : IsScalarTower R (Localization.Away ((a₀ : R))) (Localization S) :=
    IsScalarTower.of_algebraMap_eq' hcompalg.symm
  haveI : IsLocalization (S.map (algebraMap R (Localization.Away ((a₀ : R)))))
      (Localization S) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away ((a₀ : R)))
      (Localization S) (Submonoid.powers ((a₀ : R))) S (Submonoid.powers_le.mpr ha₀S)
  have hclear : ∀ x y : Localization.Away ((a₀ : R)), j₀ x = j₀ y →
      ∃ c : S, algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * x
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * y := by
    intro x y hxy
    have hxy' : algebraMap (Localization.Away ((a₀ : R))) (Localization S) x
        = algebraMap (Localization.Away ((a₀ : R))) (Localization S) y := hxy
    obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists
      (S.map (algebraMap R (Localization.Away ((a₀ : R))))) (Localization S)).mp hxy'
    obtain ⟨cc, hccS, hcceq⟩ := Submonoid.mem_map.mp c'.2
    refine ⟨⟨cc, hccS⟩, ?_⟩
    show algebraMap R (Localization.Away ((a₀ : R))) cc * x
      = algebraMap R (Localization.Away ((a₀ : R))) cc * y
    rw [hcceq]
    exact hc'
  have hclear_dvd : ∀ {c c' : S} {x y : Localization.Away ((a₀ : R))}, c ∣ c' →
      algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * x
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * y →
      algebraMap R (Localization.Away ((a₀ : R))) ((c' : R)) * x
        = algebraMap R (Localization.Away ((a₀ : R))) ((c' : R)) * y := by
    intro c c' x y hcc h
    exact mul_right_cancel_of_dvd (map_dvd _ (map_dvd (Submonoid.subtype S) hcc)) h
  -- the five coefficient clearers
  have h1 := congrArg WeierstrassCurve.a₁ hXY
  have h2 := congrArg WeierstrassCurve.a₂ hXY
  have h3 := congrArg WeierstrassCurve.a₃ hXY
  have h4 := congrArg WeierstrassCurve.a₄ hXY
  have h6 := congrArg WeierstrassCurve.a₆ hXY
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h1 h2 h3 h4 h6
  obtain ⟨e₁, he₁⟩ := hclear _ _ h1
  obtain ⟨e₂, he₂⟩ := hclear _ _ h2
  obtain ⟨e₃, he₃⟩ := hclear _ _ h3
  obtain ⟨e₄, he₄⟩ := hclear _ _ h4
  obtain ⟨e₆, he₆⟩ := hclear _ _ h6
  -- ### the cocycle comparison over `Localization.Away (a₀ : R)`, and its clearers
  have hfixa₀ : ∀ g : G, g • ((a₀ : R)) = ((a₀ : R)) := fun g => a₀.2 g
  set Cgₗ : G → VariableChange (Localization.Away ((a₀ : R))) :=
    fun g => (C g).map (algebraMap R (Localization.Away ((a₀ : R)))) with hCgₗdef
  set Dgₗ : G → VariableChange (Localization.Away ((a₀ : R))) :=
    fun g => Dₗ.map (MulSemiringAction.awayHom hfixa₀ g) with hDgₗdef
  have hequivj₀ : ∀ g : G, j₀.comp (MulSemiringAction.awayHom hfixa₀ g)
      = (MulSemiringAction.toRingHom G (Localization S) g).comp j₀ := by
    intro g
    apply IsLocalization.ringHom_ext (Submonoid.powers ((a₀ : R)))
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [MulSemiringAction.awayHom_algebraMap hfixa₀ g x, hj₀_alg, hj₀_alg]
    exact (hcomp g x).symm
  have hDCg : ∀ g : G, (Dₗ * Cgₗ g).map j₀ = (Dgₗ g).map j₀ := by
    intro g
    have hL : (Dₗ * Cgₗ g).map j₀ = D' * C' g := by
      rw [show (Dₗ * Cgₗ g).map j₀ = Dₗ.map j₀ * (Cgₗ g).map j₀ from
        map_mul (VariableChange.mapHom j₀) _ _, hDₗj]
      congr 1
      show ((C g).map (algebraMap R (Localization.Away ((a₀ : R))))).map j₀ = C' g
      rw [VariableChange.map_map, hcompalg]
    have hR : (Dgₗ g).map j₀ = g • D' := by
      show (Dₗ.map (MulSemiringAction.awayHom hfixa₀ g)).map j₀ = g • D'
      rw [VariableChange.map_map, hequivj₀ g, ← VariableChange.map_map, hDₗj,
        ← vcSMul_eq_map, ← vcSMul_smul_def]
    rw [hL, hR, hDcob g]
  have hcob4 : ∀ g : G, ∃ c : S,
      (algebraMap R (Localization.Away ((a₀ : R))) ((c : R))
          * (((Dₗ * Cgₗ g).u : Localization.Away ((a₀ : R))))
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R))
          * (((Dgₗ g).u : Localization.Away ((a₀ : R))))) ∧
      (algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dₗ * Cgₗ g).r
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dgₗ g).r) ∧
      (algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dₗ * Cgₗ g).s
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dgₗ g).s) ∧
      (algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dₗ * Cgₗ g).t
        = algebraMap R (Localization.Away ((a₀ : R))) ((c : R)) * (Dgₗ g).t) := fun g =>
    exists_common_clear_variableChange (algebraMap R (Localization.Away ((a₀ : R)))) j₀ hclear
      (hDCg g)
  choose cg hcgu hcgr hcgs hcgt using hcob4
  -- ### fold all clearers into a single element of `S` and enlarge `a₀`
  set cAll : S := ((((e₁ * e₂) * e₃) * e₄) * e₆) * ∏ g : G, cg g with hcAlldef
  have hdvdE₁ : e₁ ∣ cAll :=
    ((((dvd_mul_right e₁ e₂).mul_right e₃).mul_right e₄).mul_right e₆).mul_right _
  have hdvdE₂ : e₂ ∣ cAll :=
    ((((dvd_mul_left e₂ e₁).mul_right e₃).mul_right e₄).mul_right e₆).mul_right _
  have hdvdE₃ : e₃ ∣ cAll :=
    (((dvd_mul_left e₃ (e₁ * e₂)).mul_right e₄).mul_right e₆).mul_right _
  have hdvdE₄ : e₄ ∣ cAll :=
    ((dvd_mul_left e₄ ((e₁ * e₂) * e₃)).mul_right e₆).mul_right _
  have hdvdE₆ : e₆ ∣ cAll :=
    (dvd_mul_left e₆ (((e₁ * e₂) * e₃) * e₄)).mul_right _
  have hdvdcg : ∀ g : G, cg g ∣ cAll := fun g =>
    (Finset.dvd_prod_of_mem cg (Finset.mem_univ g)).mul_left _
  set aF : FixedPoints.subring R G := a₀ * pre cAll with haFdef
  have haF : aF ∉ p := hmulmem ha₀ (hpre_mem _)
  have ha₀_dvd : a₀ ∣ aF := ⟨pre cAll, haFdef⟩
  have hpre_dvd : pre cAll ∣ aF := ⟨a₀, by rw [haFdef]; ring⟩
  -- ### the maps from level `a₀` to level `aF`
  have hfKu : ∀ y : Submonoid.powers a₀,
      IsUnit (algebraMap _ (Localization.Away aF) ((y : FixedPoints.subring R G))) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap _ (Localization.Away aF) (a₀ ^ n))
    rw [map_pow]
    exact (isUnit_algebraMap_away ha₀_dvd).pow n
  set fK : Localization.Away a₀ →+* Localization.Away aF := IsLocalization.lift hfKu
    with hfKdef
  have hfK_alg : ∀ v : FixedPoints.subring R G,
      fK (algebraMap _ (Localization.Away a₀) v) = algebraMap _ (Localization.Away aF) v :=
    fun v => IsLocalization.lift_eq hfKu v
  have haR_dvd : ((a₀ : R)) ∣ ((aF : R)) := ⟨((pre cAll : R)), rfl⟩
  have hfRu : ∀ y : Submonoid.powers ((a₀ : R)),
      IsUnit (algebraMap R (Localization.Away ((aF : R))) ((y : R))) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap R (Localization.Away ((aF : R))) (((a₀ : R)) ^ n))
    rw [map_pow]
    exact (isUnit_algebraMap_away haR_dvd).pow n
  set fR : Localization.Away ((a₀ : R)) →+* Localization.Away ((aF : R)) :=
    IsLocalization.lift hfRu with hfRdef
  have hfR_alg : ∀ x : R,
      fR (algebraMap R (Localization.Away ((a₀ : R))) x)
        = algebraMap R (Localization.Away ((aF : R))) x :=
    fun x => IsLocalization.lift_eq hfRu x
  -- ### descent of cleared equations along `fR`
  have hUcAll : IsUnit (algebraMap R (Localization.Away ((aF : R))) ((cAll : R))) := by
    apply isUnit_algebraMap_away
    rw [← hpre_eq cAll]
    exact map_dvd (algebraMap (FixedPoints.subring R G) R) hpre_dvd
  have hdescend : ∀ {x y : Localization.Away ((a₀ : R))},
      algebraMap R (Localization.Away ((a₀ : R))) ((cAll : R)) * x
        = algebraMap R (Localization.Away ((a₀ : R))) ((cAll : R)) * y → fR x = fR y := by
    intro x y h
    have h2 := congrArg fR h
    rw [map_mul, map_mul, hfR_alg] at h2
    exact hUcAll.mul_left_cancel h2
  -- ### the commuting square and the final assembly
  have hsquare : (fixedAwayMap aF).comp fK = fR.comp k₀ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a₀)
    ext v
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hfK_alg, fixedAwayMap_algebraMap, hk₀_alg, hfR_alg]
  have hfRcomp : fR.comp (algebraMap R (Localization.Away ((a₀ : R))))
      = algebraMap R (Localization.Away ((aF : R))) := RingHom.ext hfR_alg
  refine ⟨aF, haF, W₁ₗ.map fK, (Dₗ.map fR)⁻¹, ?_, ?_⟩
  · -- the Weierstrass model equation
    rw [inv_inv, WeierstrassCurve.map_map, hsquare, ← WeierstrassCurve.map_map]
    have hY : (Dₗ.map fR) • (W₀.map (algebraMap R (Localization.Away ((aF : R)))))
        = (Dₗ • (W₀.map (algebraMap R (Localization.Away ((a₀ : R)))))).map fR := by
      rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map, hfRcomp]
    rw [hY]
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · exact hdescend (hclear_dvd hdvdE₁ he₁)
    · exact hdescend (hclear_dvd hdvdE₂ he₂)
    · exact hdescend (hclear_dvd hdvdE₃ he₃)
    · exact hdescend (hclear_dvd hdvdE₄ he₄)
    · exact hdescend (hclear_dvd hdvdE₆ he₆)
  · -- the coboundary identity
    intro g
    rw [show (((Dₗ.map fR)⁻¹).map (MulSemiringAction.awayHom (fun g' => aF.2 g') g))
        = ((Dₗ.map fR).map (MulSemiringAction.awayHom (fun g' => aF.2 g') g))⁻¹ from
      map_inv (VariableChange.mapHom _) _, inv_inv, eq_inv_mul_iff_mul_eq]
    have hfRequiv : (MulSemiringAction.awayHom (fun g' => aF.2 g') g).comp fR
        = fR.comp (MulSemiringAction.awayHom hfixa₀ g) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers ((a₀ : R)))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [hfR_alg, MulSemiringAction.awayHom_algebraMap,
        MulSemiringAction.awayHom_algebraMap, hfR_alg]
    have hL : (Dₗ.map fR) * ((C g).map (algebraMap R (Localization.Away ((aF : R)))))
        = (Dₗ * Cgₗ g).map fR := by
      rw [show (Dₗ * Cgₗ g).map fR = Dₗ.map fR * (Cgₗ g).map fR from
        map_mul (VariableChange.mapHom fR) _ _]
      congr 1
      show (C g).map (algebraMap R (Localization.Away ((aF : R))))
        = ((C g).map (algebraMap R (Localization.Away ((a₀ : R))))).map fR
      rw [VariableChange.map_map, hfRcomp]
    have hRt : ((Dₗ.map fR).map (MulSemiringAction.awayHom (fun g' => aF.2 g') g))
        = (Dgₗ g).map fR := by
      show _ = (Dₗ.map (MulSemiringAction.awayHom hfixa₀ g)).map fR
      rw [VariableChange.map_map, VariableChange.map_map, hfRequiv]
    rw [hL, hRt]
    refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
    · show fR (((Dₗ * Cgₗ g).u : Localization.Away ((a₀ : R))))
        = fR (((Dgₗ g).u : Localization.Away ((a₀ : R))))
      exact hdescend (hclear_dvd (hdvdcg g) (hcgu g))
    · exact hdescend (hclear_dvd (hdvdcg g) (hcgr g))
    · exact hdescend (hclear_dvd (hdvdcg g) (hcgs g))
    · exact hdescend (hclear_dvd (hdvdcg g) (hcgt g))

end Main

end ModularCurves

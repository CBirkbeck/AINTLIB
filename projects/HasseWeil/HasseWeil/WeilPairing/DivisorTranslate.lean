/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslateOrdInfty
import HasseWeil.EC.TranslateValuation
import HasseWeil.WeilPairing.Constancy
import HasseWeil.WeilPairing.WeilFunction

/-!
# Divisor transport under translation (Silverman III.8, ticket T-R2-EVAL)

This file ships the **divisor-transport-under-translation** foundation needed
to define the Weil pairing `e_ℓ(S, T)` as the constant ratio `(τ_S^* g_T)/g_T`.

The translation-by-`S` map on the curve is `P ↦ P + S`, and its pullback
`τ_S = translateAlgEquivOfPoint W S` on the function field transports a place
`P` to the place `P + S`. Concretely, the already-shipped ord-transport brick
(`HasseWeil.translate_ord_eq_all_nonzero`) gives, for an affine smooth point
`P` with `P + S ≠ O`,
```
  ord_P P (τ_S f) = ord_{P+S} f .
```
The **point at infinity** `O` is NOT fixed by translation: it maps to the
affine point `S`, and the affine point `−S` maps to `O`. So the projective
divisor `projectiveDivisorOf` transports by a *full permutation* of all
projective places (affine points together with `∞`), realised as the
`Finsupp` push-forward `Finsupp.mapDomain` along the projective-place
translation bijection induced by `Q ↦ Q + S`.

## Main definitions

* `placeTranslate W S` — the bijection of projective places `v ↦ (v + S)`
  (the place corresponding to translating the underlying `Point` by `S`),
  built from `Affine.Point.equivProjectiveSmoothPoint` and `Equiv.addRight S`.
* `ordProj W v f` — the order of `f` at the projective place `v`
  (`ord_P` at an affine point, `ordAtInfty` at `∞`).

## Main results

* `ord_P_translate` — item 1, the affine ord transport
  `ord_P P (τ_S f) = ord_P (P + S) f` (sign pinned: `τ_S` moves `P ↦ P + S`).
* `ordProj_translate` — the **single isolated residual**: the uniform
  projective ord transport `ordProj v (τ_S f) = ordProj (placeTranslate v) f`.
  The affine→affine case is fully discharged from `translate_ord_eq_all_nonzero`;
  the residual content is exactly the two infinity-touching cases
  (`P + S = O` and the `∞` place), which require the order-at-infinity
  transport (`IsTranslateOrdAtInftyCompatible`), undischarged upstream.
* `projectiveDivisorOf_translate` — item 3, lifting to the full projective
  divisor: `projectiveDivisorOf (τ_S f) = mapDomain (placeTranslate S).symm
  (projectiveDivisorOf f)`.
* `projectiveDivisorOf_translate_self_of_invariant` and
  `projectiveDivisorOf_translate_div_eq_zero_of_invariant` — item 4, the
  pairing payoff: if `projectiveDivisorOf g` is invariant under the place
  translation, then `projectiveDivisorOf (τ_S g / g) = 0`, exactly the
  hypothesis `pairing_const_of_transport` consumes.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

open HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- The bijection of projective places induced by translating the underlying
`Point` by `S`: `v ↦ (v.toAffinePoint + S).toProjectiveSmoothPoint`.

Built as `equivProjectiveSmoothPoint⁻¹ ≫ (· + S) ≫ equivProjectiveSmoothPoint`.
This is the geometric translation that moves the place `P` to the place
`P + S`; in particular it sends `∞ ↦ S` and `(−S) ↦ ∞`, mixing affine places
with the place at infinity. -/
noncomputable def placeTranslate (S : W.toAffine.Point) :
    ProjectiveSmoothPoint (W_smooth W) ≃ ProjectiveSmoothPoint (W_smooth W) :=
  (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
      (W := W.toAffine)).symm.trans
    ((Equiv.addRight S).trans
      (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint (W := W.toAffine)))

theorem placeTranslate_apply (S : W.toAffine.Point)
    (v : ProjectiveSmoothPoint (W_smooth W)) :
    placeTranslate W S v =
      (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint (W := W.toAffine))
        (v.toAffinePoint + S) := by
  rfl

@[simp] theorem placeTranslate_affine (S : W.toAffine.Point)
    (P : (W_smooth W).SmoothPoint) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      (@HAdd.hAdd W.toAffine.Point W.toAffine.Point W.toAffine.Point _
        P.toAffinePoint S).toProjectiveSmoothPoint := by
  rw [placeTranslate_apply]
  rfl

@[simp] theorem placeTranslate_infinity (S : W.toAffine.Point) :
    placeTranslate W S ProjectiveSmoothPoint.infinity =
      S.toProjectiveSmoothPoint := by
  rw [placeTranslate_apply]
  change (((0 : W.toAffine.Point) + S)).toProjectiveSmoothPoint = _
  rw [zero_add]

/-- Translation by `O` is the identity place permutation. -/
@[simp] theorem placeTranslate_zero :
    placeTranslate W (0 : W.toAffine.Point) = Equiv.refl _ := by
  refine Equiv.ext fun v ↦ ?_
  rw [placeTranslate_apply, add_zero, Equiv.refl_apply]
  exact WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint v

/-- The order of `f` at the projective place `v`: `ord_P` at an affine point,
`ordAtInfty` at the place at infinity. This packages the two valuations
`projectiveDivisorOf` is built from into a single function of the place. -/
noncomputable def ordProj (v : ProjectiveSmoothPoint (W_smooth W))
    (f : KE) : WithTop ℤ :=
  match v with
  | ProjectiveSmoothPoint.affine P => (W_smooth W).ord_P P f
  | ProjectiveSmoothPoint.infinity => (W_smooth W).ordAtInfty f

@[simp] theorem ordProj_affine (P : (W_smooth W).SmoothPoint) (f : KE) :
    ordProj W (ProjectiveSmoothPoint.affine P) f = (W_smooth W).ord_P P f := rfl

@[simp] theorem ordProj_infinity (f : KE) :
    ordProj W ProjectiveSmoothPoint.infinity f = (W_smooth W).ordAtInfty f := rfl

/-- `projectiveDivisorOf f` read off place-by-place: its coefficient at `v` is
`(ordProj v f).untopD 0`. Unifies `projectiveDivisorOf_apply_affine` and
`projectiveDivisorOf_apply_infinity`. -/
theorem projectiveDivisorOf_apply_ordProj (f : KE)
    (v : ProjectiveSmoothPoint (W_smooth W)) :
    (W_smooth W).projectiveDivisorOf f v = (ordProj W v f).untopD 0 := by
  cases v with
  | affine P =>
    rw [(W_smooth W).projectiveDivisorOf_apply_affine, ordProj_affine]
  | infinity =>
    rw [(W_smooth W).projectiveDivisorOf_apply_infinity, ordProj_infinity]

/-- **Item 1, affine ord transport.** For nonzero `f` and an affine smooth
point `P` whose translate `P + S` is finite, the order of `τ_S f` at `P`
equals the order of `f` at `P + S`:
```
  ord_P P (τ_S f) = ord_P (P + S) f .
```
This pins the sign: the pullback `τ_S` transports the place `P` to `P + S`. -/
theorem ord_P_translate (P : (W_smooth W).SmoothPoint)
    (S : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + S).IsSome) (f : KE) (hf : f ≠ 0) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W S f) =
      (W_smooth W).ord_P (P.translate_of_finite S h) f := by
  rcases S with _ | ⟨xk, yk, h_ns⟩
  · change (W_smooth W).ord_P P f = (W_smooth W).ord_P
      (P.translate_of_finite (0 : (W_smooth W).toAffine.Point) h) f
    rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_zero]
  · exact translate_ord_eq_all_nonzero W P xk yk h_ns h f hf

/-- When the translate `P + S` is finite (`IsSome`), the place
`placeTranslate W S (affine P)` is the affine place of the translated smooth
point `P.translate_of_finite S h`. -/
theorem placeTranslate_affine_of_isSome (S : (W_smooth W).toAffine.Point)
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint + S).IsSome) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.affine (P.translate_of_finite S h) := by
  apply (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
    (W := W.toAffine)).symm.injective
  rw [placeTranslate_apply, Equiv.symm_apply_apply]
  exact (Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint
    P S h).symm

/-- When `P + S = O` (the translate hits infinity), the place
`placeTranslate W S (affine P)` is the place at infinity. -/
theorem placeTranslate_affine_eq_infinity (S : (W_smooth W).toAffine.Point)
    (P : (W_smooth W).SmoothPoint)
    (hz : P.toAffinePoint + S = (0 : W.toAffine.Point)) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.infinity := by
  apply (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
    (W := W.toAffine)).symm.injective
  rw [placeTranslate_apply, Equiv.symm_apply_apply]
  exact hz

/-- **The single isolated residual.** The projective ord transport
`ordProj v (τ_S f) = ordProj (placeTranslate v) f` at the infinity-touching
places: those `v` with `v = ∞` or `placeTranslate W S v = ∞` (equivalently,
`v` is the place that translates to `O`). This is exactly the order-at-infinity
transport under `τ_S = translateAlgEquivOfPoint W S`, the upstream obligation
`IsTranslateOrdAtInftyCompatible` (and its `∞`-source mirror), undischarged.

Mathematically: pullback by translation moves the place `v` to `v + S`, and
the order of `τ_S f` at `v` equals the order of `f` at `v + S`. The affine
case is `translate_ord_eq_all_nonzero`; this residual is the same statement
for the place at infinity. -/
theorem ordProj_translate_infinity (S : (W_smooth W).toAffine.Point)
    (f : KE) (hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W))
    (hv : v = ProjectiveSmoothPoint.infinity ∨
      placeTranslate W S v = ProjectiveSmoothPoint.infinity) :
    ordProj W v (translateAlgEquivOfPoint W S f) =
      ordProj W (placeTranslate W S v) f := by
  rcases eq_or_ne S (0 : W.toAffine.Point) with hS | hS
  · subst hS
    rw [placeTranslate_zero, Equiv.refl_apply]
    rw [show translateAlgEquivOfPoint W (0 : W.toAffine.Point) f = f from rfl]
  · cases v with
    | affine P =>
      have hv_eq : placeTranslate W S (ProjectiveSmoothPoint.affine P) =
          ProjectiveSmoothPoint.infinity := by
        rcases hv with hv | hv
        · exact absurd hv (by simp)
        · exact hv
      have hz : P.toAffinePoint + S = (0 : W.toAffine.Point) := by
        have h := congrArg (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
          (W := W.toAffine)).symm hv_eq
        rwa [placeTranslate_apply, Equiv.symm_apply_apply] at h
      rw [ordProj_affine, hv_eq, ordProj_infinity]
      exact isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P S hz f
    | infinity =>
      rw [ordProj_infinity, placeTranslate_infinity]
      obtain ⟨xk, yk, h_ns, hS_some⟩ :
          ∃ xk yk, ∃ h_ns : W.toAffine.Nonsingular xk yk,
            S = Affine.Point.some xk yk h_ns := by
        rcases S with _ | ⟨xk, yk, h_ns⟩
        · exact absurd rfl hS
        · exact ⟨xk, yk, h_ns, rfl⟩
      subst hS_some
      -- `a` is named as a `W.toAffine.Point` (not via `P_S.toAffinePoint`) so
      -- `a`, `-a`, `a + -a` share one `AddCommGroup` instance and
      -- `add_neg_cancel` matches syntactically.
      set P_S : (W_smooth W).SmoothPoint := ⟨xk, yk, h_ns⟩
      set a : W.toAffine.Point := P_S.toAffinePoint
      change (W_smooth W).ordAtInfty (translateAlgEquivOfPoint W a f) =
        (W_smooth W).ord_P P_S f
      have hfeq : translateAlgEquivOfPoint W (-a)
          (translateAlgEquivOfPoint W a f) = f := by
        have hsum := translateAlgEquivOfPoint_add_apply W a (-a) f
        rw [add_neg_cancel] at hsum
        exact hsum.symm
      have hcompat := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint
        W P_S (-a) (add_neg_cancel a)
        (translateAlgEquivOfPoint W a f)
      rw [hfeq] at hcompat
      exact hcompat.symm

/-- **The uniform projective ord transport** (item 1 lifted to all places).
For nonzero `f` and every projective place `v`,
```
  ordProj v (τ_S f) = ordProj (placeTranslate W S v) f ,
```
i.e. the pullback `τ_S` transports the order at `v` to the order at the
translated place `v + S`. The affine→affine case is `ord_P_translate`; the
infinity-touching cases are the isolated residual `ordProj_translate_infinity`. -/
theorem ordProj_translate (S : (W_smooth W).toAffine.Point)
    (f : KE) (hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W)) :
    ordProj W v (translateAlgEquivOfPoint W S f) =
      ordProj W (placeTranslate W S v) f := by
  cases v with
  | infinity =>
    exact ordProj_translate_infinity W S f hf ProjectiveSmoothPoint.infinity
      (Or.inl rfl)
  | affine P =>
    by_cases h : (P.toAffinePoint + S).IsSome
    · rw [placeTranslate_affine_of_isSome W S P h, ordProj_affine, ordProj_affine]
      exact ord_P_translate W P S h f hf
    · have hz : P.toAffinePoint + S = (0 : W.toAffine.Point) := by
        unfold WeierstrassCurve.Affine.Point.IsSome at h
        exact not_not.mp h
      exact ordProj_translate_infinity W S f hf (ProjectiveSmoothPoint.affine P)
        (Or.inr (placeTranslate_affine_eq_infinity W S P hz))

/-- **Item 3 — projective divisor transport.** The projective divisor of
`τ_S f` is the push-forward of `projectiveDivisorOf f` along the place
translation `(placeTranslate W S).symm`:
```
  projectiveDivisorOf (τ_S f) = equivMapDomain (placeTranslate W S).symm
                                  (projectiveDivisorOf f) .
```
-/
theorem projectiveDivisorOf_translate (S : (W_smooth W).toAffine.Point)
    (f : KE) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) =
      Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf f) := by
  by_cases hf : f = 0
  · subst hf
    have hL : (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S (0 : KE)) = 0 := by
      rw [show translateAlgEquivOfPoint W S (0 : KE) = 0 from map_zero _]
      exact (W_smooth W).projectiveDivisorOf_zero
    have hR : (W_smooth W).projectiveDivisorOf (0 : KE) = 0 :=
      (W_smooth W).projectiveDivisorOf_zero
    rw [hL, hR, Finsupp.equivMapDomain_zero]
  · refine Finsupp.ext fun w ↦ ?_
    rw [Finsupp.equivMapDomain_apply, projectiveDivisorOf_apply_ordProj,
      projectiveDivisorOf_apply_ordProj, Equiv.symm_symm, ordProj_translate W S f hf w]

/-- **Item 3 — projective divisor transport (`mapDomain` form).** Same as
`projectiveDivisorOf_translate`, phrased with `Finsupp.mapDomain` (the form the
divisor API uses elsewhere): the affine and infinity places transport by the
single projective-place translation bijection. -/
theorem projectiveDivisorOf_translate_mapDomain (S : (W_smooth W).toAffine.Point)
    (f : KE) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) =
      Finsupp.mapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf f) := by
  rw [projectiveDivisorOf_translate, Finsupp.equivMapDomain_eq_mapDomain]

/-- **Item 2 — affine divisor transport.** Reading off the affine places of
the projective transport: the affine divisor of `τ_S f` at an affine place is
the affine divisor of `f` at the translated place. (The affine `divisorOf`
alone does NOT transport to an affine `mapDomain`, because translation moves
the affine place `−S` to the place at infinity; the clean statement is the
projective one above. This pointwise affine form is the directly-usable
shadow.) -/
theorem divisorOf_translate_apply (S : (W_smooth W).toAffine.Point)
    (f : KE) (hf : f ≠ 0) (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).divisorOf (translateAlgEquivOfPoint W S f) P =
      (ordProj W (placeTranslate W S (ProjectiveSmoothPoint.affine P)) f).untopD 0 := by
  change (ordProj W (ProjectiveSmoothPoint.affine P)
    (translateAlgEquivOfPoint W S f)).untopD 0 = _
  exact congrArg (WithTop.untopD 0)
    (ordProj_translate W S f hf (ProjectiveSmoothPoint.affine P))

/-- **`projectiveDivisorOf (τ_S g)` equals `projectiveDivisorOf g`** when the
latter is invariant under the place translation `placeTranslate W S`. -/
theorem projectiveDivisorOf_translate_self_of_invariant
    (S : (W_smooth W).toAffine.Point) (g : KE)
    (hinv : Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf g) =
      (W_smooth W).projectiveDivisorOf g) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) =
      (W_smooth W).projectiveDivisorOf g := by
  rw [projectiveDivisorOf_translate, hinv]

/-- **Item 4 — the pairing payoff (abstract invariance form).** If
`projectiveDivisorOf g` is invariant under `placeTranslate W S`, then the
quotient `τ_S g / g` has trivial projective divisor:
```
  projectiveDivisorOf ((translateAlgEquivOfPoint W S) g / g) = 0 .
```
This is exactly the hypothesis `htransport` of
`HasseWeil.WeilPairing.pairing_const_of_transport`
(with `τ = (translateAlgEquivOfPoint W S).toRingEquiv`), which then yields the
constant `e_ℓ(S, T)`. -/
theorem projectiveDivisorOf_translate_div_eq_zero_of_invariant
    (S : (W_smooth W).toAffine.Point) (g : KE) (hg : g ≠ 0)
    (hinv : Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf g) =
      (W_smooth W).projectiveDivisorOf g) :
    (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S g / g) = 0 := by
  have hτg : translateAlgEquivOfPoint W S g ≠ 0 :=
    (map_ne_zero_iff _ (translateAlgEquivOfPoint W S).injective).mpr hg
  have hself : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) =
      (W_smooth W).projectiveDivisorOf g :=
    projectiveDivisorOf_translate_self_of_invariant W S g hinv
  calc (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g / g)
      = (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) +
          (W_smooth W).projectiveDivisorOf g⁻¹ := by
        rw [div_eq_mul_inv]
        exact (W_smooth W).projectiveDivisorOf_mul hτg (inv_ne_zero hg)
    _ = (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) -
          (W_smooth W).projectiveDivisorOf g := by
        rw [(W_smooth W).projectiveDivisorOf_inv hg, sub_eq_add_neg]
    _ = 0 := by rw [hself, sub_self]

/-- The `toAffinePoint` of a translated place is `w.toAffinePoint + S`. -/
theorem placeTranslate_toAffinePoint (S : (W_smooth W).toAffine.Point)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    (placeTranslate W S w).toAffinePoint =
      @HAdd.hAdd W.toAffine.Point W.toAffine.Point W.toAffine.Point _
        w.toAffinePoint S := by
  rw [placeTranslate_apply]
  exact WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint _

/-- **Coefficient formula for the fibre-sum divisor.** Reading off the
coefficient of `pullbackDiv f h Q` at a projective place `w`: it is `1` if
`w.toAffinePoint` lies in the fibre over `Q` (`f (w.toAffinePoint) = Q`), and
`0` otherwise. (Each fibre point contributes a single place; the places are
pairwise distinct.) -/
theorem pullbackDiv_apply (f : W.toAffine.Point →+ W.toAffine.Point)
    (hker : Finite f.ker) (Q : W.toAffine.Point)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q w =
      if f w.toAffinePoint = Q then (1 : ℤ) else 0 := by
  letI : Fintype {P : W.toAffine.Point // f P = Q} :=
    @Fintype.ofFinite _ (fiber_finite f hker Q)
  rw [pullbackDiv, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  have hkey : ∀ P : W.toAffine.Point,
      (P.toProjectiveSmoothPoint = w) ↔ (P = w.toAffinePoint) := by
    intro P
    constructor
    · intro hPw
      rw [← WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint P,
        hPw]
    · intro hPeq
      rw [hPeq,
        WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint]
  by_cases hQ : f w.toAffinePoint = Q
  · rw [if_pos hQ, Finset.sum_eq_single (⟨w.toAffinePoint, hQ⟩ :
      {P : W.toAffine.Point // f P = Q})]
    · rw [if_pos ((hkey w.toAffinePoint).mpr rfl)]
    · rintro ⟨P, hP⟩ _ hne
      rw [if_neg]
      intro hPw
      exact hne (Subtype.ext ((hkey P).mp hPw))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hQ]
    apply Finset.sum_eq_zero
    rintro ⟨P, hP⟩ _
    rw [if_neg]
    intro hPw
    exact hQ (by rw [← (hkey P).mp hPw]; exact hP)

/-- **Pointwise invariance of a fibre-sum divisor.** When `f S = 0`, the
coefficient of `pullbackDiv f hker Q` at the translated place equals its
coefficient at the original place: `f` kills the shift `S`, so the fibre
condition `f (w + S) = Q` is unchanged. -/
theorem pullbackDiv_placeTranslate_apply (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (Q : W.toAffine.Point) (hfS : f S = 0)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q (placeTranslate W S w) =
      pullbackDiv (W := W.toAffine) f hker Q w := by
  rw [pullbackDiv_apply, pullbackDiv_apply, placeTranslate_toAffinePoint]
  congr 1
  rw [map_add, hfS, add_zero]

/-- **General coefficient formula for the translated fibre-sum divisor** (no kernel hypothesis).
For *any* `S`, the coefficient of `pullbackDiv f hker Q` at the translated place
`placeTranslate W S w` equals the coefficient of `pullbackDiv f hker (Q − f S)` at `w`: the
fibre condition `f (w + S) = Q` is `f w = Q − f S`. This is the general shift law for the fibre
divisor; the `f S = 0` special case (`pullbackDiv_placeTranslate_apply`) drops the `f S` term. -/
theorem pullbackDiv_placeTranslate_apply_general (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (Q : W.toAffine.Point) (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q (placeTranslate W S w) =
      pullbackDiv (W := W.toAffine) f hker (Q - f S) w := by
  rw [pullbackDiv_apply, pullbackDiv_apply, placeTranslate_toAffinePoint]
  congr 1
  rw [map_add]
  exact propext eq_sub_iff_add_eq.symm

/-- **General translation law for the fibre-sum divisor** (no kernel hypothesis): the push-forward
of `pullbackDiv f hker Q` along the place-translation `(placeTranslate W S).symm` is
`pullbackDiv f hker (Q − f S)`. Translating the fibre over `Q` by `−S` lands it on the fibre
over `Q − f S` (since `f (P − S) = f P − f S`). This is the divisor-level form of
`[ℓ]^*(Q) ∘ τ_S = [ℓ]^*(Q − [ℓ]S)`, the engine of the alternating telescoping. -/
theorem equivMapDomain_placeTranslate_pullbackDiv (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) :
    Finsupp.equivMapDomain (placeTranslate W S).symm (pullbackDiv (W := W.toAffine) f hker Q) =
      pullbackDiv (W := W.toAffine) f hker (Q - f S) := by
  refine Finsupp.ext fun w ↦ ?_
  rw [Finsupp.equivMapDomain_symm_apply]
  exact pullbackDiv_placeTranslate_apply_general W S f hker Q w

/-- **`equivMapDomain` fixes a divisor invariant under the place translation.**
If `D (placeTranslate W S w) = D w` for all places `w`, then
`equivMapDomain (placeTranslate W S).symm D = D`. (This is the `Finsupp`-level
restatement of `placeTranslate`-invariance, via `equivMapDomain_symm_apply`.) -/
theorem equivMapDomain_placeTranslate_symm_eq_self
    (S : (W_smooth W).toAffine.Point)
    (D : ProjectiveDivisor (W_smooth W))
    (hD : ∀ w, D (placeTranslate W S w) = D w) :
    Finsupp.equivMapDomain (placeTranslate W S).symm D = D := by
  refine Finsupp.ext fun w ↦ ?_
  rw [Finsupp.equivMapDomain_symm_apply]
  exact hD w

/-- **The Weil-function (fibre-difference) divisor is `placeTranslate`-invariant**
when `f S = 0`. -/
theorem equivMapDomain_placeTranslate_pullbackDiv_sub
    (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (T : W.toAffine.Point) (hfS : f S = 0) :
    Finsupp.equivMapDomain (placeTranslate W S).symm
        (pullbackDiv (W := W.toAffine) f hker T -
          pullbackDiv (W := W.toAffine) f hker 0) =
      pullbackDiv (W := W.toAffine) f hker T -
        pullbackDiv (W := W.toAffine) f hker 0 := by
  refine equivMapDomain_placeTranslate_symm_eq_self W S _ (fun w ↦ ?_)
  change pullbackDiv (W := W.toAffine) f hker T (placeTranslate W S w) -
      pullbackDiv (W := W.toAffine) f hker 0 (placeTranslate W S w) =
    pullbackDiv (W := W.toAffine) f hker T w -
      pullbackDiv (W := W.toAffine) f hker 0 w
  rw [pullbackDiv_placeTranslate_apply W S f hker T hfS,
    pullbackDiv_placeTranslate_apply W S f hker 0 hfS]

/-- **Item 4 capstone (Weil-function form).** Let `g` be a nonzero function
whose projective divisor is the fibre difference
`pullbackDiv f hker T − pullbackDiv f hker 0` (the divisor of the Weil function
for `T`, with `f = [ℓ]` the multiplication-by-`ℓ` point map). If `f S = 0`
(`S ∈ E[ℓ]`), then
```
  projectiveDivisorOf ((translateAlgEquivOfPoint W S) g / g) = 0 .
```
This is exactly the hypothesis `htransport` consumed by
`HasseWeil.WeilPairing.pairing_const_of_transport` (with curve
`⟨W.toAffine⟩ = W_smooth W` and `τ = (translateAlgEquivOfPoint W S).toRingEquiv`)
to extract the constant pairing value `e_ℓ(S, T)`. -/
theorem projectiveDivisorOf_translate_weilFunction_div_eq_zero
    (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (T : W.toAffine.Point) (hfS : f S = 0)
    (g : KE) (hg : g ≠ 0)
    (hg_div : (W_smooth W).projectiveDivisorOf g =
      pullbackDiv (W := W.toAffine) f hker T -
        pullbackDiv (W := W.toAffine) f hker 0) :
    (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S g / g) = 0 := by
  refine projectiveDivisorOf_translate_div_eq_zero_of_invariant W S g hg ?_
  rw [hg_div]
  exact equivMapDomain_placeTranslate_pullbackDiv_sub W S f hker T hfS

end HasseWeil


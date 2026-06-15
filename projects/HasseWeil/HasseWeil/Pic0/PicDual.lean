import HasseWeil.Pic0.IsogenyClassGroup
import HasseWeil.Pic0.ToClassSurjective
import HasseWeil.Basic

/-!
# The Pic⁰ dual isogeny and the dual relation `α ∘ α̂ = [deg α]` (Silverman III.6.1)

For an endomorphism `α : Isogeny E E` of an elliptic curve `E`, equipped with a coordinate-ring
restriction witness `ch : α.CoordHom` (the comorphism `α* : R → R` on `R := E.CoordinateRing`),
this file builds the **Pic⁰ dual** as a point endomorphism and proves the dual relation, following
**Silverman, *The Arithmetic of Elliptic Curves*, III.6.1** *to the letter*.

## Silverman III.6.1 (verified against the in-repo PDF, book p.80–82)

Let `κ : E ≅ Pic⁰(E)`, `P ↦ class of `(P) − (O)``.  Silverman III.6.1(b) **defines** the dual via
the **divisor pullback** `φ*` (II.3.6/II.3.7):

```
            κ            φ*              κ⁻¹
  φ̂ :  E ───→ Pic⁰(E) ───→ Pic⁰(E) ───→ E ,
```

i.e. `φ̂ = κ⁻¹ ∘ φ* ∘ κ`, where `φ* : Pic⁰(E) → Pic⁰(E)` is the **pullback** of divisor classes
`(Q) ↦ Σ_{P ↦ Q} e_φ(P)·(P)` (Silverman II.3, book p.29).  At the level of the affine ideal class
group `Pic⁰(E) ≅ ClassGroup R`, this pullback is the **ideal extension** `𝔪_Q ↦ 𝔪_Q·𝒪 = ∏ 𝔓^{e}`,
which is exactly the shipped `HasseWeil.Isogeny.classMap` (= `HasseWeil.ClassGroup.map`).

The companion **divisor pushforward** `φ_*` (II.3.6/II.3.7), `(P) ↦ (φP)`, is at the ideal level the
**relative norm** `𝔓 ↦ 𝔮^{f}`, the shipped `HasseWeil.Isogeny.classNorm` (= `ClassGroup.relNorm`).
Silverman II.3.6(e) gives `φ_* ∘ φ* = [deg φ]` on `Pic⁰`; its shipped shadow is
`HasseWeil.Isogeny.classNorm_comp_classMap` (`classNorm (classMap c) = c ^ finrank R R`).

## Main definitions

* `HasseWeil.Isogeny.picDual` — `φ̂ = κ⁻¹ ∘ classMap ∘ κ` as a point endomorphism `E.Point →+
  E.Point` (the III.6.1(b) construction; `classMap` = extension = the divisor pullback `φ*`).
* `HasseWeil.Isogeny.picPushforward` — `κ⁻¹ ∘ classNorm ∘ κ`, the κ-transport of the divisor
  pushforward `φ_*` (= `classNorm` = relative norm).

## Main results

* `HasseWeil.Isogeny.picPushforward_comp_picDual` / `..._degree` — **unconditional** (modulo the
  carried `CoordHom`/`Module.Finite`/tower witnesses): the κ-transport of Silverman II.3.6(e),
  `picPushforward ∘ picDual = [finrank R R]` (resp. `= [α.degree]`), as `AddMonoidHom`s.
* `HasseWeil.Isogeny.toAddMonoidHom_comp_picDual` — **the III.6.1 target** `α ∘ α̂ = [deg α]`
  (`α.toAddMonoidHom.comp α.picDual = [α.degree]`), carrying the III.3.4 **naturality** of `κ` on
  the point map (`hnat : κ ∘ α = classNorm ∘ κ`) as a witness-parametric hypothesis.
* `HasseWeil.Isogeny.picDual_comp_toAddMonoidHom` — the companion `α̂ ∘ α = [deg α]`
  (III.6.2(a) order), under the same naturality witness.

## Why the III.3.4 naturality is a *carried hypothesis*, not derived

The unconditional results above tie `picDual` to `picPushforward` (both κ-transports), with **no**
extra input.  Identifying `picPushforward` with the *actual* point map `α.toAddMonoidHom` is the
**III.3.4 naturality** `κ ∘ α = classNorm ∘ κ` (i.e. `κ₂(αP) = φ_*κ₁(P)`).  As documented in
`HasseWeil/Pic0/ToClassFunctorial.lean`, the point-map ↔ ideal-map link the shipped API exposes is
the **`comap`** (set-theoretic point image), which on a prime `𝔓 / 𝔮` gives `𝔮`, whereas the
pushforward `φ_* = relNorm` gives `𝔮^{f}` — they differ by the **inertia/residue degree** `f`.
Bridging them is exactly the ramification bookkeeping `relNorm (comap …) = (·)^?`
(`relNorm_eq_pow_of_isMaximal`, needing `PerfectField (FractionRing R)`), the III.3.4 content the
`Isogeny` carries as *independent data*.  It is therefore taken as a hypothesis here (dischargeable
per isogeny: Frobenius, multiplication-by-`n`), keeping every theorem `#print axioms`-clean.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.3.6–3.7 (divisor pullback/pushforward,
  `φ_*φ* = [deg]`), III.3.4 (functoriality of `E ≅ Pic⁰(E)`), III.6.1 (the dual isogeny).
-/

open WeierstrassCurve Polynomial
open scoped nonZeroDivisors

namespace HasseWeil.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : Affine F} [E.IsElliptic]
variable {α : Isogeny E E}

/-- **κ-transport of a class-group endomorphism to a point endomorphism.**

Given a monoid hom `m : ClassGroup R →* ClassGroup R` (with `R := E.CoordinateRing`), conjugate it
by the isomorphism `κ = E.Point.toClassEquiv' : E.Point ≃+ Additive (ClassGroup R)` to obtain a
point endomorphism `κ⁻¹ ∘ (additive-wrap of m) ∘ κ : E.Point →+ E.Point`.

This is the algebraic incarnation of conjugating a `Pic⁰(E)`-endomorphism back to `E` along
Silverman's `κ`.  Used to define both `picDual` (from `classMap`) and `picPushforward` (from
`classNorm`). -/
noncomputable def classTransport (m : ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing) :
    E.Point →+ E.Point :=
  (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm.toAddMonoidHom.comp
    ((AddMonoidHom.mk'
        (fun a : Additive (ClassGroup E.CoordinateRing) => Additive.ofMul (m a.toMul))
        (by intro a b; simp [map_mul])).comp
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).toAddMonoidHom)

@[simp]
theorem classTransport_apply
    (m : ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing) (P : E.Point) :
    classTransport m P =
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm
        (Additive.ofMul (m (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)) :=
  rfl

/-- **The Pic⁰ dual `φ̂` as a point endomorphism (Silverman III.6.1(b)).**

`α.picDual ch hinj hfin = κ⁻¹ ∘ classMap ∘ κ`, where `classMap` is the class-group **extension**
map (= `ClassGroup.map`, the ideal extension `𝔪 ↦ 𝔪·𝒪`), which is the affine-ideal incarnation of
Silverman's **divisor pullback** `φ* : Pic⁰(E) → Pic⁰(E)`.  This is *exactly* the III.6.1(b)
definition `φ̂ = κ₁⁻¹ ∘ φ* ∘ κ₂`.

The `CoordHom` witness `ch`, injectivity `hinj`, and finiteness `hfin` are the data/hypotheses the
shipped `classMap` requires (carried, not discharged universally — instantiable per isogeny). -/
noncomputable def picDual (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    E.Point →+ E.Point :=
  classTransport (α.classMap ch hinj hfin)

@[simp]
theorem picDual_apply (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (P : E.Point) :
    α.picDual ch hinj hfin P =
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm
        (Additive.ofMul ((α.classMap ch hinj hfin)
          (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)) :=
  rfl

/-- **The κ-transport of the divisor pushforward `φ_*`.**

`α.picPushforward ch hinj hfin = κ⁻¹ ∘ classNorm ∘ κ`, where `classNorm` is the class-group
**relative norm** (= `ClassGroup.relNorm`), the affine-ideal incarnation of Silverman's **divisor
pushforward** `φ_* : Pic⁰(E) → Pic⁰(E)`, `(P) ↦ (φP)` (a prime `𝔓/𝔮` maps to `𝔮^{f}`).

Under the III.3.4 naturality of `κ` (carried as a hypothesis in `toAddMonoidHom_comp_picDual`) this
agrees with the actual point map `α.toAddMonoidHom`; unconditionally it is the κ-conjugate of the
norm, the left factor of `φ_* ∘ φ* = [deg]` (Silverman II.3.6(e)). -/
noncomputable def picPushforward (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    E.Point →+ E.Point :=
  classTransport (α.classNorm ch hinj hfin)

@[simp]
theorem picPushforward_apply (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (P : E.Point) :
    α.picPushforward ch hinj hfin P =
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm
        (Additive.ofMul ((α.classNorm ch hinj hfin)
          (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)) :=
  rfl

/-- **General κ-transport composition engine.** For monoid homs
`m₁, m₂ : ClassGroup R →* ClassGroup R` with `m₂ (m₁ c) = c ^ n` for all `c`, the κ-transport
composite `classTransport m₂ ∘ classTransport m₁` is `[n]` on the point group.  The inner
`κ ∘ κ⁻¹` cancels and the class-group power `c ^ n` becomes the `n`-fold point sum `n • P`.

Reused for both composition orders: `(m₁, m₂) = (classMap, classNorm)` gives `φ_* ∘ φ*` (the
forward order, II.3.6(e)); `(classNorm, classMap)` gives `φ* ∘ φ_*` (III.6.2(a)). -/
theorem classTransport_comp_eq
    (m₁ m₂ : ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing) (n : ℕ)
    (hcomp : ∀ c : ClassGroup E.CoordinateRing, m₂ (m₁ c) = c ^ n) :
    (classTransport m₂).comp (classTransport m₁) =
      (mulByInt E (n : ℤ)).toAddMonoidHom := by
  ext P
  rw [AddMonoidHom.comp_apply, classTransport_apply, classTransport_apply]
  rw [show (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E))
        ((WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm
          (Additive.ofMul (m₁ (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)))
        = Additive.ofMul (m₁ (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)
      from (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).apply_symm_apply _]
  rw [show (Additive.ofMul
          (m₁ (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)).toMul
        = m₁ (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul from rfl, hcomp]
  rw [show Additive.ofMul
        ((WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul ^ n)
        = n • (Additive.ofMul
          (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul) from rfl]
  rw [show Additive.ofMul (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul
        = WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P from rfl]
  rw [map_nsmul, (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm_apply_apply,
    mulByInt_apply]
  exact (natCast_zsmul P n).symm

/-! ### The dual relation `φ_* ∘ φ* = [deg]`, transported to the point group

Silverman II.3.6(e): `φ_* ∘ φ* = [deg φ]` on `Pic⁰(E)`.  Its shipped class-group shadow is
`classNorm_comp_classMap` (`classNorm (classMap c) = c ^ finrank R R`).  We transport it across `κ`
to obtain `picPushforward ∘ picDual = [finrank R R]` as point endomorphisms — **unconditionally**
(beyond the carried `CoordHom`/`Module.Finite` witnesses the `classMap`/`classNorm` already need).
The `α.degree` form follows from the degree bridge `classNorm_comp_classMap_degree`. -/

/-- **κ-transport of `φ_* ∘ φ* = [deg]` (coordinate-ring `finrank` form).**

`picPushforward ∘ picDual = [finrank R R]` as point endomorphisms, the κ-conjugate of the shipped
class-group identity `classNorm (classMap c) = c ^ finrank R R` (= Silverman II.3.6(e)
`φ_* ∘ φ* = [deg]`).  Unconditional beyond the carried `CoordHom`/`Module.Finite` witnesses.

The composite `picPushforward ∘ picDual` is literally `κ⁻¹ ∘ classNorm ∘ classMap ∘ κ` (the inner
`κ ∘ κ⁻¹` cancels), and `classNorm (classMap c) = c ^ n` turns the class-group power into the
`n`-fold sum `n • P` on points, i.e. `(mulByInt E n).toAddMonoidHom`. -/
theorem picPushforward_comp_picDual (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    (α.picPushforward ch hinj hfin).comp (α.picDual ch hinj hfin) =
      (mulByInt E (letI := ch.toAlgebra;
        ((@Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule : ℕ) :
          ℤ))).toAddMonoidHom :=
  -- `picPushforward ∘ picDual = classTransport classNorm ∘ classTransport classMap`, and
  -- `classNorm (classMap c) = c ^ finrank` is the shipped `classNorm_comp_classMap`.
  classTransport_comp_eq (α.classMap ch hinj hfin) (α.classNorm ch hinj hfin) _
    (α.classNorm_comp_classMap ch hinj hfin)

/-- **κ-transport of `φ_* ∘ φ* = [deg]` (`α.degree` form, Silverman II.3.6(e)).**

`picPushforward ∘ picDual = [α.degree]` as point endomorphisms, with the exponent expressed as the
function-field degree `α.degree`.  Obtained from `picPushforward_comp_picDual` by rewriting the
exponent through the degree bridge `degree_eq_finrank_coordinateRing_of_tower_eq`, whose
fraction-field tower witness `(S, S', …)` is carried as hypotheses (dischargeable per isogeny). -/
theorem picPushforward_comp_picDual_degree (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree) :
    (α.picPushforward ch hinj hfin).comp (α.picDual ch hinj hfin) =
      (mulByInt E (α.degree : ℤ)).toAddMonoidHom := by
  rw [picPushforward_comp_picDual ch hinj hfin]
  congr 2
  exact_mod_cast (α.degree_eq_finrank_coordinateRing_of_tower_eq ch S S' hSR hS'FF).symm

/-! ### The III.6.1 target `α ∘ α̂ = [deg α]` on the point group

The unconditional `picPushforward_comp_picDual` ties `picDual` to `picPushforward`.  To reach the
brief's target `α ∘ α̂ = [deg α]` — with the *actual* point map `α.toAddMonoidHom` — we additionally
need the **Silverman III.3.4 naturality** of `κ` on the point map: that under `κ`, the point map
`α.toAddMonoidHom` corresponds to the divisor pushforward `φ_*` (= `classNorm`).  In the κ-conjugate
form, this is exactly `α.toAddMonoidHom = α.picPushforward …`.

As documented in `HasseWeil/Pic0/ToClassFunctorial.lean`, the shipped point-map ↔ ideal-map link is
the **`comap`** (set-theoretic point image), which differs from `φ_* = relNorm` by the residue
degree; bridging them is the III.3.4 ramification bookkeeping the `Isogeny` carries as independent
data.  We therefore take the naturality as a witness-parametric hypothesis (dischargeable per
isogeny), keeping the result `#print axioms`-clean. -/

/-- **The III.3.4 naturality witness, raw form**: under `κ = toClassEquiv'`, the point map of `α`
corresponds to the relative-norm class map `classNorm` (the divisor pushforward `φ_*`):
`κ (α P) = classNorm (κ P)` for every `P`.  This is Silverman III.3.4 for the point map; it is the
`comap`-vs-`relNorm` (residue-degree) content `ToClassFunctorial` documents as carried data. -/
def Naturality (α : Isogeny E E) (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) : Prop :=
  ∀ P : E.Point,
    WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) (α.toAddMonoidHom P) =
      Additive.ofMul ((α.classNorm ch hinj hfin)
        (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E) P).toMul)

/-- The naturality witness is exactly the statement that the actual point map equals the
κ-transport `picPushforward` of the pushforward/norm.  (κ-conjugate reformulation of
`Naturality`.) -/
theorem toAddMonoidHom_eq_picPushforward_iff (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    α.toAddMonoidHom = α.picPushforward ch hinj hfin ↔ α.Naturality ch hinj hfin := by
  constructor
  · intro h P
    rw [h, picPushforward_apply,
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).apply_symm_apply]
  · intro h
    ext P
    rw [picPushforward_apply, ← h P,
      (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)).symm_apply_apply]

/-! #### Isolating the `hnat` residual to the rational-point ideal identity (`comap = relNorm`)

`Naturality` is structurally a **carried datum**: an abstract `Isogeny E E` stores its `pullback`
and `toAddMonoidHom` as *independent* fields (`HasseWeil/Basic.lean`), with no derivation linking
the point map to the comorphism `ch` — so `hnat` cannot be proved in general, only verified per
isogeny where both fields are explicit (Frobenius, mult-by-`n`).

What we *can* ship axiom-clean is the exact reduction of the **right-hand side** of `Naturality` to
a concrete ideal class.  The RHS `classNorm (κ P)` for a rational point `P = (x, y)` is the `mk0`
class of the **relative norm** `relNorm (maximalIdealAt P) = relNorm ⟨X − x, Y − y⟩` (Silverman's
divisor pushforward `φ_*`).  Combined with the shipped `ToClassFunctorial.toClass_toPointMap`
(whose ideal is the **`comap`** `α*⁻¹(maximalIdealAt P)`), this pins the *entire* remaining content
of `hnat` to the single residue-degree identity

```
class (relNorm (maximalIdealAt P)) = class (comap α* (maximalIdealAt P))     (rational P)
```

which holds because a rational point has residue degree `f = 1`, so `relNorm 𝔪_P = 𝔪_P ∩ R =
comap α* 𝔪_P` (for `f = 1`, `relNorm 𝔭 = (comap 𝔭)^f = comap 𝔭`).  Mathlib has no
`relNorm = (comap)^{inertiaDeg}` lemma (and the project's `inertiaDeg = 1`-at-smooth-points
computation is `Module.Free`-diamond-blocked, see `Curves/GenericFiber.lean` Piece 9), so this last
step stays a per-isogeny obligation; the lemma below is the bridge that *reduces to it*. -/

/-- **The `classNorm`/`κ` side of `Naturality`, evaluated at a rational point (axiom-clean bridge).**

For a rational point `P = (x, y)` (a mathlib `Point.some`), the value of the relative-norm class map
`classNorm` on `κ P = toClassEquiv' P` is the `mk0` class of the **relative ideal norm** of the
maximal ideal `XYIdeal E x (C y) = ⟨X − x, Y − y⟩` at `P` (= Silverman's divisor pushforward `φ_*`,
packaged as `relNorm0`).  This unfolds the *right-hand side* of the III.3.4 naturality predicate
`Naturality` at `Point.some`, reducing the whole `hnat` obligation to the ideal-class identity
`class (relNorm 𝔪_P) = class (comap α* 𝔪_P)` against the shipped `toClass_toPointMap` (the
`comap` form) — exactly the residue-degree-`1` content (see the section note).

Proof: `κ (some) = toClass (some) = mk (XYIdeal' h) = mk0 ⟨XYIdeal, _⟩` (the project's
`mk0_eq_mk_XYIdeal'` bridge), then `ClassGroup.relNorm_mk0` computes the norm on the integral
representative. -/
theorem classNorm_toClassEquiv'_some (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {x y : F} (h : E.Nonsingular x y)
    (hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
      (Ideal E.CoordinateRing)⁰) :
    (α.classNorm ch hinj hfin)
        (WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)
          (WeierstrassCurve.Affine.Point.some x y h)).toMul =
      letI := ch.toAlgebra
      haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
      haveI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
        ch.isTorsionFree hinj
      ClassGroup.mk0 (HasseWeil.relNorm0 (R := E.CoordinateRing) (S := E.CoordinateRing)
        ⟨WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y), hmem⟩) := by
  letI := ch.toAlgebra
  haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
        ch.isTorsionFree hinj
  rw [WeierstrassCurve.Affine.Point.toClassEquiv'_apply,
    WeierstrassCurve.Affine.Point.toClass_some,
    ← WeierstrassCurve.Affine.Point.mk0_eq_mk_XYIdeal' h hmem]
  show HasseWeil.ClassGroup.relNorm (ClassGroup.mk0 _) = _
  rw [HasseWeil.ClassGroup.relNorm_mk0]

/-! #### Discharging `hnat`: the residue-degree-`1` (`comap = relNorm`) step at rational points

Combining the shipped `classNorm_toClassEquiv'_some` (the `relNorm0` form of the `Naturality` RHS)
with the residue-degree bridge of `ClassGroupNorm` (`relNorm 𝔪 = comap 𝔪` at `inertiaDeg = 1`, the
`inertiaDeg = 1` itself supplied **diamond-free** by `Ideal`.`inertiaDeg_under_eq_one_of_algHom_…`),
we reduce the entire `hnat`/`Naturality` obligation to the **point-map ↔ `comap` agreement** — that
the actual point map `α.toAddMonoidHom` sends `(x, y)` to a point whose `κ`-class is the contraction
`comap α* 𝔪_{(x,y)}` (Silverman III.3.4, the `comap` form shipped as `toClass_toPointMap`).

The residue-degree step needs `PerfectField (FractionRing R) = PerfectField K(E)` (the hypothesis of
mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`).  This holds for perfect base fields (e.g. `char 0`,
or algebraically closed of characteristic `0`).  **Honest residual:** for a function field over a
*finite* field `K(E)` is *imperfect*, so this last `relNorm = comap` step is not covered by the
mathlib lemma there; pinning the exponent without `PerfectField`/Galois would require a degree-count
adaptation of the project's `relNorm_maximalIdealAt` (`Curves/NormValuation.lean`) to the twisted
`R →[α*] R` extension.  Everything *below* the `PerfectField` hypothesis is unconditional. -/

/-- **The `comap α* 𝔪_P` ideal is a nonzero divisor** (carried side condition for the `mk0` class).
For a rational point `P = (x, y)`, the contraction `comap α* (XYIdeal E x (C y))` of the (nonzero)
maximal ideal is nonzero, because `α*` is module-finite (hence integral) so a nonzero prime does not
contract to `⊥` (`Ideal.under_ne_bot`). -/
theorem comap_XYIdeal_mem_nonZeroDivisors (ch : α.CoordHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {x y : F}
    (hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
      (Ideal E.CoordinateRing)⁰) :
    Ideal.comap ch.toAlgHom.toRingHom
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) ∈
    (Ideal E.CoordinateRing)⁰ := by
  letI := ch.toAlgebra
  haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI : Algebra.IsIntegral E.CoordinateRing E.CoordinateRing :=
    Algebra.IsIntegral.of_finite _ _
  have hbot : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp hmem
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.under_ne_bot (A := E.CoordinateRing) (B := E.CoordinateRing) hbot)

set_option maxHeartbeats 1600000 in
-- The residue-field `finrank` bookkeeping + the twisted `R →[α*] R` instance chain need extra room.
/-- **The `classNorm`/`comap` identity at a rational point (residue degree `1`) — UNCONDITIONAL.**

For a rational point `P = (x, y)` and a coordinate-ring restriction `ch`, the relative-norm class
`classNorm0 (XYIdeal E x (C y))` (the `Naturality` RHS, via `classNorm_toClassEquiv'_some`) equals
the class of the **contraction** `comap α* (XYIdeal E x (C y))` — Silverman's divisor pushforward
`φ_*` collapses to the set-theoretic point image at a rational point, where the residue degree
`f = 1`.

**`PerfectField`-free.**  Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal` is gated on
`[PerfectField (FractionRing R)]` (its proof reduces to the Galois case, which fails for a function
field over a finite base), but that hypothesis is *not* needed at `f = 1`: the shipped
`ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one` (`ClassGroupNorm.lean`) discharges
`relNorm 𝔪 = comap 𝔪` from `inertiaDeg = 1` alone via the module-length / DVR-base route, with **no**
`PerfectField`.  This removes the previous `[PerfectField E.FunctionField]` hypothesis.

Proof: `XYIdeal` is maximal (`quotientXYIdealEquiv`) with residue field `F` (so `finrank F (R/𝔪) =
1`), hence `inertiaDeg (𝔪.under R) 𝔪 = 1`
(`Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one`, diamond-free); then
`ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one` (`relNorm 𝔪 = comap 𝔪` under `f = 1`,
unconditional) finishes. -/
theorem mk0_relNorm0_XYIdeal_eq_mk0_comap
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {x y : F} (h : E.Nonsingular x y)
    (hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
      (Ideal E.CoordinateRing)⁰)
    (hcomap : Ideal.comap ch.toAlgHom.toRingHom
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) ∈
      (Ideal E.CoordinateRing)⁰) :
    letI := ch.toAlgebra
    haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
    haveI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
        ch.isTorsionFree hinj
    ClassGroup.mk0 (HasseWeil.relNorm0 (R := E.CoordinateRing) (S := E.CoordinateRing)
        ⟨WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y), hmem⟩) =
      ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)), hcomap⟩ :
        (Ideal E.CoordinateRing)⁰) := by
  letI := ch.toAlgebra
  haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
        ch.isTorsionFree hinj
  haveI hMmax : (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      ((WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv h.1).toRingEquiv.isField
        (Field.toIsField F))
  have hf : Ideal.inertiaDeg
      ((WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)).under
        E.CoordinateRing)
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) = 1 :=
    Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one ch.toAlgHom hfin _
      (WeierstrassCurve.Affine.Point.finrank_quotient_XYIdeal_eq_one h.1)
  exact ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one
    (R := E.CoordinateRing) (S := E.CoordinateRing)
    ⟨WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y), hmem⟩ hf hcomap

/-- **The cleanest `hnat` reduction (unconditional): point map ↔ `relNorm0` class.**

The `Naturality` predicate `hnat` holds iff, for every rational point `P = (x, y)`, the `κ`-class of
the actual point image `α.toAddMonoidHom (x, y)` equals the `mk0` class of the relative norm
`relNorm0 (XYIdeal E x (C y))` (the divisor pushforward `φ_*`).  This is *exactly*
`classNorm_toClassEquiv'_some` matched against the point map — **no `PerfectField` and no extra
hypothesis** beyond the carried `CoordHom`/`Module.Finite` data: it is the honest restatement of the
remaining `hnat` content as the per-point obligation `κ(α P) = mk0(relNorm 𝔪_P)`.

A caller discharges the `hpoint` hypothesis per isogeny by *any* route — the `comap` form below
(`Naturality_of_toClassEquiv'_some_eq_comap`, via `PerfectField`), the Galois route, or a degree
count à la `relNorm_maximalIdealAt`.  The basepoint case is automatic. -/
theorem Naturality_of_toClassEquiv'_some_eq_relNorm0
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hpoint : ∀ (x y : F) (h : E.Nonsingular x y)
      (hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
        (Ideal E.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)
          (α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (letI := ch.toAlgebra
          haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
          haveI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _
            ch.toAlgebra.toModule := ch.isTorsionFree hinj
          ClassGroup.mk0 (HasseWeil.relNorm0 (R := E.CoordinateRing) (S := E.CoordinateRing)
            ⟨WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y), hmem⟩))) :
    α.Naturality ch hinj hfin := by
  intro P
  cases P with
  | zero =>
    rw [show α.toAddMonoidHom (Affine.Point.zero : E.Point) = 0 from map_zero _,
      show (Affine.Point.zero : E.Point) = 0 from rfl]
    simp
  | some x y h =>
    have hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
        (Ideal E.CoordinateRing)⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero]
      intro hbot
      have hm : WeierstrassCurve.Affine.CoordinateRing.XClass E x ∈
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal]
        exact Ideal.subset_span (Set.mem_insert _ _)
      rw [hbot, Submodule.mem_bot] at hm
      exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := E) x hm
    rw [classNorm_toClassEquiv'_some ch hinj hfin h hmem]
    exact hpoint x y h hmem

/-- **Discharging `hnat` from point-map ↔ `comap` agreement (residue degree `1`) — UNCONDITIONAL.**

The `Naturality` predicate `hnat` holds whenever, for every rational point `P = (x, y)`, the actual
point map `α.toAddMonoidHom` sends `(x, y)` to a point whose `κ`-class is the contraction
`comap α* 𝔪_{(x,y)}` (the `comap` form of Silverman III.3.4 — exactly what `toClass_toPointMap`
supplies for a *geometric* isogeny whose point map is `toPointMap`).  This is the precise reduction
of `hnat` to its remaining content: the `relNorm`-vs-`comap` gap is closed here by the residue
identity `mk0_relNorm0_XYIdeal_eq_mk0_comap`, which is now **`PerfectField`-free** (it routes through
the shipped `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`, valid at `f = 1` with no
`PerfectField`).  **No `PerfectField E.FunctionField` hypothesis** — the only residual is the
point-map ↔ `comap` agreement `hpoint`, i.e. Silverman III.3.4 for the *actual* point map (supplied
per isogeny by `toClass_toPointMap` whenever the point map is the geometric `toPointMap`).

The basepoint case is automatic (`κ 0 = 0 = ofMul (classNorm 1)`). -/
theorem Naturality_of_toClassEquiv'_some_eq_comap
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hpoint : ∀ (x y : F) (h : E.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) ∈
        (Ideal E.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)
          (α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)), hcomap⟩ :
          (Ideal E.CoordinateRing)⁰))) :
    α.Naturality ch hinj hfin := by
  intro P
  cases P with
  | zero =>
    rw [show α.toAddMonoidHom (Affine.Point.zero : E.Point) = 0 from map_zero _,
      show (Affine.Point.zero : E.Point) = 0 from rfl]
    simp
  | some x y h =>
    -- `XYIdeal` is a nonzero divisor (it contains the nonzero `XClass`).
    have hmem : WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) ∈
        (Ideal E.CoordinateRing)⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero]
      intro hbot
      have hm : WeierstrassCurve.Affine.CoordinateRing.XClass E x ∈
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal]
        exact Ideal.subset_span (Set.mem_insert _ _)
      rw [hbot, Submodule.mem_bot] at hm
      exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := E) x hm
    have hcomap := comap_XYIdeal_mem_nonZeroDivisors ch hfin hmem
    -- RHS: `classNorm (κ (some)) = mk0 (relNorm0 𝔪) = mk0 (comap 𝔪)`; LHS: `hpoint`.
    rw [classNorm_toClassEquiv'_some ch hinj hfin h hmem,
      mk0_relNorm0_XYIdeal_eq_mk0_comap ch hinj hfin h hmem hcomap]
    exact hpoint x y h hcomap

/-- **UNCONDITIONAL `Naturality` from a `CoordHom` (Silverman III.3.4) — the `hnat` discharge.**

Given a coordinate-ring restriction `ch : α.CoordHom` and the **single genuine residual** that the
actual point map `α.toAddMonoidHom` realises the III.3.4 *set-theoretic point image* — i.e. for each
rational `(x, y)` the `κ`-class of `α.toAddMonoidHom (x, y)` is the contraction `comap α* 𝔪_{(x,y)}`
(`hpoint`, exactly what the shipped `toClass_toPointMap` supplies for an isogeny whose point map is
the geometric `toPointMap`) — the full naturality `α.Naturality ch hinj hfin` holds.

This is the **unconditional** wiring requested for the Route-C `hnat` discharge: it threads the
divisor-pushforward RHS (`classNorm_toClassEquiv'_some`) through the residue-degree-`1`
identity `relNorm 𝔪 = comap 𝔪`, now **`PerfectField`-free** (`mk0_relNorm0_XYIdeal_eq_mk0_comap` →
`ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`, `inertiaDeg = 1` from
`Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one`).  The `relNorm`-vs-`comap`
residue bookkeeping is *fully discharged*; the only carried datum is `hpoint`, the point-map ↔
`comap` agreement (Silverman III.3.4 for the actual point map), which is the genuine per-isogeny /
base-change content (CoordHom data) — **not** a `PerfectField`/Galois obligation.

Identical statement to `Naturality_of_toClassEquiv'_some_eq_comap`; provided under the
`naturality_of_coordHom` name the Route-C assembly consumes. -/
theorem naturality_of_coordHom
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hpoint : ∀ (x y : F) (h : E.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) ∈
        (Ideal E.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)
          (α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)), hcomap⟩ :
          (Ideal E.CoordinateRing)⁰))) :
    α.Naturality ch hinj hfin :=
  Naturality_of_toClassEquiv'_some_eq_comap ch hinj hfin hpoint

/-- **Silverman III.6.1 target: `α ∘ α̂ = [deg α]` on the point group (`finrank` exponent).**

`α.toAddMonoidHom.comp (α.picDual …) = [finrank R R]` as point endomorphisms, under the III.3.4
naturality witness `hnat`.  Combines the unconditional `picPushforward_comp_picDual`
(= `φ_* ∘ φ* = [deg]`, Silverman II.3.6(e)) with `α.toAddMonoidHom = picPushforward` (III.3.4
naturality), so the actual point map replaces `picPushforward`. -/
theorem toAddMonoidHom_comp_picDual (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin) :
    α.toAddMonoidHom.comp (α.picDual ch hinj hfin) =
      (mulByInt E (letI := ch.toAlgebra;
        ((@Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule : ℕ) :
          ℤ))).toAddMonoidHom := by
  rw [(toAddMonoidHom_eq_picPushforward_iff ch hinj hfin).mpr hnat]
  exact picPushforward_comp_picDual ch hinj hfin

/-- **Silverman III.6.1 target: `α ∘ α̂ = [deg α]` on the point group (`α.degree` exponent).**

`α.toAddMonoidHom.comp (α.picDual …) = [α.degree]`, the function-field-degree form of
`toAddMonoidHom_comp_picDual`, obtained by additionally carrying the fraction-field tower witness
`(S, S', …)` for the degree bridge `degree_eq_finrank_coordinateRing_of_tower_eq`. -/
theorem toAddMonoidHom_comp_picDual_degree (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree) :
    α.toAddMonoidHom.comp (α.picDual ch hinj hfin) =
      (mulByInt E (α.degree : ℤ)).toAddMonoidHom := by
  rw [(toAddMonoidHom_eq_picPushforward_iff ch hinj hfin).mpr hnat]
  exact picPushforward_comp_picDual_degree ch hinj hfin S S' hSR hS'FF

/-! ### The companion order `α̂ ∘ α = [deg α]` (Silverman III.6.2(a))

Silverman III.6.2(a) gives the *other* composition order `α̂ ∘ α = [deg]`, used by the QF expansion
for `β = φ + ψ`.  At the point level, with the III.3.4 naturality
`α.toAddMonoidHom = picPushforward = κ⁻¹ ∘ classNorm ∘ κ` and `picDual = κ⁻¹ ∘ classMap ∘ κ`, the
composite `picDual ∘ α.toAddMonoidHom` is `κ⁻¹ ∘ (classMap ∘ classNorm) ∘ κ`.

**Honest scope note.** This is `φ* ∘ φ_*` (extension after norm) — the **opposite** order to the
shipped `classNorm_comp_classMap` (`classNorm ∘ classMap = φ_* ∘ φ*`).  The two orders are *not*
interchangeable from commutativity of `ClassGroup` alone (`f(g c) = g(f c)` needs `f ∘ g = g ∘ f`
as maps, not a commutative codomain), and mathlib provides only `relNorm_algebraMap`
(`relNorm ∘ map`), **not** `map ∘ relNorm = (·)^n`.  The reverse-order class identity
`classMap (classNorm c) = c ^ n` is therefore a genuine separate Silverman ingredient (III.6.2(a),
equivalently II.3.6(e) applied to the dual `α̂`), carried here as a witness-parametric hypothesis
`hother` (exactly mirroring how `classNorm_comp_classMap` is the *forward*-order fact).  It is
*not* faked: supplying it is the honest reverse-order obligation. -/

/-! #### Silverman's actual III.6.2(a) derivation: right-cancel the nonconstant `α̂`

Silverman III.6.2(a) does **not** prove the second composition order from a fresh reverse-order
divisor identity.  Instead it derives `φ ∘ φ̂ = [m]` from `φ̂ ∘ φ = [m]` (and vice versa) by
**right-cancelling the nonconstant isogeny** (II.2.3: a nonconstant isogeny has injective
comorphism, hence is right-cancellable; geometrically, it is surjective on `E(K̄)`):

> `(φ ∘ φ̂) ∘ φ = φ ∘ (φ̂ ∘ φ) = φ ∘ [m] = [m] ∘ φ`, then cancel `φ`.

We reproduce this *to the letter* at the point/`AddMonoidHom` level.  The cancellation hypothesis
is the **surjectivity of `picDual`** (`= α̂`) as a point map — which over `K̄` is automatic (an
isogeny is surjective on geometric points, III.4.10a), and is the *geometric*, Silverman-faithful
form of the obligation.  This **replaces** the opaque reverse-order class identity `hother` with
the standard surjectivity input, and the result needs only the III.3.4 naturality `hnat` (used by
`toAddMonoidHom_comp_picDual`) plus that surjectivity. -/

/-- **Generic right-cancellation of an additive point endomorphism (Silverman's II.2.3 move).**

If `g : E.Point →+ E.Point` is **surjective** and `f.comp g = (mulByInt E m).toAddMonoidHom`, then
the *reverse* composite `g.comp f` is also `[m]`.  This is the abstract content of Silverman's
right-cancellation of a nonconstant isogeny: from `f ∘ g = [m]` we get
`(g ∘ f) ∘ g = g ∘ (f ∘ g) = g ∘ [m] = [m] ∘ g` (the last step because `g` is additive, so it
commutes with `[m] = m • ·`), and surjectivity of `g` cancels it on the right. -/
theorem comp_eq_mulByInt_of_comp_eq_of_surjective
    {f g : E.Point →+ E.Point} (m : ℤ) (hg : Function.Surjective g)
    (hfg : f.comp g = (mulByInt E m).toAddMonoidHom) :
    g.comp f = (mulByInt E m).toAddMonoidHom := by
  -- Right-cancel `g`: it suffices to check equality after pre-composing with the surjection `g`.
  ext R
  obtain ⟨Q, rfl⟩ := hg R
  -- `(g ∘ f)(g Q) = g (f (g Q))`; and `f (g Q) = (f ∘ g) Q = m • Q` by `hfg`.
  rw [AddMonoidHom.comp_apply]
  have hf : f (g Q) = m • Q := by
    have := congrArg (fun h : E.Point →+ E.Point => h Q) hfg
    simpa [AddMonoidHom.comp_apply, mulByInt_apply] using this
  -- `g (f (g Q)) = g (m • Q) = m • g Q`, and the RHS `[m] (g Q) = m • g Q`.
  rw [hf, g.map_zsmul, mulByInt_apply]

/-- **Right-cancellation of a surjective additive point endomorphism (Silverman II.2.3, equality
form).**  If `g : E.Point →+ E.Point` is **surjective** and two maps `f₁, f₂` agree after
post-composition with `g` (i.e. `f₁ ∘ g = f₂ ∘ g`), then `f₁ = f₂`.  This is the abstract content of
Silverman's *right-cancellation of a nonconstant isogeny* (II.2.3): a nonconstant isogeny is
surjective on geometric points, hence right-cancellable.  It is the cancellation step of the
**dual-isogeny uniqueness** III.6.1(a) (two maps that both compose with a surjection to give `[m]`
are equal). -/
theorem eq_of_comp_eq_of_surjective {f₁ f₂ g : E.Point →+ E.Point} (hg : Function.Surjective g)
    (h : f₁.comp g = f₂.comp g) : f₁ = f₂ := by
  ext a
  obtain ⟨b, rfl⟩ := hg a
  have := congrArg (fun k : E.Point →+ E.Point => k b) h
  simpa [AddMonoidHom.comp_apply] using this

/-- **Silverman III.6.2(a) via right-cancellation: `α̂ ∘ α = [deg α]` (`finrank` exponent).**

`(α.picDual …).comp α.toAddMonoidHom = [finrank R R]`, derived from the III.6.1 target
`α ∘ α̂ = [finrank R R]` (`toAddMonoidHom_comp_picDual`, needing the III.3.4 naturality `hnat`)
by **right-cancelling the nonconstant `α̂ = picDual`** — exactly Silverman's III.6.2(a) argument.
The cancellation input is `hsurj : Function.Surjective (α.picDual …)` (the surjectivity of `α̂` on
points, automatic over `K̄` by III.4.10a), which **replaces** the opaque reverse-order class
identity `hother`.  Both `hnat` and `hsurj` are dischargeable per isogeny (and unconditional over
`K̄`). -/
theorem picDual_comp_toAddMonoidHom_of_surjective (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hsurj : Function.Surjective (α.picDual ch hinj hfin)) :
    (α.picDual ch hinj hfin).comp α.toAddMonoidHom =
      (mulByInt E (letI := ch.toAlgebra;
        ((@Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule : ℕ) :
          ℤ))).toAddMonoidHom :=
  -- `α ∘ α̂ = [m]` is `toAddMonoidHom_comp_picDual` (III.6.1, given `hnat`); right-cancel `α̂`.
  comp_eq_mulByInt_of_comp_eq_of_surjective _ hsurj
    (toAddMonoidHom_comp_picDual ch hinj hfin hnat)

/-- **Silverman III.6.2(a) via right-cancellation: `α̂ ∘ α = [deg α]` (`α.degree` exponent).**

The `α.degree` form of `picDual_comp_toAddMonoidHom_of_surjective`, obtained by additionally
carrying the fraction-field tower witness `(S, S', …)` for the degree bridge
`degree_eq_finrank_coordinateRing_of_tower_eq`. -/
theorem picDual_comp_toAddMonoidHom_of_surjective_degree (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hsurj : Function.Surjective (α.picDual ch hinj hfin))
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree) :
    (α.picDual ch hinj hfin).comp α.toAddMonoidHom =
      (mulByInt E (α.degree : ℤ)).toAddMonoidHom := by
  rw [picDual_comp_toAddMonoidHom_of_surjective ch hinj hfin hnat hsurj]
  congr 2
  exact_mod_cast (α.degree_eq_finrank_coordinateRing_of_tower_eq ch S S' hSR hS'FF).symm

/-! ### Silverman III.6.1(a) dual *uniqueness*: `α̂` is the unique point map with `δ ∘ α = [deg α]`

Silverman III.6.1(a)/III.6.2 states the dual is **unique**: `φ̂` is the *only* `δ` with
`δφ = [deg φ]`.  The proof is right-cancellation of the surjective (nonconstant) `φ`.  We give the
point-map form:
from `(picDual α) ∘ α = [deg α]` (the shipped `picDual_comp_toAddMonoidHom_of_surjective`) and any
hypothetical `β` with `β ∘ α = [deg α]`, the surjection `α` cancels on the right to force
`picDual α = β`.  Specialising `β` to the κ-transport of a *shipped* dual isogeny (e.g. the
Verschiebung `V` of Frobenius `π`, with `V ∘ π = [q]` from `IsDualOf V π`) **identifies `picDual π`
with `V`** — the milestone "Pic⁰ dual of Frobenius = Verschiebung". -/

/-- **Silverman III.6.1(a) dual uniqueness: `α̂ = β` for any point map `β` with `β ∘ α = [deg α]`.**

If a point endomorphism `β : E.Point →+ E.Point` satisfies `β ∘ α = [deg α]` (the *defining*
property of the dual, here in the `finrank` exponent form `[finrank R R]`), and `α` is
**surjective** on points, then `β` agrees with the Pic⁰ dual `α̂ = picDual` (as point maps):
`α.picDual … = β`.

This is the **uniqueness** half of Silverman III.6.1 — the dual is the *unique* `δ` with
`δα = [deg α]` — obtained by right-cancelling the surjective `α` from
`(picDual α) ∘ α = [deg α] = β ∘ α` (`eq_of_comp_eq_of_surjective`).  The first composite is
`picDual_comp_toAddMonoidHom_of_surjective` (needs the III.3.4 naturality `hnat` and surjectivity of
`picDual`); the cancellation needs `α` surjective on points (automatic over `K̄` by III.4.10a).  All
three inputs are dischargeable per isogeny (and unconditional over `K̄`). -/
theorem picDual_eq_of_comp_toAddMonoidHom_eq (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (α.picDual ch hinj hfin))
    (hsurjα : Function.Surjective α.toAddMonoidHom)
    {β : E.Point →+ E.Point}
    (hβ : β.comp α.toAddMonoidHom =
      (mulByInt E (letI := ch.toAlgebra;
        ((@Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule : ℕ) :
          ℤ))).toAddMonoidHom) :
    α.picDual ch hinj hfin = β :=
  -- `(picDual α) ∘ α = [m] = β ∘ α`; right-cancel the surjective `α`.
  eq_of_comp_eq_of_surjective hsurjα
    ((picDual_comp_toAddMonoidHom_of_surjective ch hinj hfin hnat hsurjDual).trans hβ.symm)

/-- **Silverman III.6.1(a) dual uniqueness, `α.degree` exponent.**  As
`picDual_eq_of_comp_toAddMonoidHom_eq`, with the dual-defining composite written in the
function-field degree form `[α.degree]`; the extra fraction-field tower witness `(S, S', …)` feeds
the degree bridge `degree_eq_finrank_coordinateRing_of_tower_eq`.  Conclusion: `α.picDual … = β`.

This is the form used to conclude **`picDual π = V`** (Frobenius dual = Verschiebung): take
`α := π` (`degree = #K = q`), `β := V.toAddMonoidHom`, and `hβ` from `IsDualOf V π` (whose first
component `V ∘ π = [q]` becomes `V.toAddMonoidHom.comp π.toAddMonoidHom = [q]` via
`Isogeny.comp_toAddMonoidHom`). -/
theorem picDual_eq_of_comp_toAddMonoidHom_eq_degree (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (α.picDual ch hinj hfin))
    (hsurjα : Function.Surjective α.toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree)
    {β : E.Point →+ E.Point}
    (hβ : β.comp α.toAddMonoidHom = (mulByInt E (α.degree : ℤ)).toAddMonoidHom) :
    α.picDual ch hinj hfin = β :=
  eq_of_comp_eq_of_surjective hsurjα
    ((picDual_comp_toAddMonoidHom_of_surjective_degree ch hinj hfin hnat hsurjDual
      S S' hSR hS'FF).trans hβ.symm)

/-! #### Non-circular `picDual` of a *single* isogeny whose degree is independently known

The III.6.1(a) uniqueness `picDual_eq_of_comp_toAddMonoidHom_eq_degree` identifies `picDual α` with
any point map `δ` satisfying `δ ∘ α = [deg α]` — **non-circularly whenever `deg α` is known
independently** of the Pic⁰ chain.  Two such cases, used to seed the dual algebra for `rπ − s`:

* **`picDual π = V`** (Frobenius dual = Verschiebung), where `deg π = #K = q` is shipped
  (`frobeniusIsog_degree`) and `V ∘ π = [q]` comes from `IsDualOf V π`.
* **`picDual [n] = [n]`** (scalar self-dual, III.6.2(b)/(d)), where `deg [n] = n²` and
  `[n] ∘ [n] = [n²]` are shipped (`mulByInt_degree`, `mulByInt_comp_eq_mul`).

Both are genuinely non-circular: the degree of a *single* Frobenius / scalar is shipped, unlike
`deg(rπ − s)` (which is the Route-C conclusion).  They are the seeds for the dual-additivity step
`picDual(rπ − s) = rV − s` — whose *combination* nonetheless needs III.6.2(c) (see the note in
`RouteCGeometric.lean`). -/

/-- **`picDual α = δ` when `δ ∘ α = [d]` and `α.degree = d` (degree given as data, non-circular).**

The III.6.1(a) uniqueness specialised to an *explicit integer degree* `d`: if `α.degree = d` (an
**independently-shipped** degree, e.g. `frobeniusIsog_degree`, `mulByInt_degree`) and a point map
`δ` satisfies `δ ∘ α = [d]`, then `picDual α = δ`.  This is the non-circular seed form (it does not
route through the Pic⁰ push-pull degree, only through the *given* `d`). -/
theorem picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (α.picDual ch hinj hfin))
    (hsurjα : Function.Surjective α.toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree)
    {d : ℤ} (hdeg : (α.degree : ℤ) = d)
    {δ : E.Point →+ E.Point}
    (hδ : δ.comp α.toAddMonoidHom = (mulByInt E d).toAddMonoidHom) :
    α.picDual ch hinj hfin = δ :=
  picDual_eq_of_comp_toAddMonoidHom_eq_degree ch hinj hfin hnat hsurjDual hsurjα S S' hSR hS'FF
    (by rw [hdeg]; exact hδ)

/-- **`picDual(r • α) = r • α̂` (route-2 dual-of-`zsmul`, NON-circular).**

The III.6.2(b) dual-of-composition `(φ∘ψ)^ = ψ̂∘φ̂` specialised to `r • α = [r] ∘ α` gives
`picDual(r • α) = α̂ ∘ [r] = r • α̂`.  We obtain it from the III.6.1(a) uniqueness
`picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq` with the **independently-known** degree
`deg(r • α) = deg α · r²` (`Isogeny.zsmul_degree` / `mulByInt_degree`) and the composite
`(r • δ) ∘ (r • α) = r² • (δ ∘ α) = r² • [deg α] = [r² · deg α]`, where `δ` is the dual value of `α`
(any point map with `δ ∘ α = [deg α]`, e.g. the κ-transport of a shipped `IsDualOf` partner).

This is **non-circular**: it routes only through the *given* degree `deg α` (independently shipped
for a single Frobenius / scalar / `α`), never through the Pic⁰ push-pull degree of `r • α`.  It is
the generic engine behind the Route-C seed `picDual(rπ) = rV` (take `α = π`, `δ = V`,
`deg π = #K = q`).

Residuals: the per-`(r • α)` CoordHom data (`chr` + the two surjectivities + tower `(S, S')`),
exactly as the single-isogeny seeds. -/
theorem picDual_zsmul_eq_zsmul_of_comp_eq
    {α : Isogeny E E} (r : ℤ) (hr : r ≠ 0)
    (chr : (α.zsmul r).CoordHom)
    (hinjr : Function.Injective chr.toAlgHom)
    (hfinr : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ chr.toAlgebra.toModule)
    (hnatr : (α.zsmul r).Naturality chr hinjr hfinr)
    (hsurjDualr : Function.Surjective ((α.zsmul r).picDual chr hinjr hfinr))
    (hsurjr : Function.Surjective (α.zsmul r).toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ chr.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = (α.zsmul r).degree)
    {δ : E.Point →+ E.Point}
    (hδ : δ.comp α.toAddMonoidHom = (mulByInt E (α.degree : ℤ)).toAddMonoidHom) :
    (α.zsmul r).picDual chr hinjr hfinr = r • δ := by
  -- `deg(r • α) = deg α · r²`, an independently-known integer.
  have hdeg : (((α.zsmul r).degree : ℤ)) = (α.degree : ℤ) * r ^ 2 := by
    rw [Isogeny.zsmul_degree, mulByInt_degree E r hr]
    push_cast
    rw [Int.toNat_of_nonneg (sq_nonneg r)]
  -- The composite `(r • δ) ∘ (r • α) = [r² · deg α]` on points, from `δ ∘ α = [deg α]` scaled.
  have hδα : ∀ P : E.Point, δ (α.toAddMonoidHom P) = (α.degree : ℤ) • P := by
    intro P
    have := DFunLike.congr_fun hδ P
    simpa only [AddMonoidHom.comp_apply, mulByInt_apply] using this
  have hcomp : (r • δ).comp (α.zsmul r).toAddMonoidHom =
      (mulByInt E ((α.degree : ℤ) * r ^ 2)).toAddMonoidHom := by
    ext P
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, Isogeny.zsmul_apply, mulByInt_apply]
    -- `r • δ (r • α P) = r • (r • δ (α P)) = r² • (deg α • P) = (deg α · r²) • P`.
    rw [map_zsmul, hδα P, smul_smul, smul_smul]
    congr 1
    ring
  exact picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq chr hinjr hfinr hnatr hsurjDualr
    hsurjr S S' hSR hS'FF hdeg hcomp

/-- **`picDual(r • α) = r • α̂` from a shipped `IsDualOf` partner (route-2 seed, `IsDualOf` form).**

As `picDual_zsmul_eq_zsmul_of_comp_eq`, but taking the dual value of `α` in the *full-isogeny*
`IsDualOf δ_isog α` form (`δ_isog ∘ α = [deg α]`), which is how the Route-C Vieta bundle supplies it
(e.g. `IsDualOf V π`).  Concludes `picDual(r • α) = r • δ_isog` at the point-map level. -/
theorem picDual_zsmul_eq_zsmul_of_isDual
    {α δ_isog : Isogeny E E} (r : ℤ) (hr : r ≠ 0)
    (h_isDual : δ_isog.comp α = mulByInt E (α.degree : ℤ))
    (chr : (α.zsmul r).CoordHom)
    (hinjr : Function.Injective chr.toAlgHom)
    (hfinr : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ chr.toAlgebra.toModule)
    (hnatr : (α.zsmul r).Naturality chr hinjr hfinr)
    (hsurjDualr : Function.Surjective ((α.zsmul r).picDual chr hinjr hfinr))
    (hsurjr : Function.Surjective (α.zsmul r).toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ chr.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = (α.zsmul r).degree) :
    (α.zsmul r).picDual chr hinjr hfinr = r • δ_isog.toAddMonoidHom := by
  refine picDual_zsmul_eq_zsmul_of_comp_eq r hr chr hinjr hfinr hnatr hsurjDualr hsurjr
    S S' hSR hS'FF ?_
  rw [← Isogeny.comp_toAddMonoidHom, h_isDual]

/-- **III.8 trace-relation reduction: `α̂ = δ` from same-trace witnesses (point maps).**

The Silverman III.8 trace relation `α + α̂ = [tr α]` *determines* `α̂` once a candidate point map
`δ` satisfies the *same* relation `α + δ = [tr α]`: subtract `α` to get `α̂ = [tr α] − α = δ`.  This
is a pure point-group cancellation (no degree, no uniqueness, **non-circular**).

It is the final algebraic step of the Route-C dual-additivity output `picDual(rπ−s) = rV − s`: with
`α = rπ − s`, the irreducible input `htrace_dual` is III.8 for `α` (equivalently III.6.2(c)
additivity, since `tr(rπ−s) = r·t − 2s`), while the candidate identity `htrace_delta`
(`α + (rV − s) = [r·t − 2s]`) is derived *non-circularly* from the shipped `π + V = [t]`.  This
lemma performs the subtraction generically. -/
theorem picDual_eq_of_trace_relations (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (tr : ℤ) {δ : E.Point →+ E.Point}
    (htrace_dual : α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E tr).toAddMonoidHom)
    (htrace_delta : α.toAddMonoidHom + δ = (mulByInt E tr).toAddMonoidHom) :
    α.picDual ch hinj hfin = δ := by
  ext P
  have hd := DFunLike.congr_fun htrace_dual P
  have he := DFunLike.congr_fun htrace_delta P
  simp only [AddMonoidHom.add_apply, mulByInt_apply] at hd he
  -- `α P + α̂ P = tr • P = α P + δ P` ⟹ `α̂ P = δ P` (left-cancel `α P`).
  exact add_left_cancel (hd.trans he.symm)

/-- **`[r·t − 2s] − (r·π − s) = r·V − s` from `π + V = [t]` (the candidate trace half, point maps).**

The point-map identity `(r·π − s) + (r·V − s) = [r·t − 2s]` for abstract endomorphisms `π, V` of
`E.Point` satisfying `π + V = [t]` (the Frobenius trace relation).  This is the **non-circular** half
of the Route-C dual-additivity output: pointwise
`r·π P − s·P + r·V P − s·P = r·(π P + V P) − 2s·P = r·(t·P) − 2s·P = (r·t − 2s)·P`.

It carries no `picDual` and no degree — pure point-group algebra from `hsum` — and is the candidate
identity `htrace_delta` consumed by `picDual_eq_of_trace_relations` (with `δ = r·V − s`). -/
theorem smul_sub_add_smul_sub_eq_mulByInt
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hsum : π + V = (mulByInt E t).toAddMonoidHom) :
    (r • π - s • (AddMonoidHom.id _)) + (r • V - s • (AddMonoidHom.id _)) =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom := by
  ext P
  have hsum_P := DFunLike.congr_fun hsum P
  simp only [AddMonoidHom.add_apply, mulByInt_apply] at hsum_P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, mulByInt_apply]
  -- `r • π P = r • (t • P − V P) = (r·t)•P − r•V P`, then `abel`.
  have hrπ : r • π P = (r * t) • P - r • V P := by
    have hπ : π P = t • P - V P := by rw [← hsum_P]; abel
    rw [hπ, smul_sub, smul_smul]
  rw [hrπ, sub_zsmul, mul_zsmul, mul_zsmul]
  abel

/-- **III.6.2(c) dual-additivity output `picDual α = r·V − s` (generic `rπ − s` form, point maps).**

For an endomorphism `α` of `E` whose **point map** has the `r·π − s` shape (`hbeta`) where `π, V`
are abstract point endomorphisms with `π + V = [t]` (`hsum`, the Frobenius trace relation), the
Pic⁰ dual `picDual α` equals `r·V − s` — *provided* the Silverman III.8 trace relation for `α`,
`α + picDual α = [r·t − 2s]` (`htrace_dual`), holds.

`htrace_dual` is the **single irreducible residual** (Silverman III.8 for `α`, equivalently
III.6.2(c) additivity since `tr α = r·t − 2s`); everything else — the candidate trace half
`smul_sub_add_smul_sub_eq_mulByInt` — is **non-circular** from `hsum`.  This is the engine that
discharges the Route-C `hpicval` (take `α = rπ − s`, `π = π.toAddMonoidHom`, `V = V.toAddMonoidHom`;
`hbeta` is the `rfl`-true `genuineIsogSmulSub_toAddMonoidHom`-shape and `hsum` the shipped
`π + V = [t]`).  The per-piece `picDual` values `picDual π = V`, `picDual(rπ) = rV`,
`picDual [n] = [n]` (the non-circular seeds) are exactly what `htrace_dual` decomposes into. -/
theorem picDual_eq_smul_sub_of_sum_trace (ch : α.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom)
    (htrace_dual : α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom) :
    α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _) := by
  refine picDual_eq_of_trace_relations ch hinj hfin (r * t - 2 * s) htrace_dual ?_
  rw [hbeta]
  exact smul_sub_add_smul_sub_eq_mulByInt r s t hsum

/-- **Silverman III.6.2(a): `α̂ ∘ α = [deg α]` on the point group (`finrank` exponent).**

`(α.picDual …).comp α.toAddMonoidHom = [finrank R R]`, the companion composition order, under the
III.3.4 naturality witness `hnat` **and** the reverse-order class identity
`hother : classMap (classNorm c) = c ^ finrank` (= `φ* ∘ φ_* = [deg]`, Silverman III.6.2(a); the
honest separate ingredient — see the section note for why it is not derivable from
`classNorm_comp_classMap`).  Both witnesses are dischargeable per isogeny.

(See `picDual_comp_toAddMonoidHom_of_surjective` for the route that derives this from the *forward*
order by right-cancelling `α̂`, replacing `hother` with surjectivity of `picDual` — Silverman's own
III.6.2(a) argument.) -/
theorem picDual_comp_toAddMonoidHom (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hnat : α.Naturality ch hinj hfin)
    (hother : ∀ c : ClassGroup E.CoordinateRing,
      (α.classMap ch hinj hfin) ((α.classNorm ch hinj hfin) c) =
        c ^ (letI := ch.toAlgebra;
          @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)) :
    (α.picDual ch hinj hfin).comp α.toAddMonoidHom =
      (mulByInt E (letI := ch.toAlgebra;
        ((@Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule : ℕ) :
          ℤ))).toAddMonoidHom := by
  -- Replace the point map by `picPushforward` (III.3.4 naturality); both are `classTransport`s.
  rw [(toAddMonoidHom_eq_picPushforward_iff ch hinj hfin).mpr hnat]
  exact classTransport_comp_eq (α.classNorm ch hinj hfin) (α.classMap ch hinj hfin) _ hother

end HasseWeil.Isogeny

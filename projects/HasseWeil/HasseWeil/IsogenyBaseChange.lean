import HasseWeil.Basic
import HasseWeil.Curves.BaseChange
import HasseWeil.Curves.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finite.Basic

/-!
# Base-change of isogenies (witness-parametric API)

For an isogeny `α : Isogeny W₁ W₂` over a field `F` and an `F`-algebra
`L` (typically `L = AlgebraicClosure F`), this file provides the
witness-parametric API for the base-changed isogeny
`α_L : Isogeny (W₁.baseChange L) (W₂.baseChange L)`.

The full construction of `α_L` from `α` (= `Isogeny.baseChange`) requires
careful wiring through the project's existing CurveMap/CoordHom
base-change machinery (`HasseWeil/Curves/CurveMapBaseChange.lean`) plus
`IsLocalization.lift` for the function-field side. This file exposes:

* `HasseWeil.Isogeny.mkBaseChange` — explicit constructor taking the
  base-changed pullback and toAddMonoidHom as inputs (~5 LOC). Useful
  when the caller already has these from another route (e.g., for
  Frobenius / Verschiebung where the formulas are explicit).

* `HasseWeil.Isogeny.degree_eq_of_finrank_eq` — degree-preservation
  packaged via the `Module.finrank` equality (the finrank witness
  follows from `Module.finrank_baseChange` once the function-field
  base-change is identified with a tensor extension).

These pieces let the alg-closure-descend strategy proceed downstream
once a concrete `α_L` is in hand for the relevant `α` (Frobenius,
Verschiebung, ℤ[π] elements).

## References

* Reviewer round-4 reframe (2026-05-13): use `[IsAlgClosed]` internally
  via base-change to `AlgebraicClosure F`; descend the integer
  `qf_nonneg` inequality.
-/

namespace HasseWeil

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
variable (L : Type*) [Field L] [Algebra F L] [DecidableEq L]

/-- **Explicit constructor for a base-changed isogeny**: given
    the base-changed pullback (an `L`-algebra hom on the base-changed
    function fields) and toAddMonoidHom (a group hom on the base-changed
    points), package them as an `Isogeny`.

    Used when the caller has both pieces from an explicit construction
    (e.g., Frobenius's pullback is the obvious extension to `L[X]`; its
    point map is the L-power Frobenius). -/
noncomputable def mkBaseChange
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (pullback_L : (W₂.baseChange L).toAffine.FunctionField →ₐ[L]
                  (W₁.baseChange L).toAffine.FunctionField)
    (toAddMonoidHom_L : (W₁.baseChange L).toAffine.Point →+
                        (W₂.baseChange L).toAffine.Point) :
    HasseWeil.Isogeny (W₁.baseChange L) (W₂.baseChange L) :=
  { pullback := pullback_L
    toAddMonoidHom := toAddMonoidHom_L }

@[simp] theorem mkBaseChange_pullback
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (pullback_L : (W₂.baseChange L).toAffine.FunctionField →ₐ[L]
                  (W₁.baseChange L).toAffine.FunctionField)
    (toAddMonoidHom_L : (W₁.baseChange L).toAffine.Point →+
                        (W₂.baseChange L).toAffine.Point) :
    (mkBaseChange L pullback_L toAddMonoidHom_L).pullback = pullback_L := rfl

@[simp] theorem mkBaseChange_toAddMonoidHom
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (pullback_L : (W₂.baseChange L).toAffine.FunctionField →ₐ[L]
                  (W₁.baseChange L).toAffine.FunctionField)
    (toAddMonoidHom_L : (W₁.baseChange L).toAffine.Point →+
                        (W₂.baseChange L).toAffine.Point) :
    (mkBaseChange L pullback_L toAddMonoidHom_L).toAddMonoidHom =
      toAddMonoidHom_L := rfl

/-- **Degree-preservation under base-change (witness-parametric)**: given
    a base-changed isogeny `α_L` and a `Module.finrank` equality witness
    relating `K(W_L)`-finranks to `K(W)`-finranks, the isogeny degrees agree.

    The finrank witness is the substantive content: it follows from
    mathlib's `Module.finrank_baseChange` once one identifies
    `K(W_L)` with `K(W) ⊗_F L` (the function-field base-change as a
    tensor extension). -/
theorem degree_eq_of_finrank_eq
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (α : HasseWeil.Isogeny W₁ W₂)
    (α_L : HasseWeil.Isogeny (W₁.baseChange L) (W₂.baseChange L))
    (h_finrank :
      @Module.finrank (W₂.baseChange L).toAffine.FunctionField
          (W₁.baseChange L).toAffine.FunctionField _ _ α_L.toAlgebra.toModule =
        @Module.finrank W₂.FunctionField W₁.FunctionField _ _
          α.toAlgebra.toModule) :
    α_L.degree = α.degree :=
  h_finrank

end Isogeny

/-! ### T-III-6-002 (dual via Pic⁰) — witness-parametric API

The dual isogeny construction via Pic⁰ functoriality (Silverman III.6.2)
requires a Pic⁰ pullback hom + the pushforward-pullback identity
`α_∗ ∘ α* = [deg α]` on Pic⁰. This file provides the witness-parametric
glue: given those data + `picZeroIsoE` (T-III-3-004) on both sides, the
dual isogeny is determined.

For the alg-closure-descend strategy, all of these inputs live over
`L = AlgebraicClosure F` where `[IsAlgClosed L]` holds. The qf_nonneg
descent then pulls back through `degree_eq_of_finrank_eq`. -/

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **Witness-parametric dual isogeny construction**: given an isogeny
    `α : Isogeny W W` (an endomorphism), its pushforward `α_∗` on Pic⁰,
    a candidate "pullback" `α_*_pic` on Pic⁰, and the identity
    `α_*_pic ∘ α_∗ = [deg α]` on Pic⁰, plus the iso `Pic⁰ ≃+ W.Point`
    (T-III-3-004), construct an `IsDualOf` witness for the resulting
    point-level dual `β`.

    The candidate `β` is `iso ∘ α_*_pic ∘ iso.symm` (the conjugate of
    the pullback by the iso). The dual property follows mechanically
    from the Pic⁰ identity + iso compatibility.

    This is T-III-6-002 over `W` (typically used with `W = W₀.baseChange L`
    over the algebraic closure).

    The function-field pullback of the dual is NOT synthesizable at the Pic⁰
    level (the Pic⁰ data are point-level only), so it is supplied explicitly
    as `dual_pullback`. Callers pass the genuine pullback of the candidate
    dual isogeny (e.g. `α_dual.pullback` in `dualViaPicZero`). -/
noncomputable def dualOfPicZeroPullback
    (Pic0_W : Type*) [AddCommGroup Pic0_W]
    (iso : Pic0_W ≃+ W.Point)
    (_α : HasseWeil.Isogeny W W)
    (_α_pushforward : Pic0_W →+ Pic0_W)
    (α_pullback : Pic0_W →+ Pic0_W)
    (dual_pullback : W.FunctionField →ₐ[F] W.FunctionField) :
    HasseWeil.Isogeny W W :=
  -- The candidate dual β at point level: conjugate α_pullback by iso.
  -- The function-field pullback is the genuine `dual_pullback` supplied by
  -- the caller; the toAddMonoidHom is the Pic⁰ conjugate.
  { pullback := dual_pullback
    toAddMonoidHom := iso.toAddMonoidHom.comp
      (α_pullback.comp iso.symm.toAddMonoidHom) }

/-- The dual property `dualOf.toAddMonoidHom ∘ α.toAddMonoidHom = [deg α]`
    follows from the Pic⁰ identity hypothesis. (Witness-parametric.) -/
theorem dualOfPicZeroPullback_property
    (Pic0_W : Type*) [AddCommGroup Pic0_W]
    (iso : Pic0_W ≃+ W.Point)
    (α : HasseWeil.Isogeny W W)
    (α_pushforward : Pic0_W →+ Pic0_W)
    (α_pullback : Pic0_W →+ Pic0_W)
    (dual_pullback : W.FunctionField →ₐ[F] W.FunctionField)
    (h_pushforward_compat : ∀ P : W.Point,
      α_pushforward (iso.symm P) = iso.symm (α.toAddMonoidHom P))
    (h_pic_id : α_pullback.comp α_pushforward =
      (AddMonoidHom.id Pic0_W).comp (α.degree • AddMonoidHom.id Pic0_W)) :
    ∀ P : W.Point,
      (dualOfPicZeroPullback Pic0_W iso α α_pushforward α_pullback
          dual_pullback).toAddMonoidHom
        (α.toAddMonoidHom P) = α.degree • P := by
  intro P
  change iso.toAddMonoidHom (α_pullback (iso.symm.toAddMonoidHom (α.toAddMonoidHom P)))
    = α.degree • P
  -- Use the compatibility: iso.symm (α P) = α_pushforward (iso.symm P)
  rw [show iso.symm.toAddMonoidHom (α.toAddMonoidHom P) =
      α_pushforward (iso.symm P) from (h_pushforward_compat P).symm]
  -- α_pullback (α_pushforward _) = (deg α) • _ via h_pic_id
  rw [show α_pullback (α_pushforward (iso.symm P)) =
      (α_pullback.comp α_pushforward) (iso.symm P) from rfl, h_pic_id]
  simp [AddMonoidHom.smul_apply]

/-! ### §5.4 keystone (III.6.2(c) restricted) — the bound's true bottleneck

For r, s ∈ ℤ, on E.Point we have (over k̄):
  (rV_π - s) ∘ (rπ - s) = qr² - trs + s²    (as End(E))
where q = deg π, t = trace = deg(1+π) - q - 1.

This is the §5.5 Frobenius-plane degree formula's key identity, and it
depends on §5.4 dual additivity restricted to ℤ[π]. The hypotheses
package the trace identity (V_π + π = [t]) and Frobenius-dual identity
(V_π ∘ π = [q]) — both of which are consequences of §5.4 + §5.5 in the
Silverman writeup. -/

theorem cross_compose_zPi_witness
    (π V_π : HasseWeil.Isogeny W W)
    (q : ℕ) (t : ℤ)
    -- Trace identity at the point level:
    (h_trace : ∀ P : W.Point, V_π.toAddMonoidHom P + π.toAddMonoidHom P = t • P)
    -- Frobenius dual identity at the point level:
    (h_q : ∀ P : W.Point, V_π.toAddMonoidHom (π.toAddMonoidHom P) = (q : ℤ) • P)
    (r s : ℤ) (P : W.Point) :
    r • V_π.toAddMonoidHom (r • π.toAddMonoidHom P - s • P) -
        s • (r • π.toAddMonoidHom P - s • P) =
      ((q : ℤ) * r^2 - t * r * s + s^2) • P := by
  -- Push `V_π` through the subtraction and scalars, then apply the Frobenius-dual identity.
  rw [(V_π.toAddMonoidHom).map_sub, (V_π.toAddMonoidHom).map_zsmul,
      (V_π.toAddMonoidHom).map_zsmul, h_q P]
  rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  -- Regroup so the two middle `smul` terms share a factor, then collapse them via `h_trace`.
  have group : ∀ (a b c d : W.Point), a - b - (c - d) = a + d - (b + c) := by
    intros; abel
  rw [group, show (r * s) • V_π.toAddMonoidHom P + (s * r) • π.toAddMonoidHom P =
      (r * s) • (V_π.toAddMonoidHom P + π.toAddMonoidHom P) by
    rw [smul_add]; congr 1; rw [mul_comm]]
  rw [h_trace P, smul_smul]
  -- Collect the three `smul` coefficients into one and finish with `ring`.
  rw [show (r * r * (q : ℤ)) • P + (s * s) • P - (r * s * t) • P =
      ((r * r * (q : ℤ)) + (s * s) - (r * s * t)) • P by
    rw [sub_smul, add_smul]]
  congr 1; ring

/-! ### III.6.3 polarisation → qf_nonneg (witness-parametric bridge)

The §5.5 polarisation identity says: for r, s ∈ ℤ, there is an isogeny
`α_{r,s} := r·π - s` with `deg α_{r,s} = q·r² - t·r·s + s²`. Combined
with `Isogeny.degree : ℕ` (so the integer cast is `≥ 0`), this discharges
qf_nonneg.

This bridge factors out the substantive content (the polarisation
realisation) from the trivial sign step. -/

/-- **qf_nonneg from polarisation realisation**: if for every (r,s) the
    quadratic form `q·r² - t·r·s + s²` equals the integer degree of some
    isogeny on `W`, then it is non-negative.

    The substantive content is the realisation hypothesis (§5.5 polarisation,
    derived from §5.4 dual additivity = `cross_compose_zPi_witness` plus the
    dual-property side); the conclusion is then mechanical from
    `Isogeny.degree : ℕ`. -/
theorem qf_nonneg_from_polarisation_witness
    (q : ℕ) (t : ℤ)
    (h_realised : ∀ r s : ℤ, ∃ α : HasseWeil.Isogeny W W,
      ((q : ℤ) * r^2 - t * r * s + s^2) = (α.degree : ℤ))
    (r s : ℤ) :
    0 ≤ (q : ℤ) * r^2 - t * r * s + s^2 := by
  obtain ⟨α, hα⟩ := h_realised r s
  rw [hα]
  exact Int.natCast_nonneg _

/-! ### Connector: dualOfPicZeroPullback feeds `h_dual_comp` of `degree_quadratic_closed`

The Hasse-bound polarisation chain in `DegreeQuadraticForm.degree_quadratic_closed`
consumes a hypothesis

  `h_dual_comp : ∀ P, α_dual.toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P`

which is exactly III.6.1 (β̂ ∘ β = [deg β]) at the `AddMonoidHom` level. Our
`dualOfPicZeroPullback_property` produces this with the ℕ-scalar on the RHS;
the connector below converts to the ℤ-scalar form expected by the consumer. -/

theorem h_dual_comp_from_picZeroPullback_witness
    (Pic0_W : Type*) [AddCommGroup Pic0_W]
    (iso : Pic0_W ≃+ W.Point)
    (α : HasseWeil.Isogeny W W)
    (α_pushforward α_pullback : Pic0_W →+ Pic0_W)
    (dual_pullback : W.FunctionField →ₐ[F] W.FunctionField)
    (h_pushforward_compat : ∀ P : W.Point,
      α_pushforward (iso.symm P) = iso.symm (α.toAddMonoidHom P))
    (h_pic_id : α_pullback.comp α_pushforward =
      (AddMonoidHom.id Pic0_W).comp (α.degree • AddMonoidHom.id Pic0_W)) :
    ∀ P : W.Point,
      (dualOfPicZeroPullback Pic0_W iso α α_pushforward α_pullback
          dual_pullback).toAddMonoidHom
        (α.toAddMonoidHom P) = (α.degree : ℤ) • P := by
  intro P
  have h := dualOfPicZeroPullback_property Pic0_W iso α α_pushforward α_pullback
    dual_pullback h_pushforward_compat h_pic_id P
  rw [h, ← Nat.cast_smul_eq_nsmul ℤ]

/-! ### Pic⁰ pullback functoriality — UNCONDITIONAL discharge over k̄

For an arbitrary endomorphism α : Isogeny W W and a Pic⁰ ≅ E iso, the
Pic⁰-level pushforward and pullback can be defined as iso conjugates of
α and its dual α_dual respectively. The compatibility identities
`h_pushforward_compat` and `h_pic_id` then become unconditional theorems
(no `_witness` suffix) — they follow from the iso being a group equiv
plus the dual-composition identity at the point level.

Key consumers:
* For α = Frobenius over k̄, α_dual = Verschiebung (shipped as
  `verschiebungIsog_of_witness_isDualOf_frobenius`); the compatibility
  identities then plug into the qf_nonneg cascade.
* For arbitrary α with a known dual, the lemmas in this section produce
  the Pic⁰-level inputs `dualOfPicZeroPullback` consumes. -/

variable {Pic0 : Type*} [AddCommGroup Pic0] (iso : Pic0 ≃+ W.Point)

/-- **Pic⁰-level pushforward via iso conjugation**: given the iso `Pic⁰ ≃+ E`,
    transfer α's point-level action to Pic⁰. -/
noncomputable def isogPicPushforward (α : HasseWeil.Isogeny W W) :
    Pic0 →+ Pic0 :=
  iso.symm.toAddMonoidHom.comp (α.toAddMonoidHom.comp iso.toAddMonoidHom)

/-- **Pic⁰-level pullback via iso conjugation by the dual**: given a dual
    α_dual of α at the Isogeny level, transfer α_dual's point-level
    action to Pic⁰ as the pullback. -/
noncomputable def isogPicPullback (α_dual : HasseWeil.Isogeny W W) :
    Pic0 →+ Pic0 :=
  iso.symm.toAddMonoidHom.comp (α_dual.toAddMonoidHom.comp iso.toAddMonoidHom)

/-- **h_pushforward_compat (unconditional)**: the iso-conjugate pushforward
    of `iso.symm P` is `iso.symm (α P)`. Pure algebraic identity from the
    iso being a group equiv. -/
theorem isogPicPushforward_compat (α : HasseWeil.Isogeny W W) (P : W.Point) :
    isogPicPushforward iso α (iso.symm P) = iso.symm (α.toAddMonoidHom P) := by
  change iso.symm (α.toAddMonoidHom (iso (iso.symm P))) = iso.symm (α.toAddMonoidHom P)
  rw [iso.apply_symm_apply]

/-- **h_pic_id (unconditional)**: given that α_dual ∘ α = [deg α] at the
    point level, the composition of iso-conjugate pullback and pushforward
    on Pic⁰ equals scalar multiplication by deg α.

    Pure algebraic consequence of the iso being a group equiv plus the
    point-level dual identity. -/
theorem isogPicPullback_comp_pushforward
    (α α_dual : HasseWeil.Isogeny W W)
    (h_dual : ∀ P : W.Point, α_dual.toAddMonoidHom (α.toAddMonoidHom P) =
      α.degree • P) :
    (isogPicPullback iso α_dual).comp (isogPicPushforward iso α) =
      (AddMonoidHom.id Pic0).comp (α.degree • AddMonoidHom.id Pic0) := by
  ext D
  change iso.symm (α_dual.toAddMonoidHom
        (iso (iso.symm (α.toAddMonoidHom (iso D))))) = _
  rw [iso.apply_symm_apply, h_dual (iso D)]
  change iso.symm (α.degree • iso D) = α.degree • D
  rw [map_nsmul, iso.symm_apply_apply]

/-! ### Frobenius-twist trivialisation over k̄ for E defined over F_p

For E defined over `k = F_p` (the prime field) and base-changed to a
field `L` of characteristic `p`, the Frobenius twist
`(W.baseChange L).frobeniusTwist p` equals `W.baseChange L` definitionally,
because the p-Frobenius restricted to `F_p` is the identity (Fermat's
little theorem) and so commutes with `algebraMap k L`.

This is the foundational lemma for constructing
`frobeniusIsog_baseChange : Isogeny (W.baseChange L) (W.baseChange L)`
when `k = F_p`. The general case (k = F_{p^n}, n > 1) requires either
n iterations of the relative p-Frobenius or a direct q-Frobenius
construction. -/

variable {k : Type*} [Field k] [DecidableEq k]

/-- The p-Frobenius on F_p is the identity (Fermat's little theorem):
    `frobenius (F_p) p = id` as a ring hom. -/
theorem frobenius_eq_id_of_charP_prime (p : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)] :
    (frobenius k p : k →+* k) = RingHom.id k := by
  ext x
  change x ^ p = x
  -- Fermat's little theorem: `x ^ #k = x` and `#k = p`.
  rw [show p = Fintype.card k from (Fact.out : Fintype.card k = p).symm]
  exact FiniteField.pow_card x

/-- For E defined over k = F_p (a prime field) and base-changed to any
    L (of char p), the p-Frobenius twist of E_L equals E_L. -/
theorem frobeniusTwist_baseChange_eq_self_of_charP_prime
    (p : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W : WeierstrassCurve k)
    (L : Type*) [Field L] [Algebra k L] [ExpChar L p] :
    (W.baseChange L).frobeniusTwist p = W.baseChange L := by
  change W.map ((frobenius L p).comp (algebraMap k L)) = W.map (algebraMap k L)
  congr 1
  -- `frobenius L ∘ algebraMap k L = algebraMap k L ∘ frobenius k = algebraMap k L`,
  -- the last step because `frobenius k = id` on the prime field.
  rw [← RingHom.frobenius_comm (algebraMap k L) p,
      show (frobenius k p : k →+* k) = RingHom.id k from
        frobenius_eq_id_of_charP_prime (k := k) p,
      RingHom.comp_id]

/-! ### `frobeniusIsog_baseChange` for E over F_p (n=1 case)

Composes the relative p-Frobenius `frobeniusIsog_relative p (W.baseChange L)`
with the trivial-twist identification (shipped above) to give the p-Frobenius
endomorphism of `W.baseChange L` over k̄ when `k = F_p`.

This unconditionally discharges the Pic⁰ functoriality inputs `h_pic_id`
and `h_pushforward_compat` for Frobenius over k̄ in the n=1 case via
`isogPicPushforward_compat` and `isogPicPullback_comp_pushforward`.

The general n>1 case requires q-Frobenius construction (n iterations of
the relative p-Frobenius); ticketed as future work. -/

/-- **Frobenius isogeny over k̄ for E over F_p**: composes the relative
    p-Frobenius `frobeniusIsog_relative p (W.baseChange L)` with the
    trivial-twist identity to give an endomorphism of `W.baseChange L`. -/
noncomputable def frobeniusIsog_baseChange_charP_prime
    (p : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W : WeierstrassCurve k) [W.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] :
    HasseWeil.Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
  -- The relative Frobenius E_L → E_L^{(p)}, where E_L^{(p)} = E_L by
  -- `frobeniusTwist_baseChange_eq_self_of_charP_prime`.
  -- Use cast via congrArg .toAffine on the type equality.
  cast (by
    congr 2
    exact frobeniusTwist_baseChange_eq_self_of_charP_prime (k := k) p W L)
    (HasseWeil.frobeniusIsog_relative p (W.baseChange L))

/-! ### Concrete h_pushforward_compat discharge for Frobenius over k̄

Plugs `frobeniusIsog_baseChange_charP_prime` into `isogPicPushforward_compat`
to give the unconditional discharge of `h_pushforward_compat` for the
Frobenius case. -/

/-- **Unconditional `h_pushforward_compat` for Frobenius over k̄ (n=1 case)**:
    for E over k = F_p base-changed to L = k̄, the Pic⁰-level pushforward
    by the Frobenius isogeny `frobeniusIsog_baseChange_charP_prime`
    commutes with the canonical iso `Pic⁰ ≃+ E.Point`. Direct application
    of the unconditional `isogPicPushforward_compat`.

    Caller supplies the `iso` (typically `picZeroIsoE_baseChange`) and any
    `Pic0` type (typically `PicProj₀`); this lemma is parametric in those
    so it can be specialised to the canonical iso once the typeclass
    requirements are satisfied. -/
theorem isogPicPushforward_compat_frobenius_baseChange_charP_prime
    (p : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W : WeierstrassCurve k) [W.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    {Pic0_W : Type*} [AddCommGroup Pic0_W]
    (iso : Pic0_W ≃+ (W.baseChange L).toAffine.Point)
    (P : (W.baseChange L).toAffine.Point) :
    isogPicPushforward iso (frobeniusIsog_baseChange_charP_prime p W L)
        (iso.symm P) =
      iso.symm
        ((frobeniusIsog_baseChange_charP_prime p W L).toAddMonoidHom P) :=
  isogPicPushforward_compat iso (frobeniusIsog_baseChange_charP_prime p W L) P

/-! ### `frobeniusTwistIterate` trivialization for E over F_{p^r}

Iterated form of `frobeniusTwist_baseChange_eq_self_of_charP_prime`. For
E defined over k = F_{p^r} (a finite field of cardinality p^r) and
base-changed to L (with ExpChar p), the r-fold iterated p-Frobenius
twist of `(W.baseChange L)` equals `W.baseChange L`, because the r-fold
p-Frobenius on F_{p^r} is the identity (Fermat's). -/

/-- **r-fold iterated Frobenius on F_{p^r} is identity**. Generalizes
`frobenius_eq_id_of_charP_prime` to k = F_{p^r}. Direct from
`FiniteField.pow_card`. -/
theorem iterateFrobenius_eq_id_of_charP_pow (p r : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)] :
    (iterateFrobenius k p r : k →+* k) = RingHom.id k := by
  ext x
  change iterateFrobenius k p r x = x
  rw [iterateFrobenius_def,
      show p ^ r = Fintype.card k from (Fact.out : Fintype.card k = p ^ r).symm]
  exact FiniteField.pow_card x

/-- **`(W.baseChange L).map (iterateFrobenius L p r) = W.baseChange L`**
for E over k = F_{p^r}. Generalizes
`frobeniusTwist_baseChange_eq_self_of_charP_prime` to the iterated
case. -/
theorem frobeniusTwistIterate_baseChange_eq_self_of_charP_pow
    (p r : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W : WeierstrassCurve k)
    (L : Type*) [Field L] [Algebra k L] [ExpChar L p] :
    (W.baseChange L).map (iterateFrobenius L p r) = W.baseChange L := by
  change (W.map (algebraMap k L)).map (iterateFrobenius L p r) = W.map (algebraMap k L)
  rw [WeierstrassCurve.map_map]
  -- `iterateFrobenius L ∘ algebraMap k L = algebraMap k L ∘ iterateFrobenius k = algebraMap k L`,
  -- the last step because the r-fold Frobenius is `id` on `F_{p^r}`.
  rw [← RingHom.iterateFrobenius_comm (algebraMap k L) p r,
      show (iterateFrobenius k p r : k →+* k) = RingHom.id k from
        iterateFrobenius_eq_id_of_charP_pow (k := k) p r,
      RingHom.comp_id]

/-! ### Iterated relative Frobenius isogeny

For a Weierstrass curve `W` over `k` (with `[CharP k p]`), the r-fold
composition of the relative p-Frobenius `frobeniusIsog_relative` gives
an isogeny `W → W.map (iterateFrobenius k p r)`.

Defined recursively on `r`: base case is the identity (after type cast
through `iterateFrobenius_zero`); inductive case composes the (n)-fold
iterate with one more relative p-Frobenius. -/

/-- **r-fold iterated relative Frobenius isogeny**. Composes r copies
of `frobeniusIsog_relative p`, landing in
`W.map (iterateFrobenius k p r)`. -/
noncomputable def frobeniusIsog_relative_iterate (p : ℕ) [hp : Fact p.Prime]
    [ExpChar k p] (W : WeierstrassCurve k) [W.toAffine.IsElliptic] :
    ∀ (r : ℕ), HasseWeil.Isogeny W.toAffine
      (W.map (iterateFrobenius k p r)).toAffine
  | 0 =>
    -- W.map (iterateFrobenius k p 0) = W.map (RingHom.id k) = W
    cast (by
      congr 2
      rw [iterateFrobenius_zero, WeierstrassCurve.map_id])
      (HasseWeil.Isogeny.id W.toAffine)
  | n + 1 =>
    -- prev : Isogeny W (W.map (iter k p n))
    -- next : Isogeny (W.map (iter k p n)) ((W.map (iter k p n)).frobeniusTwist p)
    --      = Isogeny (W.map (iter k p n)) (W.map ((frobenius k p).comp (iter k p n)))
    --      = Isogeny (W.map (iter k p n)) (W.map (iter k p (n+1)))
    cast (by
      congr 2
      change (W.map (iterateFrobenius k p n)).map (frobenius k p) =
        W.map (iterateFrobenius k p (n + 1))
      rw [WeierstrassCurve.map_map]
      congr 1
      have h_iter : iterateFrobenius k p (n + 1) =
          (iterateFrobenius k p 1).comp (iterateFrobenius k p n) := by
        rw [add_comm n 1]
        exact iterateFrobenius_add k p 1 n
      rw [h_iter, iterateFrobenius_one])
      ((HasseWeil.frobeniusIsog_relative p (W.map (iterateFrobenius k p n))).comp
        (frobeniusIsog_relative_iterate p W n))

/-- **q-Frobenius isogeny on `W.baseChange L` for k = F_{p^r}, q = p^r**.
Composes the r-fold iterated relative Frobenius with the trivialization
`(W.baseChange L).map (iterateFrobenius L p r) = W.baseChange L` (which
holds because the r-fold p-Frobenius is identity on F_{p^r} by
Fermat). -/
noncomputable def frobeniusIsog_baseChange_charP_pow
    (p r : ℕ) [hp : Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W : WeierstrassCurve k) [W.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] :
    HasseWeil.Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
  cast (by
    congr 2
    exact frobeniusTwistIterate_baseChange_eq_self_of_charP_pow (k := k) p r W L)
    (frobeniusIsog_relative_iterate p (W.baseChange L) r)

/-! ### T-FROBENIUS-TWIST-EQUIV-SELF — same-field iterated Frobenius is identity

R25h Worker-A Round 3 (2026-05-20). The same-field iterated p-Frobenius
acts as the identity on `W : WeierstrassCurve K` when `K = F_{p^r}`:

```
W.map (iterateFrobenius K p r) = W
```

Direct corollary of the shipped `iterateFrobenius_eq_id_of_charP_pow`
(IsogenyBaseChange.lean:469): under `[Fact (Fintype.card K = p ^ r)]`,
the r-fold p-Frobenius on K is `RingHom.id K`; hence
`W.map (RingHom.id K) = W` via `WeierstrassCurve.map_id`.

**Round-9 D-R9-A-03/04**: shipped at the `[Fact (Fintype.card K = p ^ r)]`
instance shape (matching the existing API). The r=1 corollary is a one-
line specialization.

**Why this matters**: was required for the (now-deleted) T7 stub
`mulByPN_factors_unconditional` in the r > 1 case: identifies
`W.map (iterateFrobenius K p r)` (the codomain of the iterated relative
Frobenius) with `W` itself, allowing a cofactor `ψ : W → W.map (iter...)`
to be re-typed as `ψ : W → W`. (The factorisation shipped via
`qth_root_witness_general`, `Verschiebung/QthRootRouteB.lean`.)

* **Silverman**: III.4 (Frobenius/Verschiebung), II.4 (Frobenius twist).
* **Ticket**: `T-FROBENIUS-TWIST-EQUIV-SELF` (B3 in round-7 priority).
* **R25h Worker-A Round 3**: shipped axiom-clean via the
  `iterateFrobenius_eq_id_of_charP_pow` reduction.
-/

/-- **T-FROBENIUS-TWIST-EQUIV-SELF (curve-level, axiom-clean)**: for
`W : WeierstrassCurve K` over a finite field `K` of cardinality `p^r`,
the r-fold p-Frobenius twist equals `W` itself. Direct corollary of
`iterateFrobenius_eq_id_of_charP_pow` (which says the r-fold p-Frobenius
ring hom on `K = F_{p^r}` is the identity) + `WeierstrassCurve.map_id`. -/
theorem map_iterateFrobenius_eq_self_of_card_eq_pow
    (p r : ℕ) [Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W : WeierstrassCurve k) :
    W.map (iterateFrobenius k p r) = W := by
  rw [show (iterateFrobenius k p r : k →+* k) = RingHom.id k from
      iterateFrobenius_eq_id_of_charP_pow (k := k) p r]
  exact WeierstrassCurve.map_id W

/-- **r = 1 corollary**: for `W : WeierstrassCurve K` over `K = F_p`
(prime-field case), the p-Frobenius twist `W.frobeniusTwist p` equals
`W`. One-line specialization of `map_iterateFrobenius_eq_self_of_card_eq_pow`
at `r := 1` after reducing `iterateFrobenius _ p 1 = frobenius _ p`
(= `W.frobeniusTwist p` by definition). -/
theorem frobeniusTwist_eq_self_of_card_eq_p
    (p : ℕ) [Fact p.Prime]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W : WeierstrassCurve k) :
    W.frobeniusTwist p = W := by
  haveI : Fact (Fintype.card k = p ^ 1) :=
    ⟨by simpa using (Fact.out : Fintype.card k = p)⟩
  have h := map_iterateFrobenius_eq_self_of_card_eq_pow (k := k) p 1 W
  rw [iterateFrobenius_one] at h
  exact h

/-- **T08 (R27)**: in characteristic `p`, the `e`-fold iterated Frobenius is
an isogeny `W → W.iterateFrobeniusTwist p e`.

Wraps the shipped `frobeniusIsog_relative_iterate` (`IsogenyBaseChange.lean:512`)
with the canonical `iterateFrobeniusTwist` name. The codomain's `IsElliptic`
instance follows from mathlib's `(W.map f).IsElliptic` propagation.

Reference: Silverman III.4 Example 4.6 (page 70).

The witness shape `Σ' (_isElliptic : ...), Isogeny ...` lets the caller
destructure into the IsElliptic witness and the isogeny in one bundle. -/
noncomputable def iteratedFrobenius_isog
    {K : Type*} [Field K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (e : ℕ) :
    Σ' (_isElliptic : (W.iterateFrobeniusTwist p e).toAffine.IsElliptic),
      HasseWeil.Isogeny W.toAffine (W.iterateFrobeniusTwist p e).toAffine :=
  haveI : ExpChar K p := ExpChar.prime Fact.out
  haveI : (W.map (iterateFrobenius K p e)).IsElliptic := inferInstance
  haveI : (W.iterateFrobeniusTwist p e).IsElliptic :=
    show (W.map (iterateFrobenius K p e)).IsElliptic from inferInstance
  ⟨show (W.map (iterateFrobenius K p e)).toAffine.IsElliptic from inferInstance,
   frobeniusIsog_relative_iterate p W e⟩

end Isogeny

end HasseWeil

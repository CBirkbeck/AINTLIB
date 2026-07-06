import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The group schemes `μ_N` and `ℤ/N` over a base

Two basic finite flat group schemes, needed as the target of the Weil pairing (`μ_N`) and as
the source of Drinfeld generators (`ℤ/N`, KM 1.4.4(5)).

* `μ_N = Spec ℤ[T]/(Tᴺ − 1)`, the scheme of `N`-th roots of unity; over a base `S` its
  `T`-points are `{a ∈ Γ(T, O_T) : aᴺ = 1}` (KM 1.12 "Roots of unity").
* The constant group scheme `(ℤ/N)_S`, the disjoint union of `N` copies of `S`
  (KM 1.4.4(5): "the constant `S`-scheme `ℤ/Nℤ`").

Both are finite locally free of rank `N` over the base, étale exactly when `N` is invertible;
`μ_N` and `ℤ/N` are Cartier dual (KM 2.8-adjacent; statement in `WeilPairing/Basic.lean`).

The group-object structures are registered constructions (DS3): the comultiplication
`T ↦ T ⊗ T` is elementary, but wiring it through the `Over S`/`GrpObj` API is genuine work
(ticket `T-B2`), and nothing downstream may assume unstated properties of them.
-/

open AlgebraicGeometry CategoryTheory Limits Polynomial

universe u

noncomputable section

namespace ModularCurves

/-- The coordinate ring `ℤ[T]/(Tᴺ − 1)` of `μ_N`. -/
def muNRing (N : ℕ) : CommRingCat.{u} :=
  .of (ULift.{u} (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}))

/-- The absolute scheme of `N`-th roots of unity, `μ_N = Spec ℤ[T]/(Tᴺ − 1)`.
Source: KM 1.12. -/
def muNAbs (N : ℕ) : Scheme.{u} := Spec (muNRing N)

/-- `μ_N` over an arbitrary base `S`: the base change of `muNAbs` to `S` (fibre product over
the terminal scheme `Spec ℤ`). -/
def muN (S : Scheme.{u}) (N : ℕ) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (muNAbs N))

/-- The structure morphism of `μ_{N,S}`. -/
def muNπ (S : Scheme.{u}) (N : ℕ) : muN S N ⟶ S := pullback.fst _ _

/-- The constant `S`-scheme on a finite type `A`: the disjoint union of copies of `S`
indexed by `A`. For `A = ZMod N` this is the constant group scheme `(ℤ/N)_S` of
KM 1.4.4(5). -/
def constScheme (S : Scheme.{u}) (A : Type) [Finite A] : Scheme.{u} :=
  ∐ fun _ : A ↦ S

/-- The structure morphism of the constant scheme. -/
def constSchemeπ (S : Scheme.{u}) (A : Type) [Finite A] : constScheme S A ⟶ S :=
  Sigma.desc fun _ ↦ 𝟙 S

section PointsFunctor

/-! ### The points functor of `μ_{N,S}` (ticket T-B2)

`μ_N`-points over `g : T ⟶ S` are the `N`-th roots of unity of `Γ(T, ⊤)`. Following
the pattern of `Mathlib.AlgebraicGeometry.AffineSpace` (`toSpecMvPolyIntEquiv`), the
equivalence is assembled from the universal property of `Spec ℤ[T]/(Tᴺ − 1)` and of
the defining pullback. The group-object structure (DS3a) is then *induced* from the
presheaf of groups it represents (`GrpObj.ofRepresentableBy`), which makes the points
description `muNPointsEquiv` — together with its naturality and multiplicativity —
the definitional pin of the group law, as required by the DATA-SORRY register. On
points the induced multiplication is multiplication of roots of unity, i.e. the
comultiplication `T ↦ T ⊗ T` of KM 1.12. -/

/-- The universal `N`-th root of unity: the class of `T` in `ℤ[T]/(Tᴺ − 1)`. -/
private def muNRingGen (N : ℕ) : muNRing N :=
  ULift.up (Ideal.Quotient.mk _ (X : Polynomial ℤ))

private lemma muNRingGen_pow (N : ℕ) : muNRingGen N ^ N = 1 :=
  ULift.down_injective <| by
    show (Ideal.Quotient.mk (Ideal.span {(X : Polynomial ℤ) ^ N - 1}) X) ^ N = 1
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {(X : Polynomial ℤ) ^ N - 1}))]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)

/-- Two ring homomorphisms out of `ℤ[T]/(Tᴺ − 1)` agreeing on the class of `T` agree. -/
private lemma muNRing_hom_ext {N : ℕ} {R : CommRingCat.{u}} {f g : muNRing N ⟶ R}
    (h : f (muNRingGen N) = g (muNRingGen N)) : f = g := by
  have key : (f.hom.comp (ULift.ringEquiv.symm.toRingHom :
        (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}) →+* muNRing N)).comp
        (Ideal.Quotient.mk _) =
      (g.hom.comp (ULift.ringEquiv.symm.toRingHom :
        (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}) →+* muNRing N)).comp
        (Ideal.Quotient.mk _) :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) h
  ext x
  obtain ⟨x⟩ := x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun key p

private lemma muNRing_span_vanish {N : ℕ} {R : CommRingCat.{u}} (a : R) (ha : a ^ N = 1) :
    ∀ p ∈ Ideal.span {(X : Polynomial ℤ) ^ N - 1},
      Polynomial.eval₂RingHom (Int.castRingHom R) a p = 0 := by
  intro p hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, ha, sub_self, zero_mul]

/-- The ring homomorphism `ℤ[T]/(Tᴺ − 1) ⟶ R` classifying an `N`-th root of unity. -/
private def muNRingLift {N : ℕ} {R : CommRingCat.{u}} (a : R) (ha : a ^ N = 1) :
    muNRing N ⟶ R :=
  CommRingCat.ofHom <|
    (Ideal.Quotient.lift (Ideal.span {(X : Polynomial ℤ) ^ N - 1})
      (Polynomial.eval₂RingHom (Int.castRingHom R) a)
      (muNRing_span_vanish a ha)).comp (ULift.ringEquiv : muNRing N ≃+* _).toRingHom

private lemma muNRingLift_gen {N : ℕ} {R : CommRingCat.{u}} (a : R) (ha : a ^ N = 1) :
    muNRingLift a ha (muNRingGen N) = a := by
  show (Ideal.Quotient.lift (Ideal.span {(X : Polynomial ℤ) ^ N - 1})
      (Polynomial.eval₂RingHom (Int.castRingHom R) a) (muNRing_span_vanish a ha))
    (Ideal.Quotient.mk (Ideal.span {(X : Polynomial ℤ) ^ N - 1}) (X : Polynomial ℤ)) = a
  rw [Ideal.Quotient.lift_mk]
  simp [Polynomial.coe_eval₂RingHom]

/-- Morphisms into an affine scheme are determined by their action on global sections. -/
private lemma specHom_ext {R : CommRingCat.{u}} {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec R}
    (h : f₁.appTop = f₂.appTop) : f₁ = f₂ := by
  apply (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.injective
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [Functor.rightOp_map, Quiver.Hom.unop_op, Scheme.Γ_map]
  exact congrArg (fun t ↦ t.op.unop) h

/-- Morphisms into `Spec ℤ[T]/(Tᴺ − 1)` are `N`-th roots of unity of `Γ(X, ⊤)`. -/
private def muNSpecHomEquiv {N : ℕ} {X : Scheme.{u}} :
    (X ⟶ Spec (muNRing N)) ≃ { a : Γ(X, ⊤) // a ^ N = 1 } where
  toFun f := ⟨f.appTop ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)), by
    rw [← map_pow, ← map_pow, muNRingGen_pow, map_one, map_one]⟩
  invFun a := X.toSpecΓ ≫ Spec.map (muNRingLift a.1 a.2)
  left_inv f := by
    apply specHom_ext
    refine (cancel_epi (Scheme.ΓSpecIso (muNRing N)).inv).mp ?_
    refine muNRing_hom_ext ?_
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply,
      ← CommRingCat.comp_apply ((Scheme.ΓSpecIso (muNRing N)).inv)
        (Spec.map (muNRingLift (f.appTop ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)))
          (by rw [← map_pow, ← map_pow, muNRingGen_pow, map_one, map_one]))).appTop,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_apply, muNRingLift_gen]
  right_inv a := Subtype.ext <| by
    show (X.toSpecΓ ≫ Spec.map (muNRingLift a.1 a.2)).appTop
        ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)) = a.1
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply ((Scheme.ΓSpecIso (muNRing N)).inv)
        (Spec.map (muNRingLift a.1 a.2)).appTop,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_apply, muNRingLift_gen]

/-- `S`-morphisms into `μ_{N,S}` over `g` are morphisms into the absolute `μ_N`
(universal property of the defining pullback). -/
private def muNHomEquivAbsHom (S : Scheme.{u}) (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    { h : T ⟶ muN S N // h ≫ muNπ S N = g } ≃ (T ⟶ muNAbs N) where
  toFun h := h.1 ≫ pullback.snd _ _
  invFun k := ⟨pullback.lift g k (by simp), pullback.lift_fst _ _ _⟩
  left_inv h := Subtype.ext <| by
    have hw : h.1 ≫ pullback.fst (terminal.from S) (terminal.from (muNAbs N)) = g := h.2
    exact pullback.hom_ext (by rw [pullback.lift_fst]; exact hw.symm)
      (by rw [pullback.lift_snd]; rfl)
  right_inv k := pullback.lift_snd _ _ _

/-- The core points description (engine for `muNGrpObj` and `muNPointsEquiv`). -/
private def muNPointsEquivAux (S : Scheme.{u}) (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    { h : T ⟶ muN S N // h ≫ muNπ S N = g } ≃ { a : Γ(T, ⊤) // a ^ N = 1 } :=
  (muNHomEquivAbsHom S N g).trans muNSpecHomEquiv

private lemma muNPointsEquivAux_coe (S : Scheme.{u}) (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    (h : { h : T ⟶ muN S N // h ≫ muNπ S N = g }) :
    (muNPointsEquivAux S N g h : Γ(T, ⊤)) =
      (h.1 ≫ pullback.snd (terminal.from S) (terminal.from (muNAbs N))).appTop
        ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)) := rfl

private lemma muNPointsEquivAux_natural (S : Scheme.{u}) (N : ℕ) {T T' : Scheme.{u}}
    (g : T ⟶ S) (k : T' ⟶ T) (h : { h : T ⟶ muN S N // h ≫ muNπ S N = g }) :
    (muNPointsEquivAux S N (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ : Γ(T', ⊤)) =
      k.appTop ((muNPointsEquivAux S N g h : Γ(T, ⊤))) := by
  rw [muNPointsEquivAux_coe, muNPointsEquivAux_coe, Category.assoc,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The group of `N`-th roots of unity of a commutative monoid, as a group structure
on the subtype `{a // a ^ N = 1}` (upstream candidate; file-local). -/
private instance nthRootsCommGroup (R : Type*) [CommMonoid R] (N : ℕ) [NeZero N] :
    CommGroup { a : R // a ^ N = 1 } where
  mul a b := ⟨a.1 * b.1, by rw [mul_pow, a.2, b.2, one_mul]⟩
  one := ⟨1, one_pow N⟩
  inv a := ⟨a.1 ^ (N - 1), by rw [← pow_mul, mul_comm, pow_mul, a.2, one_pow]⟩
  mul_assoc a b c := Subtype.ext (mul_assoc _ _ _)
  one_mul a := Subtype.ext (one_mul _)
  mul_one a := Subtype.ext (mul_one _)
  mul_comm a b := Subtype.ext (mul_comm _ _)
  inv_mul_cancel a := Subtype.ext <| by
    show a.1 ^ (N - 1) * a.1 = 1
    rw [← pow_succ, tsub_add_cancel_of_le NeZero.one_le, a.2]

/-- Roots of unity are functorial along monoid homomorphisms. -/
private def nthRootsMap {R R' : Type*} [CommMonoid R] [CommMonoid R'] {N : ℕ} [NeZero N]
    (f : R →* R') : { a : R // a ^ N = 1 } →* { a : R' // a ^ N = 1 } where
  toFun a := ⟨f a.1, by rw [← map_pow, a.2, map_one]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f _ _)

@[simp]
private lemma nthRootsMap_coe {R R' : Type*} [CommMonoid R] [CommMonoid R'] {N : ℕ}
    [NeZero N] (f : R →* R') (a : { a : R // a ^ N = 1 }) :
    (nthRootsMap f a : R') = f a.1 := rfl

/-- The presheaf of groups on `Over S` represented by `μ_{N,S}`: `N`-th roots of unity
of the global sections, with pointwise multiplication. -/
private def muNGrpFunctor (S : Scheme.{u}) (N : ℕ) [NeZero N] : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj Y := GrpCat.of { a : Γ(Y.unop.left, ⊤) // a ^ N = 1 }
  map k := GrpCat.ofHom (nthRootsMap k.unop.left.appTop.hom.toMonoidHom)
  map_id Y := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ Subtype.ext ?_)
    simp
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ Subtype.ext ?_)
    simp

/-- `μ_{N,S}` represents its points presheaf. -/
private def muNRepresentableBy (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    (muNGrpFunctor S N ⋙ forget _).RepresentableBy (Over.mk (muNπ S N)) where
  homEquiv {Y} :=
    (⟨fun f ↦ ⟨f.left, Over.w f⟩, fun h ↦ Over.homMk h.1 h.2, fun _ ↦ rfl,
        fun _ ↦ by ext; rfl⟩ :
      (Y ⟶ Over.mk (muNπ S N)) ≃ { h : Y.left ⟶ muN S N // h ≫ muNπ S N = Y.hom }).trans
    (muNPointsEquivAux S N Y.hom)
  homEquiv_comp {Y Y'} f h := Subtype.ext <| by
    show ((f ≫ h).left ≫ pullback.snd (terminal.from S) (terminal.from (muNAbs N))).appTop
        ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)) =
      f.left.appTop
        ((h.left ≫ pullback.snd (terminal.from S) (terminal.from (muNAbs N))).appTop
          ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N)))
    rw [Over.comp_left, Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- **(DS3a, ticket T-B2)** The group structure on `μ_{N,S}` in `Over S`, with
comultiplication `Spec` of `T ↦ T ⊗ T`. Constructed by representability
(`GrpObj.ofRepresentableBy`) from the presheaf of `N`-th roots of unity, so that the
registered points description `muNPointsEquiv` (with `muNPointsEquiv_natural`,
`muNPointsEquiv_one`, `muNPointsEquiv_mul`) pins the group law: on `T`-points it is
multiplication of `N`-th roots of unity, i.e. `Spec` of `T ↦ T ⊗ T` (KM 1.12). -/
noncomputable instance muNGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (muNπ S N)) :=
  .ofRepresentableBy _ (muNGrpFunctor S N) (muNRepresentableBy S N)

end PointsFunctor

/-- **(DS3b, ticket T-B2)** The group structure on the constant group scheme `(ℤ/N)_S`.
DATA-SORRY (register entry DS3). -/
instance constZModGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (constSchemeπ S (ZMod N))) := sorry

/-- **(DS3c / T-B2a, specification of DS3a)** The canonical points description of
`μ_{N,S}`: for `T ⟶ S`, the `T`-points of `μ_{N,S}` over `S` are the `N`-th roots of unity
of `Γ(T, O_T)`. Registered as canonical data (the equivalence is induced by the universal
property of `Spec ℤ[T]/(Tᴺ−1)` and pullback; naturality statements `muNPointsEquiv_natural`
in ticket `T-B2`).
Source: KM 1.12; Loeffler's representability example (`ℤ[T]/(Tⁿ−1)` represents "`n`-th
roots of unity in `R`"). -/
noncomputable def muNPointsEquiv (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) :
    { h : T ⟶ muN S N // h ≫ muNπ S N = g } ≃ { a : Γ(T, ⊤) // a ^ N = 1 } :=
  muNPointsEquivAux S N g

/-- **(T-B7)** `μ_{N,S} ⟶ S` is finite locally free of rank `N`, étale iff `N` is invertible
on `S`. (Two statements; étale case.) Source: KM 1.12; standard. -/
theorem muNπ_isFinite (S : Scheme.{u}) (N : ℕ) [NeZero N] : IsFinite (muNπ S N) := by sorry

/-- **(T-B7)** `μ_{N,S} ⟶ S` is flat, of constant rank `N`. -/
theorem muNπ_flat (S : Scheme.{u}) (N : ℕ) [NeZero N] : Flat (muNπ S N) := by sorry

theorem muNπ_finrank (S : Scheme.{u}) (N : ℕ) [NeZero N] (s : S) :
    (muNπ S N).finrank s = N := by sorry

/-- **(T-B7, étale criterion — iff form per the T-B7 spec)** `μ_{N,S} ⟶ S` is étale
iff `N` is invertible on `S` (`Tᴺ − 1` separable ⟺ `N` a unit; both sides vacuous
for `S = ∅`). -/
theorem muNπ_etale_iff (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    Etale (muNπ S N) ↔ IsUnit (N : Γ(S, ⊤)) := by sorry

/-- **(T-B2, DS3 naturality spec — register rule (iii))** The points description of
`μ_N` is natural: restriction along `k : T' ⟶ T` corresponds to applying `Γ`-map. -/
theorem muNPointsEquiv_natural (S : Scheme.{u}) (N : ℕ) [NeZero N]
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (h : { h : T ⟶ muN S N // h ≫ muNπ S N = g }) :
    (muNPointsEquiv S N (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ : Γ(T', ⊤)) =
      (Scheme.Γ.map k.op).hom (muNPointsEquiv S N g h : Γ(T, ⊤)) :=
  muNPointsEquivAux_natural S N g k h

end ModularCurves

end

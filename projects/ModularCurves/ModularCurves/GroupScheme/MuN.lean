import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.LocallyConstant.Algebra

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

The group-object structures are registered constructions (DS3, constructed in ticket
`T-B2`): both are induced by representability (`GrpObj.ofRepresentableBy`) from their
presheaves of points — `N`-th roots of unity of `Γ(T, ⊤)` for `μ_N` (so the group law
is `Spec` of the comultiplication `T ↦ T ⊗ T`, pinned by `muNPointsEquiv` +
`muNPointsEquiv_natural`/`_one`/`_mul`), and locally constant `ℤ/N`-valued functions
for `(ℤ/N)_S` (pinned by `constSchemePointsEquiv` + naturality). Downstream code uses
them only through these stated specifications (DATA-SORRY register rule).
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
@[reducible] def constScheme (S : Scheme.{u}) (A : Type) [Finite A] : Scheme.{u} :=
  ∐ fun _ : A ↦ S

/-- The structure morphism of the constant scheme. -/
@[reducible] def constSchemeπ (S : Scheme.{u}) (A : Type) [Finite A] : constScheme S A ⟶ S :=
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

section ConstPointsFunctor

/-! ### The points functor of the constant scheme (ticket T-B2)

An `S`-morphism `T ⟶ ∐_A S` over `g : T ⟶ S` is precisely a locally constant
function `T → A` — the index of the copy of `S` each point is sent to. The
group-object structure on `(ℤ/N)_S` (DS3b) is induced from this presheaf by
representability, exactly as for `μ_N`. The engine recognising a clopen partition of
`T` as a coproduct decomposition is mathlib's `nonempty_isColimit_cofanMk_of`. -/

variable {S : Scheme.{u}} {A : Type} [Finite A]

private instance sigmaι_isOpenImmersion (a : A) :
    IsOpenImmersion (Sigma.ι (fun _ : A ↦ S) a) :=
  (sigmaOpenCover (fun _ : A ↦ S)).map_prop a

private lemma exists_sigmaι_eq {T : Scheme.{u}} (h : T ⟶ constScheme S A) (t : T) :
    ∃ a, h t ∈ Set.range (Sigma.ι (fun _ : A ↦ S) a) := by
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun _ : A ↦ S)).exists_eq (h t)
  exact ⟨i, y, hy⟩

/-- The index function of a morphism into the constant scheme (the copy of `S` each
point lands in; well defined by disjointness of the copies). -/
private def constIndex {T : Scheme.{u}} (h : T ⟶ constScheme S A) (t : T) : A :=
  (exists_sigmaι_eq h t).choose

private lemma constIndex_mem {T : Scheme.{u}} (h : T ⟶ constScheme S A) (t : T) :
    h t ∈ Set.range (Sigma.ι (fun _ : A ↦ S) (constIndex h t)) :=
  (exists_sigmaι_eq h t).choose_spec

private lemma constIndex_eq_iff {T : Scheme.{u}} (h : T ⟶ constScheme S A) (t : T) (a : A) :
    constIndex h t = a ↔ h t ∈ Set.range (Sigma.ι (fun _ : A ↦ S) a) := by
  constructor
  · intro ht
    exact ht ▸ constIndex_mem h t
  · intro hmem
    by_contra hne
    have hd := disjoint_opensRange_sigmaι (fun _ : A ↦ S) (constIndex h t) a hne
    have hmem2 : h t ∈ ((Sigma.ι (fun _ : A ↦ S) (constIndex h t)).opensRange ⊓
        (Sigma.ι (fun _ : A ↦ S) a).opensRange : (constScheme S A).Opens) :=
      ⟨constIndex_mem h t, hmem⟩
    rw [hd.eq_bot] at hmem2
    simp at hmem2

private lemma isLocallyConstant_constIndex {T : Scheme.{u}} (h : T ⟶ constScheme S A) :
    IsLocallyConstant (constIndex h) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun a ↦ ?_
  have heq : constIndex h ⁻¹' {a} = ⇑h ⁻¹' Set.range (Sigma.ι (fun _ : A ↦ S) a) := by
    ext t
    exact constIndex_eq_iff h t a
  rw [heq]
  exact (Sigma.ι (fun _ : A ↦ S) a).opensRange.isOpen.preimage h.continuous

/-- The clopen piece of `T` where a locally constant function takes the value `a`. -/
private def constFiber {T : Scheme.{u}} (c : LocallyConstant T A) (a : A) : T.Opens :=
  ⟨⇑c ⁻¹' {a}, c.isLocallyConstant {a}⟩

omit [Finite A] in
private lemma mem_constFiber {T : Scheme.{u}} (c : LocallyConstant T A) (t : T) :
    t ∈ constFiber c (c t) := rfl

/-- A locally constant function exhibits `T` as the disjoint union of its fibres. -/
private def constFiberCofanIsColimit {T : Scheme.{u}} (c : LocallyConstant T A) :
    IsColimit (Cofan.mk T fun a ↦ (constFiber c a).ι) :=
  (nonempty_isColimit_cofanMk_of _
    (by
      rw [eq_top_iff]
      intro t _
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨c t, by rw [Scheme.Opens.opensRange_ι]; exact mem_constFiber c t⟩)
    (by
      intro a b hab
      rw [Function.onFun, Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
        disjoint_iff]
      refine TopologicalSpace.Opens.ext ?_
      simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot]
      ext t
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hta htb
      exact hab ((show c t = a from hta).symm.trans (show c t = b from htb)))).some

/-- The morphism to the constant scheme classified by a locally constant function. -/
private def constDesc {T : Scheme.{u}} (g : T ⟶ S) (c : LocallyConstant T A) :
    T ⟶ constScheme S A :=
  (constFiberCofanIsColimit c).desc
    (Cofan.mk (constScheme S A) fun a ↦ (constFiber c a).ι ≫ g ≫ Sigma.ι (fun _ : A ↦ S) a)

private lemma constFiber_ι_constDesc {T : Scheme.{u}} (g : T ⟶ S) (c : LocallyConstant T A)
    (a : A) :
    (constFiber c a).ι ≫ constDesc g c =
      (constFiber c a).ι ≫ g ≫ Sigma.ι (fun _ : A ↦ S) a :=
  (constFiberCofanIsColimit c).fac _ ⟨a⟩

private lemma constDesc_π {T : Scheme.{u}} (g : T ⟶ S) (c : LocallyConstant T A) :
    constDesc g c ≫ constSchemeπ S A = g :=
  (constFiberCofanIsColimit c).hom_ext fun ⟨a⟩ ↦ by
    show (constFiber c a).ι ≫ constDesc g c ≫ Sigma.desc (fun _ : A ↦ 𝟙 S) =
      (constFiber c a).ι ≫ g
    rw [← Category.assoc, constFiber_ι_constDesc, Category.assoc, Category.assoc,
      Sigma.ι_desc, Category.comp_id]

/-- **(DS3b pin, ticket T-B2)** `S`-morphisms into the constant scheme `∐_A S` over
`g : T ⟶ S` are the locally constant `A`-valued functions on `T`.
Source: KM 1.4.4(5) ("the constant `S`-scheme `ℤ/Nℤ`"); consumed by the
Drinfeld-generator dictionary (stream D). -/
def constSchemePointsEquiv (S : Scheme.{u}) (A : Type) [Finite A] {T : Scheme.{u}}
    (g : T ⟶ S) :
    { h : T ⟶ constScheme S A // h ≫ constSchemeπ S A = g } ≃ LocallyConstant T A where
  toFun h := ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩
  invFun c := ⟨constDesc g c, constDesc_π g c⟩
  left_inv h := Subtype.ext <| (constFiberCofanIsColimit
      ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩).hom_ext fun ⟨a⟩ ↦ by
    have hrange : Set.range ((constFiber ⟨constIndex h.1,
        isLocallyConstant_constIndex h.1⟩ a).ι ≫ h.1) ⊆
        Set.range (Sigma.ι (fun _ : A ↦ S) a) := by
      rintro _ ⟨⟨t, ht⟩, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (constIndex_eq_iff h.1 t a).mp ht
    have hfac := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : A ↦ S) a)
      ((constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫ h.1) hrange
    have hπ : Sigma.ι (fun _ : A ↦ S) a ≫ constSchemeπ S A = 𝟙 S := Sigma.ι_desc _ _
    have hlift : IsOpenImmersion.lift (Sigma.ι (fun _ : A ↦ S) a)
        ((constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫ h.1) hrange =
        (constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫ g := by
      calc IsOpenImmersion.lift _ _ hrange
          = IsOpenImmersion.lift _ _ hrange ≫ Sigma.ι (fun _ : A ↦ S) a ≫ constSchemeπ S A := by
            rw [hπ, Category.comp_id]
        _ = ((constFiber _ a).ι ≫ h.1) ≫ constSchemeπ S A := by rw [← Category.assoc, hfac]
        _ = (constFiber _ a).ι ≫ g := by rw [Category.assoc, h.2]
    show (constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫
        constDesc g ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ =
      (constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫ h.1
    calc (constFiber ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩ a).ι ≫
          constDesc g ⟨constIndex h.1, isLocallyConstant_constIndex h.1⟩
        = (constFiber _ a).ι ≫ g ≫ Sigma.ι (fun _ : A ↦ S) a := constFiber_ι_constDesc g _ a
      _ = ((constFiber _ a).ι ≫ g) ≫ Sigma.ι (fun _ : A ↦ S) a := (Category.assoc _ _ _).symm
      _ = IsOpenImmersion.lift _ _ hrange ≫ Sigma.ι (fun _ : A ↦ S) a := by rw [hlift]
      _ = (constFiber _ a).ι ≫ h.1 := hfac
  right_inv c := by
    ext t
    have key : constDesc g c ((constFiber c (c t)).ι ⟨t, mem_constFiber c t⟩) =
        ((constFiber c (c t)).ι ≫ g ≫ Sigma.ι (fun _ : A ↦ S) (c t)) ⟨t, mem_constFiber c t⟩ := by
      rw [← Scheme.Hom.comp_apply, constFiber_ι_constDesc]
    rw [Scheme.Opens.ι_apply] at key
    show constIndex (constDesc g c) t = c t
    rw [constIndex_eq_iff, key, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _

/-- Naturality of the constant-scheme points description: restriction along
`k : T' ⟶ T` is composition with `k` on locally constant functions. -/
lemma constSchemePointsEquiv_natural (S : Scheme.{u}) (A : Type) [Finite A]
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (h : { h : T ⟶ constScheme S A // h ≫ constSchemeπ S A = g }) :
    constSchemePointsEquiv S A (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
      (constSchemePointsEquiv S A g h).comap k.base.hom := by
  ext t
  rw [LocallyConstant.coe_comap_apply]
  show constIndex (k ≫ h.1) t = constIndex h.1 (k.base.hom t)
  rw [constIndex_eq_iff, Scheme.Hom.comp_apply]
  exact constIndex_mem h.1 (k t)

/-- The presheaf of groups on `Over S` represented by the constant scheme `(ℤ/N)_S`:
locally constant `ℤ/N`-valued functions under pointwise addition (written
multiplicatively for mathlib's `GrpObj`). -/
private def constGrpFunctor (S : Scheme.{u}) (N : ℕ) [NeZero N] : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj Y := GrpCat.of (Multiplicative (LocallyConstant Y.unop.left (ZMod N)))
  map k := GrpCat.ofHom
    (AddMonoidHom.toMultiplicative (LocallyConstant.comapAddMonoidHom k.unop.left.base.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `(ℤ/N)_S` represents its points presheaf. -/
private def constRepresentableBy (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    (constGrpFunctor S N ⋙ forget _).RepresentableBy
      (Over.mk (constSchemeπ S (ZMod N))) where
  homEquiv {Y} :=
    (⟨fun f ↦ ⟨f.left, Over.w f⟩, fun h ↦ Over.homMk h.1 h.2, fun _ ↦ rfl,
        fun _ ↦ by ext; rfl⟩ :
      (Y ⟶ Over.mk (constSchemeπ S (ZMod N))) ≃
        { h : Y.left ⟶ constScheme S (ZMod N) // h ≫ constSchemeπ S (ZMod N) = Y.hom }).trans
    ((constSchemePointsEquiv S (ZMod N) Y.hom).trans Multiplicative.ofAdd)
  homEquiv_comp {Y Y'} f h :=
    congrArg Multiplicative.ofAdd <| LocallyConstant.ext fun t ↦ by
      show constIndex ((f ≫ h).left) t = constIndex h.left (f.left.base.hom t)
      rw [constIndex_eq_iff]
      show h.left (f.left t) ∈ Set.range (Sigma.ι (fun _ : ZMod N ↦ S)
        (constIndex h.left (f.left t)))
      exact constIndex_mem h.left (f.left t)

/-- **(DS3b, ticket T-B2)** The group structure on the constant group scheme `(ℤ/N)_S`,
induced by representability from the presheaf of locally constant `ℤ/N`-valued
functions; the points description `constSchemePointsEquiv` (+ naturality) pins it.
Source: KM 1.4.4(5). -/
noncomputable instance constZModGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (constSchemeπ S (ZMod N))) :=
  .ofRepresentableBy _ (constGrpFunctor S N) (constRepresentableBy S N)

end ConstPointsFunctor

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

section RankAndEtale

/-! ### `μ_N` is finite locally free of rank `N` (ticket T-B7)

`ℤ[T]/(Tᴺ − 1)` is free of rank `N` over `ℤ` (monic quotient basis `1, …, T^{N−1}`),
so the absolute `μ_N ⟶ Spec ℤ` is finite flat of rank `N`; the relative statements
follow by base change along the defining pullback square, transported from the
abstract terminal scheme to `Spec (ULift ℤ)`. -/

private lemma muN_poly_monic (N : ℕ) [NeZero N] : ((X : Polynomial ℤ) ^ N - 1).Monic := by
  simpa using Polynomial.monic_X_pow_sub_C (1 : ℤ) (NeZero.ne N)

/-- The structure ring map of the absolute `μ_N`, out of the coordinate ring of the
terminal scheme. -/
private def muNRingMap (N : ℕ) : CommRingCat.of (ULift.{u} ℤ) ⟶ muNRing N :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm.toRingHom.comp
    (algebraMap ℤ (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}))).comp
    ULift.ringEquiv.toRingHom)

private lemma muNRingMap_finite (N : ℕ) [NeZero N] : (muNRingMap N).hom.Finite := by
  refine RingHom.Finite.comp ?_ ?_
  · refine RingHom.Finite.comp ?_ ?_
    · exact RingHom.Finite.of_surjective _ ULift.ringEquiv.symm.surjective
    · exact RingHom.finite_algebraMap.mpr (muN_poly_monic N).finite_quotient
  · exact RingHom.Finite.of_surjective _ ULift.ringEquiv.surjective

private lemma muNRingMap_flat (N : ℕ) [NeZero N] : (muNRingMap N).hom.Flat := by
  haveI := (muN_poly_monic N).free_quotient
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective ULift.ringEquiv.bijective)
    (RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective))

/-- The defining square of `μ_{N,S}`, with the cospan corner moved from the abstract
terminal scheme to `Spec (ULift ℤ)`. -/
private lemma isPullback_muN (S : Scheme.{u}) (N : ℕ) :
    IsPullback (muNπ S N) (pullback.snd (terminal.from S) (terminal.from (muNAbs N)))
      (terminal.from S ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom)
      (Spec.map (muNRingMap N)) := by
  have h2 : terminal.from (muNAbs N) ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom
      = Spec.map (muNRingMap N) := specULiftZIsTerminal.hom_ext _ _
  have t : IsPullback (terminal.from (muNAbs N)) (𝟙 (muNAbs N))
      (terminalIsoIsTerminal specULiftZIsTerminal).hom (Spec.map (muNRingMap N)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, h2]⟩
  have main := (IsPullback.of_hasPullback (terminal.from S)
    (terminal.from (muNAbs N))).paste_vert t
  rw [Category.comp_id] at main
  exact main

/-- **(T-B7)** `μ_{N,S} ⟶ S` is finite locally free of rank `N`, étale iff `N` is invertible
on `S`. (Two statements; étale case.) Source: KM 1.12; standard. -/
theorem muNπ_isFinite (S : Scheme.{u}) (N : ℕ) [NeZero N] : IsFinite (muNπ S N) :=
  MorphismProperty.of_isPullback (isPullback_muN S N).flip
    ((IsFinite.SpecMap_iff _).mpr (muNRingMap_finite N))

/-- **(T-B7)** `μ_{N,S} ⟶ S` is flat, of constant rank `N`. -/
theorem muNπ_flat (S : Scheme.{u}) (N : ℕ) [NeZero N] : Flat (muNπ S N) :=
  MorphismProperty.of_isPullback (isPullback_muN S N).flip
    (Flat.SpecMap_iff.mpr (muNRingMap_flat N))

private lemma muNRingMap_finrank (N : ℕ) [NeZero N] (y : PrimeSpectrum (ULift.{u} ℤ)) :
    (muNRingMap N).hom.finrank y = N := by
  haveI := (muN_poly_monic N).free_quotient
  have hcomp : ULift.ringEquiv.symm.toRingHom.comp
      (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ) = RingHom.id _ :=
    RingHom.ext fun x ↦ rfl
  have hy : y = PrimeSpectrum.comap (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ)
      (PrimeSpectrum.comap ULift.ringEquiv.symm.toRingHom y) := by
    rw [← PrimeSpectrum.comap_comp_apply, hcomp, PrimeSpectrum.comap_id]
  show ((ULift.ringEquiv.symm.toRingHom.comp
      (algebraMap ℤ (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}))).comp
      (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ)).finrank y = N
  rw [RingHom.finrank_comp_right_of_bijective _ _ ULift.ringEquiv.bijective
      (RingHom.Finite.comp
        (RingHom.Finite.of_surjective _ ULift.ringEquiv.symm.surjective)
        (RingHom.finite_algebraMap.mpr (muN_poly_monic N).finite_quotient))
      (RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
        (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective))
      y (PrimeSpectrum.comap ULift.ringEquiv.symm.toRingHom y) hy,
    RingHom.finrank_comp_left_of_bijective _ _ ULift.ringEquiv.symm.bijective
      (RingHom.finite_algebraMap.mpr (muN_poly_monic N).finite_quotient)
      (RingHom.flat_algebraMap_iff.mpr inferInstance),
    RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  have hfr : Module.finrank ℤ (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}) = N := by
    have h := (AdjoinRoot.powerBasis' (muN_poly_monic N)).finrank
    rw [AdjoinRoot.powerBasis'_dim] at h
    exact h.trans (by simpa using Polynomial.natDegree_X_pow_sub_C (n := N) (r := (1 : ℤ)))
  simp only [Pi.natCast_apply, Nat.cast_id]
  exact hfr

theorem muNπ_finrank (S : Scheme.{u}) (N : ℕ) [NeZero N] (s : S) :
    (muNπ S N).finrank s = N := by
  rw [@Scheme.Hom.finrank_of_isPullback (muN S N) (muNAbs N) S
      (Spec (CommRingCat.of (ULift.{u} ℤ)))
      (pullback.snd (terminal.from S) (terminal.from (muNAbs N))) (muNπ S N)
      (Spec.map (muNRingMap.{u} N))
      (terminal.from S ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom)
      (isPullback_muN S N).flip
      (Flat.SpecMap_iff.mpr (muNRingMap_flat N))
      ((IsFinite.SpecMap_iff _).mpr (muNRingMap_finite N)) s]
  refine Eq.trans ?_ (muNRingMap_finrank N
    ((terminal.from S ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom) s))
  exact congrFun
    (Scheme.Hom.finrank_SpecMap_eq_finrank (muNRingMap_finite N) (muNRingMap_flat N)) _

/-- **(T-B7, étale criterion — iff form per the T-B7 spec)** `μ_{N,S} ⟶ S` is étale
iff `N` is invertible on `S` (`Tᴺ − 1` separable ⟺ `N` a unit; both sides vacuous
for `S = ∅`). -/
private lemma etale_muNπ_of_isUnit (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (h : IsUnit (N : Γ(S, ⊤))) : Etale (muNπ S N) := by sorry

private lemma isUnit_of_etale_muNπ (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (h : Etale (muNπ S N)) : IsUnit (N : Γ(S, ⊤)) := by sorry

theorem muNπ_etale_iff (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    Etale (muNπ S N) ↔ IsUnit (N : Γ(S, ⊤)) :=
  ⟨isUnit_of_etale_muNπ S N, etale_muNπ_of_isUnit S N⟩

end RankAndEtale

/-- **(T-B2, DS3 naturality spec — register rule (iii))** The points description of
`μ_N` is natural: restriction along `k : T' ⟶ T` corresponds to applying `Γ`-map. -/
theorem muNPointsEquiv_natural (S : Scheme.{u}) (N : ℕ) [NeZero N]
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (h : { h : T ⟶ muN S N // h ≫ muNπ S N = g }) :
    (muNPointsEquiv S N (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ : Γ(T', ⊤)) =
      (Scheme.Γ.map k.op).hom (muNPointsEquiv S N g h : Γ(T, ⊤)) :=
  muNPointsEquivAux_natural S N g k h

open MonObj in
/-- **(T-B2, DS3a group-law pin)** The points description of `μ_{N,S}` sends the unit
of the group structure `muNGrpObj` to `1`. -/
theorem muNPointsEquiv_one (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) :
    letI : Monoid (Over.mk g ⟶ Over.mk (muNπ S N)) := Hom.monoid
    (muNPointsEquiv S N g ⟨(1 : Over.mk g ⟶ Over.mk (muNπ S N)).left, Over.w _⟩ :
      Γ(T, ⊤)) = 1 :=
  congrArg Subtype.val
    (((yonedaMonObjIsoOfRepresentableBy (Over.mk (muNπ S N))
        (muNGrpFunctor S N ⋙ forget₂ GrpCat MonCat) (muNRepresentableBy S N)).hom.app
      (Opposite.op (Over.mk g))).hom.map_one)

open MonObj in
/-- **(T-B2, DS3a group-law pin — register rule (iii))** The points description of
`μ_{N,S}` is multiplicative: the group structure `muNGrpObj` is, on `T`-points,
multiplication of `N`-th roots of unity in `Γ(T, ⊤)` — i.e. `Spec` of the
comultiplication `T ↦ T ⊗ T` (KM 1.12). -/
theorem muNPointsEquiv_mul (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) (f₁ f₂ : Over.mk g ⟶ Over.mk (muNπ S N)) :
    letI : Monoid (Over.mk g ⟶ Over.mk (muNπ S N)) := Hom.monoid
    (muNPointsEquiv S N g ⟨(f₁ * f₂).left, Over.w _⟩ : Γ(T, ⊤)) =
      (muNPointsEquiv S N g ⟨f₁.left, Over.w f₁⟩ : Γ(T, ⊤)) *
        (muNPointsEquiv S N g ⟨f₂.left, Over.w f₂⟩ : Γ(T, ⊤)) :=
  congrArg Subtype.val
    (((yonedaMonObjIsoOfRepresentableBy (Over.mk (muNπ S N))
        (muNGrpFunctor S N ⋙ forget₂ GrpCat MonCat) (muNRepresentableBy S N)).hom.app
      (Opposite.op (Over.mk g))).hom.map_mul f₁ f₂)

end ModularCurves

end

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.Etale.StandardEtale
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

The construction pattern follows `Mathlib.AlgebraicGeometry.AffineSpace`
(`toSpecMvPolyIntEquiv`): the points equivalences are assembled from the universal
properties of `Spec ℤ[T]/(Tᴺ − 1)` and of the defining pullback, resp. — for the constant
scheme — from mathlib's `nonempty_isColimit_cofanMk_of`, which recognises the clopen
partition of `T` by a locally constant function as a coproduct decomposition. For the rank
and étale statements (T-B7): `ℤ[T]/(Tᴺ − 1)` is free of rank `N` over `ℤ` (monic quotient
basis `1, …, T^{N−1}`), and the relative statements descend along the defining pullback
square. Étaleness for invertible `N` is transported from the model `AdjoinRoot (Xᴺ − 1)`
over `ℤ[1/N]` — a pushout of the coordinate ring, standard étale because `f′·X − N·f = N`
exhibits `(Xᴺ − 1, C N)` as a standard étale pair; the converse reduces along residue
fields to the field case, where `X^{N/q} − 1` is a nonzero nilpotent in characteristic
`q ∣ N`.
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

/-- Base-change functoriality of `μ_N`: the canonical comparison `μ_{N,S'} ⟶ μ_{N,S}`
over `g : S' ⟶ S` (both sides are pulled back from the absolute `μ_N`). -/
noncomputable def muNMapAlong {S' S : Scheme.{u}} (g : S' ⟶ S) (N : ℕ) :
    muN S' N ⟶ muN S N :=
  pullback.map (terminal.from S') (terminal.from (muNAbs N))
    (terminal.from S) (terminal.from (muNAbs N)) g (𝟙 (muNAbs N)) (𝟙 (⊤_ Scheme.{u}))
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The base-change comparison lies over `g`. -/
theorem muNMapAlong_π {S' S : Scheme.{u}} (g : S' ⟶ S) (N : ℕ) :
    muNMapAlong g N ≫ muNπ S N = muNπ S' N ≫ g := by
  rw [muNMapAlong, muNπ, muNπ]; exact pullback.lift_fst _ _ _

/-- Base-change comparisons compose. -/
theorem muNMapAlong_comp {S₁ S₂ S₃ : Scheme.{u}} (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃)
    (N : ℕ) :
    muNMapAlong (g₁ ≫ g₂) N = muNMapAlong g₁ N ≫ muNMapAlong g₂ N := by
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans
      (((Category.assoc _ _ _).trans
        ((congrArg (muNMapAlong g₁ N ≫ ·) (pullback.lift_fst _ _ _)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ g₂) (pullback.lift_fst _ _ _)).trans
              (Category.assoc _ _ _))))).symm)
  · exact (pullback.lift_snd _ _ _).trans
      (((Category.assoc _ _ _).trans
        ((congrArg (muNMapAlong g₁ N ≫ ·) ((pullback.lift_snd _ _ _).trans
            (Category.comp_id _))).trans
          (pullback.lift_snd _ _ _))).symm)

/-- The constant `S`-scheme on a finite type `A`: the disjoint union of copies of `S`
indexed by `A`. For `A = ZMod N` this is the constant group scheme `(ℤ/N)_S` of
KM 1.4.4(5). -/
abbrev constScheme (S : Scheme.{u}) (A : Type) [Finite A] : Scheme.{u} :=
  ∐ fun _ : A ↦ S

/-- The structure morphism of the constant scheme. -/
abbrev constSchemeπ (S : Scheme.{u}) (A : Type) [Finite A] : constScheme S A ⟶ S :=
  Sigma.desc fun _ ↦ 𝟙 S

section PointsFunctor

private def muNRingGen (N : ℕ) : muNRing N :=
  ULift.up (Ideal.Quotient.mk _ (X : Polynomial ℤ))

private lemma muNRingGen_pow (N : ℕ) : muNRingGen N ^ N = 1 :=
  ULift.down_injective <| by
    change (Ideal.Quotient.mk (Ideal.span {(X : Polynomial ℤ) ^ N - 1}) X) ^ N = 1
    simp [← map_pow, Ideal.Quotient.mk_eq_one_iff_sub_mem]

private lemma muNRing_hom_ext {N : ℕ} {R : CommRingCat.{u}} {f g : muNRing N ⟶ R}
    (h : f (muNRingGen N) = g (muNRingGen N)) : f = g := by
  have key : (f.hom.comp ULift.ringEquiv.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g.hom.comp ULift.ringEquiv.symm.toRingHom).comp (Ideal.Quotient.mk _) :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) h
  ext ⟨x⟩
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

section ConstBaseChange

/-- The base-change comparison of constant schemes along `k : T ⟶ S`: the copy-wise
map `∐_A T ⟶ ∐_A S`. -/
noncomputable def constSchemeMapAlong {T : Scheme.{u}} (k : T ⟶ S) (A : Type) [Finite A] :
    constScheme T A ⟶ constScheme S A :=
  Limits.Sigma.map fun _ => k

@[reassoc (attr := simp)]
theorem ι_constSchemeMapAlong {T : Scheme.{u}} (k : T ⟶ S) (A : Type) [Finite A] (a : A) :
    Sigma.ι (fun _ : A => T) a ≫ constSchemeMapAlong k A
      = k ≫ Sigma.ι (fun _ : A => S) a :=
  Limits.Sigma.ι_map _ _

@[reassoc]
theorem constSchemeMapAlong_π {T : Scheme.{u}} (k : T ⟶ S) (A : Type) [Finite A] :
    constSchemeMapAlong k A ≫ constSchemeπ S A = constSchemeπ T A ≫ k := by
  apply Sigma.hom_ext
  intro a
  rw [ι_constSchemeMapAlong_assoc]
  show k ≫ Sigma.ι (fun _ : A => S) a ≫ Sigma.desc (fun _ => 𝟙 S)
    = (Sigma.ι (fun _ : A => T) a ≫ Sigma.desc (fun _ => 𝟙 T)) ≫ k
  rw [Sigma.ι_desc, Sigma.ι_desc, Category.comp_id, Category.id_comp]

private lemma constIndex_mapAlong {T W : Scheme.{u}} (k : T ⟶ S)
    (h : W ⟶ constScheme T A) (t : W) :
    constIndex (h ≫ constSchemeMapAlong k A) t = constIndex h t := by
  rw [constIndex_eq_iff, Scheme.Hom.comp_apply]
  obtain ⟨y, hy⟩ := constIndex_mem h t
  rw [← hy, ← Scheme.Hom.comp_apply, ι_constSchemeMapAlong, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

/-- The points-read of a coproduct inclusion is the constant function. -/
lemma constSchemePointsEquiv_sigmaι (a : A) :
    constSchemePointsEquiv S A (𝟙 S)
      ⟨Sigma.ι (fun _ : A ↦ S) a, Sigma.ι_desc _ _⟩ =
    LocallyConstant.const S a := by
  ext t
  show constIndex (Sigma.ι (fun _ : A ↦ S) a) t = a
  rw [constIndex_eq_iff]
  exact Set.mem_range_self _

/-- The points-read is unchanged by the base-change comparison map. -/
lemma constSchemePointsEquiv_mapAlong {T W : Scheme.{u}} (k : T ⟶ S) (g : W ⟶ T)
    (h : { h : W ⟶ constScheme T A // h ≫ constSchemeπ T A = g }) :
    constSchemePointsEquiv S A (g ≫ k)
      ⟨h.1 ≫ constSchemeMapAlong k A, by
        rw [Category.assoc, constSchemeMapAlong_π, ← Category.assoc, h.2]⟩ =
    constSchemePointsEquiv T A g h := by
  ext t
  show constIndex (h.1 ≫ constSchemeMapAlong k A) t = constIndex h.1 t
  exact constIndex_mapAlong k h.1 t

/-- **Constant schemes are stable under base change**: the comparison square

    `∐_A T ⟶ ∐_A S`, verticals the structure maps, bottom `k : T ⟶ S`

is cartesian. Proven by the functor-of-points description
(`constSchemePointsEquiv`): a `W`-point of `∐_A S` together with a lift of its
base point to `T` is exactly a `W`-point of `∐_A T` — the locally constant label
is the same. -/
theorem isPullback_constSchemeMapAlong {T : Scheme.{u}} (k : T ⟶ S)
    (A : Type) [Finite A] :
    IsPullback (constSchemeMapAlong k A) (constSchemeπ T A) (constSchemeπ S A) k := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (constSchemeMapAlong_π k A)
    (fun s => ((constSchemePointsEquiv T A s.snd).symm
      (constSchemePointsEquiv S A (s.snd ≫ k) ⟨s.fst, s.condition⟩)).1)
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_)
    )
  · -- the first face: composing with the comparison recovers the given point
    set c := constSchemePointsEquiv S A (s.snd ≫ k) ⟨s.fst, s.condition⟩ with hc
    set l := (constSchemePointsEquiv T A s.snd).symm c with hl
    have hπ : (l.1 ≫ constSchemeMapAlong k A) ≫ constSchemeπ S A = s.snd ≫ k := by
      rw [Category.assoc, constSchemeMapAlong_π, ← Category.assoc, l.2]
    have himg : constSchemePointsEquiv S A (s.snd ≫ k) ⟨l.1 ≫ constSchemeMapAlong k A, hπ⟩
        = c := by
      ext t
      show constIndex (l.1 ≫ constSchemeMapAlong k A) t = c t
      rw [constIndex_mapAlong]
      have hlc : constSchemePointsEquiv T A s.snd l = c := by
        rw [hl, Equiv.apply_symm_apply]
      have := congrArg (fun m => m t) (congrArg LocallyConstant.toFun hlc)
      exact this
    have := congrArg Subtype.val
      ((constSchemePointsEquiv S A (s.snd ≫ k)).injective
        (himg.trans (by rw [hc])))
    exact this
  · -- the second face: the structure triangle
    exact ((constSchemePointsEquiv T A s.snd).symm _).2
  · -- uniqueness
    set c := constSchemePointsEquiv S A (s.snd ≫ k) ⟨s.fst, s.condition⟩ with hc
    have hπ : (m ≫ constSchemeMapAlong k A) ≫ constSchemeπ S A = s.snd ≫ k := by
      rw [Category.assoc, constSchemeMapAlong_π, ← Category.assoc, hm₂]
    have himg : constSchemePointsEquiv T A s.snd ⟨m, hm₂⟩ = c := by
      ext t
      show constIndex m t = c t
      rw [← constIndex_mapAlong k m t]
      have hval : m ≫ constSchemeMapAlong k A = s.fst := hm₁
      rw [hval]
      rfl
    have : (⟨m, hm₂⟩ : { h : _ ⟶ constScheme T A // h ≫ constSchemeπ T A = s.snd })
        = (constSchemePointsEquiv T A s.snd).symm c := by
      rw [← himg, Equiv.symm_apply_apply]
    exact congrArg Subtype.val this

end ConstBaseChange

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

/-- The points dictionary is natural in the base: reading a point after the
base-change comparison gives the same `Γ`-value (the read factors through the
absolute leg, which `muNMapAlong` preserves). -/
lemma muNPointsEquiv_mapAlong {S' S : Scheme.{u}} (g : S' ⟶ S) (N : ℕ) [NeZero N]
    {W : Scheme.{u}} (t : W ⟶ S')
    (v : { h : W ⟶ muN S' N // h ≫ muNπ S' N = t }) :
    (muNPointsEquiv S N (t ≫ g) ⟨v.1 ≫ muNMapAlong g N, by
        rw [Category.assoc, muNMapAlong_π, ← Category.assoc, v.2]⟩ : Γ(W, ⊤)) =
      (muNPointsEquiv S' N t v : Γ(W, ⊤)) := by
  rw [muNPointsEquiv, muNPointsEquiv, muNPointsEquivAux_coe, muNPointsEquivAux_coe]
  refine congrArg (fun (m : W ⟶ muNAbs N) => m.appTop
    ((Scheme.ΓSpecIso (muNRing N)).inv (muNRingGen N))) ?_
  rw [Category.assoc]
  exact congrArg (Subtype.val v ≫ ·)
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

section RankAndEtale

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

private abbrev muNAwayRing (N : ℕ) : Type u := ULift.{u} (Localization.Away (N : ℤ))

private abbrev muNModelPoly (A : Type u) [CommRing A] (N : ℕ) : Polynomial A :=
  X ^ N - 1

private def muNModelRing (A : Type u) [CommRing A] (N : ℕ) : CommRingCat.{u} :=
  .of (AdjoinRoot (muNModelPoly A N))

/-- The unique map `ℤ → A`, universe-lifted. -/
private def muNBaseMap (A : Type u) [CommRing A] :
    CommRingCat.of (ULift.{u} ℤ) ⟶ .of A :=
  CommRingCat.ofHom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom)

/-- The structure map of the model over `A`. -/
private def muNModelStruct (A : Type u) [CommRing A] (N : ℕ) :
    CommRingCat.of A ⟶ muNModelRing A N :=
  CommRingCat.ofHom (AdjoinRoot.of (muNModelPoly A N))

private lemma muNModel_root_pow (A : Type u) [CommRing A] (N : ℕ) :
    (AdjoinRoot.root (muNModelPoly A N)) ^ N = 1 := by
  have h := AdjoinRoot.mk_self (f := muNModelPoly A N)
  rw [muNModelPoly, map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] at h
  exact h

/-- The comparison `ℤ[T]/(Tᴺ−1) → A[T]/(Tᴺ−1)`, classifying the root. -/
private def muNModelCompare (A : Type u) [CommRing A] (N : ℕ) :
    muNRing N ⟶ muNModelRing A N :=
  muNRingLift (AdjoinRoot.root (muNModelPoly A N)) (muNModel_root_pow A N)

/-- Ring homomorphisms out of `ULift ℤ` agree. -/
private lemma uliftZ_hom_ext {R : CommRingCat.{u}} {f g : CommRingCat.of (ULift.{u} ℤ) ⟶ R} :
    f = g := by
  have key : f.hom.comp (ULift.ringEquiv.symm.toRingHom : ℤ →+* ULift.{u} ℤ)
      = g.hom.comp ULift.ringEquiv.symm.toRingHom := RingHom.ext_int _ _
  ext x
  obtain ⟨x⟩ := x
  exact DFunLike.congr_fun key x

private lemma muNModel_eval₂_vanish (A : Type u) [CommRing A] (N : ℕ)
    {Rc : CommRingCat.{u}} (i : A →+* Rc) (x : Rc) (hx : x ^ N = 1) :
    (muNModelPoly A N).eval₂ i x = 0 := by
  simp [muNModelPoly, hx]

private lemma pushout_inr_gen_pow (A : Type u) [CommRing A] (N : ℕ)
    (s : PushoutCocone (muNBaseMap A) (muNRingMap N)) :
    (s.inr (muNRingGen N)) ^ N = 1 := by
  rw [← map_pow, muNRingGen_pow, map_one]

/-- The model over `A` is the pushout (base change) of `μ_N`'s coordinate ring. -/
private lemma muNModel_isPushout (A : Type u) [CommRing A] (N : ℕ) :
    IsPushout (muNBaseMap A) (muNRingMap N) (muNModelStruct A N) (muNModelCompare A N) := by
  have test : ∀ (s : PushoutCocone (muNBaseMap A) (muNRingMap N)),
      (muNModelPoly A N).eval₂ (s.inl.hom : A →+* s.pt) (s.inr (muNRingGen N)) = 0 :=
    fun s ↦ muNModel_eval₂_vanish A N (s.inl.hom : A →+* s.pt)
      (s.inr (muNRingGen N)) (pushout_inr_gen_pow A N s)
  refine IsPushout.of_isColimit' ⟨uliftZ_hom_ext⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (AdjoinRoot.lift (s.inl.hom : A →+* s.pt)
      (s.inr (muNRingGen N)) (test s)))
    (fun s ↦ CommRingCat.hom_ext (AdjoinRoot.lift_comp_of (test s)))
    (fun s ↦ muNRing_hom_ext (by
      rw [CommRingCat.comp_apply,
        show (muNModelCompare A N) (muNRingGen N) = AdjoinRoot.root (muNModelPoly A N) from
          muNRingLift_gen _ _]
      show AdjoinRoot.lift (s.inl.hom : A →+* s.pt) (s.inr (muNRingGen N)) (test s)
        (AdjoinRoot.root (muNModelPoly A N)) = s.inr (muNRingGen N)
      exact AdjoinRoot.lift_root (test s)))
    (fun s m' hleft hright ↦ ?_))
  have hC : m'.hom.comp (AdjoinRoot.of (muNModelPoly A N)) = s.inl.hom := by
    have h3 := congrArg CommRingCat.Hom.hom hleft
    exact h3
  have hX : m'.hom (AdjoinRoot.root (muNModelPoly A N)) = s.inr (muNRingGen N) := by
    have h2 := congrArg (fun (t : muNRing N ⟶ s.pt) ↦ t (muNRingGen N)) hright
    simpa [CommRingCat.comp_apply,
      show (muNModelCompare A N) (muNRingGen N) = AdjoinRoot.root (muNModelPoly A N) from
        muNRingLift_gen _ _] using h2
  have key : m'.hom.comp (AdjoinRoot.mk (muNModelPoly A N)) =
      (AdjoinRoot.lift (s.inl.hom : A →+* s.pt) (s.inr (muNRingGen N))
        (test s)).comp (AdjoinRoot.mk (muNModelPoly A N)) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · rw [show (m'.hom.comp (AdjoinRoot.mk (muNModelPoly A N))).comp Polynomial.C =
          m'.hom.comp (AdjoinRoot.of (muNModelPoly A N)) from rfl, hC]
      exact (AdjoinRoot.lift_comp_of (test s)).symm
    · have hmkX : (AdjoinRoot.mk (muNModelPoly A N)) X = AdjoinRoot.root (muNModelPoly A N) :=
        AdjoinRoot.mk_X
      exact ((congrArg (fun t ↦ m'.hom t) hmkX).trans hX).trans
        (((congrArg (fun t ↦ (AdjoinRoot.lift (s.inl.hom : A →+* s.pt)
          (s.inr (muNRingGen N)) (test s)) t) hmkX).trans
            (AdjoinRoot.lift_root (test s))).symm)
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  exact DFunLike.congr_fun key p

private lemma muNAway_natCast_isUnit (N : ℕ) [NeZero N] : IsUnit (N : muNAwayRing N) := by
  have h0 : IsUnit (algebraMap ℤ (Localization.Away (N : ℤ)) (N : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h1 : IsUnit ((N : ℕ) : Localization.Away (N : ℤ)) := by simpa using h0
  have h2 := h1.map
    (ULift.ringEquiv.symm : Localization.Away (N : ℤ) ≃+* muNAwayRing N).toRingHom
  simpa using h2

/-- `(Xᴺ − 1, C N)` is a standard étale pair: `f'·X − N·f = N`. -/
private def muNStdPair (N : ℕ) [NeZero N] : StandardEtalePair (muNAwayRing N) where
  f := muNModelPoly (muNAwayRing N) N
  monic_f := by simpa using Polynomial.monic_X_pow_sub_C (1 : muNAwayRing N) (NeZero.ne N)
  g := Polynomial.C (N : muNAwayRing N)
  cond := by
    refine ⟨X, -Polynomial.C (N : muNAwayRing N), 1, ?_⟩
    have h1 : (X : (muNAwayRing N)[X]) ^ (N - 1) * X = X ^ N := by
      rw [← pow_succ, Nat.sub_add_cancel NeZero.one_le]
    have hder : derivative (muNModelPoly (muNAwayRing N) N)
        = Polynomial.C (N : muNAwayRing N) * X ^ (N - 1) := by
      simp [muNModelPoly, Polynomial.derivative_X_pow]
    rw [hder, mul_assoc, h1]
    ring

private lemma muNModel_algebra_etale (N : ℕ) [NeZero N] :
    Algebra.Etale (muNAwayRing N) (AdjoinRoot (muNModelPoly (muNAwayRing N) N)) := by
  have hg : IsUnit (AdjoinRoot.mk (muNStdPair N).f (muNStdPair N).g) := by
    show IsUnit (AdjoinRoot.mk (muNModelPoly (muNAwayRing N) N)
      (Polynomial.C (N : muNAwayRing N)))
    rw [AdjoinRoot.mk_C]
    exact (muNAway_natCast_isUnit N).map (AdjoinRoot.of (muNModelPoly (muNAwayRing N) N))
  have e2 := IsLocalization.atUnits (AdjoinRoot (muNStdPair N).f)
    (Submonoid.powers (AdjoinRoot.mk (muNStdPair N).f (muNStdPair N).g))
    (S := Localization.Away (AdjoinRoot.mk (muNStdPair N).f (muNStdPair N).g))
    (Submonoid.powers_le.mpr ((IsUnit.mem_submonoid_iff _).mpr hg))
  have e3 : (muNStdPair N).Ring ≃ₐ[muNAwayRing N]
      AdjoinRoot (muNModelPoly (muNAwayRing N) N) :=
    (muNStdPair N).equivAwayAdjoinRoot.trans
      (AlgEquiv.restrictScalars (muNAwayRing N) e2).symm
  exact Algebra.Etale.of_equiv e3

private lemma muNModelStruct_etale (N : ℕ) [NeZero N] :
    RingHom.Etale (muNModelStruct (muNAwayRing N) N).hom := by
  have h5 := (RingHom.etale_algebraMap (R := muNAwayRing N)
    (S := AdjoinRoot (muNModelPoly (muNAwayRing N) N))).mpr (muNModel_algebra_etale N)
  rw [AdjoinRoot.algebraMap_eq] at h5
  exact h5

/-- **(T-B7, étale criterion — iff form per the T-B7 spec)** `μ_{N,S} ⟶ S` is étale
iff `N` is invertible on `S` (`Tᴺ − 1` separable ⟺ `N` a unit; both sides vacuous
for `S = ∅`). -/
private lemma etale_muNπ_of_isUnit (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (h : IsUnit (N : Γ(S, ⊤))) : Etale (muNπ S N) := by
  have hZ : IsUnit ((Int.castRingHom Γ(S, ⊤)) (N : ℤ)) := by simpa using h
  let ψ : muNAwayRing N →+* Γ(S, ⊤) :=
    (IsLocalization.Away.lift (N : ℤ) hZ).comp ULift.ringEquiv.toRingHom
  let factor : S ⟶ Spec (.of (muNAwayRing N)) :=
    S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hfactor : factor ≫ Spec.map (muNBaseMap (muNAwayRing N))
      = terminal.from S ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom :=
    specULiftZIsTerminal.hom_ext _ _
  have t := (isPullback_SpecMap_of_isPushout _ _ _ _
    (muNModel_isPushout (muNAwayRing N) N)).flip
  have big := (isPullback_muN S N).flip
  rw [← hfactor] at big
  let mid := t.lift (pullback.snd (terminal.from S) (terminal.from (muNAbs N)))
    (muNπ S N ≫ factor) (by rw [← Category.assoc]; exact big.w)
  have hmid1 : mid ≫ Spec.map (muNModelCompare (muNAwayRing N) N) = pullback.snd _ _ :=
    t.lift_fst _ _ _
  have hmid2 : mid ≫ Spec.map (muNModelStruct (muNAwayRing N) N) = muNπ S N ≫ factor :=
    t.lift_snd _ _ _
  rw [← hmid1] at big
  have LEFT := IsPullback.of_right big hmid2 t
  exact MorphismProperty.of_isPullback LEFT
    (HasRingHomProperty.Spec_iff.mpr (muNModelStruct_etale N))

/-- Base change of `μ_{N}` along `g : T ⟶ S`: `μ_{N,T} ⟶ μ_{N,S}` exhibiting `μ_{N,T}` as the
base change `μ_{N,S} ×_S T`. Made public for consumers (e.g. the char-0 Weil-pairing
base-change naturality, `WeilPairing/CharZeroDescent.lean`). -/
lemma isPullback_muN_baseChange (S T : Scheme.{u}) (N : ℕ) (g : T ⟶ S) :
    ∃ θ : muN T N ⟶ muN S N, IsPullback θ (muNπ T N) (muNπ S N) g := by
  have t := (isPullback_muN S N).flip
  have big := (isPullback_muN T N).flip
  have hterm : terminal.from T ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom
      = g ≫ (terminal.from S ≫ (terminalIsoIsTerminal specULiftZIsTerminal).hom) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [hterm] at big
  let θ := t.lift (pullback.snd (terminal.from T) (terminal.from (muNAbs N)))
    (muNπ T N ≫ g) (by rw [← Category.assoc]; exact big.w)
  have hθ1 : θ ≫ pullback.snd (terminal.from S) (terminal.from (muNAbs N))
      = pullback.snd _ _ := t.lift_fst _ _ _
  have hθ2 : θ ≫ muNπ S N = muNπ T N ≫ g := t.lift_snd _ _ _
  rw [← hθ1] at big
  exact ⟨θ, IsPullback.of_right big hθ2 t⟩

/-- Field case of the converse: if `μ_N` is étale over a field, `N` is nonzero in it. -/
private lemma etale_field_nezero (K : Type u) [Field K] (N : ℕ) [NeZero N]
    (h : Etale (muNπ (Spec (CommRingCat.of K)) N)) : (N : K) ≠ 0 := by
  intro hNK
  -- transfer étale to the model over K (LEFT square with identity factor)
  have t := (isPullback_SpecMap_of_isPushout _ _ _ _ (muNModel_isPushout K N)).flip
  have hterm : terminal.from (Spec (CommRingCat.of K)) ≫
      (terminalIsoIsTerminal specULiftZIsTerminal).hom = Spec.map (muNBaseMap K) :=
    specULiftZIsTerminal.hom_ext _ _
  have b := (isPullback_muN (Spec (CommRingCat.of K)) N).flip
  rw [hterm] at b
  let mid := t.lift (pullback.snd _ _) (muNπ _ N) b.w
  have hmid1 : mid ≫ Spec.map (muNModelCompare K N) = pullback.snd _ _ := t.lift_fst _ _ _
  have hmid2 : mid ≫ Spec.map (muNModelStruct K N) = muNπ _ N := t.lift_snd _ _ _
  have big2 : IsPullback (mid ≫ Spec.map (muNModelCompare K N))
      (muNπ (Spec (CommRingCat.of K)) N) (Spec.map (muNRingMap N))
      (𝟙 (Spec (CommRingCat.of K)) ≫ Spec.map (muNBaseMap K)) := by
    rw [Category.id_comp, hmid1]
    exact b
  have LEFT := IsPullback.of_right big2 (by rw [Category.comp_id]; exact hmid2) t
  have triv : IsPullback (𝟙 (Spec (muNModelRing K N))) (Spec.map (muNModelStruct K N))
      (Spec.map (muNModelStruct K N)) (𝟙 (Spec (CommRingCat.of K))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hSpecEtale : Etale (Spec.map (muNModelStruct K N)) := by
    have hesnd : (LEFT.isoIsPullback _ _ triv).hom ≫ Spec.map (muNModelStruct K N)
        = muNπ (Spec (CommRingCat.of K)) N :=
      LEFT.isoIsPullback_hom_snd _ _ triv
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
      (LEFT.isoIsPullback _ _ triv).hom, hesnd]
    exact h
  have hre : RingHom.Etale (muNModelStruct K N).hom :=
    HasRingHomProperty.Spec_iff.mp hSpecEtale
  haveI halg : Algebra.Etale K (AdjoinRoot (muNModelPoly K N)) := by
    refine (RingHom.etale_algebraMap (R := K)
      (S := AdjoinRoot (muNModelPoly K N))).mp ?_
    rw [AdjoinRoot.algebraMap_eq]
    exact hre
  haveI hred : IsReduced (AdjoinRoot (muNModelPoly K N)) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  -- char analysis: q := ringChar K divides N
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hqdvd : ringChar K ∣ N := (CharP.cast_eq_zero_iff K (ringChar K) N).mp hNK
  have hqprime : (ringChar K).Prime := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
    · exact hp
    · rw [h0] at hqdvd
      exact absurd (zero_dvd_iff.mp hqdvd) (NeZero.ne N)
  haveI := Fact.mk hqprime
  haveI : CharP (Polynomial K) (ringChar K) := by
    constructor
    intro n
    rw [← Polynomial.C_eq_natCast, Polynomial.C_eq_zero]
    exact CharP.cast_eq_zero_iff K _ n
  -- the nonzero nilpotent
  have hy : (AdjoinRoot.mk (muNModelPoly K N) (X ^ (N / ringChar K) - 1)) ^ ringChar K
      = 0 := by
    rw [← map_pow, sub_pow_char, one_pow, ← pow_mul, Nat.div_mul_cancel hqdvd]
    exact AdjoinRoot.mk_self
  have h1q : N / ringChar K ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hqprime.ne_zero,
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hqdvd⟩
  have hne : (X : Polynomial K) ^ (N / ringChar K) - 1 ≠ 0 := by
    simpa using (Polynomial.monic_X_pow_sub_C (1 : K) h1q).ne_zero
  have hnil : IsNilpotent (AdjoinRoot.mk (muNModelPoly K N) (X ^ (N / ringChar K) - 1)) :=
    ⟨ringChar K, hy⟩
  have h0 := hnil.eq_zero
  have hdvd := AdjoinRoot.mk_eq_zero.mp h0
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
  have hNle : N ≤ N / ringChar K := by
    have e1 : (muNModelPoly K N).natDegree = N := by
      simpa using Polynomial.natDegree_X_pow_sub_C (n := N) (r := (1 : K))
    have e2 : ((X : Polynomial K) ^ (N / ringChar K) - 1).natDegree = N / ringChar K := by
      simpa using Polynomial.natDegree_X_pow_sub_C (n := N / ringChar K) (r := (1 : K))
    rw [e1, e2] at hdeg
    exact hdeg
  have hlt : N / ringChar K < N :=
    Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne N)) hqprime.one_lt
  omega

private lemma isUnit_of_etale_muNπ (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (h : Etale (muNπ S N)) : IsUnit (N : Γ(S, ⊤)) := by
  by_contra hN
  have hex : ∃ x : S, (N : S.residueField x) = 0 := by
    by_contra hall
    refine hN (S.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤
      (N : Γ(S, ⊤)) fun x hx ↦ ?_)
    have hg : S.presheaf.germ ⊤ x hx ((N : Γ(S, ⊤))) = (N : S.presheaf.stalk x) :=
      map_natCast (S.presheaf.germ ⊤ x hx).hom N
    rw [hg]
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
    have hres : IsLocalRing.residue (S.presheaf.stalk x) (N : S.presheaf.stalk x)
        = (N : S.residueField x) := map_natCast (IsLocalRing.residue _) N
    rw [hres]
    exact not_exists.mp hall x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨θ, sq⟩ := isPullback_muN_baseChange S (Spec (S.residueField x)) N
    (S.fromSpecResidueField x)
  have hT : Etale (muNπ (Spec (S.residueField x)) N) :=
    MorphismProperty.of_isPullback sq h
  exact absurd hx (etale_field_nezero (S.residueField x) N hT)

theorem muNπ_etale_iff (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    Etale (muNπ S N) ↔ IsUnit (N : Γ(S, ⊤)) :=
  ⟨isUnit_of_etale_muNπ S N, etale_muNπ_of_isUnit S N⟩

/-- **[T-CV-1a]** The étale model: for `N` a unit in `A`, the algebra
`A[X]/(Xᴺ − 1)` is étale over `A` (standard étale pair `(Xᴺ − 1, C N)`). -/
theorem muNModel_algebra_etale_of_isUnit (A : Type u) [CommRing A] (N : ℕ)
    [NeZero N] (h : IsUnit (N : A)) :
    Algebra.Etale A (AdjoinRoot ((X : Polynomial A) ^ N - 1)) := by
  let P : StandardEtalePair A :=
    { f := (X : Polynomial A) ^ N - 1
      monic_f := by simpa using Polynomial.monic_X_pow_sub_C (1 : A) (NeZero.ne N)
      g := Polynomial.C (N : A)
      cond := by
        refine ⟨X, -Polynomial.C (N : A), 1, ?_⟩
        have h1 : (X : (Polynomial A)) ^ (N - 1) * X = X ^ N := by
          rw [← pow_succ, Nat.sub_add_cancel NeZero.one_le]
        have hder : derivative ((X : Polynomial A) ^ N - 1)
            = Polynomial.C (N : A) * X ^ (N - 1) := by
          simp [Polynomial.derivative_X_pow]
        rw [hder, mul_assoc, h1]
        ring }
  have hg : IsUnit (AdjoinRoot.mk P.f P.g) := by
    show IsUnit (AdjoinRoot.mk ((X : Polynomial A) ^ N - 1) (Polynomial.C (N : A)))
    rw [AdjoinRoot.mk_C]
    exact h.map (AdjoinRoot.of ((X : Polynomial A) ^ N - 1))
  have e2 := IsLocalization.atUnits (AdjoinRoot P.f)
    (Submonoid.powers (AdjoinRoot.mk P.f P.g))
    (S := Localization.Away (AdjoinRoot.mk P.f P.g))
    (Submonoid.powers_le.mpr ((IsUnit.mem_submonoid_iff _).mpr hg))
  have e3 : P.Ring ≃ₐ[A] AdjoinRoot ((X : Polynomial A) ^ N - 1) :=
    P.equivAwayAdjoinRoot.trans (AlgEquiv.restrictScalars A e2).symm
  exact Algebra.Etale.of_equiv e3

/-- **[T-CV-1a]** The model is module-finite (the defining polynomial is monic). -/
theorem muNModel_finite (A : Type u) [CommRing A] (N : ℕ) [NeZero N] :
    Module.Finite A (AdjoinRoot ((X : Polynomial A) ^ N - 1)) := by
  have hm : ((X : Polynomial A) ^ N - 1).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : A) (NeZero.ne N)
  exact hm.finite_quotient

/-- **[T-CV-1a]** Over a field, `μ_N` is `Spec` of the model `K[X]/(Xᴺ − 1)`. -/
noncomputable def muNSpecFieldIso (K : Type u) [Field K] (N : ℕ) [NeZero N] :
    muN (Spec (CommRingCat.of K)) N ≅
      Spec (CommRingCat.of (AdjoinRoot ((X : Polynomial K) ^ N - 1))) := by
  have t := (isPullback_SpecMap_of_isPushout _ _ _ _ (muNModel_isPushout K N)).flip
  have hterm : terminal.from (Spec (CommRingCat.of K)) ≫
      (terminalIsoIsTerminal specULiftZIsTerminal).hom = Spec.map (muNBaseMap K) :=
    specULiftZIsTerminal.hom_ext _ _
  have b := (isPullback_muN (Spec (CommRingCat.of K)) N).flip
  rw [hterm] at b
  let mid := t.lift (pullback.snd _ _) (muNπ _ N) b.w
  have hmid1 : mid ≫ Spec.map (muNModelCompare K N) = pullback.snd _ _ :=
    t.lift_fst _ _ _
  have hmid2 : mid ≫ Spec.map (muNModelStruct K N) = muNπ _ N := t.lift_snd _ _ _
  have big2 : IsPullback (mid ≫ Spec.map (muNModelCompare K N))
      (muNπ (Spec (CommRingCat.of K)) N) (Spec.map (muNRingMap N))
      (𝟙 (Spec (CommRingCat.of K)) ≫ Spec.map (muNBaseMap K)) := by
    rw [Category.id_comp, hmid1]
    exact b
  have LEFT := IsPullback.of_right big2 (by rw [Category.comp_id]; exact hmid2) t
  have triv : IsPullback (𝟙 (Spec (muNModelRing K N))) (Spec.map (muNModelStruct K N))
      (Spec.map (muNModelStruct K N)) (𝟙 (Spec (CommRingCat.of K))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact LEFT.isoIsPullback _ _ triv

/-- **[T-CV-1a]** The field-model identification lies over the base. -/
theorem muNSpecFieldIso_struct (K : Type u) [Field K] (N : ℕ) [NeZero N] :
    (muNSpecFieldIso K N).hom ≫
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of ((X : Polynomial K) ^ N - 1))) =
      muNπ (Spec (CommRingCat.of K)) N := by
  have t := (isPullback_SpecMap_of_isPushout _ _ _ _ (muNModel_isPushout K N)).flip
  have hterm : terminal.from (Spec (CommRingCat.of K)) ≫
      (terminalIsoIsTerminal specULiftZIsTerminal).hom = Spec.map (muNBaseMap K) :=
    specULiftZIsTerminal.hom_ext _ _
  have b := (isPullback_muN (Spec (CommRingCat.of K)) N).flip
  rw [hterm] at b
  let mid := t.lift (pullback.snd _ _) (muNπ _ N) b.w
  have hmid1 : mid ≫ Spec.map (muNModelCompare K N) = pullback.snd _ _ :=
    t.lift_fst _ _ _
  have hmid2 : mid ≫ Spec.map (muNModelStruct K N) = muNπ _ N := t.lift_snd _ _ _
  have big2 : IsPullback (mid ≫ Spec.map (muNModelCompare K N))
      (muNπ (Spec (CommRingCat.of K)) N) (Spec.map (muNRingMap N))
      (𝟙 (Spec (CommRingCat.of K)) ≫ Spec.map (muNBaseMap K)) := by
    rw [Category.id_comp, hmid1]
    exact b
  have LEFT := IsPullback.of_right big2 (by rw [Category.comp_id]; exact hmid2) t
  have triv : IsPullback (𝟙 (Spec (muNModelRing K N))) (Spec.map (muNModelStruct K N))
      (Spec.map (muNModelStruct K N)) (𝟙 (Spec (CommRingCat.of K))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact LEFT.isoIsPullback_hom_snd _ _ triv

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

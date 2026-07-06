import ModularCurves.LevelStructure.Basic

/-!
# The category Ell/R and moduli problems (KM Ch. 4; Loeffler §3.7)

Katz–Mazur's stacks-without-saying-so formalism, transcribed from Loeffler Def 3.7.1
(verbatim):

> "Let `Ell/R` be the following category: objects are diagrams `E → S` where `S` is some
> `R`-scheme and `E` is an elliptic curve over `S`; morphisms are squares … where
> `E ≅ E' ×_T S`. A *moduli problem* for elliptic curves over `R` is a contravariant
> functor `P : Ell/R → Set`. We say that `P` is *representable* if it is representable; it
> is *relatively representable* if, for every `E/S ∈ Ob(Ell/R)`, the functor
> `Sch/S → Set, T ↦ P(E ×_S T/T)` is representable."

and Loeffler Def 3.7.3 / Thm 3.7.4 (KM 4.7):

> "`P` is *rigid* if for all `E/S`, `Aut(E/S)` acts on `P(E/S)` without fixed points."
> "(Katz–Mazur) `P` is representable if and only if it is relatively representable and
> rigid."

The stack remark (Loeffler, after 3.7.1): "The category `Ell/R` is `Sch/Y` for a `Y` that
does not exist. … This is the idea of *stacks*" — the stack-facing packaging lives in
`Moduli/Stack.lean`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- An object of `Ell/R`: an `R`-scheme `S` together with an elliptic curve `E/S`.
Source: Loeffler Def 3.7.1; KM 4.1. -/
structure EllObj (R : CommRingCat.{u}) where
  /-- The base `R`-scheme. -/
  base : Scheme.{u}
  /-- The structure morphism to `Spec R`. -/
  structMap : base ⟶ Spec R
  /-- The elliptic curve over the base. -/
  curve : EllipticCurve base

variable {R : CommRingCat.{u}}

/-- A morphism of `Ell/R`: a cartesian square over a morphism of `R`-schemes,
compatible with the zero sections.

On `zero_w` (adversarial adjudication, 2026-07-06): the zero clause is NOT in
Loeffler's display (the ellipsis in the quoted Def 3.7.1 is only the square diagram)
and is NOT automatic — a translation `τ_P` over `𝟙` is a cartesian non-pointed square.
It is nonetheless the sources' intended category: "elliptic curve" is the pair
`(E, 0)`, without it the level-structure functors are not functors (translations
destroy torsion data), and Loeffler's own Thm 3.7.4 would be false (Aut would contain
all translations). Verbatim KM 4.1 reconciliation: PENDING-SOURCE(KM Ch. 4).
Source: Loeffler Def 3.7.1 ("morphisms are squares … where `E ≅ E' ×_T S`"); KM 4.1. -/
structure EllHom (X Y : EllObj R) where
  baseHom : X.base ⟶ Y.base
  base_w : baseHom ≫ Y.structMap = X.structMap
  top : X.curve.E ⟶ Y.curve.E
  /-- The square is cartesian: `E ≅ E' ×_T S`. -/
  isPullback : IsPullback top X.curve.π Y.curve.π baseHom
  /-- Compatibility with the zero sections. -/
  zero_w : X.curve.zero ≫ top = baseHom ≫ Y.curve.zero

attribute [ext] EllHom

instance : Category (EllObj R) where
  Hom := EllHom
  id X :=
    { baseHom := 𝟙 _
      base_w := by simp
      top := 𝟙 _
      isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
      zero_w := by simp }
  comp f g :=
    { baseHom := f.baseHom ≫ g.baseHom
      base_w := by rw [Category.assoc, g.base_w, f.base_w]
      top := f.top ≫ g.top
      isPullback := f.isPullback.paste_horiz g.isPullback
      zero_w := by rw [← Category.assoc, f.zero_w, Category.assoc, g.zero_w,
        Category.assoc] }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp

/-- A **moduli problem** for elliptic curves over `R`: a contravariant functor
`Ell/R → Set`. Source: Loeffler Def 3.7.1(2); KM 4.2. -/
abbrev ModuliProblem (R : CommRingCat.{u}) := (EllObj R)ᵒᵖ ⥤ Type u

namespace ModuliProblem

/-- The base change of an `Ell/R` object along `g : T ⟶ S` (an `R`-scheme morphism over
the base of `X`). Total space `E ×_S T`. -/
noncomputable def _root_.ModularCurves.EllObj.pullbackAlong (X : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X.base) : EllObj R where
  base := T
  structMap := g ≫ X.structMap
  curve := X.curve.baseChange g

/-- The canonical comparison morphism `X ×_S T' ⟶ X ×_S T` in `Ell/R` induced by
`k : T' ⟶ T` over `g : T ⟶ X.base` (base-change functoriality). -/
noncomputable def _root_.ModularCurves.EllObj.pullbackAlongMap (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) :
    X.pullbackAlong (k ≫ g) ⟶ X.pullbackAlong g where
  baseHom := k
  base_w := by simp [EllObj.pullbackAlong]
  top := Limits.pullback.map _ _ _ _ (𝟙 _) k (𝟙 _) (by simp) (by simp)
  isPullback := by
    have hbig := IsPullback.of_hasPullback X.curve.π (k ≫ g)
    have hfst : Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
          (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
        Limits.pullback.fst X.curve.π (k ≫ g) := by
      rw [Limits.pullback.lift_fst, Category.comp_id]
    rw [← hfst] at hbig
    refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback X.curve.π g)
    show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) ≫ Limits.pullback.snd X.curve.π g =
      Limits.pullback.snd X.curve.π (k ≫ g) ≫ k
    rw [Limits.pullback.lift_snd]
  zero_w := by
    show Limits.pullback.lift ((k ≫ g) ≫ X.curve.zero) (𝟙 T')
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
      Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) =
      k ≫ Limits.pullback.lift (g ≫ X.curve.zero) (𝟙 T)
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id, Category.id_comp])
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      rw [show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
            (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
          Limits.pullback.fst X.curve.π (k ≫ g) ≫ 𝟙 _ from
        Limits.pullback.lift_fst _ _ _]
      rw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
      exact Category.comp_id _
    · simp only [Category.assoc]
      rw [show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
            (by simp) (by simp) ≫ Limits.pullback.snd X.curve.π g =
          Limits.pullback.snd X.curve.π (k ≫ g) ≫ k from
        Limits.pullback.lift_snd _ _ _]
      rw [Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
      exact (Category.id_comp k).trans (Category.comp_id k).symm

/-- `P` is **representable** if it is a representable presheaf on `Ell/R` — mathlib's
`Functor.IsRepresentable`, under the project's name (kept as an `abbrev` so the two
never diverge). Source: Loeffler Def 3.7.1(3); KM 4.3. -/
abbrev Representable (P : ModuliProblem R) : Prop :=
  P.IsRepresentable

/-- `P` is **relatively representable**: for every `E/S` in `Ell/R`, the functor
`Sch/S → Set`, `T ↦ P(E ×_S T / T)` is representable — stated with its naturality
clause (the representing bijections commute with restriction along `T' ⟶ T`).
Source: Loeffler Def 3.7.1(3); KM 4.2. Full comma-category packaging: ticket `T-E3`. -/
def RelativelyRepresentable (P : ModuliProblem R) : Prop :=
  ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base),
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ Z // h ≫ f = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          P.map (X.pullbackAlongMap g k).op (eqv g h)

/-- `P` is **rigid**: for every `E/S`, `Aut(E/S)` (automorphisms over the identity of the
base) acts on `P(E/S)` without fixed points.
Source: Loeffler Def 3.7.3; KM 4.4 ("rigid moduli problems"). -/
def Rigid (P : ModuliProblem R) : Prop :=
  ∀ (X : EllObj R) (e : X ≅ X), e.hom.baseHom = 𝟙 X.base → e ≠ Iso.refl X →
    ∀ a : P.obj (Opposite.op X), P.map e.hom.op a ≠ a

/-- **(T-E5 = Loeffler Thm 3.7.4 = KM 4.7)** A moduli problem is representable iff it is
relatively representable and rigid. (⇐ is the hard direction: bootstrap through naive
level 3 over `ℤ[1/3]` and the Legendre problem over `ℤ[1/2]`, take quotients by the finite
group actions, and glue over `ℤ[1/6]` — Loeffler's proof sketch; KM Ch. 4 + explicit
constructions. Requires quotients by finite groups: workstream E blocks on `T-E6`.) -/
theorem representable_iff (P : ModuliProblem R) :
    P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid := by sorry

end ModuliProblem

end ModularCurves

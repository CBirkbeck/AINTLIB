import ModularCurves.ForMathlib.FiniteProperProduct
import ModularCurves.ForMathlib.SchemeTheoreticImage

/-!
# Scheme-theoretic closures in finite products of proper schemes

This file packages the closure of a compatible family of morphisms in a finite product of
proper schemes over a common base.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteProperClosure

noncomputable section

variable {S T : Scheme.{u}} {ι : Type u} [Finite ι]
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ S)
variable (q : T ⟶ S) (f : ∀ i, T ⟶ Z i) (hf : ∀ i, f i ≫ p i = q)

/-- The map from the common open subscheme to the finite proper product. -/
abbrev diagonal : T ⟶ FiniteProperProduct.obj p :=
  FiniteProperProduct.lift p q f hf

/-- The scheme-theoretic closure of the common open subscheme in the finite proper product. -/
abbrev obj : Scheme.{u} :=
  (diagonal p q f hf).image

/-- The closed immersion of the closure into the finite proper product. -/
abbrev inclusion : obj p q f hf ⟶ FiniteProperProduct.obj p :=
  (diagonal p q f hf).imageι

/-- The canonical map from the common open subscheme to its closure. -/
abbrev toClosure : T ⟶ obj p q f hf :=
  (diagonal p q f hf).toImage

/-- The structure map from the closure to the base. -/
abbrev π : obj p q f hf ⟶ S :=
  inclusion p q f hf ≫ FiniteProperProduct.π p

/-- The projection from the closure to the `i`-th proper factor. -/
abbrev proj (i : ι) : obj p q f hf ⟶ Z i :=
  inclusion p q f hf ≫ FiniteProperProduct.proj p i

@[reassoc (attr := simp)]
lemma toClosure_inclusion :
    toClosure p q f hf ≫ inclusion p q f hf = diagonal p q f hf :=
  Scheme.Hom.toImage_imageι _

@[reassoc]
lemma proj_comp (i : ι) : proj p q f hf i ≫ p i = π p q f hf := by
  simp only [proj, π, Category.assoc, FiniteProperProduct.proj_comp]

@[reassoc]
lemma toClosure_proj (i : ι) : toClosure p q f hf ≫ proj p q f hf i = f i := by
  simp only [proj, toClosure_inclusion_assoc, FiniteProperProduct.lift_proj]

/-- The closure is proper over the base. -/
lemma π_isProper (hp : ∀ i, IsProper (p i)) : IsProper (π p q f hf) := by
  letI : IsProper (FiniteProperProduct.π p) := FiniteProperProduct.π_isProper p hp
  infer_instance

/-- The projections from the closure to the proper factors are proper. -/
lemma proj_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (proj p q f hf i) := by
  letI : IsProper (FiniteProperProduct.proj p i) :=
    FiniteProperProduct.proj_isProper p hp i
  infer_instance

/-- The common open subscheme is scheme-theoretically dense in its closure. -/
lemma toClosure_isSchemeTheoreticallyDominant [QuasiCompact (diagonal p q f hf)] :
    IsSchemeTheoreticallyDominant (toClosure p q f hf) :=
  Scheme.Hom.toImage_isSchemeTheoreticallyDominant _

/-- If the coordinate maps are immersions, the common open subscheme is open in its closure. -/
lemma toClosure_isOpenImmersion [Nonempty ι] (hfi : ∀ i, IsImmersion (f i))
    [QuasiCompact (diagonal p q f hf)] : IsOpenImmersion (toClosure p q f hf) := by
  letI : IsImmersion (diagonal p q f hf) :=
    FiniteProperProduct.lift_isImmersion p q f hf hfi
  infer_instance

end

end AlgebraicGeometry.Scheme.FiniteProperClosure

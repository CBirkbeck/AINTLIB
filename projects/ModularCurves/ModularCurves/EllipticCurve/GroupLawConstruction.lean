import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelVariableChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The group law on the projective Weierstrass model, uniformly over every ring

**(T-W7 skeleton, lanes P0/P1 — `/develop --decompose` 2026-07-07.)** Negation and
multiplication as *morphisms of schemes* on `projModel W`, for every Weierstrass curve `W`
over every ring `R` (with unit discriminant), via the **Bosma–Lenstra complete system of two
addition laws of bidegree (2,2)** — the laws of the lines `Z = 0` (exceptional locus: the
diagonal) and `Y = 0` (exceptional: `P₁ − P₂ ∈ E ∩ {Y = 0}`), whose exceptional loci are
disjoint over every field since `O = (0:1:0) ∉ {Y = 0}`. The group axioms are stated at the
`Over (Spec R)` monoidal level; their proofs go through the field-points dictionary + the
extensionality principle of `PointsDictionary.lean` over the (reduced, universal) atlas, then
transport to every `R` by the base-change naturality `mulModelHom_map` along the classifying
map — no rigidity, no cohomology.

Sources: Bosma–Lenstra, *Complete systems of two addition laws for elliptic curves*, JNT 53
(1995) 229–240 (Thm 1, Thm 2, §5 formulas; local `refs/`, verbatim quotes in
`.mathlib-quality/tw7-source-quotes.md`); Lange–Ruppert, Invent. Math. 79 (1985); reviewer
round 1 §Q1; audits A2/A5/A6.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-! ## Lane P0: the atlas ring is a domain; negation -/

/-- **(T-W7.0a-i)** The universal discriminant is a nonzero polynomial (evaluate at
`y² = x³ − x` over `ℚ`: `Δ = 64`). -/
theorem universalWeierstrass_Δ_ne_zero : universalWeierstrass.Δ ≠ 0 := by
  sorry

/-- **(T-W7.0a)** The Weierstrass atlas ring `ℤ[a₁,…,a₆][Δ⁻¹]` is an integral domain —
the substrate making the universal atlas products *reduced*, hence amenable to the
field-points extensionality principle. Source: `IsLocalization.isDomain_localization`
(mathlib, verified) + `universalWeierstrass_Δ_ne_zero`. -/
instance : IsDomain WeierstrassAtlasRing :=
  sorry

/-- **(T-W7.0b)** Negation on the projective Weierstrass model: the projectivisation of
`(x, y) ↦ (x, −y − a₁x − a₃)` (denominator-free, hence a morphism outright; linear on the
infinity chart). Source: Silverman III.2; mathlib `Affine.negY`. -/
noncomputable def negModelHom (W : WeierstrassCurve R) : projModel W ⟶ projModel W :=
  sorry

/-- **(T-W7.0b-π)** Negation is a morphism over `Spec R`. -/
@[reassoc]
theorem negModelHom_π (W : WeierstrassCurve R) :
    negModelHom W ≫ projModelπ W = projModelπ W := by
  sorry

/-- **(T-W7.0b-invol)** Negation is an involution. -/
theorem negModelHom_negModelHom (W : WeierstrassCurve R) :
    negModelHom W ≫ negModelHom W = 𝟙 (projModel W) := by
  sorry

/-- **(T-W7.0b-zero)** Negation fixes the point at infinity. -/
theorem negModelHom_zero (W : WeierstrassCurve R) :
    projModelZero W ≫ negModelHom W = projModelZero W := by
  sorry

/-- **(T-W7.0b-points)** On field points, `negModelHom` is mathlib's negation through the
dictionary. Source: `Affine.negY` vs the projectivised formula; `projModelPointsEquiv`. -/
theorem negModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨P.1 ≫ negModelHom W, by rw [Category.assoc, negModelHom_π, P.2]⟩ =
      -(projModelPointsEquiv W K P) := by
  sorry

/-! ## Lane P1: the Bosma–Lenstra two-law multiplication -/

/-- **(T-W7.0c·c1-Z, the open)** The regularity open of the `Z = 0` addition law on
`E ×_R E`: the complement of its exceptional divisor, which over every field is exactly the
locus `P₁ ≠ P₂` (B–L Thm 2 at the line `Z = 0`: exceptional ⟺ `P₁ − P₂ ∈ E ∩ {Z=0} = {O}`).
Source: B–L Thm 2 + "lines y = 0, z = 0" (quotes file). -/
noncomputable def blOpenZ (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  sorry

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the `Y = 0` addition law: over every
field, the locus `P₁ − P₂ ∉ E ∩ {Y = 0}` (contains the diagonal and the infinity loci since
`O ∉ {Y=0}`). Source: B–L Thm 2 at the line `Y = 0`. -/
noncomputable def blOpenY (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  sorry

/-- **(T-W7.0c·c1-Z, the morphism)** The `Z = 0` addition law as a morphism on its
regularity open: the explicit bidegree-(2,2) polynomial triple of B–L §5. Source: B–L §5
(transcribe from the PDF at implementation; CAS-verify each polynomial first). -/
noncomputable def addOnZ (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).toScheme ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c1-Y, the morphism)** The `Y = 0` addition law as a morphism on its
regularity open. Source: B–L §5. -/
noncomputable def addOnY (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).toScheme ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c2)** The two regularity opens cover the product: the exceptional divisors
are disjoint over every field (their common zero would be a point with `P₁ − P₂ = O` and
`P₁ − P₂ ∈ {Y = 0}`, but `O ∉ {Y = 0}`), and coverage is a fibrewise/topological statement.
Source: B–L Thm 2 + p. 230–231 ("any two distinct lines … intersect outside E(k)"). -/
theorem blOpen_cover (W : WeierstrassCurve R) [W.IsElliptic] :
    blOpenZ W ⊔ blOpenY W = ⊤ := by
  sorry

/-- **(T-W7.0c·c3)** The two laws agree on the overlap: a polynomial identity modulo the two
curve relations, bidegree-(2,2)-by-(2,2), over `ℤ[a₁,…,a₆]` — discharged by
`linear_combination` with precomputed cofactors, split per coordinate. NO `maxHeartbeats`.
Source: B–L Thm 2 (both laws compute the group law where defined, so they agree on points;
the scheme-level identity is the §5 polynomial identity). -/
theorem addOn_agree (W : WeierstrassCurve R) [W.IsElliptic] :
    (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_left ≫ addOnZ W =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnY W := by
  sorry

/-- **(T-W7.0c·c4)** THE multiplication morphism on the projective Weierstrass model, glued
from the two Bosma–Lenstra addition laws. Source: B–L Thm 1 (two laws suffice — and are
necessary: no single law is total); glue via `Scheme.Cover.glueMorphisms`-style plumbing on
the two-open cover. -/
noncomputable def mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    pullback (projModelπ W) (projModelπ W) ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c4-Z-spec)** `mulModelHom` restricts to the `Z`-law on its open. -/
theorem blOpenZ_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).ι ≫ mulModelHom W = addOnZ W := by
  sorry

/-- **(T-W7.0c·c4-Y-spec)** `mulModelHom` restricts to the `Y`-law on its open. -/
theorem blOpenY_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).ι ≫ mulModelHom W = addOnY W := by
  sorry

/-- **(T-W7.0d)** Multiplication is a morphism over `Spec R`. Source: the B–L triples are
bihomogeneous with coefficients in `R` — the composite to `Spec R` is the structure map on
each piece. -/
@[reassoc]
theorem mulModelHom_π (W : WeierstrassCurve R) [W.IsElliptic] :
    mulModelHom W ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  sorry

/-- **(T-W7.0c·c6, the spec)** On field points, `mulModelHom` is mathlib's `Point.add`
through the dictionary — for EVERY pair (the B–L laws compute the chord–tangent sum wherever
each is defined, and the two opens cover). This single spec is what every group axiom
consumes. Source: B–L Thm 2 ("addition law" = computes the sum in `E(K)`); mathlib
`Affine.Point.add`; §5 formulas vs `Affine.slope`/`addX`/`addY` on the secant locus. -/
theorem mulModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W, by
          rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv W K P + projModelPointsEquiv W K Q := by
  sorry

/-- **(T-W7.0c·nat)** Base-change naturality of the multiplication morphism: the B–L
polynomial data has coefficients entering polynomially, so `mulModelHom` commutes with base
change along any ring map. This is the transport that carries the universal-atlas group
axioms to every ring (audit A6: universality-by-instantiation). Source: B–L p. 231
("coefficients … enter polynomially into all formulae … the same formulae can be used …
over commutative rings"). -/
theorem mulModelHom_map {R' : Type u} [CommRing R'] (f : R →+* R')
    (W : WeierstrassCurve R) [W.IsElliptic] [(W.map f).IsElliptic] :
    mulModelHom (W.map f) ≫ projModelBaseChange f W =
      pullback.map (projModelπ (W.map f)) (projModelπ (W.map f))
          (projModelπ W) (projModelπ W)
          (projModelBaseChange f W) (projModelBaseChange f W)
          (Spec.map (CommRingCat.ofHom f))
          (projModelBaseChange_π f W).symm (projModelBaseChange_π f W).symm ≫
        mulModelHom W := by
  sorry

/-! ## Lane P1 (join with P0/P2): the group axioms at the `Over (Spec R)` level -/

variable (W : WeierstrassCurve R) [W.IsElliptic]

/-- The model as an object of `Over (Spec R)`. -/
noncomputable abbrev modelOver (W : WeierstrassCurve R) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (projModelπ W)

/-- **(T-W7.0g-mul)** The multiplication as an `Over`-morphism from the cartesian tensor
(whose underlying scheme is the fibre product). -/
noncomputable def mulOver : modelOver W ⊗ modelOver W ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-mul-left)** The underlying scheme morphism of `mulOver` is `mulModelHom`. -/
theorem mulOver_left : (mulOver W).left = mulModelHom W := by
  sorry

/-- **(T-W7.0g-one)** The unit as an `Over`-morphism, via the zero section. -/
noncomputable def oneOver : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-one-left)** The underlying morphism of the unit is the zero section
(precomposed with the structure map of the monoidal unit). -/
theorem oneOver_left :
    (oneOver W).left = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W := by
  sorry

/-- **(T-W7.0g-inv)** The inverse as an `Over`-morphism, via `negModelHom`. -/
noncomputable def invOver : modelOver W ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-inv-left)** The underlying morphism of the inverse is `negModelHom`. -/
theorem invOver_left : (invOver W).left = negModelHom W := by
  sorry

/-- **(T-W7.0g-assoc)** Associativity, as the monoid-object equation in `Over (Spec R)`.
Proof route: over the universal atlas by field-points extensionality + the dictionary +
mathlib's `add_assoc` on `Affine.Point`; then for every `R` by instantiating the naturality
`mulModelHom_map` along the classifying map. Source: reviewer round 1 §Q4/Q5; audit A5/A6;
GIT-free, cohomology-free. -/
theorem mulOver_assoc :
    (mulOver W ▷ modelOver W) ≫ mulOver W =
      (α_ (modelOver W) (modelOver W) (modelOver W)).hom ≫
        (modelOver W ◁ mulOver W) ≫ mulOver W := by
  sorry

/-- **(T-W7.0g-one-mul)** Left unit law. -/
theorem oneOver_mulOver :
    (oneOver W ▷ modelOver W) ≫ mulOver W = (λ_ (modelOver W)).hom := by
  sorry

/-- **(T-W7.0g-mul-one)** Right unit law. -/
theorem mulOver_oneOver :
    (modelOver W ◁ oneOver W) ≫ mulOver W = (ρ_ (modelOver W)).hom := by
  sorry

/-- **(T-W7.0g-comm)** Commutativity. -/
theorem mulOver_comm :
    (β_ (modelOver W) (modelOver W)).hom ≫ mulOver W = mulOver W := by
  sorry

/-- **(T-W7.0g-inv-law)** The left inverse law. -/
theorem invOver_mulOver :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W := by
  sorry

/-! ## Lane P1 (with P3): variable-change equivariance -/

/-- **(T-W7.0h)** Global variable-change equivariance of the multiplication morphism:
the model isomorphism of a variable change intertwines the two glued multiplications —
including the diagonal, anti-diagonal and infinity loci (reviewer round 1 caveat: the affine
cocycle alone is not enough). Proof route: field-points extensionality over the universal
VC-base `R ⊗ ℤ[u^±, r, s, t]` (a domain) + the affine cocycle (`pointEquiv` machinery,
project, DONE) at points. Source: audit item 8; `ForMathlib/AffinePointVariableChange`. -/
theorem mulModelHom_vc (C : VariableChange R) (W : WeierstrassCurve R)
    [W.IsElliptic] [(C • W).IsElliptic] :
    mulModelHom (C • W) ≫ (projModelVCIso C W).hom =
      pullback.map (projModelπ (C • W)) (projModelπ (C • W))
          (projModelπ W) (projModelπ W)
          (projModelVCIso C W).hom (projModelVCIso C W).hom (𝟙 (Spec (CommRingCat.of R)))
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm)
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm) ≫
        mulModelHom W := by
  sorry

end ModularCurves

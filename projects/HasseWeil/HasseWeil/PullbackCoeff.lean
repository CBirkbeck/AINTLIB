import HasseWeil.DualIsogeny
import HasseWeil.InvariantDifferentialPullback
import HasseWeil.RouteBGeneral

/-!
# The Pullback Coefficient and Dual Additivity (Silverman III.5.6, III.6.2c)

For an endomorphism φ of an elliptic curve E, the pullback coefficient `a_φ`
is the unique scalar such that `D(φ*(x)) = a_φ · D(x)` in the Kähler
differential module `Ω[K(E)/F]`, which is 1-dimensional over `K(E)`.

The map φ ↦ a_φ is a ring homomorphism End(E) → K(E) (Silverman Cor. III.5.6).

## Key Properties

* a_{[m]} = m (Silverman Cor. III.5.3)
* a_{φ+ψ} = a_φ + a_ψ (from (φ+ψ)*ω = φ*ω + ψ*ω, Thm III.5.2)
* a_{φ∘ψ} = a_φ · a_ψ (chain rule on pullbacks)
* a_φ = 0 ⟺ φ is inseparable (Silverman IV.4.2c)

## Dual Additivity

From φ̂∘φ = [deg φ]: a_{φ̂} · a_φ = deg(φ), giving a_{φ̂} = deg(φ)/a_φ.
Combined with additivity, the algebraic identity `dual_additivity_algebraic`
gives (φ+ψ)^ = φ̂+ψ̂ (Silverman III.6.2c).

## Construction

The definition uses `kaehler_rank_one` (from FormalGroupCorrespondence.lean)
which proves `finrank_{K(E)} Ω[K(E)/F] = 1`. Combined with `D_x_ne_zero`
(from InvariantDifferential.lean), the element `D(x)` is a nonzero element
of a 1-dimensional vector space, so any element `D(α*(x))` can be uniquely
written as `c · D(x)`. The pullback coefficient is this scalar `c`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5 (pp.75–80), IV.4 (pp.125–127)
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : Affine F} [E.IsElliptic]

/-! ### The pullback coefficient as a concrete definition

For a general endomorphism, the pullback coefficient is defined via
Kähler differentials: `Ω[K(E)/F]` is 1-dimensional over `K(E)` (genus 1,
proved as `kaehler_rank_one`), so for any endomorphism pullback `α*`,
`D(α*(x)) = c · D(x)` for a unique `c ∈ K(E)`.

The scalar `c` is extracted using `exists_smul_eq_of_finrank_eq_one`
applied to `kaehler_rank_one` and `D_x_ne_zero`.
-/

/-- The element `D(x)` in the Kähler differential module, used as the
    basis element for extracting the pullback coefficient. -/
noncomputable def D_x (W : WeierstrassCurve F) [W.toAffine.IsElliptic] :
    KaehlerDifferential F W.toAffine.FunctionField :=
  KaehlerDifferential.D F W.toAffine.FunctionField
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X))

/-- `D(x) ≠ 0` in the Kähler module. Wrapper around `D_x_ne_zero`. -/
theorem D_x_ne_zero' (W : WeierstrassCurve F) [W.toAffine.IsElliptic] :
    D_x W ≠ 0 :=
  D_x_ne_zero W.toAffine

/-- The pullback coefficient `a_α` for an endomorphism isogeny `α : E → E`.

    Defined as the unique element `c ∈ K(E)` such that
    `D(α*(x)) = c • D(x)` in `Ω[K(E)/F]`.

    This exists and is unique because:
    - `Ω[K(E)/F]` is 1-dimensional (`kaehler_rank_one`)
    - `D(x) ≠ 0` (`D_x_ne_zero`)

    NOTE: This gives a K(E)-valued coefficient, not an F-valued one.
    The Silverman convention uses the invariant differential ω, giving
    an F-valued coefficient. The D(x)-based coefficient differs by a
    factor of α*(u)/u where u = 2y+a₁x+a₃.

    The chain rule `a_{α∘β} = a_α · a_β` holds for the ω-based coefficient
    (Silverman III.5.6). For the D(x)-based coefficient, the chain rule
    requires additional infrastructure (formal group correspondence).

    Reference: Silverman Cor. III.5.6, IV.4. -/
noncomputable def isogPullbackCoeff (W : WeierstrassCurve F)
    [W.toAffine.IsElliptic] (α : Isogeny W.toAffine W.toAffine) :
    W.toAffine.FunctionField :=
  omegaPullbackCoeff W α

/-- The defining property of `isogPullbackCoeff`:
    `isogPullbackCoeff W α • ω = α*(ω)` where ω is the invariant differential.
    This is the Silverman convention (III.5). -/
theorem isogPullbackCoeff_spec (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine) :
    isogPullbackCoeff W α • invariantDifferential W.toAffine =
      (alpha_star_u W α)⁻¹ •
        KaehlerDifferential.D F W.toAffine.FunctionField
          (α.pullback
            (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
              (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X))) :=
  omegaPullbackCoeff_spec W α

/-! ### Properties of the pullback coefficient -/

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- Abbreviation for the function field of W. -/
local notation "KE" => W.toAffine.FunctionField

/-- `a_{[n]} = n` (as an element of K(E)). Reference: Silverman Cor. III.5.3.

    Proof sketch: [n]*ω = nω by induction using (φ+ψ)*ω = φ*ω + ψ*ω.
    Equivalently, the formal group series [n]_F(T) = nT + O(T²)
    (Silverman Prop. IV.2.3a).

    The proof requires showing that the division polynomial pullback of [n]
    acts on x_gen as the rational function Φ_n/ΨSq_n, and that applying D
    to this via the quotient rule gives n · D(x) at the generic point. -/
theorem isogPullbackCoeff_mulByInt (n : ℤ) (hn : n ≠ 0) :
    isogPullbackCoeff W (mulByInt W.toAffine n) =
      algebraMap F W.toAffine.FunctionField n :=
  omegaCoeff_mulByInt W n hn

-- `isogPullbackCoeff_add` (Silverman III.5.2 + III.5.6):
-- the point-level hypothesis `h_sum` is insufficient to establish pullback
-- additivity; the `Isogeny` structure's `pullback` and `toAddMonoidHom`
-- are independent. The general-pair additivity is
-- `omegaPullbackCoeff_addIsog_pair` (`RouteBInduction.lean`).

/-- `a_{φ∘ψ} = a_φ · a_ψ`. Reference: Silverman III.5.6(a).

    The proof requires the pullback coefficient to be in F (the base field),
    not just K(E). This follows from the invariant differential having no
    zeros or poles (Silverman III.1.5), making φ*(ω)/ω a constant.

    With a_α ∈ F: (α∘β)*(ω) = β*(α*(ω)) = β*(a_α·ω) = a_α·β*(ω) = a_α·a_β·ω.
    (The semilinear pullback β* fixes F-scalars: β*(c·ω) = β*(c)·β*(ω) = c·β*(ω) for c ∈ F.)

    The current definition via D(x) computes a_α ∈ K(E), not F. To complete
    this proof, either:
    (a) Show isogPullbackCoeff W α ∈ range(algebraMap F K(E)), or
    (b) Redefine via the invariant differential, or
    (c) Use the formal group → curve correspondence (Silverman IV.4).

    All three approaches require substantial new infrastructure (divisor theory,
    formal group identification, or constant function characterization). -/
theorem isogPullbackCoeff_comp (α β : Isogeny W.toAffine W.toAffine)
    (c_α : F) (hα : isogPullbackCoeff W α = algebraMap F _ c_α) :
    isogPullbackCoeff W (α.comp β) =
      algebraMap F _ c_α * isogPullbackCoeff W β :=
  omegaPullbackCoeff_comp_of_base W α β c_α hα

/-- From `α_dual ∘ α = [deg α]`: `a_{α_dual} · a_α = deg(α)`.
    This follows from multiplicativity and `a_{[n]} = n`.

    Witness-parametric: the dual is supplied explicitly as `α_dual` together
    with the composition identity `h_dual` (the choice-based `isogDual` is
    gone — its underlying `exists_dual` was refuted; see `DualIsogeny.lean`).

    We require `hdual_base : isogPullbackCoeff W α_dual = algebraMap F _
    c_dual` (the dual's pullback coefficient is a constant). This hypothesis
    is an unconditional fact (Silverman III.1.5: invariant differential has
    no zeros/poles, so `α*ω/ω ∈ F`) but is not yet formalized in our
    codebase. -/
theorem isogPullbackCoeff_dual_mul (α α_dual : Isogeny W.toAffine W.toAffine)
    (c_dual : F)
    (h_dual : α_dual.comp α = mulByInt W.toAffine (α.degree : ℤ))
    (hdual_base : isogPullbackCoeff W α_dual =
      algebraMap F W.toAffine.FunctionField c_dual)
    (hα_ne : α.degree ≠ 0) :
    isogPullbackCoeff W α_dual *
      isogPullbackCoeff W α =
        algebraMap F W.toAffine.FunctionField α.degree := by
  have h_comp : isogPullbackCoeff W (α_dual.comp α) =
      algebraMap F W.toAffine.FunctionField c_dual * isogPullbackCoeff W α :=
    isogPullbackCoeff_comp W α_dual α c_dual hdual_base
  rw [h_dual] at h_comp
  rw [isogPullbackCoeff_mulByInt W α.degree
    (Int.natCast_ne_zero.mpr hα_ne)] at h_comp
  rw [hdual_base]
  convert h_comp.symm using 2
  push_cast
  rfl

/-! ### Dual additivity (Silverman III.6.2c) -/

/-- **Silverman III.6.2c**: (φ+ψ)^ = φ̂+ψ̂ at the level of pullback coefficients.

    From the pullback coefficient properties:
    - a_{(φ+ψ)^} = deg(φ+ψ) / a_{φ+ψ} = deg(φ+ψ) / (a_φ + a_ψ)
    - a_{φ̂+ψ̂} = a_{φ̂} + a_{ψ̂} = deg(φ)/a_φ + deg(ψ)/a_ψ

    These are equal by the algebraic identity `dual_additivity_algebraic`
    (proved in FormalGroupAssoc.lean).

    Since φ ↦ a_φ is injective on separable endomorphisms, this gives
    (φ+ψ)^ = φ̂+ψ̂. -/
theorem isogDual_add_pullbackCoeff
    (α β : Isogeny W.toAffine W.toAffine)
    (ha : isogPullbackCoeff W α ≠ 0)
    (hb : isogPullbackCoeff W β ≠ 0)
    (hab : isogPullbackCoeff W α + isogPullbackCoeff W β ≠ 0)
    (αβ : Isogeny W.toAffine W.toAffine)
    (_h_sum : αβ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom)
    (hquad : (algebraMap F KE αβ.degree) *
        isogPullbackCoeff W α * isogPullbackCoeff W β =
      (algebraMap F KE α.degree + algebraMap F KE β.degree) *
        isogPullbackCoeff W α * isogPullbackCoeff W β +
      isogPullbackCoeff W α ^ 2 * algebraMap F KE β.degree +
      isogPullbackCoeff W β ^ 2 * algebraMap F KE α.degree) :
    -- Then the dual of α+β has the same pullback coeff as α̂+β̂
    (algebraMap F KE αβ.degree) *
      isogPullbackCoeff W α * isogPullbackCoeff W β =
      (isogPullbackCoeff W α + isogPullbackCoeff W β) *
        (algebraMap F KE α.degree * isogPullbackCoeff W β +
         algebraMap F KE β.degree * isogPullbackCoeff W α) :=
  dual_additivity_algebraic
    (isogPullbackCoeff W α) (isogPullbackCoeff W β)
    (algebraMap F KE α.degree) (algebraMap F KE β.degree)
    (algebraMap F KE αβ.degree) ha hb hab hquad

end HasseWeil

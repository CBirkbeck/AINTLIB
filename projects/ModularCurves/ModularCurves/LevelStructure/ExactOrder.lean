import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.EllipticCurve.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Points of exact order N (Drinfeld / KM 1.4)

The delicate definition this project exists to get right. Transcribed from KM 1.4
(verbatim source with proofs in hand — preview, book pp. 15–19):

* KM 1.3.6: an effective Cartier divisor `D` in a smooth group-curve `C/S`, proper over
  `S`, **is a subgroup** "if for every `S`-scheme `T` the subset `D(T)` of the group `C(T)`
  is in fact a sub-group".
* KM 1.4.1: "We say that a point `P ∈ C(S)` has **'exact order N'** if the effective
  Cartier divisor `D` in `C/S` of degree `N` defined by `D := [P] + [2P] + ⋯ + [NP]` is a
  subgroup of `C/S`."
* KM 1.4.2: exact order `N` ⇒ `NP = 0` (via: a finite locally free commutative group
  scheme of rank `N` is killed by `N`, KM cite [Oort–Tate] — black-box register item
  BB-DELIGNE).
* Caution 1.4.3: over an `𝔽_p`-scheme the zero section has "exact order `pⁿ`" for every
  `n` (it generates `Ker(Fⁿ)`) — "a given point can have many different 'exact orders'".
* KM 1.4.4: for `N` invertible on `S`, exact order `N` ⇔ geometric-fibrewise the `N`
  points `{a P}` are pairwise distinct ⇔ `Σₐ [aP]` is finite étale over `S` ⇔ the map
  `ℤ/Nℤ → C`, `1 ↦ P`, is a closed immersion onto `Σₐ [aP]`.

This is precisely the subtlety flagged for `Y₁(N)`: "what it means to be a point of exact
order `N` … is slightly delicate over schemes, even if `N` is invertible on the base."
The naive fibrewise notion is recovered — as a *theorem* — exactly when `N` is invertible.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- A section of `E/S`, i.e. a point `P ∈ E(S)`. -/
abbrev Section := E.Point (𝟙 S)

/-- Pull a point back along `t : T ⟶ S` (restriction of a section to a `T`-point). -/
def Point.pull {T : Scheme.{u}} (t : T ⟶ S) (P : E.Section) : E.Point t :=
  ⟨t ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩

/-- **KM 1.3.6**: a relative effective Cartier divisor `D` in `E/S` *is a subgroup* if for
every `T ⟶ S` the subset of `E(T)` consisting of points factoring through `D` is a
subgroup of `E(T)`: it contains `0`, and is stable under addition and negation. -/
def _root_.ModularCurves.RelEffCartierDiv.IsSubgroup (D : RelEffCartierDiv E.π) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S),
    ∃ H : AddSubgroup (E.Point g),
      ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = P.1

/-- The divisor `[P] + [2P] + ⋯ + [NP]` of KM 1.4.1 (via DS4a). -/
noncomputable def Section.orderDivisor (P : E.Section) (N : ℕ) : RelEffCartierDiv E.π :=
  RelEffCartierDiv.sectionsDivisor E.π
    (fun a : Fin N => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)))

/-- **KM 1.4.1 — a point of exact order `N`** (Drinfeld): `P ∈ E(S)` has exact order `N`
if the degree-`N` relative effective Cartier divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup
of `E/S`. -/
def Section.HasExactOrder (P : E.Section) (N : ℕ) [NeZero N] : Prop :=
  (P.orderDivisor E N).IsSubgroup E

/-- **Register box `BB-DELIGNE` (KM 1.4.2, cite [Oort–Tate])**, in the project's
subgroup-divisor encoding: a subgroup divisor of constant degree `N` is killed by `N`
— every point factoring through it is annihilated by `N`. KM (verbatim): *"a finite
locally free commutative group scheme of rank `N` is killed by `N`"*. -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by sorry

/-- `IdealSheafData.ideal` as a monoid homomorphism (products of ideal sheaves are
computed pointwise). -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.idealMonoidHom
    (X : Scheme.{u}) :
    X.IdealSheafData →* (∀ U : X.affineOpens, Ideal Γ(X, U.1)) where
  toFun := Scheme.IdealSheafData.ideal
  map_one' := by
    funext U
    simp [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top,
      Ideal.one_eq_top]
  map_mul' I J := Scheme.IdealSheafData.ideal_mul I J

/-- **(T-D5 = KM 1.4.2)** Exact order `N` implies `N • P = 0`. Black box BB-DELIGNE: a
finite locally free commutative group scheme of rank `N` is killed by `N` (KM cite
[Oort–Tate]). -/
theorem Section.HasExactOrder.smul_eq_zero {P : E.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder E N) : (N : ℤ) • P = 0 := by
  haveI hsep : IsSeparated E.π := inferInstance
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨hsep, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E N).degree s = N := fun s =>
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  refine RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E h hdeg (𝟙 S) P ?_
  have hideal : (P.orderDivisor E N).ideal =
      ∏ a : Fin N, Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1 := by
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  have h0 : (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)) = P := by
    simp
  have hle : (P.orderDivisor E N).ideal ≤ Scheme.Hom.ker P.1 := by
    rw [hideal]
    have hle0 : (∏ a : Fin N,
        Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1) ≤
        Scheme.Hom.ker (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)).1 := by
      intro U
      have hprod : (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal =
          ∏ a : Fin N,
            (Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal :=
        map_prod (Scheme.IdealSheafData.idealMonoidHom E.E) _ _
      calc (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U
          = ∏ a : Fin N, (Scheme.Hom.ker
              (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U := by
            rw [hprod]
            exact Finset.prod_apply U Finset.univ _
        _ ≤ _ :=
          Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ (0 : Fin N)))
    rw [h0] at hle0
    exact hle0
  haveI hPc : IsClosedImmersion P.1 := by
    have h1 : IsClosedImmersion (P.1 ≫ E.π) := by
      rw [P.2]
      infer_instance
    exact IsClosedImmersion.of_comp P.1 E.π
  refine ⟨P.1.toImage ≫ Scheme.IdealSheafData.inclusion hle, ?_⟩
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact P.1.toImage_imageι

/-- **(T-D6 = KM 1.4.4, (1) ⇔ (3), verbatim source in hand with proof)** For a point
`P` **killed by `N`** (KM's standing hypothesis "Let `P ∈ C(S)` be a point killed by
`N`" — REQUIRED: over `S = Spec ℚ̄[ε]` a lift `P̃` of an exact-order-`N` point with
`N•P̃ ≠ 0` in the tangent kernel satisfies the geometric right-hand side but not the
left; adversarial pass 2026-07-06) and `N` invertible on `S`: `P` has exact order `N`
iff on every geometric point the induced point has exact order `N` "in the usual sense
that `N` is the least positive integer which kills `P_k`". -/
theorem Section.hasExactOrder_iff_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        (N : ℤ) • Point.pull E t P = 0 ∧
        ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0 := by sorry

/-- **(T-D7 = KM 1.4.4, (1) ⇔ (4))** For a point `P` killed by `N` (KM's standing
hypothesis — required: the same `ℚ̄[ε]` lift makes `[P̃] + [2P̃]` a disjoint union
`S ⊔ S`, finite étale, without `P̃` having exact order 2) and `N` invertible on `S`:
`P` has exact order `N` iff the divisor `Σₐ [aP]` is finite étale over `S`. -/
theorem Section.hasExactOrder_iff_etale {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      Etale ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) := by sorry

end EllipticCurve

end ModularCurves

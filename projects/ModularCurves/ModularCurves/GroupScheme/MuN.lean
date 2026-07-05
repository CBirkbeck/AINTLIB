import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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

/-- **(DS3a, ticket T-B2)** The group structure on `μ_{N,S}` in `Over S`, with
comultiplication `Spec` of `T ↦ T ⊗ T`. DATA-SORRY (register entry DS3). -/
instance muNGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (muNπ S N)) := sorry

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
    { h : T ⟶ muN S N // h ≫ muNπ S N = g } ≃ { a : Γ(T, ⊤) // a ^ N = 1 } := sorry

/-- **(T-B7)** `μ_{N,S} ⟶ S` is finite locally free of rank `N`, étale iff `N` is invertible
on `S`. (Two statements; étale case.) Source: KM 1.12; standard. -/
theorem muNπ_isFinite (S : Scheme.{u}) (N : ℕ) [NeZero N] : IsFinite (muNπ S N) := by sorry

theorem muNπ_etale_of_invertible (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (h : IsUnit (N : Γ(S, ⊤))) : Etale (muNπ S N) := by sorry

end ModularCurves

end

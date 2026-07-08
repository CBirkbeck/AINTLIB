import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Cartier duality and Deligne's order theorem (BB-DELIGNE)

This file develops the abstract Hopf-algebraic layer (Layer A of `plan-deligne.md`) of
**Deligne's theorem**: a finite locally free commutative group scheme of rank `N` is killed
by `N`. The route is Tate's, from J. Tate, *Finite flat group schemes* (in Cornell–Silverman–
Stevens, *Modular Forms and Fermat's Last Theorem*), §3.8, book pp. 143–145.

The mathematical content of §3.8, in the affine/Hopf-algebra picture `G = Spec A`, `R` the base
ring, `A` a finite locally free `R`-Hopf algebra of rank `n`:

* `A' := Hom_R(A, R)` is the **Cartier dual** — itself a commutative `R`-Hopf algebra when `A` is
  cocommutative (equivalently `G` commutative), finite locally free of the same rank `n`. In
  mathlib this convolution algebra is `WithConv (A →ₗ[R] R)` (`LinearMap.convAlgebra`, and
  `LinearMap.convCommRing` under `IsCocomm R A`).
* A `B`-point of `G`, i.e. an `R`-algebra map `A → B`, is a **group-like** element `λ` of
  `A'_B := WithConv (A →ₗ[R] B)` — a *unit* whose convolution powers `λ^k` are the multiples
  `k • Q` of the point. (Tate p. 144: "`G(R) = Hom_(R-alg)(A,R) ⊂ Hom_(R-mod)(A,R) = A'`
  identifies `G(R)` with the multiplicative group of group-like elements of `A'`.")
* The free rank-`n` left `A'`-module `A' ⊗_R A` carries operators `τ = id ⊗ τ_λ`, `ρ` (right
  mult by `id`), `ℓ` (right mult by `λ ⊗ 1`) with `τ ρ τ⁻¹ ρ⁻¹ = ℓ` (Prop 3.8.1), and `ℓ` is
  the scalar matrix `λ · Iₙ`.
* Since `A'` is commutative, `det : GLₙ(A') → (A')ˣ` kills the commutator, so
  `det(λ · Iₙ) = λⁿ = 1` (Tate p. 144). Equivalently `n • Q = 0`.

This file proves the pieces bottom-up. The determinant step (leaf **T-D5f**) is pure matrix
algebra over a commutative ring and is complete; the point↔convolution-unit dictionary
(**T-D5c**) and the Cartier-dual algebra (**T-D5a**) are discharged from mathlib's convolution
API; the operator/commutator package (**T-D5d/e**, Prop 3.8.1) and the final assembly
(**T-D5g**) remain. The geometric bridge (Layer B) lives in
`ModularCurves.GroupScheme.DeligneOrder`.

See `.mathlib-quality/plan-deligne.md` for the full ticket board and verbatim source quotes.
-/

open scoped Matrix
open HopfAlgebra Coalgebra WithConv

namespace ModularCurves.CartierDual

universe u v w

/-! ## Layer A leaf T-D5f — the determinant step

The determinant homomorphism `GLₙ(S) → Sˣ` over a *commutative* ring `S` kills commutators;
applied to the scalar matrix `λ · Iₙ = A B A⁻¹ B⁻¹` this gives `λⁿ = 1`. In Deligne's proof
`S = A'` is the (commutative) Cartier dual, `λ` the group-like element attached to a point,
and `n` the rank of `G` — so this leaf is exactly the last two sentences of Tate §3.8 (p. 144):
"we can use the determinant homomorphism `GLₙ(A') → (A')*` to conclude that `λⁿ = 1`." -/

/-- The determinant of a `unit` matrix and of its inverse multiply to `1`: `det ↑A · det ↑A⁻¹ = 1`.
A packaging of `Matrix.det_mul` + `Units.mul_inv` used repeatedly below. -/
theorem det_val_mul_det_val_inv {S : Type u} [CommRing S] {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) S)ˣ) :
    (↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

/-- **(T-D5f — determinant step, Tate §3.8 p. 144.)** Over a commutative ring `S`, if the scalar
matrix `λ • Iₙ` is a commutator `A · B · A⁻¹ · B⁻¹` of invertible `n × n` matrices, then `λⁿ = 1`.

Proof: `det` is multiplicative and `S` is commutative, so `det(A B A⁻¹ B⁻¹) = 1`; and
`det(λ • Iₙ) = λⁿ` by `Matrix.det_smul`. This is the leaf discharged purely from mathlib
(`Matrix.det_smul`, `Matrix.det_mul`, `Matrix.det_one`, `Units.mul_inv`). -/
theorem pow_eq_one_of_smul_one_eq_commutator {S : Type u} [CommRing S] {n : ℕ}
    (lam : S) (A B : (Matrix (Fin n) (Fin n) S)ˣ)
    (h : lam • (1 : Matrix (Fin n) (Fin n) S) = ↑(A * B * A⁻¹ * B⁻¹)) :
    lam ^ n = 1 := by
  -- Take determinants of both sides.
  have key := congrArg Matrix.det h
  -- LHS: det (λ • 1) = λ ^ n.
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  rw [key]
  -- RHS: det of the commutator is 1.
  simp only [Units.val_mul]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  -- goal: det↑A * det↑B * det↑A⁻¹ * det↑B⁻¹ = 1
  calc (↑A : Matrix (Fin n) (Fin n) S).det * (↑B : Matrix (Fin n) (Fin n) S).det
          * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det
      = ((↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det)
          * ((↑B : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det) := by
        ring
    _ = 1 * 1 := by rw [det_val_mul_det_val_inv, det_val_mul_det_val_inv]
    _ = 1 := by ring

/-! ## The Cartier dual algebra and points as group-like elements

We fix a commutative `R`-Hopf algebra `A` (`= 𝒪(G)`), cocommutative (`G` commutative), and a
test `R`-algebra `B`. Tate's `A'_B` is mathlib's `WithConv (A →ₗ[R] B)`: the convolution
algebra of `R`-linear maps `A → B`, whose product is dual to the comultiplication of `A`. -/

/-- **(T-D5a — Cartier dual algebra, Tate §3.8 p. 143.)** The Cartier dual `A' = Hom_R(A, R)`
(i.e. `Module.Dual R A`) with its convolution product, as a commutative `R`-algebra. This is
mathlib's `WithConv (A →ₗ[R] R)`; the instances `LinearMap.convAlgebra` and (under `IsCocomm R A`,
i.e. `G` commutative) `LinearMap.convCommRing` supply the `R`-algebra and commutativity. -/
abbrev _root_.ModularCurves.CartierDual (R : Type u) (A : Type v) [CommRing R] [AddCommGroup A]
    [Module R A] [Coalgebra R A] : Type max u v := WithConv (A →ₗ[R] R)

section Point

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **(T-D5c — points as convolution elements, Tate §3.8 p. 144.)** A `B`-point `φ : A →ₐ[R] B`,
viewed in `A'_B = WithConv (A →ₗ[R] B)` as the group-like element `λ_φ`. The group law of
`G(B)` is convolution, so the `k`-th convolution power `(pointConv φ)^k` is `k • Q`. -/
def pointConv (φ : A →ₐ[R] B) : WithConv (A →ₗ[R] B) := toConv φ.toLinearMap

@[simp] lemma ofConv_pointConv (φ : A →ₐ[R] B) : ofConv (pointConv φ) = φ.toLinearMap := rfl

/-- The convolution inverse of a point is the point composed with the antipode: this is the
Hopf-algebra identity `∑ φ(a₍₁₎) · φ(S a₍₂₎) = φ(∑ a₍₁₎ · S a₍₂₎) = φ(ε(a) • 1) = ε_B(a)`,
i.e. `λ_φ · (λ_φ ∘ S) = 1` in `A'_B`. (Tate p. 144: "λ is group-like iff it is invertible in
`A'` and the map `λ : A → R` is multiplicative … invertible iff `λ(1) = 1`.") -/
theorem mul_pointConv_antipode_eq_one (φ : A →ₐ[R] B) :
    pointConv φ * toConv (φ.toLinearMap ∘ₗ antipode R) = 1 := by
  refine ofConv_injective (LinearMap.ext fun a => ?_)
  rw [(Coalgebra.ℛ R a).convMul_apply, LinearMap.convOne_apply]
  have hsum : ∀ i, (pointConv φ) ((Coalgebra.ℛ R a).left i)
      * (toConv (φ.toLinearMap ∘ₗ antipode R)) ((Coalgebra.ℛ R a).right i)
      = φ ((Coalgebra.ℛ R a).left i * antipode R ((Coalgebra.ℛ R a).right i)) :=
    fun i => by simp [pointConv, map_mul]
  rw [Finset.sum_congr rfl fun i _ => hsum i, ← map_sum,
    sum_mul_antipode_eq_algebraMap_counit (Coalgebra.ℛ R a), AlgHom.commutes]

/-- **(T-D5c — corollary.)** A `B`-point `φ` is a *unit* in `A'_B` (its convolution inverse
being `φ ∘ S`). This is the statement that the points of `G` are group-like elements of `A'`,
in particular invertible — needed so `λ_φ · Iₙ ∈ GLₙ(A'_B)` in the determinant step. Requires
`G` commutative (`IsCocomm R A`) so that `A'_B` is a commutative ring. -/
theorem isUnit_pointConv [IsCocomm R A] (φ : A →ₐ[R] B) : IsUnit (pointConv φ) :=
  ⟨⟨pointConv φ, toConv (φ.toLinearMap ∘ₗ antipode R), mul_pointConv_antipode_eq_one φ,
    by rw [mul_comm]; exact mul_pointConv_antipode_eq_one φ⟩, rfl⟩

end Point

/-! ## The commutator package (Prop 3.8.1) and the final assembly — REMAINING

The heart of §3.8: on the free rank-`n` left `A'`-module `A' ⊗_R A`, the scalar `λ · Iₙ` is a
commutator, so `det` gives `λⁿ = 1`. Prop 3.8.1 (leaf T-D5e, itself resting on the operator
`τ_λ` of T-D5d) is stated in the concrete existential form the determinant step consumes; it is
`sorry` here and proved in its sub-tickets. The assembly `deligne_pointConv_pow` (T-D5g) then
combines it with `pow_eq_one_of_smul_one_eq_commutator`. -/

section Commutator

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] [IsCocomm R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **(T-D5e — Proposition 3.8.1, Tate §3.8 p. 144.)** On the free rank-`n` left-`A'`-module
`A' ⊗_R A`, with `τ = id ⊗ τ_λ`, `ρ =` right mult by `id`, `ℓ =` right mult by `λ ⊗ 1`, one has
`τ ρ τ⁻¹ ρ⁻¹ = ℓ`, and `ℓ` is the scalar operator `λ • Iₙ`. Consequently `λ • Iₙ` is a
commutator in `GLₙ(A'_B)`.

Stated in the concrete form the determinant step consumes: over the commutative ring
`S := A'_B = WithConv (A →ₗ[R] B)` there exist `P Q ∈ GLₙ(S)` with
`(pointConv φ) • Iₙ = P Q P⁻¹ Q⁻¹`. Proof deferred to sub-tickets (the `τ_λ`/`ρ`/`ℓ`
construction of T-D5d and the commutator computation of Prop 3.8.1). -/
theorem exists_commutator_eq_pointConv_smul_one (φ : A →ₐ[R] B)
    {n : ℕ} (hn : Module.finrank R A = n) [Module.Free R A] [Module.Finite R A] :
    ∃ P Q : (Matrix (Fin n) (Fin n) (WithConv (A →ₗ[R] B)))ˣ,
      (pointConv φ) • (1 : Matrix (Fin n) (Fin n) (WithConv (A →ₗ[R] B)))
        = ↑(P * Q * P⁻¹ * Q⁻¹) := by
  sorry

/-- **(T-D5g — Deligne's order theorem, group-like form; Tate §3.8 pp. 144–145.)** For a
cocommutative Hopf algebra `A` finite free of rank `n` over `R`, any `B`-point `φ : A →ₐ[R] B`
satisfies `(pointConv φ)^n = 1` — the `n`-fold convolution power is the trivial point.
Equivalently `n • Q = 0`: Deligne's theorem that a commutative finite flat group scheme is
killed by its order. Assembled from the commutator `λ Iₙ = P Q P⁻¹ Q⁻¹` (Prop 3.8.1,
`exists_commutator_eq_pointConv_smul_one`) and the determinant step (T-D5f,
`pow_eq_one_of_smul_one_eq_commutator`). -/
theorem deligne_pointConv_pow (φ : A →ₐ[R] B)
    {n : ℕ} (hn : Module.finrank R A = n) [Module.Free R A] [Module.Finite R A] :
    (pointConv φ) ^ n = 1 := by
  obtain ⟨P, Q, hPQ⟩ := exists_commutator_eq_pointConv_smul_one φ hn
  exact pow_eq_one_of_smul_one_eq_commutator (pointConv φ) P Q hPQ

end Commutator

end ModularCurves.CartierDual

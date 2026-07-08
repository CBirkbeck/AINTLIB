import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
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

open scoped Matrix TensorProduct
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

/-- **(T-D5f′ — determinant step, endomorphism form.)** The same as
`pow_eq_one_of_smul_one_eq_commutator` but phrased with `LinearMap.det` on a free finite module
`M` (rank `n`), which is the form the geometric operators `τ, ρ, ℓ` of §3.8 naturally take: if
`λ • id_M` is a commutator `P Q P⁻¹ Q⁻¹` of `S`-linear automorphisms of `M`, then `λⁿ = 1`.

Proof: `LinearMap.det` is a monoid hom killing commutators over the commutative ring `S`, and
`det(λ • id_M) = λ^(finrank M) = λⁿ` (`LinearMap.det_smul`, `LinearMap.det_id`). -/
theorem pow_eq_one_of_smul_id_eq_commutator {S : Type u} [CommRing S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M]
    {n : ℕ} (hn : Module.finrank S M = n) (lam : S)
    (P Q : (M →ₗ[S] M)ˣ)
    (h : lam • (LinearMap.id : M →ₗ[S] M) = ↑(P * Q * P⁻¹ * Q⁻¹)) :
    lam ^ n = 1 := by
  have key := congrArg LinearMap.det h
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hn] at key
  rw [key]
  have hP : LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑P⁻¹ : M →ₗ[S] M) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQ : LinearMap.det (↑Q : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  calc LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑Q : M →ₗ[S] M)
          * LinearMap.det (↑P⁻¹ : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M)
      = (LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑P⁻¹ : M →ₗ[S] M))
          * (LinearMap.det (↑Q : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M)) := by ring
    _ = 1 := by rw [hP, hQ]; ring

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
  ext a
  rw [(ℛ R a).convMul_apply, LinearMap.convOne_apply]
  have hsum : ∀ i, (pointConv φ) ((ℛ R a).left i)
      * (toConv (φ.toLinearMap ∘ₗ antipode R)) ((ℛ R a).right i)
      = φ ((ℛ R a).left i * antipode R ((ℛ R a).right i)) :=
    fun i => by simp [pointConv, map_mul]
  simp only [hsum]
  rw [← map_sum φ, sum_mul_antipode_eq_algebraMap_counit (ℛ R a), AlgHom.commutes]

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

/-! ### General right-multiplication lemmas (Hopf-free)

The commutator computation of Prop 3.8.1 rests on two facts about right multiplication in a
commutative `S`-algebra `M`, neither involving Hopf algebras:

* conjugating `R_u` (right mult by a unit `u`) by an `S`-algebra automorphism `τ` gives
  `R_{τ(u)}`, so `τ R_u τ⁻¹ R_{u}⁻¹ = R_{u⁻¹ · τ(u)}` (`mulRight_conj_mulRight_inv`);
* over `M = S ⊗_R A`, right multiplication by `λ ⊗ 1` is the scalar `λ • id`
  (`mulRight_tmul_one`). -/

section RightMul

variable {S : Type*} [CommRing S] {M : Type*} [CommRing M] [Algebra S M]

/-- Conjugating right-multiplication `R_u` by an `S`-algebra automorphism `τ` and then
composing with `R_{u⁻¹}` yields right-multiplication by `u⁻¹ · τ(u)`:
`τ ∘ R_u ∘ τ⁻¹ ∘ R_{u⁻¹} = R_{u⁻¹ · τ(u)}`. Pure ring theory (`map_mul`, associativity). -/
theorem mulRight_conj_mulRight_inv (τ : M ≃ₐ[S] M) (u : Mˣ) :
    (τ.toLinearMap ∘ₗ LinearMap.mulRight S (↑u : M)) ∘ₗ
        (τ.symm.toLinearMap ∘ₗ LinearMap.mulRight S (↑u⁻¹ : M))
      = LinearMap.mulRight S ((↑u⁻¹ : M) * τ (↑u : M)) := by
  ext y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    AlgEquiv.toLinearMap_apply, map_mul, AlgEquiv.apply_symm_apply]
  ring

end RightMul

section RightMulTensor

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- Over `M = S ⊗_R A`, right multiplication by `λ ⊗ 1` is the scalar `λ • id_M`
(`R_{λ⊗1} = λ • id`). This is the identification `ℓ = λ • Iₙ` of Tate §3.8 (p. 144). -/
theorem mulRight_tmul_one (lam : S) :
    LinearMap.mulRight S ((lam ⊗ₜ[R] 1 : S ⊗[R] A)) = lam • LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      simp only [LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', smul_eq_mul]
      rw [mul_comm s lam]
  | add z w hz hw => simp only [map_add, hz, hw]

end RightMulTensor

section Commutator

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] [IsCocomm R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **(Hopf core of Prop 3.8.1 = Lemma 3.8.2, Tate §3.8 p. 144 — SORRIED sub-ticket T-D5e-core.)**
The operators underlying Deligne's commutator: for a `B`-point `φ` (with `λ = pointConv φ`), there
is a unit `u` of the ring `M = A'_B ⊗_R A` — the **coevaluation element** `∑ eᵢ' ⊗ eᵢ`, i.e.
`id ∈ G(A)` under `A' ⊗ A ≅ End_R A` — and an `A'_B`-algebra automorphism `τ` of `M` — namely
`id_{A'} ⊗ τ_λ`, from the right-translation automorphism `τ_λ = (λ ⊗ id) ∘ Δ` on `A` — satisfying
`τ(u) = u · (λ ⊗ 1)`. This last equation is Tate's **Lemma 3.8.2** specialised to `φ = τ_λ`
("`(id_{A'} ⊗ φ)(id) = (id_A ⊗ φ')(id)`"), the sole remaining ingredient of Deligne's proof.

This is the genuinely Hopf-algebraic leaf: constructing `u` (coevaluation, needing the finite-free
dual basis), `τ_λ` (right translation), and verifying `τ(u) = u·(λ⊗1)` via the dual-basis/Sweedler
identity. Split into T-D5e-core-{u,τ,3.8.2} for the build. -/
theorem deligne_operators (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A] :
    ∃ (u : (WithConv (A →ₗ[R] B) ⊗[R] A)ˣ)
      (τ : WithConv (A →ₗ[R] B) ⊗[R] A ≃ₐ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A),
      τ (↑u : WithConv (A →ₗ[R] B) ⊗[R] A)
        = (↑u : WithConv (A →ₗ[R] B) ⊗[R] A) * (pointConv φ ⊗ₜ[R] (1 : A)) := by
  sorry

/-- **(T-D5e — Proposition 3.8.1, Tate §3.8 p. 144.)** On the free rank-`n` left-`A'`-module
`M := A'_B ⊗_R A`, the scalar map `λ • id_M` — which is right multiplication by `λ ⊗ 1` — is the
commutator `τ ρ τ⁻¹ ρ⁻¹`, where `ρ` is right multiplication by the coevaluation unit `u = 𝟙 ∈ M`
and `τ = id_{A'} ⊗ τ_λ` is the ring automorphism of `M` induced by right translation `τ_λ` on `A`.
The key relation (Lemma 3.8.2 with `φ = τ_λ`) is `τ(u) = u · (λ ⊗ 1)`, whence for a ring
automorphism `τ`, `τ ρ τ⁻¹ = R_{τ(u)}` and `R_{τ(u)} ρ⁻¹ = R_{u⁻¹ · τ(u)} = R_{λ⊗1} = λ • id`.

Stated in the form the determinant step (`pow_eq_one_of_smul_id_eq_commutator`) consumes: over
`S := A'_B = WithConv (A →ₗ[R] B)` and the free `S`-module `M = S ⊗_R A`, there exist units
`P Q` of `End_S M` (i.e. `S`-linear automorphisms of `M`) with `λ • id_M = P Q P⁻¹ Q⁻¹`. Proof
deferred to the sub-tickets T-D5e1–e5 (tensor module, `τ_λ`, right-mult operators, Lemma 3.8.2,
commutator identity). -/
theorem exists_commutator_eq_pointConv_smul_one (φ : A →ₐ[R] B)
    [Module.Free R A] [Module.Finite R A] :
    ∃ P Q : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)]
              WithConv (A →ₗ[R] B) ⊗[R] A)ˣ,
      pointConv φ • (LinearMap.id : WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)]
              WithConv (A →ₗ[R] B) ⊗[R] A)
        = ↑(P * Q * P⁻¹ * Q⁻¹) := by
  obtain ⟨u, τ, hτu⟩ := deligne_operators φ
  -- `P` = the automorphism `τ`; `Q` = right multiplication `ρ = R_u` by the unit `u`.
  let P : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A)ˣ :=
    { val := τ.toLinearMap, inv := τ.symm.toLinearMap,
      val_inv := LinearMap.ext fun y => by simp [Module.End.mul_eq_comp]
      inv_val := LinearMap.ext fun y => by simp [Module.End.mul_eq_comp] }
  let Q : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A)ˣ :=
    { val := LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u)
      inv := LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u⁻¹)
      val_inv := LinearMap.ext fun y => by
        simp [Module.End.mul_eq_comp, LinearMap.mulRight_apply, mul_assoc]
      inv_val := LinearMap.ext fun y => by
        simp [Module.End.mul_eq_comp, LinearMap.mulRight_apply, mul_assoc] }
  refine ⟨P, Q, ?_⟩
  have hP : (↑P : _ →ₗ[_] _) = τ.toLinearMap := rfl
  have hPi : (↑P⁻¹ : _ →ₗ[_] _) = τ.symm.toLinearMap := rfl
  have hQ : (↑Q : _ →ₗ[_] _)
      = LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u : WithConv (A →ₗ[R] B) ⊗[R] A) := rfl
  have hQi : (↑Q⁻¹ : _ →ₗ[_] _)
      = LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u⁻¹ : WithConv (A →ₗ[R] B) ⊗[R] A) := rfl
  -- `λ • id = τ ∘ R_u ∘ τ⁻¹ ∘ R_{u⁻¹} = R_{u⁻¹ · τ u} = R_{λ⊗1} = λ • id`.
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hP, hQ, hPi, hQi,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, mulRight_conj_mulRight_inv τ u, hτu, ← mul_assoc,
    Units.inv_mul, one_mul, mulRight_tmul_one]

/-- **(T-D5g — Deligne's order theorem, group-like form; Tate §3.8 pp. 144–145.)** For a
cocommutative Hopf algebra `A` finite free over `R`, any `B`-point `φ : A →ₐ[R] B` satisfies
`(pointConv φ)^n = 1`, where `n` is the `S`-rank of `M = S ⊗_R A` (`S := A'_B`) — which for a
nontrivial base equals the order `finrank R A` of `G`. Equivalently `n • Q = 0`: Deligne's
theorem that a commutative finite flat group scheme is killed by its order. Assembled from the
commutator `λ • id_M = P Q P⁻¹ Q⁻¹` (Prop 3.8.1, `exists_commutator_eq_pointConv_smul_one`) and
the determinant step (`pow_eq_one_of_smul_id_eq_commutator`).

The rank `n` is taken as `finrank S (S ⊗_R A)` (supplied by the caller) rather than reduced to
`finrank R A`: the reduction `finrank S (S ⊗_R A) = finrank R A` needs `StrongRankCondition` on
both rings (i.e. a nontrivial base), which the geometric consumer (Layer B) provides in context.
See `deligne_pointConv_pow_finrank` for that reduced form. -/
theorem deligne_pointConv_pow (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A]
    {n : ℕ}
    (hn : Module.finrank (WithConv (A →ₗ[R] B)) (WithConv (A →ₗ[R] B) ⊗[R] A) = n) :
    (pointConv φ) ^ n = 1 := by
  obtain ⟨P, Q, hPQ⟩ := exists_commutator_eq_pointConv_smul_one φ
  haveI : Module.Finite (WithConv (A →ₗ[R] B)) (WithConv (A →ₗ[R] B) ⊗[R] A) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R A).baseChange _)
  exact pow_eq_one_of_smul_id_eq_commutator hn (pointConv φ) P Q hPQ

/-- **(T-D5g, reduced form.)** For a *nontrivial* base ring `R` (so `finrank` is well-behaved),
Deligne's theorem reads `(pointConv φ)^(finrank R A) = 1`: the point is killed by the order
`finrank R A` of `G`. Uses `Module.finrank_baseChange` (`finrank S (S ⊗_R A) = finrank R A`),
which requires `StrongRankCondition R` — supplied here by `[Nontrivial R]` via
`commRing_strongRankCondition`. -/
theorem deligne_pointConv_pow_finrank (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A]
    [Nontrivial R] [Nontrivial (WithConv (A →ₗ[R] B))] :
    (pointConv φ) ^ (Module.finrank R A) = 1 :=
  deligne_pointConv_pow φ (Module.finrank_baseChange)

end Commutator

end ModularCurves.CartierDual

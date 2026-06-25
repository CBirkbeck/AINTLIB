/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyKernel
import HasseWeil.EC.TranslationOrd
import HasseWeil.Frobenius
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.Verschiebung.QthRoots

/-!
# `E(F_q) = ker(1 − π)` on rational points (Silverman V.1 setup, T-V-1-001)

In our Lean encoding, `W.toAffine.Point` over a finite field `K = F_q` *is* the
group of `K`-rational points `E(F_q)`. The `q`-power Frobenius isogeny
`frobeniusIsog W` carries `toAddMonoidHom = AddMonoidHom.id` (by construction,
encoding the fact that Frobenius acts as the identity on `F_q`-rational points —
see `frobeniusAlgHom_eq_id` for the field-level statement).

Therefore `(oneSubFrobeniusIsog W).toAddMonoidHom = id − id = 0` on
`W.toAffine.Point`, so every rational point lies in the kernel, i.e.
`ker (1 − π) = ⊤` as an `AddSubgroup`. This is the "point-level" form of
Silverman V.1's opening observation that `E(F_q) = ker(1 − π)`.

The cardinality corollary `#ker (1 − π) = #E(F_q)` is a direct consequence and
closes the counting side needed for `pointCount_eq` (T-V-1-003).

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], V.1 setup.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- The Frobenius isogeny acts as the identity on `K`-rational points.
    Encoded by construction in `frobeniusIsog` (cf. `frobeniusAlgHom_eq_id` for
    the field-level statement `x^q = x` on `K`). -/
@[simp] theorem frobeniusIsog_apply (P : W.toAffine.Point) :
    (frobeniusIsog W).toAddMonoidHom P = P := rfl

/-- Generalized form of `oneSubFrobeniusIsog_kernel_eq_top` for any witness
    isogeny with the same point-map as `1 − π`. -/
theorem kernel_eq_top_of_hom_eq_id_sub_frobenius
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom) :
    β.kernel = ⊤ := by
  ext P
  simp only [Isogeny.mem_kernel_iff, AddSubgroup.mem_top, iff_true]
  rw [h_hom]
  change (AddMonoidHom.id _) P - (frobeniusIsog W).toAddMonoidHom P = 0
  rw [frobeniusIsog_apply]
  exact sub_self _

/-- **Witness-parametric T-V-1-003**: if `β` has point-map `id − π` and its
    degree equals the cardinality of its kernel (the content of T-III-4-015
    applied to `β`), then `β.degree = #E(F_q)`.

    The hypothesis `h_ker_deg` is exactly what the
    "separable ⇒ `#ker = deg`" direction of Silverman III.4.10 provides for
    separable `β`; together with T-V-1-002 (`1 − π` is separable) it gives the
    classical identity `#E(F_q) = deg(1 − π)`. -/
theorem degree_eq_pointCount_of_witness
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_ker_deg : Nat.card β.kernel = β.degree) :
    (β.degree : ℤ) = pointCount W.toAffine := by
  have hcard : Nat.card β.kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W β h_hom, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  rw [← h_ker_deg, hcard]

/-- If an isogeny's pullback is the identity `AlgHom`, its ω-pullback
    coefficient is `1` — from the defining property of the coefficient and
    the invariant differential being `u⁻¹ • D(x)`. Applies to
    `oneSubFrobeniusIsog W` (placeholder) and any future concrete
    representation of `1 − π` whose pullback happens to be the identity
    on the function field (e.g., over `F_q`, where `1 − π` acts trivially
    on rational functions of `x`). -/
theorem omegaPullbackCoeff_of_pullback_eq_id
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine)
    (hα : α.pullback = AlgHom.id F W.toAffine.FunctionField) :
    omegaPullbackCoeff W α = 1 := by
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, alpha_star_u_eq, hα]
  simp only [AlgHom.id_apply, one_smul]
  rfl

/-- **Composed V.1 witness form**: if `β` has point-map `id − π` and
    `#ker β = β.degree`, then `#E(F_q) = q + 1 − isogTrace π β`. -/
theorem pointCount_eq_of_hom_kernel_witness
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_ker_deg : Nat.card β.kernel = β.degree) :
    (pointCount W.toAffine : ℤ) =
      Fintype.card K + 1 - isogTrace (frobeniusIsog W) β :=
  pointCount_eq_of_witness W β (degree_eq_pointCount_of_witness W β h_hom h_ker_deg)

/-- **HOLE D closer via `|ker| = sepDegree`**: for any isogeny `β` whose
point-map is `id − π` with `β.sepDegree = pointCount W.toAffine`, there is a
fiber witness `∃ P₀, |{P // β P = β P₀}| = β.sepDegree`. -/
theorem hole_d_of_hom_and_sepDegree
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sepDeg : β.sepDegree = pointCount W.toAffine) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree := by
  apply Isogeny.fiber_witness_of_ker_card_eq_sepDegree β
  rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W β h_hom, AddSubgroup.card_top,
    Nat.card_eq_fintype_card, h_sepDeg]
  rfl

/-- **Sub-helper III-4-015-S1** (kernel-as-fiber-over-zero): for any β with
`β.toAddMonoidHom = id − π`, the kernel of β contains all F_q-rational
points (since π acts as identity on F_q-points, by `Frobenius` fixing F_q).

Direct from `kernel_eq_top_of_hom_eq_id_sub_frobenius`. -/
theorem isogOneSub_kernel_eq_top_of_hom
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom) :
    β.kernel = ⊤ :=
  kernel_eq_top_of_hom_eq_id_sub_frobenius W β h_hom

omit [Fintype K] in
/-- **Sub-helper III-4-015-S2** (kernel cardinality from kernel = ⊤):
when `β.kernel = ⊤`, `Nat.card β.kernel = pointCount W.toAffine`. -/
theorem card_kernel_eq_pointCount_of_kernel_eq_top
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_top : β.kernel = ⊤) :
    Nat.card β.kernel = pointCount W.toAffine := by
  rw [h_top, AddSubgroup.card_top, Nat.card_eq_fintype_card]
  rfl

/-- **Sub-helper III-4-015-S3** (fiber witness via degree = pointCount):
under separability + `β.degree = pointCount`, the fiber witness for the
Hasse bound consumer ships axiom-clean.

Proof chain:
1. `β.degree = pointCount` (input).
2. `β.IsSeparable` ⇒ `β.sepDegree = β.degree` (via isSeparable_iff_sepDegree_eq_degree).
3. So `β.sepDegree = pointCount`.
4. Apply `hole_d_of_hom_and_sepDegree`. -/
theorem fiber_witness_of_separable_and_degree_eq_pointCount
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sep : β.IsSeparable)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule)
    (h_deg : β.degree = pointCount W.toAffine) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree := by
  have h_sepDeg : β.sepDegree = pointCount W.toAffine := by
    rw [(Isogeny.isSeparable_iff_sepDegree_eq_degree β h_fin).mp h_sep, h_deg]
  exact hole_d_of_hom_and_sepDegree W β h_hom h_sepDeg

/-- **Sub-helper III-4-015-S4** (degree = pointCount via card-degree-witness):
when separable β has `Nat.card β.kernel = β.degree` (the III.4.10(a)
content), and `β.toAddMonoidHom = id − π`, then `β.degree = pointCount`.

Proof: `Nat.card β.kernel = pointCount` (from kernel = ⊤ structural via
sub-helper III-4-015-S2), combined with the input `Nat.card β.kernel =
β.degree` (sub-helper III-4-015-S4 input), gives `β.degree = pointCount`. -/
theorem degree_eq_pointCount_of_card_kernel_eq_degree
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_card_eq : Nat.card β.kernel = β.degree) :
    β.degree = pointCount W.toAffine := by
  rw [← h_card_eq]
  exact card_kernel_eq_pointCount_of_kernel_eq_top W β
    (isogOneSub_kernel_eq_top_of_hom W β h_hom)

/-- **Sub-helper III-4-015-S5** (full fiber witness composer): combine S4
+ S3 to get the fiber witness from `Nat.card kernel = β.degree` directly.
This is the "no-circular-dependency" version: takes the III.4.10(a)
content (`#kernel = degree`) as the substantive input, produces the
fiber witness + bound consumer chain. -/
theorem fiber_witness_of_separable_via_card_kernel_eq_degree
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sep : β.IsSeparable)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule)
    (h_card_eq : Nat.card β.kernel = β.degree) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree :=
  fiber_witness_of_separable_and_degree_eq_pointCount W β h_hom h_sep h_fin
    (degree_eq_pointCount_of_card_kernel_eq_degree W β h_hom h_card_eq)

omit [Fintype K] in
/-- **Sub-helper III-4-015-S6** (kernel-Aut bijection witness consumer):
given `Aut(K(E₁)/α*K(E₂)) ≃ α.kernel` (the substantive Galois-correspondence
content for elliptic isogenies) and a witness for `Nat.card Aut = α.degree`
(the IsGalois card_aut_eq_finrank applied to our specific algebra), derive
`Nat.card α.kernel = α.degree` axiom-clean.

Reduces the III.4.10(a) wall to two named witnesses:
1. `Nat.card Aut = α.degree` (IsGalois + finrank).
2. `Aut ≃ α.kernel` (Galois-group ↔ kernel via translation action). -/
theorem card_kernel_eq_degree_of_galois_witness
    (β : Isogeny W.toAffine W.toAffine)
    (Aut : Type*)
    (h_aut_card : Nat.card Aut = β.degree)
    (h_iso : Nonempty (Equiv Aut β.kernel)) :
    Nat.card β.kernel = β.degree := by
  obtain ⟨e⟩ := h_iso
  rw [← Nat.card_congr e]
  exact h_aut_card

/-- **Sub-helper III-4-015-S7** (full chain: Galois witnesses → fiber witness):
combines S6 with the existing fiber-witness-via-card-kernel-eq-degree to
produce the fiber witness from the two named Galois-correspondence witnesses. -/
theorem fiber_witness_via_galois_witnesses
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sep : β.IsSeparable)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule)
    (Aut : Type*)
    (h_aut_card : Nat.card Aut = β.degree)
    (h_iso : Nonempty (Equiv Aut β.kernel)) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree :=
  fiber_witness_of_separable_via_card_kernel_eq_degree W β h_hom h_sep h_fin
    (card_kernel_eq_degree_of_galois_witness W β Aut h_aut_card h_iso)

omit [Fintype K] in
/-- **Sub-helper III-4-015-S8** (Witness #1 from IsGalois + FiniteDim):
discharge `Nat.card (K(E₁) ≃ₐ[α*K(E₂)] K(E₁)) = β.degree` via
`IsGalois.card_aut_eq_finrank`, where the `Aut` is the type of `K(E₂)`-algebra
automorphisms of `K(E₁)` under `β.toAlgebra`. -/
theorem card_aut_eq_degree_of_isGalois
    (β : Isogeny W.toAffine W.toAffine)
    (hgal : letI := β.toAlgebra
      IsGalois W.toAffine.FunctionField W.toAffine.FunctionField)
    (hfin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule) :
    Nat.card (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) = β.degree := by
  letI := β.toAlgebra
  haveI := hgal
  haveI := hfin
  exact IsGalois.card_aut_eq_finrank W.toAffine.FunctionField W.toAffine.FunctionField

/-- **Sub-helper III-4-015-S9** (full chain: IsGalois + bijection → fiber witness):
final closing-arc consumer. Takes:
- The structural hypotheses (h_hom, IsSeparable, FiniteDim).
- IsGalois witness (substantive normality assumption).
- Aut ≃ β.kernel bijection (the substantive Galois-correspondence content).

Produces the fiber witness used by the historical witness-parametric
Hasse-bound route, axiom-clean.

The cascade reduces T-III-4-015 to two named witnesses via this consumer:
1. `IsGalois (α*K(E₂)) K(E₁)` (Mathlib has the structure; needs Normal).
2. `Aut ≃ β.kernel` (Galois group ↔ kernel translation bijection). -/
theorem fiber_witness_via_isGalois_and_bijection
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sep : β.IsSeparable)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule)
    (hgal : letI := β.toAlgebra
      IsGalois W.toAffine.FunctionField W.toAffine.FunctionField)
    (h_iso : Nonempty (Equiv (@AlgEquiv W.toAffine.FunctionField
        W.toAffine.FunctionField W.toAffine.FunctionField _ _ _
        β.toAlgebra β.toAlgebra) β.kernel)) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree :=
  fiber_witness_via_galois_witnesses W β h_hom h_sep h_fin
    (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra)
    (card_aut_eq_degree_of_isGalois W β hgal h_fin) h_iso

omit [Fintype K] in
/-- **Sub-helper III-4-015-S10** (bijection from forward + inverse witnesses):
abstract bijection consumer. Given a forward map `Φ : β.kernel → Aut`, an
inverse map `Φ⁻¹ : Aut → β.kernel`, and the mutual-inverse identities,
produce the equivalence consumed by S9. -/
theorem aut_kernel_equiv_of_inverse_witnesses
    (β : Isogeny W.toAffine W.toAffine)
    (Aut : Type*)
    (forward : β.kernel → Aut)
    (inverse : Aut → β.kernel)
    (h_left_inv : Function.LeftInverse inverse forward)
    (h_right_inv : Function.RightInverse inverse forward) :
    Nonempty (Equiv Aut β.kernel) :=
  ⟨{ toFun := inverse
     invFun := forward
     left_inv := h_right_inv
     right_inv := h_left_inv }⟩

/-- **Sub-helper III-4-015-S11** (full chain via inverse witnesses): combines
S10 with S9 to fire the fiber witness from forward + inverse + mutual-inverse
witnesses. -/
theorem fiber_witness_via_inverse_witnesses
    [Fintype W.toAffine.Point]
    (β : Isogeny W.toAffine W.toAffine)
    (h_hom : β.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_sep : β.IsSeparable)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β.toAlgebra.toModule)
    (hgal : @IsGalois W.toAffine.FunctionField _ W.toAffine.FunctionField _
      β.toAlgebra)
    (forward : β.kernel → @AlgEquiv W.toAffine.FunctionField
      W.toAffine.FunctionField W.toAffine.FunctionField _ _ _
      β.toAlgebra β.toAlgebra)
    (inverse : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) → β.kernel)
    (h_left_inv : Function.LeftInverse inverse forward)
    (h_right_inv : Function.RightInverse inverse forward) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree :=
  fiber_witness_via_isGalois_and_bijection W β h_hom h_sep h_fin hgal
    (aut_kernel_equiv_of_inverse_witnesses W β _ forward inverse
      h_left_inv h_right_inv)

/-- **Forward map at k = 0** (axiom-clean): the translation by 0 is the identity
algebra automorphism. -/
noncomputable def aut_of_kernel_zero
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic] :
    W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField :=
  AlgEquiv.refl

/-- **Forward map at k = 0 is the identity** (axiom-clean). -/
@[simp] theorem aut_of_kernel_zero_apply
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (f : W.toAffine.FunctionField) :
    aut_of_kernel_zero W f = f :=
  rfl

/-- **Substantive partial forward-map construction** (Sub-helper III-4-015-S12):
the forward map for the substantive cases requires the curve-translation
algebra automorphism `τ_k : K(E) ≃ₐ[F] K(E)` defined by
`τ_k(x_gen) = x-coord(P_gen + k)` and `τ_k(y_gen) = y-coord(P_gen + k)`.

Construction parallels Worker A's `addPullbackAlgHom_negFrobenius`:
1. Define `τ_k` via the addition formula (`addX`, `addY`).
2. Show it's a K-algebra hom (well-defined modulo Weierstrass).
3. Show it has inverse `τ_(-k)` (since τ is a group action).
4. For k ∈ β.kernel, show `τ_k` fixes `β.pullback`'s image.

This sub-helper takes the substantive `τ_k` AS A WITNESS — a precise
statement of what's needed beyond what's currently in mathlib. The
construction itself is ~200-300 LOC of `addCoordAlgHom`-style infrastructure
applied to the translation map. -/
noncomputable def aut_of_kernel_construction_witness
    (β : Isogeny W.toAffine W.toAffine)
    (translation_at : β.kernel →
      W.toAffine.FunctionField ≃ₐ[K] W.toAffine.FunctionField) :
    β.kernel → W.toAffine.FunctionField ≃ₐ[K] W.toAffine.FunctionField :=
  translation_at

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **Forward map** `β.kernel → K(E) ≃ₐ[F] K(E)` for any isogeny `β`. -/
noncomputable def kernelTranslateForward
    (β : Isogeny W.toAffine W.toAffine) :
    β.kernel → (W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField) :=
  fun k ↦ translateAlgEquivOfPoint W k.val

/-- **`kernelTranslateForward` at `0`** is the identity AlgEquiv. -/
@[simp] theorem kernelTranslateForward_zero
    (β : Isogeny W.toAffine W.toAffine)
    (h_zero_mem : (0 : W.toAffine.Point) ∈ β.kernel) :
    kernelTranslateForward W β ⟨0, h_zero_mem⟩ = AlgEquiv.refl := rfl

/-- **Layer 2 forward map under `β.toAlgebra`** (witness-parametric).
Takes Worker A's `translateAlgEquivOfPoint W k.val` (an F-AlgEquiv) and
the covariance identity `τ_k ∘ β.pullback = β.pullback` (provided as
hypothesis), and produces the `K(E)`-AlgEquiv (under `β.toAlgebra`)
consumed by the S10 bijection. -/
noncomputable def kernelTranslateAsAut
    (β : Isogeny W.toAffine W.toAffine)
    (k : β.kernel)
    (h_invariance : ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z) :
    @AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra :=
  letI := β.toAlgebra
  AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W k.val).toRingEquiv) h_invariance

/-- **Layer 2 forward map** (witness-parametric, all of `β.kernel`).
Provides the family `β.kernel → Aut` consumed by S11 (`forward`), conditional
on the covariance family `∀ k ∈ β.kernel, τ_k ∘ β.pullback = β.pullback`. -/
noncomputable def kernelTranslateForwardAsAut
    (β : Isogeny W.toAffine W.toAffine)
    (h_invariance_family : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z) :
    β.kernel → (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) :=
  fun k ↦ kernelTranslateAsAut W β k (h_invariance_family k)

/-- **`kernelTranslateAsAut` at `k = 0`** is the identity AlgEquiv (axiom-clean).
The `h_invariance` hypothesis at k = 0 is automatic since `τ_0 = refl`. -/
@[simp] theorem kernelTranslateAsAut_zero
    (β : Isogeny W.toAffine W.toAffine)
    (h_zero_mem : (0 : W.toAffine.Point) ∈ β.kernel)
    (h_invariance : ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W (0 : W.toAffine.Point) (β.pullback z) =
        β.pullback z) :
    kernelTranslateAsAut W β ⟨0, h_zero_mem⟩ h_invariance =
      @AlgEquiv.refl W.toAffine.FunctionField W.toAffine.FunctionField
        _ _ β.toAlgebra := by
  letI := β.toAlgebra
  apply AlgEquiv.ext
  intro f
  change translateAlgEquivOfPoint W (0 : W.toAffine.Point) f = f
  rfl

/-- **Underlying AlgEquiv coincides** with `kernelTranslateForward` (no-op
extraction): on data, `kernelTranslateAsAut` and `kernelTranslateForward`
share the same underlying ring equivalence. This is the forgetful direction
ensuring the Layer-2 promotion is conservative. -/
theorem kernelTranslateAsAut_apply
    (β : Isogeny W.toAffine W.toAffine)
    (k : β.kernel)
    (h_invariance : ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z)
    (f : W.toAffine.FunctionField) :
    kernelTranslateAsAut W β k h_invariance f =
      translateAlgEquivOfPoint W k.val f := rfl

/-- **IntermediateField equalizer**: the IntermediateField where two
F-AlgHoms `K(E) → K(E)` agree. Inherits the `Subalgebra` structure from
`AlgHom.equalizer`; closure under inverse holds because the codomain is a
field. -/
noncomputable def algHomFieldEqualizer
    (f g : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    IntermediateField F W.toAffine.FunctionField where
  toSubalgebra := AlgHom.equalizer f g
  inv_mem' := by
    intro x (hx : f x = g x)
    change f x⁻¹ = g x⁻¹
    rw [map_inv₀, map_inv₀, hx]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
@[simp] theorem mem_algHomFieldEqualizer
    (f g : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (x : W.toAffine.FunctionField) :
    x ∈ algHomFieldEqualizer W f g ↔ f x = g x := Iff.rfl

/-- **Two `F`-AlgHoms `K(E) → K(E)` agreeing on `x_gen`, `y_gen` are equal**:
`K(E)` is generated over `F` by `x_gen` and `y_gen`. -/
theorem algHom_ext_of_eq_on_xy [Fintype F]
    (f g : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (h_x : f (x_gen W) = g (x_gen W))
    (h_y : f (y_gen W) = g (y_gen W)) :
    f = g := by
  have h_top : (⊤ : IntermediateField F W.toAffine.FunctionField) ≤
      algHomFieldEqualizer W f g := by
    rw [functionField_eq_intermediateField_adjoin_xy W, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact h_x
    · exact h_y
  apply AlgHom.ext
  intro z
  exact h_top (by trivial : z ∈ (⊤ : IntermediateField F W.toAffine.FunctionField))

/-- **Generator-restricted covariance reducer**: covariance of
`translateAlgEquivOfPoint W k` with `β.pullback` on `x_gen` and `y_gen`
extends to all of `K(E)`. Reduces the per-isogeny covariance discharge to
two concrete equality checks. -/
theorem translateAlgEquivOfPoint_pullback_invariance_of_xy [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    (k : W.toAffine.Point)
    (h_x : translateAlgEquivOfPoint W k (β.pullback (x_gen W)) =
      β.pullback (x_gen W))
    (h_y : translateAlgEquivOfPoint W k (β.pullback (y_gen W)) =
      β.pullback (y_gen W)) :
    ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k (β.pullback z) = β.pullback z := fun z ↦
  DFunLike.congr_fun
    (algHom_ext_of_eq_on_xy W
      ((translateAlgEquivOfPoint W k).toAlgHom.comp β.pullback) β.pullback h_x h_y) z

/-- **Generator-restricted Layer 2 forward map** (witness-parametric on x_gen,
y_gen invariance). Composes `translateAlgEquivOfPoint_pullback_invariance_of_xy`
with `kernelTranslateAsAut` to consume the two-equality version of the
covariance hypothesis. -/
noncomputable def kernelTranslateAsAut_of_xy_invariance [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    (k : β.kernel)
    (h_x : translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
      β.pullback (x_gen W))
    (h_y : translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
      β.pullback (y_gen W)) :
    @AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra :=
  kernelTranslateAsAut W β k
    (translateAlgEquivOfPoint_pullback_invariance_of_xy W β k.val h_x h_y)

/-- **Generator-restricted Layer 2 forward map family**: pluggable into S11's
`forward` slot. Replaces the universal-z hypothesis with per-kernel-element
x_gen, y_gen invariance witnesses. -/
noncomputable def kernelTranslateForwardAsAut_of_xy_family [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W))) :
    β.kernel → (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) :=
  fun k ↦ kernelTranslateAsAut_of_xy_invariance W β k (h_xy_family k).1 (h_xy_family k).2

/-- **Kernel-pullback-invariance for `Isogeny.id`**: trivial since the
kernel is `⊥` (only `k = 0`, acting as identity). -/
theorem kernel_pullback_invariance_id
    (k : (Isogeny.id W.toAffine).kernel)
    (z : W.toAffine.FunctionField) :
    translateAlgEquivOfPoint W k.val ((Isogeny.id W.toAffine).pullback z) =
      (Isogeny.id W.toAffine).pullback z := by
  have h_k_zero : k.val = (0 : W.toAffine.Point) :=
    AddSubgroup.mem_bot.mp (Isogeny.kernel_id (W₁ := W.toAffine) ▸ k.property)
  rw [h_k_zero]
  change translateAlgEquivOfPoint W .zero ((Isogeny.id W.toAffine).pullback z) =
    (Isogeny.id W.toAffine).pullback z
  rw [translateAlgEquivOfPoint_zero]
  rfl

/-- **`SMulCommClass` for Worker A's master action**: the translation
action commutes with `F`-scalar multiplication because every
`translateAlgEquivOfPoint W k` is an F-AlgEquiv (hence F-linear). -/
instance translateMulSemiringAction_smulCommClass :
    SMulCommClass (Multiplicative W.toAffine.Point) F W.toAffine.FunctionField where
  smul_comm g c f := by
    change translateAlgEquivOfPoint W (Multiplicative.toAdd g) (c • f) =
      c • translateAlgEquivOfPoint W (Multiplicative.toAdd g) f
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

/-- **Restricted action**: `Multiplicative β.kernel` acts on `K(E)` via
the inclusion `β.kernel → E.Point` composed with Worker A's master action
`translateMulSemiringAction`. -/
noncomputable instance kernelMulSemiringAction
    (β : Isogeny W.toAffine W.toAffine) :
    MulSemiringAction (Multiplicative β.kernel) W.toAffine.FunctionField :=
  MulSemiringAction.compHom W.toAffine.FunctionField
    ((AddSubgroup.subtype β.kernel).toMultiplicative :
      Multiplicative β.kernel →* Multiplicative W.toAffine.Point)

/-- **`SMulCommClass` for the restricted action**: inherits from the master
action via the inclusion. -/
instance kernelMulSemiringAction_smulCommClass
    (β : Isogeny W.toAffine W.toAffine) :
    SMulCommClass (Multiplicative β.kernel) F W.toAffine.FunctionField where
  smul_comm g c f := by
    change translateAlgEquivOfPoint W (Multiplicative.toAdd g).val (c • f) =
      c • translateAlgEquivOfPoint W (Multiplicative.toAdd g).val f
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

/-- **Restricted action smul reduction**: under `kernelMulSemiringAction`,
`g • f = translateAlgEquivOfPoint W g.val f` for `g : Multiplicative β.kernel`. -/
@[simp] theorem kernelMulSemiringAction_smul
    (β : Isogeny W.toAffine W.toAffine)
    (g : Multiplicative β.kernel) (f : W.toAffine.FunctionField) :
    g • f = translateAlgEquivOfPoint W (Multiplicative.toAdd g).val f := rfl

/-- **Forward inclusion of the fixed-field theorem**: under the
xy-covariance family hypothesis, `β.pullback.fieldRange ⊆
FixedPoints.intermediateField (Multiplicative β.kernel)`.

Geometrically: every element in the image of `β.pullback` is fixed by
the action of every kernel element (via translation), since for k ∈ ker β
we have `β(P_gen + k) = β(P_gen)`, so `β.pullback z`'s evaluation is
unchanged under translation by k.

The witness `h_xy_family` provides the two coordinate identities (on
x_gen and y_gen); the IntermediateField equalizer extends them to all of
K(E) via `functionField_eq_intermediateField_adjoin_xy`. -/
theorem pullback_fieldRange_le_fixedField_of_xy_family [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W))) :
    β.pullback.fieldRange ≤
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
  rintro z ⟨w, rfl⟩
  intro g
  change translateAlgEquivOfPoint W (Multiplicative.toAdd g).val
      (β.pullback w) = β.pullback w
  exact translateAlgEquivOfPoint_pullback_invariance_of_xy W β
    (Multiplicative.toAdd g).val
    (h_xy_family (Multiplicative.toAdd g)).1
    (h_xy_family (Multiplicative.toAdd g)).2 w

/-- **xy-family at `k = 0`**: trivial since `τ_0 = AlgEquiv.refl`. Holds for
any isogeny β and any kernel-membership witness for 0. -/
theorem xy_family_zero
    (β : Isogeny W.toAffine W.toAffine)
    (h_zero_mem : (0 : W.toAffine.Point) ∈ β.kernel) :
    (translateAlgEquivOfPoint W (⟨0, h_zero_mem⟩ : β.kernel).val
        (β.pullback (x_gen W)) = β.pullback (x_gen W)) ∧
    (translateAlgEquivOfPoint W (⟨0, h_zero_mem⟩ : β.kernel).val
        (β.pullback (y_gen W)) = β.pullback (y_gen W)) :=
  ⟨rfl, rfl⟩

/-- **Layer 2 closure (witness-parametric on finrank match)**: under the
xy-covariance family + finrank equality, `β.pullback.fieldRange =
FixedPoints.intermediateField (Multiplicative β.kernel)`.

Direct application of `IntermediateField.eq_of_le_of_finrank_eq'` to the
forward inclusion (just shipped) plus the finrank-match witness. -/
theorem pullback_fieldRange_eq_fixedField_of_finrank_match [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    [hfindim : FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_finrank_match :
      Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField =
      Module.finrank
        ↥(FixedPoints.intermediateField (Multiplicative β.kernel) :
          IntermediateField F W.toAffine.FunctionField)
        W.toAffine.FunctionField) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) :=
  IntermediateField.eq_of_le_of_finrank_eq'
    (pullback_fieldRange_le_fixedField_of_xy_family W β h_xy_family)
    h_finrank_match

/-- **Layer 2 closure (Artin-machinery sourced)**: the finrank match
witness can be sourced from Mathlib's `FixedPoints.finrank_eq_card` (which
gives `[K(E) : FixedPoints] = |G|` axiom-clean from Faithful + Fintype) and
the cardinality match `|β.kernel| = β.degree` (Silverman III.4.10(b),
T-V-1-003 / V.1.3) plus the intrinsic relation
`[K(E) : β.pullback.fieldRange] = β.degree` (witness-parametric below).

This is the **packaged Artin-route closure**: takes the Hasse-content card
match as a witness and closes the fixed-field theorem. -/
theorem pullback_fieldRange_eq_fixedField_of_card_match [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    [hfin_ker : Fintype (Multiplicative β.kernel)]
    [hfaith : FaithfulSMul (Multiplicative β.kernel) W.toAffine.FunctionField]
    [hfindim : FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_pullback_finrank :
      Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField =
        Fintype.card (Multiplicative β.kernel)) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
  apply pullback_fieldRange_eq_fixedField_of_finrank_match W β h_xy_family
  rw [h_pullback_finrank]
  exact (FixedPoints.finrank_eq_card (Multiplicative β.kernel)
    W.toAffine.FunctionField).symm

/-- **`FaithfulSMul` (witness-parametric)**: given pointwise injectivity of
the kernel-translation map (different kernel elements produce different
F-AlgEquivs of K(E)), bundle into `FaithfulSMul` for the restricted
action `kernelMulSemiringAction`. -/
theorem faithfulSMul_kernel_of_translate_inj
    (β : Isogeny W.toAffine W.toAffine)
    (h_inj : ∀ k₁ k₂ : β.kernel,
      (∀ f : W.toAffine.FunctionField,
        translateAlgEquivOfPoint W k₁.val f =
        translateAlgEquivOfPoint W k₂.val f) →
      k₁ = k₂) :
    FaithfulSMul (Multiplicative β.kernel) W.toAffine.FunctionField where
  eq_of_smul_eq_smul {g₁ g₂} h :=
    Multiplicative.toAdd.injective
      (h_inj (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂) fun f ↦ h f)

/-- **`FaithfulSMul` (UNCONDITIONAL)**: discharges the witness in
`faithfulSMul_kernel_of_translate_inj` using
`translateAlgEquivOfPoint_injective` (just shipped in `EC/TranslationOrd`).

Direct corollary: for any isogeny β over a finite field, the restricted
action `kernelMulSemiringAction β` is faithful axiom-clean. This collapses
the FaithfulSMul witness in the Layer-2 cascade — combined with finiteness
of β.kernel (over finite F), Mathlib's Artin machinery
(`FixedPoints.finrank_eq_card`) applies unconditionally. -/
instance faithfulSMul_kernel
    (β : Isogeny W.toAffine W.toAffine) :
    FaithfulSMul (Multiplicative β.kernel) W.toAffine.FunctionField :=
  faithfulSMul_kernel_of_translate_inj W β fun _ _ h_pointwise ↦
    Subtype.ext (translateAlgEquivOfPoint_injective W (AlgEquiv.ext h_pointwise))

/-- **Intrinsic finrank relation (UNCONDITIONAL)**:
`Module.finrank ↥β.pullback.fieldRange K(E) = β.degree`.

Together with `faithfulSMul_kernel` and `Finite β.kernel`, this collapses
`pullback_fieldRange_eq_fixedField_of_card_match` to an unconditional
closure given the cardinality match `Fintype.card β.kernel = β.degree`
(the substantive Hasse content, V.1.3). -/
theorem finrank_pullback_fieldRange_eq_degree
    (β : Isogeny W.toAffine W.toAffine) :
    Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField = β.degree := by
  letI inst1 : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := β.toAlgebra
  letI inst_im : Algebra ↥β.pullback.fieldRange W.toAffine.FunctionField :=
    IntermediateField.toAlgebra _
  letI mod_im : Module ↥β.pullback.fieldRange W.toAffine.FunctionField :=
    inst_im.toModule
  change @Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField _ _ mod_im =
    β.degree
  unfold Isogeny.degree
  let i_alg : W.toAffine.FunctionField ≃ₐ[F] ↥β.pullback.range :=
    AlgEquiv.ofInjective β.pullback β.pullback_injective
  let bridge : ↥β.pullback.range ≃+* ↥β.pullback.fieldRange :=
    { toFun := fun x ↦ ⟨x.val, by obtain ⟨y, hy⟩ := x.property; exact ⟨y, hy⟩⟩
      invFun := fun x ↦ ⟨x.val, by obtain ⟨y, hy⟩ := x.property; exact ⟨y, hy⟩⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let i : W.toAffine.FunctionField ≃+* ↥β.pullback.fieldRange :=
    i_alg.toRingEquiv.trans bridge
  let j : W.toAffine.FunctionField ≃+* W.toAffine.FunctionField := RingEquiv.refl _
  have h_compat : (algebraMap ↥β.pullback.fieldRange W.toAffine.FunctionField).comp
      i.toRingHom =
      j.toRingHom.comp (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField) := by
    ext c
    rfl
  exact (Algebra.finrank_eq_of_equiv_equiv i j h_compat).symm

/-- **Layer 2 closure (UNCONDITIONAL on the intrinsic part)**: combines
`pullback_fieldRange_eq_fixedField_of_finrank_match` with the just-shipped
intrinsic finrank relation, leaving only the Hasse-content cardinality
match `Nat.card β.kernel = β.degree` as a witness.

Universal-in-q: takes the Hasse-content card-match witness and unconditionally
closes the fixed-field theorem `β.pullback.fieldRange = FixedPoints (Multiplicative β.kernel)`. -/
theorem pullback_fieldRange_eq_fixedField_of_card_match_intrinsic [Fintype F]
    (β : Isogeny W.toAffine W.toAffine)
    [hfin_ker : Fintype (Multiplicative β.kernel)]
    [hfindim : FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card_eq_degree : Fintype.card (Multiplicative β.kernel) = β.degree) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
  apply pullback_fieldRange_eq_fixedField_of_card_match W β h_xy_family
  rw [finrank_pullback_fieldRange_eq_degree W β, h_card_eq_degree]

section FrobeniusKE

variable {KK : Type*} [Field KK] [Fintype KK] [DecidableEq KK]
variable (V : WeierstrassCurve KK) [V.toAffine.IsElliptic]

omit [Fintype KK] in
/-- **Any `K`-AlgHom pullback fixes `K`-constants**: for any isogeny `β` over a
finite field `K`, `β.pullback (algebraMap K V.FunctionField c) =
algebraMap K V.FunctionField c`. -/
theorem isogeny_pullback_algebraMap_K
    (β : Isogeny V.toAffine V.toAffine) (c : KK) :
    β.pullback (algebraMap KK V.toAffine.FunctionField c) =
      algebraMap KK V.toAffine.FunctionField c :=
  β.pullback.commutes c

end FrobeniusKE

end HasseWeil

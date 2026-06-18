import HasseWeil.Endomorphism
import HasseWeil.FrobeniusIsogeny
import HasseWeil.OrdAtInftyBridge
import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius Endomorphism and Point Counting

Following Silverman III.4.6 and V.1.1, we define the Frobenius endomorphism as an
isogeny with concrete pullback `f ↦ f^q` and connect it to point counting.

## Main Definitions

- `frobeniusIsog`: The q-th power Frobenius as a `Basic.Isogeny` with concrete pullback.
- `traceOfFrobenius`: The trace of Frobenius, tr(π) = q + 1 - #E(F_q).
- `pointCount`: The number of F_q-rational points on E.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.6, V.1.1
* Sutherland, *18.783 Lecture 7*, Theorem 7.17
-/

open WeierstrassCurve

namespace HasseWeil

/-! ### Point counting basics -/

section PointCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of rational points on an affine elliptic curve, including O. -/
noncomputable def pointCount (E : Affine F) [Fintype E.Point] : ℕ := Fintype.card E.Point

end PointCount

/-! ### Frobenius endomorphism as an isogeny -/

section Frobenius

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- The `q`-th power Frobenius endomorphism as a `Basic.Isogeny` over `K`.

    The pullback `π* : K(E) →ₐ[K] K(E)` sends `f ↦ f^q` (concrete, from
    `FrobeniusIsogeny.lean`). The group homomorphism on K-rational points is
    the identity (since `x^q = x` for all `x ∈ K`).

    Reference: Silverman, Proposition III.4.6. -/
noncomputable def frobeniusIsog : Isogeny W.toAffine W.toAffine where
  pullback := FiniteField.frobeniusAlgHom K W.toAffine.FunctionField
  toAddMonoidHom := AddMonoidHom.id _

/-- The Frobenius pullback sends `f ↦ f^q`. -/
theorem frobeniusIsog_pullback_apply (f : W.toAffine.FunctionField) :
    (frobeniusIsog W).pullback f = f ^ Fintype.card K := by
  change FiniteField.frobeniusAlgHom K W.toAffine.FunctionField f = f ^ Fintype.card K
  rw [FiniteField.coe_frobeniusAlgHom]

/-! ### Order at infinity of Frobenius pullbacks

For `α = frobeniusIsog W` (the Frobenius endomorphism over a finite field
`K`), the pullback acts as `f ↦ f^q`. Composed with the order-at-infinity
formula and the strict non-archimedean inequality, this yields concrete
ord values for the addition-formula inputs:

* `ord_∞(π·x_gen) = -2q`, `ord_∞(π·y_gen) = -3q`.
* `ord_∞(π·x_gen − x_gen) = -2q` for `q ≥ 2`.
* `ord_∞(π·y_gen − y_gen) = -3q` for `q ≥ 2`.

These are the building blocks for the unconditional pole bound on
`addPullback_x W (frobeniusIsog W)` (Sorry 1's Frobenius case). -/

/-- `ord_∞(π·x_gen) = -2q` where `q = #K`. Direct from `frobeniusIsog_pullback_apply`
+ `ordAtInfty_x_gen_pow`. -/
theorem ordAtInfty_frobeniusIsog_pullback_x_gen :
    (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [frobeniusIsog_pullback_apply, ordAtInfty_x_gen_pow, ← WithTop.coe_nsmul, nsmul_eq_mul]
  congr 1
  ring

/-- `ord_∞(π·y_gen) = -3q` where `q = #K`. -/
theorem ordAtInfty_frobeniusIsog_pullback_y_gen :
    (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [frobeniusIsog_pullback_apply, ordAtInfty_y_gen_pow, ← WithTop.coe_nsmul, nsmul_eq_mul]
  congr 1
  ring

/-- For the finite field `K` (Field + Fintype), `Fintype.card K ≥ 2` since
`Field` requires `0 ≠ 1`. -/
private theorem two_le_fintype_card_K : (2 : ℕ) ≤ Fintype.card K :=
  Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

/-- `ord_∞(π·x_gen − x_gen) = -2q` for `q ≥ 2`. The strict non-archimedean
inequality `ord_∞(a − b) = ord_∞(a)` when `ord_∞(a) < ord_∞(b)`: here
`ord_∞(π·x_gen) = -2q < -2 = ord_∞(x_gen)` since `q ≥ 2`. -/
theorem ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen :
    (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W) - x_gen W) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_int : (-2 * (Fintype.card K : ℤ) : ℤ) < (-2 : ℤ) := by
    have : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast two_le_fintype_card_K (K := K)
    linarith
  have h_lt : (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W)) <
      (W_smooth W).ordAtInfty (x_gen W) := by
    rw [ordAtInfty_frobeniusIsog_pullback_x_gen, ordAtInfty_x_gen]
    exact WithTop.coe_lt_coe.mpr h_int
  exact ((W_smooth W).ordAtInfty_sub_eq_of_lt h_lt).trans
    (ordAtInfty_frobeniusIsog_pullback_x_gen W)

/-- `ord_∞(π·y_gen − y_gen) = -3q` for `q ≥ 2`. -/
theorem ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen :
    (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (y_gen W) - y_gen W) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_int : (-3 * (Fintype.card K : ℤ) : ℤ) < (-3 : ℤ) := by
    have : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast two_le_fintype_card_K (K := K)
    linarith
  have h_lt : (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty (y_gen W) := by
    rw [ordAtInfty_frobeniusIsog_pullback_y_gen, ordAtInfty_y_gen]
    exact WithTop.coe_lt_coe.mpr h_int
  exact ((W_smooth W).ordAtInfty_sub_eq_of_lt h_lt).trans
    (ordAtInfty_frobeniusIsog_pullback_y_gen W)

/-- The degree of the Frobenius isogeny is `#K`.
    Uses the sorry-free proof from `FrobeniusIsogeny.frobenius_finrank_functionField`.
    Reference: Silverman, Proposition III.4.6. -/
@[simp] theorem frobeniusIsog_degree :
    (frobeniusIsog W).degree = Fintype.card K := by
  change @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
    (frobeniusIsog W).toAlgebra.toModule = Fintype.card K
  exact frobenius_finrank_functionField K W

/-! ### Frobenius universal commute (CLOSE-C h_pb_comm for π)

The Frobenius pullback `π* z = z^q` commutes with **every** F-algebra
homomorphism on the function field. This is a structural fact: any ring
hom preserves q-th powers.

Specialised to `g = (mulByInt E n).pullback`, this gives the pullback-level
scalar commute (Route A's `h_pb_comm`) for `α = frobeniusIsog W`. -/

/-- **Frobenius universal commute**: `π.pullback ∘ g = g ∘ π.pullback` for any
    F-algebra hom `g : K(E) →ₐ[F] K(E)`. Direct from `g.map_pow` plus the
    `f ↦ f^q` characterisation of `π.pullback`. -/
theorem frobeniusIsog_pullback_universal_commute
    (g : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    (frobeniusIsog W).pullback.comp g = g.comp (frobeniusIsog W).pullback := by
  apply AlgHom.ext
  intro z
  change (frobeniusIsog W).pullback (g z) = g ((frobeniusIsog W).pullback z)
  rw [frobeniusIsog_pullback_apply, frobeniusIsog_pullback_apply, map_pow]

/-- **Route A `h_pb_comm` for Frobenius**: π.pullback commutes with
    `[n].pullback` for every integer `n`. Specialisation of
    `frobeniusIsog_pullback_universal_commute` to `g = (mulByInt E n).pullback`.

    This is the CLOSE-C h_pb_comm witness for the specific α = frobeniusIsog W
    case, applied at `n = (frobeniusIsog W).degree = #K`. Unconditional. -/
theorem frobeniusIsog_mulByInt_pullback_comm (n : ℤ) :
    (frobeniusIsog W).pullback.comp (mulByInt W.toAffine n).pullback =
      (mulByInt W.toAffine n).pullback.comp (frobeniusIsog W).pullback :=
  frobeniusIsog_pullback_universal_commute W (mulByInt W.toAffine n).pullback

/-- **Frobenius universal commute (Isogeny level)**: for any
isogeny `ψ : E → E`, the q-Frobenius isogeny commutes with `ψ` —
`φ_q.comp ψ = ψ.comp φ_q`. Lifts the pullback-level commute to the
isogeny level. The `toAddMonoidHom` part is trivial since
`φ_q.toAddMonoidHom = AddMonoidHom.id` over the F_q-rational base. -/
theorem frobeniusIsog_universal_commute_isog
    (ψ : Isogeny W.toAffine W.toAffine) :
    (frobeniusIsog W).comp ψ = ψ.comp (frobeniusIsog W) := by
  have h_pb : ψ.pullback.comp (frobeniusIsog W).pullback =
      (frobeniusIsog W).pullback.comp ψ.pullback :=
    (frobeniusIsog_pullback_universal_commute W ψ.pullback).symm
  have h_hom : (AddMonoidHom.id _).comp ψ.toAddMonoidHom =
      ψ.toAddMonoidHom.comp (AddMonoidHom.id _) := by
    rw [AddMonoidHom.id_comp, AddMonoidHom.comp_id]
  rcases ψ with ⟨pb, hom⟩
  show Isogeny.mk (pb.comp (frobeniusIsog W).pullback)
      ((AddMonoidHom.id _).comp hom) =
    Isogeny.mk ((frobeniusIsog W).pullback.comp pb) (hom.comp (AddMonoidHom.id _))
  rw [h_pb, h_hom]

/-- **F_p^k = φ_q identification (AlgHom level, power form)**: over an
F_q-rational elliptic curve with `Fintype.card K = p ^ n`, the q-Frobenius
pullback acts as the n-fold iterated p-th power on K(E). Direct from
`frobeniusIsog_pullback_apply : φ_q^*(f) = f^q` plus `q = p^n`. The
structural content of "F_p iterated k times = φ_q" reduces to this
identity once `q = p^k`. -/
theorem frobeniusIsog_pullback_eq_pow_pow
    (p n : ℕ) (h_card : Fintype.card K = p ^ n) (f : W.toAffine.FunctionField) :
    (frobeniusIsog W).pullback f = f ^ p ^ n := by
  rw [frobeniusIsog_pullback_apply, h_card]

/-! ### Verschiebung infrastructure: image of π* (CLOSE-C-VERSCHIEBUNG-FROBENIUS)

The Frobenius isogeny's pullback `π* : K(E) →ₐ[K] K(E)` is the field
endomorphism `f ↦ f^q` (where `q = #K`). Its image is the subfield
`K(E)^q` of `q`-th powers.

This is **load-bearing infrastructure** for the Verschiebung construction:
the dual `V` exists iff `[q]*K(E) ⊆ π*K(E) = K(E)^q`, and is recovered
by `AlgHom.factor` once that inclusion is established. -/

/-- The range (set image) of `π*` is the set of `q`-th powers. Direct
    consequence of `frobeniusIsog_pullback_apply : π* f = f^q`. -/
theorem frobeniusIsog_pullback_range :
    Set.range (frobeniusIsog W).pullback =
      Set.range ((· ^ Fintype.card K) :
        W.toAffine.FunctionField → W.toAffine.FunctionField) := by
  ext f
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg, frobeniusIsog_pullback_apply]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rwa [frobeniusIsog_pullback_apply]⟩

/-- The `AlgHom.fieldRange` (subfield image) of `π*` is the subfield of
    `q`-th powers. Equivalent to `frobeniusIsog_pullback_range` but in the
    `Subfield`-typed form needed by the Verschiebung's `AlgHom.factor`
    construction. -/
theorem frobeniusIsog_pullback_mem_iff (f : W.toAffine.FunctionField) :
    f ∈ (frobeniusIsog W).pullback.fieldRange ↔ ∃ g, g ^ Fintype.card K = f := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rwa [← frobeniusIsog_pullback_apply W g]⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change (frobeniusIsog W).pullback g = f
    rwa [frobeniusIsog_pullback_apply]

/-- A `q`-th power lies in the image of `π*` (one direction of the membership
    lemma, packaged for `AlgHom.factor` use). -/
theorem frobeniusIsog_pullback_pow_mem (f : W.toAffine.FunctionField) :
    f ^ Fintype.card K ∈ (frobeniusIsog W).pullback.fieldRange :=
  (frobeniusIsog_pullback_mem_iff W _).mpr ⟨f, rfl⟩

/-- The Verschiebung-existence inclusion (Silverman III.6.2): when every
    pullback `[q]* z` for `z` ranging over a generating set of `K(E)` is a
    `q`-th power, `[q].pullback` factors through `π.pullback`.

    This is the **witness form** of the inclusion `[q]*K(E) ⊆ π*K(E)`. The
    full inclusion follows from the witness applied to the generators
    `x_gen` and `y_gen` (which generate `K(E)` as an `F`-algebra modulo
    Weierstrass).

    Each q-th-power witness is itself a substantive computation
    (`x_gen → Φ_q(x_gen) / Ψ²_q(x_gen)` and analogously for `y`); these
    are deferred to Session 2 of the Verschiebung sub-ticket. -/
theorem mulByInt_pullback_pow_witness_iff_mem_frobenius_range
    (z : W.toAffine.FunctionField) :
    (∃ g, g ^ Fintype.card K = (mulByInt W.toAffine
      ((Fintype.card K : ℕ) : ℤ)).pullback z) ↔
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
      (frobeniusIsog W).pullback.fieldRange :=
  (frobeniusIsog_pullback_mem_iff W _).symm

end Frobenius

/-! ### Connection to point counting -/

section PointCounting

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-! **[2026-05-28 — placeholder removal, Strategy B].** The declarations
`pointCount_eq`, `traceOfFrobenius`, and `pointCount_eq_sub_trace` previously
lived here. They were defined through the placeholder `oneSubFrobeniusIsog`
(`pullback := AlgHom.id`, degree forced to 1), making them assert the
universally-false `#E(F_q) = 1` / `traceOfFrobenius = q`. They have been
**deleted**. The honest, witness-parametric replacement
`pointCount_eq_of_witness` (below) takes the genuine `1 − π` as input; the
genuine trace is `isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq)`,
and the top-level Hasse-bound API is
`WeilPairing.hasse_bound_unconditional` (the `hasse_bound_skeleton` milestone
was retired 2026-06-11). -/

/-- **Point count via a genuine `1 − π` witness** (Silverman V.1.1): if `β` is
any isogeny with `β.degree = pointCount`, then
`pointCount = q + 1 - isogTrace π β`.

Independent of any placeholder. The witness `β` is the genuine `1 − π`
(`isogOneSub_negFrobenius W hq`), whose `degree = pointCount` is the V.1.3
keystone (`ker_deg_skeleton` / `isogOneSub_negFrobenius_degree_eq_pointCount`). -/
theorem pointCount_eq_of_witness (β : Isogeny W.toAffine W.toAffine)
    (hβ_deg : (β.degree : ℤ) = pointCount W.toAffine) :
    (pointCount W.toAffine : ℤ) =
      Fintype.card K + 1 - isogTrace (frobeniusIsog W) β := by
  unfold isogTrace
  rw [frobeniusIsog_degree, hβ_deg]
  ring

end PointCounting

end HasseWeil

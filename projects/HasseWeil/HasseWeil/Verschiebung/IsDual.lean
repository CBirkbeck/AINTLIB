/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.DualIsogeny
import HasseWeil.EC.GenericPointZsmul
import HasseWeil.Verschiebung.Construction

/-!
# Verschiebung as `IsDualOf` Frobenius (Session 5)

Given the Session 3 inclusion `Im([q]*) ⊆ Im(π*)`, Session 4 constructed
the Verschiebung pullback `V* : K(E) →ₐ[K] K(E)` with the factoring
identity `[q]* = π* ∘ V*`.

This session:

* Bundles `V*` plus the natural toAddMonoidHom (`zsmulAddGroupHom q`,
  which is `[q]`'s point map) into a full `Isogeny W.toAffine W.toAffine`.
* Proves `IsDualOf verschiebungIsog_of_witness (frobeniusIsog W)`:
  both compositions `V ∘ π = [q]` and `π ∘ V = [q]` hold.

The key facts used:

* `mulByInt_q_factor_via_witness` (Session 4): `[q]* = π* ∘ V*`.
* `frobeniusIsog_pullback_universal_commute` (shipped commit `c916ebb`):
  `π*` commutes with every F-algebra hom, so `V* ∘ π* = π* ∘ V*`.
* For Frobenius over `F_q`, `π.toAddMonoidHom = AddMonoidHom.id` (since
  `x^q = x` on `F_q`-points), so the hom-level compositions reduce to
  `id ∘ (zsmul q) = zsmul q` and `(zsmul q) ∘ id = zsmul q`, both equal
  `[q].toAddMonoidHom`.

## Status

Witness-parametric on the Session 3 inclusion. When Session 3's
unconditional discharge lands, this file's outputs become axiom-clean.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Verschiebung as a full Isogeny

The Frobenius over a finite field has `toAddMonoidHom = AddMonoidHom.id`.
For the Verschiebung to satisfy `V ∘ π = [q]` and `π ∘ V = [q]` at the
hom level, we need `V.toAddMonoidHom = (mulByInt W q).toAddMonoidHom =
zsmulAddGroupHom q` (since composing with the identity on either side
gives the same map). -/

/-- The Verschiebung as a full `Isogeny`, witness-parametric on the
    Session 3 inclusion. The pullback comes from
    `verschiebungPullback_of_witness`; the toAddMonoidHom is
    `zsmulAddGroupHom q` (the `[q]`-point-map, since Frobenius on
    `F_q`-points is the identity). -/
noncomputable def verschiebungIsog_of_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    Isogeny W.toAffine W.toAffine where
  pullback := verschiebungPullback_of_witness W h_subset
  toAddMonoidHom := (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom

/-! ### Both compositions equal `[q]` -/

/-- **First composition**: `verschiebung ∘ π = [q]`. At the Isogeny level. -/
theorem verschiebung_comp_frobenius_eq_mulByInt_q
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (verschiebungIsog_of_witness W h_subset).comp (frobeniusIsog W) =
      mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) := by
  -- Both sides are Isogeny structures; show equality of both fields.
  -- LHS pullback: (verschiebung.comp π).pullback
  --             = π.pullback.comp verschiebung.pullback (Isogeny.comp def, reversed)
  --             = π.pullback.comp V*  (where V* = verschiebungPullback)
  --             = (mulByInt W q).pullback  (by mulByInt_q_factor_via_witness, symm)
  -- LHS hom: (verschiebung.comp π).toAddMonoidHom
  --        = verschiebung.toAddMonoidHom.comp π.toAddMonoidHom
  --        = (mulByInt q).toAddMonoidHom.comp AddMonoidHom.id
  --        = (mulByInt q).toAddMonoidHom
  show (Isogeny.mk
      ((frobeniusIsog W).pullback.comp
        (verschiebungIsog_of_witness W h_subset).pullback)
      ((verschiebungIsog_of_witness W h_subset).toAddMonoidHom.comp
        (frobeniusIsog W).toAddMonoidHom) :
    Isogeny W.toAffine W.toAffine) =
    mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)
  -- Show pullback equality: π.pullback.comp V* = (mulByInt W q).pullback
  have h_pb : (frobeniusIsog W).pullback.comp
      (verschiebungIsog_of_witness W h_subset).pullback =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback := by
    show (frobeniusIsog W).pullback.comp
      (verschiebungPullback_of_witness W h_subset) = _
    exact (mulByInt_q_factor_via_witness W h_subset).symm
  -- Show hom equality: (mulByInt q).toAddMonoidHom.comp id = (mulByInt q).toAddMonoidHom
  have h_hom : (verschiebungIsog_of_witness W h_subset).toAddMonoidHom.comp
      (frobeniusIsog W).toAddMonoidHom =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom := by
    show (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom.comp
      (AddMonoidHom.id _) = _
    exact AddMonoidHom.comp_id _
  -- Reassemble the Isogeny equality
  rcases hα : mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) with ⟨pb, hom⟩
  rw [hα] at h_pb h_hom
  simp only at h_pb h_hom
  rw [h_pb, h_hom]

/-- **Second composition**: `π ∘ verschiebung = [q]`. Uses
    `frobeniusIsog_pullback_universal_commute` to swap π* and V*, then the
    first composition. -/
theorem frobenius_comp_verschiebung_eq_mulByInt_q
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (frobeniusIsog W).comp (verschiebungIsog_of_witness W h_subset) =
      mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) := by
  -- (π.comp verschiebung).pullback
  --   = verschiebung.pullback.comp π.pullback (Isogeny.comp def, reversed)
  --   = V* ∘ π*
  --   = π* ∘ V*  (by frobeniusIsog_pullback_universal_commute)
  --   = (mulByInt W q).pullback  (by Session 4)
  -- (π.comp verschiebung).toAddMonoidHom
  --   = π.toAddMonoidHom.comp verschiebung.toAddMonoidHom
  --   = id.comp ((mulByInt q).toAddMonoidHom)
  --   = (mulByInt q).toAddMonoidHom
  show (Isogeny.mk
      ((verschiebungIsog_of_witness W h_subset).pullback.comp
        (frobeniusIsog W).pullback)
      ((frobeniusIsog W).toAddMonoidHom.comp
        (verschiebungIsog_of_witness W h_subset).toAddMonoidHom) :
    Isogeny W.toAffine W.toAffine) =
    mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)
  have h_pb : (verschiebungIsog_of_witness W h_subset).pullback.comp
      (frobeniusIsog W).pullback =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback := by
    -- V* ∘ π* = π* ∘ V* by Frobenius universal commute, then = (mulByInt q).pullback by Session 4
    show (verschiebungPullback_of_witness W h_subset).comp
      (frobeniusIsog W).pullback = _
    rw [← frobeniusIsog_pullback_universal_commute W
      (verschiebungPullback_of_witness W h_subset)]
    exact (mulByInt_q_factor_via_witness W h_subset).symm
  have h_hom : (frobeniusIsog W).toAddMonoidHom.comp
      (verschiebungIsog_of_witness W h_subset).toAddMonoidHom =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom := by
    show (AddMonoidHom.id _).comp
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom = _
    exact AddMonoidHom.id_comp _
  rcases hα : mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) with ⟨pb, hom⟩
  rw [hα] at h_pb h_hom
  simp only at h_pb h_hom
  rw [h_pb, h_hom]

/-- **Verschiebung is the dual of Frobenius**: combines both compositions. -/
theorem verschiebungIsog_of_witness_isDualOf_frobenius
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W) := by
  refine ⟨?_, ?_⟩
  · -- IsDualOf needs verschiebung.comp π = mulByInt α.degree where α = frobeniusIsog
    -- (frobeniusIsog W).degree = #K (by frobeniusIsog_degree)
    rw [frobeniusIsog_degree]
    exact verschiebung_comp_frobenius_eq_mulByInt_q W h_subset
  · rw [frobeniusIsog_degree]
    exact frobenius_comp_verschiebung_eq_mulByInt_q W h_subset

/-! ### V-side σ-commutation (foundation for V-side D-track)

For Worker B's V-side D-track to mirror the π-side, we need σ.pb to
commute with V.pb. This follows from `[q]* = π* ∘ V*` (Session 4) plus
σ commuting with both `[q]*` (mulByInt centrality) and `π*` (Frobenius
universal commute), then π*'s injectivity. Universal in q;
witness-parametric on the Session 3 inclusion. -/

/-- **σ.pb commutes with V.pb**: for any `z ∈ K(E)`,
`σ.pb (V.pb z) = V.pb (σ.pb z)`. Universal in q; witness-parametric on
the Session 3 inclusion. Foundation for V-side σ-symmetry hypotheses
in `addPullback_x_pair_sigma_invariant`. -/
theorem verschiebung_pullback_commute_mulByInt_neg_one
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (verschiebungPullback_of_witness W h_subset).comp
        (mulByInt W.toAffine (-1)).pullback =
      (mulByInt W.toAffine (-1)).pullback.comp
        (verschiebungPullback_of_witness W h_subset) := by
  apply AlgHom.ext
  intro z
  -- π.pb is injective: it suffices to show π.pb of both sides agree.
  apply (frobeniusIsog W).pullback_injective
  -- LHS: π.pb (V.pb (σ.pb z)) = [q].pb (σ.pb z) (factor identity)
  -- RHS: π.pb (σ.pb (V.pb z)) = σ.pb (π.pb (V.pb z)) (frobenius universal commute)
  --    = σ.pb ([q].pb z) (factor identity)
  --    = [q].pb (σ.pb z) (mulByInt commutativity)
  show (frobeniusIsog W).pullback
      ((verschiebungPullback_of_witness W h_subset)
        ((mulByInt W.toAffine (-1)).pullback z)) =
      (frobeniusIsog W).pullback
        ((mulByInt W.toAffine (-1)).pullback
          ((verschiebungPullback_of_witness W h_subset) z))
  -- Step 1: rewrite π.pb ∘ V.pb = [q].pb on both sides.
  have h_factor :
      (frobeniusIsog W).pullback.comp
        (verschiebungPullback_of_witness W h_subset) =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback :=
    (mulByInt_q_factor_via_witness W h_subset).symm
  have h_factor_apply : ∀ z',
      (frobeniusIsog W).pullback
        ((verschiebungPullback_of_witness W h_subset) z') =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z' :=
    DFunLike.congr_fun h_factor
  rw [h_factor_apply ((mulByInt W.toAffine (-1)).pullback z)]
  -- Goal: [q].pb (σ.pb z) = π.pb (σ.pb (V.pb z))
  -- RHS: use σ commutes with π (universal commute).
  have h_pi_sigma := frobeniusIsog_pullback_universal_commute W
    (mulByInt W.toAffine (-1)).pullback
  -- h_pi_sigma : π.pb.comp σ.pb = σ.pb.comp π.pb
  have h_pi_sigma_apply : ∀ z',
      (frobeniusIsog W).pullback
        ((mulByInt W.toAffine (-1)).pullback z') =
      (mulByInt W.toAffine (-1)).pullback
        ((frobeniusIsog W).pullback z') :=
    DFunLike.congr_fun h_pi_sigma
  rw [h_pi_sigma_apply ((verschiebungPullback_of_witness W h_subset) z),
      h_factor_apply z]
  -- Goal: [q].pb (σ.pb z) = σ.pb ([q].pb z)
  -- This is mulByInt commutativity at the pullback level.
  have h_mul_comm : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.comp
      (mulByInt W.toAffine (-1)).pullback =
      (mulByInt W.toAffine (-1)).pullback.comp
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback := by
    -- Both sides equal (mulByInt -q).pullback, by mulByInt_comp_eq_mul.
    have h_q_ne : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
      have h := Fintype.card_pos (α := K)
      omega
    have h_neg_one_ne : ((-1 : ℤ)) ≠ 0 := by norm_num
    have h_q_neg_one : ((Fintype.card K : ℕ) : ℤ) * (-1) ≠ 0 :=
      mul_ne_zero h_q_ne h_neg_one_ne
    have h_neg_one_q : ((-1 : ℤ)) * ((Fintype.card K : ℕ) : ℤ) ≠ 0 :=
      mul_ne_zero h_neg_one_ne h_q_ne
    have h1 : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
        (mulByInt W.toAffine (-1)) =
        mulByInt W.toAffine (((Fintype.card K : ℕ) : ℤ) * (-1)) :=
      mulByInt_comp_eq_mul W _ _ h_q_ne h_neg_one_ne h_q_neg_one
    have h2 : (mulByInt W.toAffine (-1)).comp
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) =
        mulByInt W.toAffine ((-1) * ((Fintype.card K : ℕ) : ℤ)) :=
      mulByInt_comp_eq_mul W _ _ h_neg_one_ne h_q_ne h_neg_one_q
    have h_eq : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
        (mulByInt W.toAffine (-1)) =
        (mulByInt W.toAffine (-1)).comp
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) := by
      rw [h1, h2]; congr 1; ring
    -- Convert isogeny equality to pullback equality (at AlgHom level).
    have h_pb : ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
          (mulByInt W.toAffine (-1))).pullback =
        ((mulByInt W.toAffine (-1)).comp
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ))).pullback :=
      congrArg Isogeny.pullback h_eq
    -- ((α.comp β).pullback = β.pullback.comp α.pullback) by Isogeny.comp def.
    show (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.comp
        (mulByInt W.toAffine (-1)).pullback =
        (mulByInt W.toAffine (-1)).pullback.comp
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
    -- LHS = ((mulByInt -1).comp (mulByInt q)).pullback.
    -- RHS = ((mulByInt q).comp (mulByInt -1)).pullback.
    -- By h_eq (in reversed form), they're equal.
    have h_lhs_eq : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.comp
        (mulByInt W.toAffine (-1)).pullback =
        ((mulByInt W.toAffine (-1)).comp
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ))).pullback := rfl
    have h_rhs_eq : (mulByInt W.toAffine (-1)).pullback.comp
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
        ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
          (mulByInt W.toAffine (-1))).pullback := rfl
    rw [h_lhs_eq, h_rhs_eq, h_eq]
  exact DFunLike.congr_fun h_mul_comm z

/-! ### σ-V commute from `IsDualOf V π` (R25h Worker-A Round 3)

A general-V variant of `verschiebung_pullback_commute_mulByInt_neg_one`:
instead of taking the witness-form Session-3 inclusion, take a concrete
`hV : IsDualOf V (frobeniusIsog W)` and derive the σ-V commute identity.

The argument is identical to the witness-form version: π is injective on
pullback, so it suffices to compare `π.pb (σ.pb (V.pb f))` and
`π.pb (V.pb (σ.pb f))`. Both reduce to `σ.pb ([q].pb f)` after applying
`hV.1` (V.comp π = [q]) + Frobenius universal commute + mulByInt
commutativity.

* **Project ticket**: R25h Worker-A Round 3 secondary task (σ-V commute
  helper for Worker C).
* **Mathematical content**: Silverman III.6.2 (the dual isogeny commutes
  with the negation isogeny at the function-field-pullback level). -/

/-- **σ-V commute from `IsDualOf V π`**: for any V dual to Frobenius,
`σ.pb (V.pb f) = V.pb (σ.pb f)` where σ = mulByInt W (-1) (negation).
Direct adaptation of `verschiebung_pullback_commute_mulByInt_neg_one`
using `hV.1 : V.comp π = [q]` in place of the witness-form factor
identity. -/
theorem sigma_V_commute_of_hV
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W)) :
    ∀ f : W.toAffine.FunctionField,
      (mulByInt W.toAffine (-1)).pullback (V.pullback f) =
        V.pullback ((mulByInt W.toAffine (-1)).pullback f) := by
  intro f
  -- Apply π.pullback (injective) to both sides; it suffices to compare images.
  apply (frobeniusIsog W).pullback_injective
  -- hV.1 gives V.comp π = mulByInt q (since π.degree = #K).
  have h_factor : (frobeniusIsog W).pullback.comp V.pullback =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback := by
    have h := hV.1
    -- h : V.comp π = mulByInt π.degree = mulByInt #K via frobeniusIsog_degree
    rw [frobeniusIsog_degree] at h
    -- (V.comp π).pullback = π.pullback.comp V.pullback by Isogeny.comp def
    exact congrArg Isogeny.pullback h
  have h_factor_apply : ∀ z',
      (frobeniusIsog W).pullback (V.pullback z') =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z' :=
    DFunLike.congr_fun h_factor
  -- LHS goal: π.pb (σ.pb (V.pb f)).
  -- Step 1: σ commutes with π via universal commute.
  have h_pi_sigma := frobeniusIsog_pullback_universal_commute W
    (mulByInt W.toAffine (-1)).pullback
  have h_pi_sigma_apply : ∀ z',
      (frobeniusIsog W).pullback ((mulByInt W.toAffine (-1)).pullback z') =
      (mulByInt W.toAffine (-1)).pullback ((frobeniusIsog W).pullback z') :=
    DFunLike.congr_fun h_pi_sigma
  show (frobeniusIsog W).pullback
      ((mulByInt W.toAffine (-1)).pullback (V.pullback f)) =
    (frobeniusIsog W).pullback
      (V.pullback ((mulByInt W.toAffine (-1)).pullback f))
  -- LHS: π.pb (σ.pb (V.pb f)) = σ.pb (π.pb (V.pb f)) = σ.pb ([q].pb f).
  rw [h_pi_sigma_apply (V.pullback f), h_factor_apply f]
  -- RHS: π.pb (V.pb (σ.pb f)) = [q].pb (σ.pb f).
  rw [h_factor_apply ((mulByInt W.toAffine (-1)).pullback f)]
  -- Goal: σ.pb ([q].pb f) = [q].pb (σ.pb f).
  -- mulByInt commutativity at pullback level.
  have h_q_ne : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    have h := Fintype.card_pos (α := K); omega
  have h_neg_one_ne : ((-1 : ℤ)) ≠ 0 := by norm_num
  have h1 : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
      (mulByInt W.toAffine (-1)) =
      mulByInt W.toAffine (((Fintype.card K : ℕ) : ℤ) * (-1)) :=
    mulByInt_comp_eq_mul W _ _ h_q_ne h_neg_one_ne
      (mul_ne_zero h_q_ne h_neg_one_ne)
  have h2 : (mulByInt W.toAffine (-1)).comp
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) =
      mulByInt W.toAffine ((-1) * ((Fintype.card K : ℕ) : ℤ)) :=
    mulByInt_comp_eq_mul W _ _ h_neg_one_ne h_q_ne
      (mul_ne_zero h_neg_one_ne h_q_ne)
  have h_eq : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
      (mulByInt W.toAffine (-1)) =
      (mulByInt W.toAffine (-1)).comp
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) := by
    rw [h1, h2]; congr 1; ring
  have h_pb : ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
        (mulByInt W.toAffine (-1))).pullback =
      ((mulByInt W.toAffine (-1)).comp
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ))).pullback :=
    congrArg Isogeny.pullback h_eq
  -- ((α.comp β).pullback = β.pullback.comp α.pullback) by Isogeny.comp def.
  exact DFunLike.congr_fun h_pb f

/-! ### Iterated `V^k · π^k = [q^k]` — Silverman III.6.1 inductive composition

Mirrors Silverman III.6.1's Frobenius-Verschiebung dual chain at the
multi-prime-power level. For `q = #K`, the V·π = π·V = [q] relation
iterates to V^k · π^k = [q^k] for all k ≥ 0.

This is the **isogeny-level** content of the inductive composition; the
polynomial-side `Φ_{p^k} ∈ R[X^{p^k}]` propagation (Worker C's Route A)
consumes this output to derive the universal Φ_q result.

Universal in k; witness-parametric on the Session 3 inclusion (same as
the underlying V). -/

/-- The k-fold composition of an isogeny with itself. The recursion puts
the new copy on the OUTSIDE: `isogenyIterate (k+1) = (isogenyIterate k).comp φ`,
so that the pullback unfolds as `φ.pb` outside `(isogenyIterate k).pb` —
the convention needed for the `[q^k].pb x_gen = (V^k.pb x_gen)^{q^k}` proof. -/
noncomputable def isogenyIterate (φ : Isogeny W.toAffine W.toAffine)
    (k : ℕ) : Isogeny W.toAffine W.toAffine :=
  Nat.rec (Isogeny.id W.toAffine) (fun _ ih ↦ ih.comp φ) k

omit [Fintype K] in
@[simp] theorem isogenyIterate_zero (φ : Isogeny W.toAffine W.toAffine) :
    isogenyIterate W φ 0 = Isogeny.id W.toAffine := rfl

omit [Fintype K] in
@[simp] theorem isogenyIterate_succ (φ : Isogeny W.toAffine W.toAffine) (k : ℕ) :
    isogenyIterate W φ (k + 1) = (isogenyIterate W φ k).comp φ := rfl

/-- **V and π commute as isogenies**: `V.comp π = π.comp V = mulByInt W q`.
Both shipped as `verschiebung_comp_frobenius_eq_mulByInt_q` and
`frobenius_comp_verschiebung_eq_mulByInt_q`. Bundled here for the
iterated-composition argument. -/
theorem verschiebungIsog_frobeniusIsog_comm
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (verschiebungIsog_of_witness W h_subset).comp (frobeniusIsog W) =
      (frobeniusIsog W).comp (verschiebungIsog_of_witness W h_subset) := by
  rw [verschiebung_comp_frobenius_eq_mulByInt_q W h_subset,
      frobenius_comp_verschiebung_eq_mulByInt_q W h_subset]

/-- **`[q^k].pb g = (V^k.pb g)^{q^k}` for every `g ∈ K(E)`** — the
generator-independent core of Silverman III.6.1's inductive composition,
shared by the `x_gen`/`y_gen` specialisations below. Universal in `k` and
`g`; witness-parametric on the Session 3 inclusion.

Proof by induction on `k`:
* `k=0`: `[1].pb g = g = g^1`, via `mulByInt_one_pullback_eq_id`.
* `k+1`: `[q^{k+1}].pb = [q].pb ∘ [q^k].pb`; by IH `[q^k].pb g
  = (V^k.pb g)^{q^k}`, so `[q^{k+1}].pb g = [q].pb((V^k.pb g)^{q^k})
  = (V^{k+1}.pb g)^{q^{k+1}}`, using `[q].pb z = π.pb (V.pb z) = (V.pb z)^q`,
  `[q^k].pb`'s commutation with `V.pb`, and K-algebra distribution. -/
private theorem mulByInt_pow_pullback_gen_eq_pow_qpow
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (g : W.toAffine.FunctionField) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback g =
      ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback
        g) ^ (Fintype.card K ^ k) := by
  induction k with
  | zero =>
    show (mulByInt W.toAffine ((1 : ℕ) : ℤ)).pullback g =
      ((Isogeny.id W.toAffine).pullback g) ^ 1
    have h1 : ((1 : ℕ) : ℤ) = 1 := by norm_num
    rw [h1, mulByInt_one_pullback_eq_id]
    simp only [Isogeny.id_pullback, AlgHom.id_apply, pow_one]
  | succ k ih =>
    have h_q_succ : (Fintype.card K ^ (k + 1) : ℕ) =
        Fintype.card K * Fintype.card K ^ k := by ring
    have h_card_pos : 0 < Fintype.card K := Fintype.card_pos
    have h_q_ne : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp h_card_pos
    have h_qk_ne : ((Fintype.card K ^ k : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (pow_pos h_card_pos k)
    have h_q_qk_ne : ((Fintype.card K : ℕ) : ℤ) * ((Fintype.card K ^ k : ℕ) : ℤ) ≠ 0 :=
      mul_ne_zero h_q_ne h_qk_ne
    -- Decompose the LHS: [q^(k+1)] = [q].comp [q^k] at the isogeny level.
    have h_decomp : mulByInt W.toAffine ((Fintype.card K ^ (k + 1) : ℕ) : ℤ) =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
          (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)) := by
      have h := mulByInt_comp_eq_mul W ((Fintype.card K : ℕ) : ℤ)
        ((Fintype.card K ^ k : ℕ) : ℤ) h_q_ne h_qk_ne h_q_qk_ne
      rw [h]
      congr 1
      push_cast [h_q_succ]; ring
    -- Apply pullback to both sides of h_decomp. `comp` is contravariant on
    -- pullback, so `([q].comp [q^k]).pb g = [q^k].pb ([q].pb g)`.
    have h_decomp_pb := congrArg Isogeny.pullback h_decomp
    have h_apply := DFunLike.congr_fun h_decomp_pb g
    rw [h_apply]
    show ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
        ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback g)) = _
    -- Rewrite [q].pb g = (V.pb g)^q via the V·π = [q] identity.
    have h_q_pb : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback g =
        ((verschiebungPullback_of_witness W h_subset) g) ^ Fintype.card K := by
      have h_factor :
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
          (frobeniusIsog W).pullback.comp
            (verschiebungPullback_of_witness W h_subset) :=
        mulByInt_q_factor_via_witness W h_subset
      have h_at := DFunLike.congr_fun h_factor g
      rw [AlgHom.comp_apply] at h_at
      rw [h_at, frobeniusIsog_pullback_apply]
    rw [h_q_pb, map_pow]
    -- Goal: ([q^k].pb (V.pb g))^q = (V^(k+1).pb g)^(q^(k+1)).
    -- V.pb commutes with [q^k].pb: [q^k].pb (V.pb g) = V.pb ([q^k].pb g).
    have h_comm : (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
        ((verschiebungPullback_of_witness W h_subset) g) =
        (verschiebungPullback_of_witness W h_subset)
          ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback g) := by
      -- Prove via π.pb injectivity: π.pb commutes with [q^k].pb (Frobenius
      -- universal commute) and with V.pb (factor identity).
      apply (frobeniusIsog W).pullback_injective
      have h_pi_qk := frobeniusIsog_pullback_universal_commute W
        (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
      have h_pi_V : (frobeniusIsog W).pullback
          ((verschiebungPullback_of_witness W h_subset) g) =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback g := by
        have h_factor :
            (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
            (frobeniusIsog W).pullback.comp
              (verschiebungPullback_of_witness W h_subset) :=
          mulByInt_q_factor_via_witness W h_subset
        have h_at := DFunLike.congr_fun h_factor g
        rw [AlgHom.comp_apply] at h_at
        exact h_at.symm
      have h_lhs_pi : (frobeniusIsog W).pullback
          ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
            ((verschiebungPullback_of_witness W h_subset) g)) =
          (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
            ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback g) := by
        have h_app := DFunLike.congr_fun h_pi_qk
          ((verschiebungPullback_of_witness W h_subset) g)
        rw [AlgHom.comp_apply, AlgHom.comp_apply] at h_app
        rw [h_app, h_pi_V]
      have h_rhs_pi : (frobeniusIsog W).pullback
          ((verschiebungPullback_of_witness W h_subset)
            ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback g)) =
          (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback
            ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback g) := by
        have h_factor :
            (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
            (frobeniusIsog W).pullback.comp
              (verschiebungPullback_of_witness W h_subset) :=
          mulByInt_q_factor_via_witness W h_subset
        have h_at := DFunLike.congr_fun h_factor
          ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback g)
        rw [AlgHom.comp_apply] at h_at
        rw [← h_at]
        -- [q] commutes with [q^k] (both mulByInt central).
        have h_qk_q := mulByInt_comp_eq_mul W ((Fintype.card K ^ k : ℕ) : ℤ)
          ((Fintype.card K : ℕ) : ℤ) h_qk_ne h_q_ne (by
            rw [mul_comm]; exact h_q_qk_ne)
        have h_q_qk := mulByInt_comp_eq_mul W ((Fintype.card K : ℕ) : ℤ)
          ((Fintype.card K ^ k : ℕ) : ℤ) h_q_ne h_qk_ne h_q_qk_ne
        have h_eq : (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).comp
            (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) =
            (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).comp
              (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)) := by
          rw [h_qk_q, h_q_qk]; congr 1; ring
        exact DFunLike.congr_fun (congrArg Isogeny.pullback h_eq) g
      rw [h_lhs_pi, h_rhs_pi]
    rw [h_comm, ih]
    -- After h_comm + ih the LHS is `V.pb ((V^k.pb g)^(q^k))`;
    -- `map_pow` pushes the power out: `(V.pb (V^k.pb g))^(q^k)`.
    rw [map_pow]
    show (((verschiebungIsog_of_witness W h_subset).pullback
        ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback
          g)) ^ Fintype.card K ^ k) ^ Fintype.card K = _
    -- V.pb (V^k.pb g) = V^(k+1).pb g by isogenyIterate_succ.
    have h_iter_succ : (isogenyIterate W (verschiebungIsog_of_witness W h_subset)
        (k + 1)).pullback g =
        (verschiebungIsog_of_witness W h_subset).pullback
          ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback
            g) := rfl
    rw [← h_iter_succ, ← pow_mul]
    push_cast [h_q_succ]; ring_nf

/-- **`[q^k].pb x_gen = (V^k.pb x_gen)^{q^k}`** — Silverman III.6.1
inductive composition at the function-field level. The `[q^k]`-pullback
of `x_gen` is a `q^k`-th power, witnessed explicitly by the k-fold
iterate of the Verschiebung pullback applied to `x_gen`.

Universal in k; witness-parametric on the Session 3 inclusion. Worker C's
polynomial-side `Φ_q^k ∈ R[X^{q^k}]` consumes this output to derive the
universal Φ_q induction.

Proof by induction on k:
* k=0: `[1].pb x_gen = x_gen = x_gen^1`. Trivial via `mulByInt_one_pullback_eq_id`.
* k+1: `[q^{k+1}].pb = [q].pb ∘ [q^k].pb`. By IH, `[q^k].pb x_gen
  = (V^k.pb x_gen)^{q^k}`. So `[q^{k+1}].pb x_gen = [q].pb((V^k.pb x_gen)^{q^k})
  = (V.pb (V^k.pb x_gen))^q · q^k = (V^{k+1}.pb x_gen)^{q^{k+1}}`, using
  `[q].pb z = π.pb (V.pb z) = (V.pb z)^q` and V.pb K-alg distribution. -/
theorem mulByInt_pow_pullback_x_gen_eq_pow_qpow
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (x_gen W) =
      ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback
        (x_gen W)) ^ (Fintype.card K ^ k) :=
  mulByInt_pow_pullback_gen_eq_pow_qpow W h_subset k (x_gen W)

/-- **`[q^k].pb y_gen = (V^k.pb y_gen)^{q^k}`** — y-side analog of
`mulByInt_pow_pullback_x_gen_eq_pow_qpow`. Same induction structure with
`y_gen` in place of `x_gen` throughout. Universal in k; witness-parametric
on the Session-3 inclusion. -/
theorem mulByInt_pow_pullback_y_gen_eq_pow_qpow
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (y_gen W) =
      ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback
        (y_gen W)) ^ (Fintype.card K ^ k) :=
  mulByInt_pow_pullback_gen_eq_pow_qpow W h_subset k (y_gen W)

end HasseWeil

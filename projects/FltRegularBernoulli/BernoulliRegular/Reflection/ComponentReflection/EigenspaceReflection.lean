module

public import BernoulliRegular.Reflection.ComponentReflection.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Eigenspace reflection (REF-25 — substantive structural argument)

This file packages the **eigenspace argument** behind REF-25.

## Setup

Given a `(ZMod p)ˣ`-action `galAction` on a `ZMod p`-module `V`, the
`k`-th eigenspace is

  `eigenspace galAction k := { v | ∀ a ∈ (ZMod p)ˣ, galAction a v = a^k • v }`.

For a non-trivial additive character `phi : V → ZMod p` of Galois
weight `k` (i.e. `phi (galAction a v) = a^k • phi v`), the explicit
projection `π_k(v) := (#(ZMod p)ˣ)⁻¹ ∑_a a^{-k} • galAction a v` lies
in `eigenspace galAction k` and preserves the phi-image.

## Strategy

We expose the eigenspace, the projection, and the **two key properties**
(`projection_mem_eigenspace`, `phi_projection_eq_phi`) that together give
the substantive REF-25 conclusion `∃ w ∈ eigenspace k, phi w ≠ 0`.

The two key properties are stated as a structure
`EigenspaceProjectionData` so that consumers can supply them once and
reuse the structural composition. The composition itself
(`exists_eigenspace_phi_nontrivial_of_projectionData`) is purely
structural.

This isolates the substantive content (the projection's eigenspace
membership and phi-preservation) from the structural reflection
conclusion.

## Main definitions

* `eigenspace galAction k` — the `k`-th eigenspace.
* `EigenspaceProjectionData galAction phi k` — bundle the substantive
  content: a projection function with `mem_eigenspace` and `phi_eq` properties.
* `exists_eigenspace_phi_nontrivial_of_projectionData` — REF-25
  structural conclusion: phi non-trivial + projection data ⟹ eigenspace
  non-trivially contributes to phi.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset

variable {p : ℕ} [Fact p.Prime]

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- The `k`-th eigenspace of a `(ZMod p)ˣ`-action on `V`:
`eigenspace galAction k = { v | ∀ a, galAction a v = a^k • v }`. -/
def eigenspace (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ) :
    AddSubgroup V where
  carrier := { v : V | ∀ a : (ZMod p)ˣ, galAction a v = ((a : ZMod p) ^ k) • v }
  zero_mem' := by
    intro a
    simp
  add_mem' {v w} hv hw := by
    intro a
    rw [map_add, hv a, hw a, smul_add]
  neg_mem' {v} hv := by
    intro a
    rw [map_neg, hv a, smul_neg]

theorem mem_eigenspace_iff (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ)
    (v : V) :
    v ∈ eigenspace galAction k ↔
      ∀ a : (ZMod p)ˣ, galAction a v = ((a : ZMod p) ^ k) • v :=
  Iff.rfl

/-- **Eigenspace projection data** packaging the substantive content of
the eigenspace projection: a function `proj : V → V` together with
witnesses that `proj v ∈ eigenspace galAction k` and `phi (proj v) = phi v`.

In the standard cyclotomic setup, `proj v := (p-1)⁻¹ ∑_a a^{-k} galAction a v`
satisfies these properties; the `EigenspaceProjectionData` structure
records them abstractly so the structural reflection composition can
proceed independently of the projection's internal computation. -/
structure EigenspaceProjectionData (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (phi : V →+ ZMod p) (k : ℕ) where
  /-- The projection. -/
  proj : V → V
  /-- The projection lands in the `k`-th eigenspace. -/
  proj_mem_eigenspace : ∀ v, proj v ∈ eigenspace galAction k
  /-- The projection preserves the phi-image. -/
  phi_proj_eq : ∀ v, phi (proj v) = phi v

/-- **Substantive REF-25 conclusion via projection data.**

Given a non-trivial `phi : V → ZMod p` of Galois weight `k` (encoded
via the projection data: the projection preserves phi), the `k`-th
eigenspace contains an element with non-zero phi-image. -/
theorem exists_eigenspace_phi_nontrivial_of_projectionData
    {galAction : (ZMod p)ˣ →* Module.End (ZMod p) V}
    {phi : V →+ ZMod p} {k : ℕ}
    (P : EigenspaceProjectionData galAction phi k)
    (phi_nontrivial : ∃ v : V, phi v ≠ 0) :
    ∃ w ∈ eigenspace (V := V) galAction k, phi w ≠ 0 := by
  obtain ⟨v, hv⟩ := phi_nontrivial
  exact ⟨P.proj v, P.proj_mem_eigenspace v, by rw [P.phi_proj_eq]; exact hv⟩

/-- **Eigenspace nontriviality from non-zero phi.** Wrapper version
extracting just the eigenspace nontriviality (existence of a non-zero
element). -/
theorem eigenspace_nontrivial_of_phi_nontrivial
    {galAction : (ZMod p)ˣ →* Module.End (ZMod p) V}
    {phi : V →+ ZMod p} {k : ℕ}
    (P : EigenspaceProjectionData galAction phi k)
    (phi_nontrivial : ∃ v : V, phi v ≠ 0) :
    ∃ w ∈ eigenspace (V := V) galAction k, w ≠ 0 := by
  obtain ⟨w, hw_mem, hw_phi⟩ :=
    exists_eigenspace_phi_nontrivial_of_projectionData P phi_nontrivial
  refine ⟨w, hw_mem, ?_⟩
  intro h_zero
  apply hw_phi
  rw [h_zero, AddMonoidHom.map_zero]

/-- **Standard cyclotomic eigenspace projection.** The explicit
projection formula `(p-1)⁻¹ ∑_a a^{-k} • galAction a v`. -/
def standardEigenspaceProjection
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ) (v : V) : V :=
  ((Fintype.card (ZMod p)ˣ : ZMod p)⁻¹) •
    ∑ a : (ZMod p)ˣ, ((a : ZMod p) ^ k)⁻¹ • galAction a v

/-- **Standard projection lands in the eigenspace.** The explicit
projection `π_k(v)` satisfies `galAction a (π_k v) = a^k • π_k v` for
every `a ∈ (ZMod p)ˣ`, via the reindexing `b ↦ a * b` on the sum. -/
theorem standardEigenspaceProjection_mem_eigenspace
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ) (v : V) :
    standardEigenspaceProjection galAction k v ∈ eigenspace galAction k := by
  classical
  intro a
  show galAction a (standardEigenspaceProjection galAction k v) =
    ((a : ZMod p) ^ k) • standardEigenspaceProjection galAction k v
  unfold standardEigenspaceProjection
  -- LHS: σ_a((p-1)⁻¹ • ∑_b b^{-k} • σ_b(v))
  rw [LinearMap.map_smul, map_sum]
  -- LHS now: (p-1)⁻¹ • ∑_b σ_a(b^{-k} • σ_b(v))
  --        = (p-1)⁻¹ • ∑_b b^{-k} • σ_a(σ_b(v))
  --        = (p-1)⁻¹ • ∑_b b^{-k} • σ_{a*b}(v)
  conv_lhs =>
    rhs
    rhs
    ext b
    rw [LinearMap.map_smul]
    rw [show galAction a (galAction b v) = galAction (a * b) v from by
        rw [galAction.map_mul]; rfl]
  -- LHS now: (p-1)⁻¹ • ∑_b b^{-k} • σ_{a*b}(v).
  -- Reindex c = a*b via Fintype.sum_equiv with e = Equiv.mulLeft a:
  rw [show ∑ b : (ZMod p)ˣ, ((b : ZMod p) ^ k)⁻¹ • galAction (a * b) v =
      ∑ c : (ZMod p)ˣ,
        ((((a⁻¹ * c : (ZMod p)ˣ)) : ZMod p) ^ k)⁻¹ • galAction c v from by
    exact Fintype.sum_equiv (Equiv.mulLeft a)
      (fun b => ((b : ZMod p) ^ k)⁻¹ • galAction (a * b) v)
      (fun c => ((((a⁻¹ * c : (ZMod p)ˣ)) : ZMod p) ^ k)⁻¹ • galAction c v)
      (fun b => by
        change ((b : ZMod p) ^ k)⁻¹ • galAction (a * b) v =
          ((((a⁻¹ * (a * b) : (ZMod p)ˣ)) : ZMod p) ^ k)⁻¹ • galAction (a * b) v
        congr 2
        rw [show a⁻¹ * (a * b) = b from by group])]
  -- Now LHS = (p-1)⁻¹ • ∑_c (a⁻¹ c)^{-k} • σ_c(v).
  -- (a⁻¹ c)^{-k} = a^k • c^{-k} (in ZMod p), so the sum factors:
  rw [show (∑ c : (ZMod p)ˣ,
              ((((a⁻¹ * c : (ZMod p)ˣ)) : ZMod p) ^ k)⁻¹ • galAction c v) =
        ((a : ZMod p) ^ k) • ∑ c : (ZMod p)ˣ,
              ((c : ZMod p) ^ k)⁻¹ • galAction c v from by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [← smul_assoc]
    congr 1
    show (((a⁻¹ * c : (ZMod p)ˣ) : ZMod p) ^ k)⁻¹ =
      ((a : ZMod p) ^ k) • ((c : ZMod p) ^ k)⁻¹
    rw [Units.val_mul, mul_pow, mul_inv, Units.val_inv_eq_inv_val, inv_pow, inv_inv]
    rfl]
  -- LHS = (p-1)⁻¹ • a^k • ∑_c c^{-k} • σ_c(v)
  -- RHS = a^k • (p-1)⁻¹ • ∑_c c^{-k} • σ_c(v)
  -- These are equal by smul_comm.
  rw [smul_comm]

/-- **Standard projection preserves phi.** Given that `phi` has Galois
weight `k` and that the cardinality `#(ZMod p)ˣ = p - 1` is invertible
in `ZMod p`, the standard projection preserves `phi`'s value.

Concretely: `phi(π_k v) = (p-1)⁻¹ · ∑_a a^{-k} · phi(σ_a v)
                       = (p-1)⁻¹ · ∑_a a^{-k} · a^k · phi v
                       = (p-1)⁻¹ · (p-1) · phi v = phi v`. -/
theorem standardEigenspaceProjection_phi_eq
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (phi : V →ₗ[ZMod p] ZMod p) (k : ℕ)
    (phi_galois : ∀ (a : (ZMod p)ˣ) (v : V),
      phi (galAction a v) = ((a : ZMod p) ^ k) * phi v)
    (h_card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)))
    (v : V) :
    phi (standardEigenspaceProjection galAction k v) = phi v := by
  classical
  unfold standardEigenspaceProjection
  -- phi((p-1)⁻¹ • ∑_a a^{-k} • σ_a v)
  -- = (p-1)⁻¹ * phi(∑_a a^{-k} • σ_a v)
  -- = (p-1)⁻¹ * ∑_a a^{-k} * phi(σ_a v)
  -- = (p-1)⁻¹ * ∑_a a^{-k} * a^k * phi v
  -- = (p-1)⁻¹ * (∑_a 1) * phi v
  -- = (p-1)⁻¹ * (p-1) * phi v = phi v.
  rw [LinearMap.map_smul, map_sum]
  simp_rw [LinearMap.map_smul, phi_galois]
  -- Goal: (p-1)⁻¹ • ∑_a (a^{-k} • (a^k * phi v)) = phi v
  -- Each term: a^{-k} • (a^k * phi v) = (a^{-k} * a^k) * phi v = 1 * phi v = phi v
  -- So the sum = #(ZMod p)ˣ * phi v.
  -- (p-1)⁻¹ • (#(ZMod p)ˣ * phi v) = phi v.
  have h_each : ∀ a : (ZMod p)ˣ,
      ((a : ZMod p) ^ k)⁻¹ • ((a : ZMod p) ^ k * phi v) = phi v := by
    intro a
    have ha_unit : IsUnit ((a : ZMod p) ^ k) := (Units.isUnit a).pow k
    rw [smul_eq_mul, ← mul_assoc, IsUnit.inv_mul_cancel ha_unit, one_mul]
  simp_rw [h_each]
  rw [Finset.sum_const, Finset.card_univ]
  -- Goal: (p-1)⁻¹ • (#(ZMod p)ˣ • phi v) = phi v
  rw [nsmul_eq_mul, smul_eq_mul, ← mul_assoc, IsUnit.inv_mul_cancel h_card_unit, one_mul]

/-- **Concrete `EigenspaceProjectionData` from the standard projection.**
Bundles the two proofs above into a single `EigenspaceProjectionData`
instance, ready for use with `exists_eigenspace_phi_nontrivial_of_projectionData`. -/
def standardEigenspaceProjectionData
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (phi : V →ₗ[ZMod p] ZMod p) (k : ℕ)
    (phi_galois : ∀ (a : (ZMod p)ˣ) (v : V),
      phi (galAction a v) = ((a : ZMod p) ^ k) * phi v)
    (h_card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p))) :
    EigenspaceProjectionData galAction phi.toAddMonoidHom k where
  proj := standardEigenspaceProjection galAction k
  proj_mem_eigenspace := standardEigenspaceProjection_mem_eigenspace galAction k
  phi_proj_eq v :=
    standardEigenspaceProjection_phi_eq galAction phi k phi_galois h_card_unit v

/-! ### Eigenspace decomposition completeness

Standard fact for `(ZMod p)ˣ`-actions on `ZMod p`-modules: for `p`
prime, the cyclic group `(ZMod p)ˣ` has order `p - 1`, which is
invertible in `ZMod p`, so the regular representation decomposes
as a direct sum of one-dimensional characters
`χ_k : (ZMod p)ˣ → (ZMod p)ˣ`, `χ_k(a) = a^k` for `k ∈ ZMod (p-1)`.

The corresponding eigenspace decomposition: `V = ⊕_{k=0}^{p-2} V_k`,
witnessed by the sum of standard projections.

The completeness statement (which we DO NOT prove here but expose as
a structural input) is:

  `∑_{k=0}^{p-2} standardEigenspaceProjection galAction k v = v`

Proving this requires the geometric-sum identity
`∑_{k=0}^{p-2} a^k = if a = 1 then p-1 else 0` in `ZMod p`,
plus the `galAction 1 = id` property of the action. We package the
completeness as a `Prop` predicate that consumers can supply. -/

/-- **Eigenspace decomposition completeness predicate**: every `v ∈ V`
is the sum of its standard projections onto the `(p-1)` eigenspaces. -/
def StandardEigenspaceDecompositionComplete
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) : Prop :=
  ∀ v : V,
    ∑ k ∈ Finset.range (p - 1), standardEigenspaceProjection galAction k v = v

/-- **Geometric sum in `ZMod p` over `Finset.range (p-1)` for `a ∈ (ZMod p)ˣ`**:
the sum `∑_{k=0}^{p-2} a^k` is `p-1` when `a = 1` and `0` otherwise.

This is the standard character-orthogonality identity: each non-trivial
multiplicative character of `(ZMod p)ˣ` integrates to 0, while the
trivial character integrates to `p-1`. -/
theorem geom_sum_zmod_units (a : (ZMod p)ˣ) :
    ∑ k ∈ Finset.range (p - 1), ((a : ZMod p) ^ k) =
      if a = 1 then ((p - 1 : ℕ) : ZMod p) else 0 := by
  classical
  by_cases ha : a = 1
  · subst ha
    rw [if_pos rfl]
    simp [Finset.sum_const, Finset.card_range]
  · rw [if_neg ha]
    have ha' : (a : ZMod p) ≠ 1 := Units.val_eq_one.ne.mpr ha
    -- ∑_{k=0}^{p-2} (a : ZMod p)^k = ((a : ZMod p)^{p-1} - 1) / ((a : ZMod p) - 1)
    rw [geom_sum_eq ha' (p - 1)]
    -- (a : ZMod p)^{p-1} = 1 by Fermat's little theorem
    have ha_pow : ((a : ZMod p)) ^ (p - 1) = 1 := by
      rw [show ((a : ZMod p)) ^ (p - 1) = ((a^(p-1) : (ZMod p)ˣ) : ZMod p) by
            push_cast; rfl]
      rw [show a ^ (p - 1) = 1 by rw [← ZMod.card_units]; exact pow_card_eq_one]
      simp
    rw [ha_pow, sub_self, zero_div]

/-- **Inverse-power form** of the character-orthogonality identity:
`∑_{k=0}^{p-2} (a^{-k}) = if a = 1 then p-1 else 0` in `ZMod p`. -/
theorem geom_sum_zmod_units_inv (a : (ZMod p)ˣ) :
    ∑ k ∈ Finset.range (p - 1), (((a : ZMod p) ^ k)⁻¹) =
      if a = 1 then ((p - 1 : ℕ) : ZMod p) else 0 := by
  classical
  -- (a^k)⁻¹ = (a⁻¹)^k = ((a⁻¹ : (ZMod p)ˣ) : ZMod p)^k
  have h_eq : ∀ k : ℕ, ((a : ZMod p) ^ k)⁻¹ =
      (((a⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ k := by
    intro k
    rw [Units.val_inv_eq_inv_val, inv_pow]
  simp_rw [h_eq]
  rw [geom_sum_zmod_units a⁻¹]
  simp only [inv_eq_one]

/-- **Substantively PROVED**: `StandardEigenspaceDecompositionComplete` for
any `(ZMod p)ˣ`-action on a `ZMod p`-module, given that
`((p - 1 : ℕ) : ZMod p)` is invertible (a standard fact for `p` prime,
since `Fintype.card (ZMod p)ˣ = p - 1`). -/
theorem standardEigenspaceDecompositionComplete_proof
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (h_pminus1_unit : IsUnit ((((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p)))) :
    StandardEigenspaceDecompositionComplete galAction := by
  classical
  intro v
  unfold standardEigenspaceProjection
  -- Goal: ∑_k (#units)⁻¹ • ∑_a (a^k)⁻¹ • galAction a v = v
  -- Step 1: pull `(#units)⁻¹` out of the outer sum.
  rw [← Finset.smul_sum]
  -- Step 2: swap the two sums.
  rw [Finset.sum_comm]
  -- Step 3: for each fixed `a`, pull the smul out:
  --   ∑_k (a^k)⁻¹ • (galAction a v) = (∑_k (a^k)⁻¹) • (galAction a v)
  conv_lhs =>
    rhs
    rhs
    ext a
    rw [show (∑ k ∈ Finset.range (p - 1),
        (((a : ZMod p) ^ k)⁻¹) • galAction a v) =
          (∑ k ∈ Finset.range (p - 1), ((a : ZMod p) ^ k)⁻¹) •
            galAction a v from (Finset.sum_smul ..).symm]
    rw [geom_sum_zmod_units_inv a]
  -- Goal: (#units)⁻¹ • ∑_a (if a = 1 then (p-1) else 0) • galAction a v = v
  -- Step 4: split the sum on `a = 1`.
  conv_lhs =>
    rhs
    rhs
    ext a
    rw [show ((if a = 1 then ((p - 1 : ℕ) : ZMod p) else 0) • galAction a v) =
        (if a = 1 then ((p - 1 : ℕ) : ZMod p) • galAction a v else 0) from
        ite_smul _ _ _ _ |>.trans (by rw [zero_smul])]
  rw [Finset.sum_ite_eq' Finset.univ (1 : (ZMod p)ˣ)
    (fun a => ((((p - 1 : ℕ) : ZMod p))) • galAction a v)]
  simp only [Finset.mem_univ, if_true]
  -- Goal: (#units)⁻¹ • ((p-1) • galAction 1 v) = v
  rw [show galAction (1 : (ZMod p)ˣ) v = v from by
    rw [galAction.map_one]; rfl]
  -- Goal: (#units)⁻¹ • ((p-1) • v) = v
  -- Now `(#units)⁻¹ • ((p-1) • v) = ((#units)⁻¹ * (p-1)) • v`. We have
  -- #units = p - 1, so `(#units)⁻¹ * (p-1) = 1`.
  rw [smul_smul]
  rw [show (((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p))⁻¹ *
      (((p - 1 : ℕ) : ZMod p)) = 1 by
    rw [show ((p - 1 : ℕ) : ZMod p) = ((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p) by
      rw [ZMod.card_units]]
    exact IsUnit.inv_mul_cancel h_pminus1_unit]
  rw [one_smul]

/-! ## Submodule form of `eigenspace`

The `eigenspace` is naturally a `Submodule (ZMod p) V` (not just an
`AddSubgroup`): if `v` is in the k-th eigenspace and `c : ZMod p`, then
for all `a`, `galAction a (c • v) = c • galAction a v = c • a^k • v =
a^k • (c • v)`, so `c • v` is in the eigenspace too.

This Submodule form is needed to state the decomposition as
`⊤ = ⨆ k, eigenspaceSubmodule k` (in `Submodule (ZMod p) V`). -/

/-- **Submodule form of `eigenspace`**: the k-th eigenspace as a
`Submodule (ZMod p) V`. -/
def eigenspaceSubmodule (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ) :
    Submodule (ZMod p) V where
  __ := eigenspace galAction k
  smul_mem' c v hv := by
    intro a
    show galAction a (c • v) = ((a : ZMod p) ^ k) • (c • v)
    rw [map_smul, hv a, smul_comm]

@[simp]
theorem mem_eigenspaceSubmodule (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ)
    (v : V) :
    v ∈ eigenspaceSubmodule galAction k ↔ v ∈ eigenspace galAction k :=
  Iff.rfl

/-! ## Direct sum decomposition `⊤ = ⨆ k, V_k`

From `standardEigenspaceDecompositionComplete_proof`, the (p-1)
eigenspaces span the whole module. Translates the
"sum of projections = id" statement into the `⨆`-form. -/

/-- **SP-1: Eigenspace decomposition of V**. Under
`(((p - 1 : ℕ) : ZMod p))` invertible (true for `p` prime), the (p-1)
eigenspaces sum to the whole module `V`. -/
theorem eigenspaceSubmodule_top_eq_iSup
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (h_pminus1_unit : IsUnit ((((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p)))) :
    (⊤ : Submodule (ZMod p) V) =
      ⨆ i ∈ Finset.range (p - 1), eigenspaceSubmodule galAction i := by
  classical
  refine le_antisymm ?_ le_top
  intro v _
  -- Use the decomposition: v = ∑_k π_k(v).
  have h_decomp :=
    standardEigenspaceDecompositionComplete_proof galAction h_pminus1_unit v
  rw [← h_decomp]
  -- Sum is in the supremum since each summand π_k(v) is in eigenspaceSubmodule k.
  refine Submodule.sum_mem _ ?_
  intro k hk
  -- π_k(v) ∈ eigenspaceSubmodule galAction k ≤ ⨆ i ∈ range (p-1), eigenspaceSubmodule i.
  refine Submodule.mem_iSup_of_mem k ?_
  refine Submodule.mem_iSup_of_mem hk ?_
  exact standardEigenspaceProjection_mem_eigenspace galAction k v

/-! ## σ_{-1}-fixed subspace = sum of even-character eigenspaces

Under `p` odd (so 2 invertible in `ZMod p`), the +1-fixed subspace of
`galAction (-1)` equals the sum of even-character eigenspaces.

The forward direction `V_i ⊆ fixed (i even)` is immediate from
`σ_{-1} v = (-1)^i • v = v` when `i` is even.

The reverse direction `fixed ⊆ ⨆ even V_i` uses the decomposition:
write `v = ∑_k π_k(v)`. Then `σ_{-1} v = ∑_k (-1)^k π_k(v)`. From
`σ_{-1} v = v`, the odd parts must satisfy `2 ∑_{k odd} π_k(v) = 0`,
hence `∑_{k odd} π_k(v) = 0` (since 2 is invertible mod p), giving
`v = ∑_{k even} π_k(v)`. -/

/-- The +1-fixed subspace of `galAction a` for `a ∈ (ZMod p)ˣ`. -/
def fixedByGalAction (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (a : (ZMod p)ˣ) :
    Submodule (ZMod p) V where
  carrier := { v : V | galAction a v = v }
  zero_mem' := by simp
  add_mem' {v w} hv hw := by
    show galAction a (v + w) = v + w
    rw [map_add, hv, hw]
  smul_mem' c v hv := by
    show galAction a (c • v) = c • v
    rw [map_smul, hv]

@[simp]
theorem mem_fixedByGalAction (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (a : (ZMod p)ˣ) (v : V) :
    v ∈ fixedByGalAction galAction a ↔ galAction a v = v :=
  Iff.rfl

/-- Helper: `(-1 : ZMod p) ≠ 1` for `p` an odd prime. -/
private lemma neg_one_ne_one_zmod (hp_odd : p ≠ 2) : ((-1 : ZMod p)) ≠ 1 := by
  haveI : Fact (2 < p) := ⟨by
    have hp_prime : Nat.Prime p := Fact.out
    have hp_ge : 2 ≤ p := hp_prime.two_le
    omega⟩
  exact ZMod.neg_one_ne_one

/-- Helper: `(2 : ZMod p) ≠ 0` for `p` an odd prime. -/
private lemma two_ne_zero_zmod (hp_odd : p ≠ 2) : ((2 : ZMod p)) ≠ 0 := by
  have hp_prime : Nat.Prime p := Fact.out
  intro h2
  haveI : CharP (ZMod p) p := ZMod.charP p
  have hp_dvd : p ∣ 2 := by
    rw [show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) from by norm_cast] at h2
    exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hp_dvd
  exact hp_odd this

/-- Helper: `(2 : ZMod p)` is a unit for `p` an odd prime. -/
private lemma two_isUnit_zmod (hp_odd : p ≠ 2) : IsUnit ((2 : ZMod p)) :=
  isUnit_iff_ne_zero.mpr (two_ne_zero_zmod hp_odd)

/-- **Even-eigenspace inclusion in σ_{-1}-fixed subspace.** Each
even-character eigenspace lies in the +1-fixed subspace under
`galAction (-1)`. Requires `p ≠ 2` so that `-1 ≠ 1` in `ZMod p`. -/
theorem eigenspaceSubmodule_even_le_fixed_neg_one
    (hp_odd : p ≠ 2)
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    {i : ℕ} (h_even : Even i) :
    eigenspaceSubmodule galAction i ≤ fixedByGalAction galAction (-1) := by
  intro v hv
  show galAction (-1) v = v
  have h_pow : (((-1 : (ZMod p)ˣ) : ZMod p) ^ i) = 1 := by
    rw [Units.val_neg, Units.val_one]
    exact (neg_one_pow_eq_one_iff_even (neg_one_ne_one_zmod hp_odd)).mpr h_even
  rw [hv (-1), h_pow, one_smul]

/-- **π_k commutes with galAction**: for any `b ∈ (ZMod p)ˣ`,
`π_k(galAction(b)(v)) = galAction(b)(π_k(v))`.

Follows from commutativity of `(ZMod p)ˣ` and the definition of `π_k`
as a linear combination of `galAction(a)`'s. -/
theorem standardEigenspaceProjection_commute_galAction
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V) (k : ℕ) (b : (ZMod p)ˣ) (v : V) :
    standardEigenspaceProjection galAction k (galAction b v) =
      galAction b (standardEigenspaceProjection galAction k v) := by
  classical
  unfold standardEigenspaceProjection
  rw [LinearMap.map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.map_smul]
  have h_ab : galAction a (galAction b v) = galAction (a * b) v := by
    rw [galAction.map_mul]; rfl
  have h_ba : galAction b (galAction a v) = galAction (b * a) v := by
    rw [galAction.map_mul]; rfl
  rw [h_ab, h_ba, mul_comm]

/-- **Key projection lemma**: for `v` fixed by `galAction (-1)`, each
odd-character projection `π_k(v) = 0`.

Proof: `π_k(v) ∈ V_k`, so `galAction(-1)(π_k(v)) = (-1)^k · π_k(v) = -π_k(v)`
(k odd). But also, by commutativity of `π_k` with `galAction`:
`galAction(-1)(π_k(v)) = π_k(galAction(-1)(v)) = π_k(v)`. So
`π_k(v) = -π_k(v)`, i.e., `2 · π_k(v) = 0`, hence `π_k(v) = 0`. -/
theorem standardEigenspaceProjection_odd_eq_zero_of_fixed_neg_one
    (hp_odd : p ≠ 2)
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    {v : V} (hv : galAction (-1) v = v)
    {k : ℕ} (h_odd : Odd k) :
    standardEigenspaceProjection galAction k v = 0 := by
  -- π_k(v) lies in V_k, so galAction(-1)(π_k(v)) = (-1)^k · π_k(v).
  have h_mem := standardEigenspaceProjection_mem_eigenspace galAction k v
  have h_act_pi : galAction (-1) (standardEigenspaceProjection galAction k v) =
      ((-1 : ZMod p) ^ k) • standardEigenspaceProjection galAction k v := by
    have := h_mem (-1)
    rw [Units.val_neg, Units.val_one] at this
    exact this
  -- For k odd: (-1)^k = -1.
  have h_neg : ((-1 : ZMod p) ^ k) = -1 :=
    (neg_one_pow_eq_neg_one_iff_odd (neg_one_ne_one_zmod hp_odd)).mpr h_odd
  rw [h_neg] at h_act_pi
  -- Also: galAction(-1)(π_k(v)) = π_k(galAction(-1)(v)) = π_k(v) (since v is fixed).
  have h_act_pi_alt : galAction (-1) (standardEigenspaceProjection galAction k v) =
      standardEigenspaceProjection galAction k v := by
    rw [← standardEigenspaceProjection_commute_galAction galAction k (-1) v, hv]
  -- Combine: π_k(v) = -π_k(v).
  have h_combined : ((-1 : ZMod p)) • standardEigenspaceProjection galAction k v =
      standardEigenspaceProjection galAction k v := by
    rw [← h_act_pi, h_act_pi_alt]
  have h_eq : standardEigenspaceProjection galAction k v =
      -standardEigenspaceProjection galAction k v := by
    rw [← neg_one_smul (ZMod p), h_combined]
  -- Hence 2 • π_k(v) = 0 ⟹ π_k(v) = 0 (2 invertible).
  have h2_smul : (2 : ZMod p) • standardEigenspaceProjection galAction k v = 0 := by
    rw [show (2 : ZMod p) • standardEigenspaceProjection galAction k v =
      standardEigenspaceProjection galAction k v +
        standardEigenspaceProjection galAction k v from by
      rw [show (2 : ZMod p) = 1 + 1 from by ring, add_smul, one_smul]]
    -- v + v = v + (-v) = 0 using h_eq.
    nth_rewrite 2 [h_eq]
    exact add_neg_cancel _
  exact (two_isUnit_zmod hp_odd).smul_eq_zero.mp h2_smul

/-- **σ_{-1}-fixed = ⨆_{i even} V_i**: the fixed subspace of `galAction (-1)`
equals the direct sum of even-character eigenspaces. -/
theorem fixed_neg_one_eq_iSup_eigenspaceSubmodule_even
    (hp_odd : p ≠ 2)
    (galAction : (ZMod p)ˣ →* Module.End (ZMod p) V)
    (h_pminus1_unit : IsUnit ((((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p)))) :
    fixedByGalAction galAction (-1) =
      ⨆ i ∈ (Finset.range (p - 1)).filter Even, eigenspaceSubmodule galAction i := by
  classical
  refine le_antisymm ?_ ?_
  · intro v hv
    have h_fixed : galAction (-1) v = v := hv
    have h_decomp :=
      standardEigenspaceDecompositionComplete_proof galAction h_pminus1_unit v
    -- First show the sum-over-even is in the target supremum.
    have h_sum_mem : (∑ k ∈ (Finset.range (p - 1)).filter Even,
        standardEigenspaceProjection galAction k v) ∈
        ⨆ i ∈ (Finset.range (p - 1)).filter Even, eigenspaceSubmodule galAction i := by
      apply Submodule.sum_mem
      intro k hk
      refine Submodule.mem_iSup_of_mem k ?_
      refine Submodule.mem_iSup_of_mem hk ?_
      exact standardEigenspaceProjection_mem_eigenspace galAction k v
    -- Now show v equals that sum. Use nth_rewrite to only touch the outer v.
    have h_v_eq : v = ∑ k ∈ (Finset.range (p - 1)).filter Even,
        standardEigenspaceProjection galAction k v := by
      -- Reverse: get ∑ all π_k v from v.
      conv_lhs => rw [← h_decomp]
      -- Split: ∑ all = ∑ even + ∑ odd.
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p - 1)) Even]
      -- ∑ odd = 0.
      rw [show (∑ k ∈ (Finset.range (p - 1)).filter (fun k => ¬ Even k),
                standardEigenspaceProjection galAction k v) = 0 from by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        exact standardEigenspaceProjection_odd_eq_zero_of_fixed_neg_one
          hp_odd galAction h_fixed (Nat.not_even_iff_odd.mp hk.2)]
      rw [add_zero]
    exact h_v_eq ▸ h_sum_mem
  · refine iSup_le ?_
    intro i
    refine iSup_le ?_
    intro hi
    rw [Finset.mem_filter] at hi
    exact eigenspaceSubmodule_even_le_fixed_neg_one hp_odd galAction hi.2

end BernoulliRegular

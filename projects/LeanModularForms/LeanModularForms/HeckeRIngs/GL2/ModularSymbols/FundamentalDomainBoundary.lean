/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodMap
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleMFinite
import LeanModularForms.Modularforms.PeterssonLevelN

/-!
# The `Γ₁(N)` fundamental-domain boundary as a `Γ`-paired-edge cycle (ES-4 leaf L2)

This file builds the **combinatorial / geometric prerequisite** of the Eichler–Shimura
period↔Petersson Green's identity `periodPairingA_eq_boundary_period`
(`PeriodInjective.lean`, Shimura (8.2.22)).

That identity needs the Petersson *area* integral over a `Γ₁(N)`-fundamental domain to equal a
*boundary* integral over `∂F`, where `∂F` is a cycle of geodesic edges **paired** by `Γ₁(N)`
(side-pairing transformations = the generators of `Γ₁(N)`), so that the boundary sum telescopes
into periods.  This file builds that paired-edge boundary object and proves the **abstract
telescoping lemma** that the Green's-identity assembly consumes.

## The cusp-endpoint model

The natural carrier for the boundary edges is the set of cusps `ℙ¹(ℚ) = Projectivization ℚ (Fin 2
→ ℚ)`: a geodesic edge runs between two cusps `α, β` and its *boundary divisor* is the degree-0
divisor `(β) − (α) = divDiff β α ∈ Div0 ℤ` (`ModuleMFinite.lean`).  This is precisely the level at
which the period functional `rawPairing f` (`PeriodMap.lean`) is defined, so the telescoping lands
exactly on the periods `rawPairing f ((β) − (α) ⊗ P)` that the Green identity must produce.

The key structural fact is that **`rawPairing f` of an edge's boundary divisor is a difference of
endpoint potentials**:
`rawPairing f (divDiff β α ⊗ P) = cuspValue f P β − cuspValue f P α`,
i.e. `Φ(e) = V(end e) − V(start e)` for the potential `V(c) = cuspValue f (P : Sym ℂ) c`.  A cycle
of such edges telescopes to `0`; a `Γ₁(N)`-*paired* edge cycle collapses to a sum of the cocycle
contributions `divDiff (γ • c) c`, which are exactly Shimura's boundary symbols.

## Main definitions

* `OrientedCuspEdge` — an oriented geodesic edge between two cusps (`tail` to `head`), with its
  boundary divisor `edgeDivisor e = divDiff e.head e.tail = (head) − (tail)`.
* `PairedBoundary N` — a finite indexed family of oriented cusp edges together with a
  fixed-point-free involution `pair` and side-pairing transformations `γ : ι → Γ₁(N)` realising the
  `Γ₁(N)`-pairing `edge (pair i) = γ i • (reverse (edge i))`.

## Main results

* `edgePotentialSum_cycle_eq_zero` — **abstract cycle telescoping** (the combinatorial heart): for
  any potential `V : κ → A` into an additive group and any *closed* chain `c : ℕ → κ` (`c n = c 0`),
  the potential-difference sum `∑_{i<n} (V (c (i+1)) − V (c i))` over the cycle is `0`
  (`edgePotential_chain_sum` is the open-chain telescoping `… = V (c n) − V (c 0)`).
* `rawPairing_edgeDivisor_eq_sub` — the period of `f` along an edge is the endpoint-potential
  difference `cuspValue f P (head e) − cuspValue f P (tail e)`;
  `rawPairing_edgeDivisor_eq_edgePotential`
  packages it as the abstract `edgePotential` with `V = cuspValue f P`.
* `PairedBoundary.two_smul_boundaryDivisor_eq_cocycle_sum` — **paired-edge collapse** (divisor
  level): twice the total boundary divisor equals the sum of per-pair cocycle defects
  `∂(edge i) − div0Rep(γ i)(∂ edge i)`, i.e. the boundary symbols.
* `PairedBoundary.two_smul_rawPairing_boundaryDivisor` — the same collapse pushed through
  `rawPairing
  f`, exhibiting `2 • ⟨boundary period⟩` as a finite `ℂ`-linear combination of periods of `f`
  (`∑ coeffᵢ · rawPairing f (yᵢ)`) — the shape `periodPairingA_eq_boundary_period` consumes.
* `exists_pairedBoundary_periodPairingA_eq` — **the concrete-FD identification (deliverable 3,
  isolated)**: existence of a `Γ₁(N)`-paired boundary realising Shimura's `A(f,g)` as such a
  boundary
  period.  The lone residual `sorry` (the research-scale Stokes / model-change step).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2, (8.2.22).
* Diamond–Shurman, *A First Course in Modular Forms*, §5.4 (Manin symbols / side pairings).
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Pointwise TensorProduct
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
  Matrix.SpecialLinearGroup

/-- Notation for the projective line `ℙ¹(ℚ)`, the cusps. -/
local notation "ℙ¹ℚ" => Projectivization ℚ (Fin 2 → ℚ)

/-! ## Abstract telescoping core

The purely combinatorial fact underlying *every* paired-edge boundary sum: along an oriented cycle,
the sum of potential differences `V(end) − V(start)` vanishes.  This is stated for an arbitrary
endpoint type `κ`, an arbitrary additive group `A`, and an arbitrary potential `V`, so it can be
reused both at the divisor level (`A = Div0 ℤ`) and at the period level (`A = ℂ`).  It is the
"combinatorial heart" the Green's-identity assembly applies with `V = cuspValue f P`. -/

variable {κ : Type*} {A : Type*} [AddCommGroup A]

/-- The potential difference assigned to a directed edge `(s, t)` (from `s` to `t`) by a potential
`V`: `Φ_V (s, t) = V t − V s`.  An edge whose endpoint divisor is `(t) − (s)` contributes this to
the boundary period (`A = ℂ`, `V = cuspValue f P`). -/
def edgePotential (V : κ → A) (s t : κ) : A := V t - V s

@[simp] theorem edgePotential_self (V : κ → A) (s : κ) : edgePotential V s s = 0 := by
  simp [edgePotential]

/-- Antisymmetry under reversing an edge: `Φ_V (t, s) = − Φ_V (s, t)`. -/
theorem edgePotential_swap (V : κ → A) (s t : κ) :
    edgePotential V t s = - edgePotential V s t := by
  simp [edgePotential]

/-- Telescoping over a chain `c : ℕ → κ`: the sum of the consecutive potential differences
`Φ_V (c i, c (i+1))` over `i = 0, …, n−1` collapses to `V (c n) − V (c 0)`.  This is the abstract
form of "the interior edges of an FD tiling cancel and only the endpoint contributions survive". -/
theorem edgePotential_chain_sum (V : κ → A) (c : ℕ → κ) (n : ℕ) :
    ∑ i ∈ Finset.range n, edgePotential V (c i) (c (i + 1)) = V (c n) - V (c 0) := by
  simpa only [edgePotential] using Finset.sum_range_sub (fun i => V (c i)) n

/-- **Abstract cycle telescoping** (the combinatorial heart of paired-edge boundary sums).  For a
*closed* chain — one that returns to its start, `c n = c 0` — the potential-difference sum over the
whole cycle vanishes.  A `Γ₁(N)`-paired-edge boundary is exactly such a cycle (the edges, read in
boundary order, close up), so any potential-difference functional `Φ_V` sums to `0` over it; the
periods then re-emerge through the `Γ₁(N)`-side-pairing identification of opposite edges. -/
theorem edgePotentialSum_cycle_eq_zero (V : κ → A) (c : ℕ → κ) (n : ℕ) (hclosed : c n = c 0) :
    ∑ i ∈ Finset.range n, edgePotential V (c i) (c (i + 1)) = 0 := by
  rw [edgePotential_chain_sum, hclosed, sub_self]

/-! ## Oriented geodesic edges between cusps

An edge of the boundary is an oriented geodesic in `ℍ` running from one cusp to another.  We model
it by its ordered pair of endpoint cusps `(tail, head) ∈ ℙ¹(ℚ)²`; the geodesic is recovered as the
hyperbolic geodesic joining them (a vertical line or a semicircle).  The *boundary divisor* of the
edge is the degree-0 divisor `(head) − (tail) = divDiff head tail`, the data the period functional
`rawPairing` consumes. -/

variable {N : ℕ} [NeZero N]

/-- An oriented geodesic edge of the fundamental-domain boundary: the geodesic in `ℍ` from cusp
`tail` to cusp `head`. -/
structure OrientedCuspEdge where
  /-- The starting cusp of the (oriented) edge. -/
  tail : ℙ¹ℚ
  /-- The terminal cusp of the (oriented) edge. -/
  head : ℙ¹ℚ

namespace OrientedCuspEdge

/-- The boundary divisor `(head) − (tail) ∈ Div0 ℤ` of an oriented cusp edge.  This is the
degree-0 divisor that the period functional `rawPairing f` pairs against. -/
noncomputable def edgeDivisor (e : OrientedCuspEdge) : Div0 ℤ := divDiff e.head e.tail

/-- The reversed edge (swap orientation): tail and head exchanged. -/
def reverse (e : OrientedCuspEdge) : OrientedCuspEdge := ⟨e.head, e.tail⟩

@[simp] theorem reverse_tail (e : OrientedCuspEdge) : e.reverse.tail = e.head := rfl
@[simp] theorem reverse_head (e : OrientedCuspEdge) : e.reverse.head = e.tail := rfl
@[simp] theorem reverse_reverse (e : OrientedCuspEdge) : e.reverse.reverse = e := rfl

/-- Reversing an edge negates its boundary divisor: `∂(reverse e) = −∂e`. -/
@[simp] theorem edgeDivisor_reverse (e : OrientedCuspEdge) :
    e.reverse.edgeDivisor = - e.edgeDivisor := by
  simp only [edgeDivisor, reverse_head, reverse_tail]
  exact divDiff_swap e.tail e.head

/-- The `Γ₁(N)`-translate `γ • e` of an oriented cusp edge: the geodesic from `γ • tail` to
`γ • head`.  Side-pairing transformations act this way on edges. -/
def smul (γ : Gamma1 N) (e : OrientedCuspEdge) : OrientedCuspEdge :=
  ⟨γ • e.tail, γ • e.head⟩

@[simp] theorem smul_tail (γ : Gamma1 N) (e : OrientedCuspEdge) :
    (smul γ e).tail = γ • e.tail := rfl

@[simp] theorem smul_head (γ : Gamma1 N) (e : OrientedCuspEdge) :
    (smul γ e).head = γ • e.head := rfl

/-- The boundary divisor is `Γ₁(N)`-equivariant: `∂(γ • e) = div0Rep γ (∂e)`.  This is the cocycle
identity (`div0Rep_divDiff_gamma1`) that powers the side-pairing telescoping. -/
theorem edgeDivisor_smul (γ : Gamma1 N) (e : OrientedCuspEdge) :
    (smul γ e).edgeDivisor = div0Rep ℤ γ.1 e.edgeDivisor := by
  rw [edgeDivisor, edgeDivisor, smul_head, smul_tail, div0Rep_divDiff_gamma1]

end OrientedCuspEdge

/-! ## The period of `f` along an edge

The bridge between the geometric edge and the period functional: `rawPairing f` of an edge's
boundary divisor (tensored with a coefficient `P`) is the **endpoint-potential difference**
`cuspValue f P (head e) − cuspValue f P (tail e)`.  This is exactly the `Φ_V` of the abstract
telescoping core, with the potential `V = cuspValue f P`.  Hence any cycle of edges telescopes,
and a paired boundary collapses to the cocycle (boundary-symbol) periods. -/

variable {k : ℤ}

/-- **The period of `f` along an oriented cusp edge is a difference of endpoint potentials.** For a
cusp form `f`, coefficient `P ∈ Sym^m(ℤ)`, and edge `e`,
`rawPairing f (∂e ⊗ P) = cuspValue f (P : Sym ℂ) (head e) − cuspValue f (P : Sym ℂ) (tail e)`.
With the potential `V(c) = cuspValue f (P : Sym ℂ) c` this is precisely `Φ_V (tail e, head e)`. -/
theorem rawPairing_edgeDivisor_eq_sub (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℤ m) (e : OrientedCuspEdge) :
    rawPairing f (e.edgeDivisor ⊗ₜ P) =
      cuspValue f (castSymPow m P) e.head - cuspValue f (castSymPow m P) e.tail := by
  rw [OrientedCuspEdge.edgeDivisor, rawPairing_tmul, divDiff_val, map_sub, LinearMap.sub_apply,
    rawBilin_single, rawBilin_single]
  push_cast; ring

/-- The period of `f` along an edge, expressed via the abstract `edgePotential` of the cusp
potential `cuspValue f P`. -/
theorem rawPairing_edgeDivisor_eq_edgePotential (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℤ m) (e : OrientedCuspEdge) :
    rawPairing f (e.edgeDivisor ⊗ₜ P) =
      edgePotential (fun c => cuspValue f (castSymPow m P) c) e.tail e.head := by
  rw [rawPairing_edgeDivisor_eq_sub]; rfl

/-! ## The `Γ₁(N)`-paired boundary

A `Γ₁(N)`-paired boundary bundles a finite indexed family of oriented cusp edges together with a
**side pairing**: a fixed-point-free involution `pair` on the index set and side-pairing
transformations `γ : ι → Γ₁(N)` with `edge (pair i) = γ i • reverse (edge i)`.  This is the
combinatorial datum produced by a fundamental-domain tiling: the interior shared edges of adjacent
`SL₂(ℤ)`-translates cancel, and the surviving outer edges come in `Γ₁(N)`-paired pairs (Diamond–
Shurman §5.4, Manin symbols / side pairings; Shimura §8.2). -/

/-- A `Γ₁(N)`-**paired boundary**: a finite family of oriented cusp edges with an explicit
side-pairing.  The involution `pair` matches each edge with its partner, `γ` are the side-pairing
group elements, and `pairing` realises the pairing geometrically (the partner edge is the
`γ`-translate of the reversed edge). -/
structure PairedBoundary (N : ℕ) [NeZero N] where
  /-- The index set of edges (finite, hence may be taken in `Type 0`). -/
  ι : Type
  /-- The edge index set is finite. -/
  [fintypeι : Fintype ι]
  /-- decidable equality on the index set (for `Finset.sum_involution`). -/
  [decEqι : DecidableEq ι]
  /-- The oriented cusp edge at each index. -/
  edge : ι → OrientedCuspEdge
  /-- The side-pairing involution on edge indices. -/
  pair : Equiv.Perm ι
  /-- `pair` is an involution. -/
  pair_involutive : Function.Involutive pair
  /-- `pair` is fixed-point-free: no edge is paired with itself. -/
  pair_ne : ∀ i, pair i ≠ i
  /-- The side-pairing transformation attached to each edge. -/
  γ : ι → Gamma1 N
  /-- **The side-pairing relation**: the partner edge `edge (pair i)` is the `γ i`-translate of the
  reversed edge `reverse (edge i)`. -/
  pairing : ∀ i, edge (pair i) = (edge i).reverse.smul (γ i)

attribute [instance] PairedBoundary.fintypeι PairedBoundary.decEqι

namespace PairedBoundary

variable (B : PairedBoundary N)

/-- The total boundary divisor `∑_i ∂(edge i) ∈ Div0 ℤ` of a paired boundary — the integral
1-cycle the period functional is evaluated on. -/
noncomputable def boundaryDivisor : Div0 ℤ := ∑ i, (B.edge i).edgeDivisor

/-- **The pairwise side-pairing identity** (the local heart of the collapse).  The two divisor
contributions of a paired pair `{i, pair i}` combine into a single *cocycle defect*
`∂(edge i) − div0Rep(γ i)(∂(edge i))`:
`∂(edge i) + ∂(edge (pair i)) = ∂(edge i) − div0Rep ℤ (γ i)(∂(edge i))`.
This is what makes the side-paired boundary telescope: the partner edge cancels the untwisted part
and leaves only the `(1 − γ)`-cocycle term, which is a boundary symbol in the sense of Shimura. -/
theorem edgeDivisor_add_pair (i : B.ι) :
    (B.edge i).edgeDivisor + (B.edge (B.pair i)).edgeDivisor =
      (B.edge i).edgeDivisor - div0Rep ℤ (B.γ i).1 (B.edge i).edgeDivisor := by
  rw [B.pairing i, OrientedCuspEdge.edgeDivisor_smul, OrientedCuspEdge.edgeDivisor_reverse, map_neg]
  abel

/-- Reindexing the boundary-divisor sum by the pairing involution leaves it unchanged:
`∑_i ∂(edge (pair i)) = ∑_i ∂(edge i)`. -/
theorem boundaryDivisor_reindex_pair :
    ∑ i, (B.edge (B.pair i)).edgeDivisor = B.boundaryDivisor :=
  Equiv.sum_comp B.pair (fun i => (B.edge i).edgeDivisor)

/-- **The paired-edge collapse** (deliverable 2, divisor level).  Twice the total boundary divisor
equals the sum of the per-pair *cocycle defects* `∂(edge i) − div0Rep(γ i)(∂(edge i))`:
`2 • boundaryDivisor = ∑_i (∂(edge i) − div0Rep ℤ (γ i)(∂(edge i)))`.

The factor `2` is the order of the side-pairing involution (each unordered pair is summed from both
its members).  Each summand is a `(1 − γ_i)`-cocycle applied to an edge divisor — precisely
Shimura's boundary symbols.  Pairing the whole identity with `rawPairing f` (see
`rawPairing_boundaryDivisor_two_smul`) thus exhibits `2 • ⟨period over ∂F⟩` as a finite `ℂ`-linear
combination of the periods `rawPairing f (yᵢ)` with `yᵢ ∈ Div⁰ ⊗ Sym`, which is exactly the shape
the Green's-identity assembly `periodPairingA_eq_boundary_period` consumes. -/
theorem two_smul_boundaryDivisor_eq_cocycle_sum :
    (2 : ℤ) • B.boundaryDivisor =
      ∑ i, ((B.edge i).edgeDivisor - div0Rep ℤ (B.γ i).1 (B.edge i).edgeDivisor) := by
  have hsum : ∑ i, ((B.edge i).edgeDivisor + (B.edge (B.pair i)).edgeDivisor) =
      (2 : ℤ) • B.boundaryDivisor := by
    rw [Finset.sum_add_distrib, B.boundaryDivisor_reindex_pair, boundaryDivisor, two_smul]
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => B.edgeDivisor_add_pair i

/-! ### The boundary period as a finite sum of periods (Green's-identity shape) -/

variable {k : ℤ}

/-- **The paired-edge collapse, pushed through the period functional** (deliverable 2, period level
— the form `periodPairingA_eq_boundary_period` consumes).  For a cusp form `f` and coefficient
`P ∈ Sym^m(ℤ)`, twice the boundary period `rawPairing f (boundaryDivisor ⊗ P)` is a finite sum of
period values, one *edge period* and one *boundary-symbol (cocycle) period* per edge:
`2 • rawPairing f (∂F ⊗ P) =
    ∑_i (rawPairing f (∂(edge i) ⊗ P) − rawPairing f (div0Rep(γ i)(∂(edge i)) ⊗ P))`.

Every term on the right is a value `rawPairing f y` at an integral modular symbol
`y ∈ Div⁰ ⊗ Sym` with coefficient `±1`, so the right-hand side is exactly a finite `ℂ`-linear
combination `∑ coeffᵢ · rawPairing f (yᵢ)` of *periods of `f`* — precisely the conclusion shape of
the Green's-identity assembly.  This is the lemma the Green's identity applies, with `f`'s periods
read off from the boundary symbols. -/
theorem two_smul_rawPairing_boundaryDivisor (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℤ m) :
    (2 : ℤ) • rawPairing f (B.boundaryDivisor ⊗ₜ P) =
      ∑ i, (rawPairing f ((B.edge i).edgeDivisor ⊗ₜ P) -
        rawPairing f (div0Rep ℤ (B.γ i).1 (B.edge i).edgeDivisor ⊗ₜ P)) := by
  rw [← map_zsmul (rawPairing f),
    show (2 : ℤ) • (B.boundaryDivisor ⊗ₜ[ℤ] P) = ((2 : ℤ) • B.boundaryDivisor) ⊗ₜ P from
      TensorProduct.smul_tmul' 2 B.boundaryDivisor P,
    B.two_smul_boundaryDivisor_eq_cocycle_sum, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.sub_tmul, map_sub]

/-- The **edge-period summands are differences of endpoint potentials** (the telescoping witness).
The "edge period" half of each summand of `two_smul_rawPairing_boundaryDivisor` is the
endpoint-potential difference `cuspValue f P (head) − cuspValue f P (tail)`; the "cocycle period"
half is the boundary symbol over the `γ`-translated endpoints.  Summed with the abstract
`edgePotential` telescoping (`edgePotentialSum_cycle_eq_zero`), this is what makes the period
emerge along the boundary cycle. -/
theorem rawPairing_cocycle_summand (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℤ m) (i : B.ι) :
    rawPairing f ((B.edge i).edgeDivisor ⊗ₜ P) -
        rawPairing f (div0Rep ℤ (B.γ i).1 (B.edge i).edgeDivisor ⊗ₜ P) =
      (cuspValue f (castSymPow m P) (B.edge i).head -
          cuspValue f (castSymPow m P) (B.edge i).tail) -
        (cuspValue f (castSymPow m P) (B.γ i • (B.edge i).head) -
          cuspValue f (castSymPow m P) (B.γ i • (B.edge i).tail)) := by
  rw [rawPairing_edgeDivisor_eq_sub, ← OrientedCuspEdge.edgeDivisor_smul,
    rawPairing_edgeDivisor_eq_sub, OrientedCuspEdge.smul_head, OrientedCuspEdge.smul_tail]

end PairedBoundary

/-! ## Connection to the concrete `Γ₁(N)` fundamental domain (deliverable 3)

The `Γ₁(N)` fundamental domain used analytically in the project, `Gamma1_fundDomain_PSL N`
(`PeterssonLevelN.lean`), is the coset tiling `⋃_q (q.out)⁻¹ • fdo` by translates of the standard
`SL₂(ℤ)` open domain `fdo`.  Its cusps are the `SL₂(ℤ)`-translates of the unique `SL₂(ℤ)`-cusp `∞`;
the paired-edge boundary structure built above is the *combinatorial / Manin* model of the same
domain's boundary, with side pairings given by generators of `Γ₁(N)`.

The two facts below split deliverable 3 into a **fully-proven coherence layer** (the cusp endpoints
of any such boundary live in the single `SL₂(ℤ)`-orbit, so they are genuine FD-tile cusps) and the
**isolated analytic interface** (the Stokes/Green identification of the FD *area* integral with the
paired-edge *boundary* period). -/

/-- Any two cusps are related by `SL(2, ℤ)` (transitivity of the `SL₂(ℤ)`-cusp action,
`isPretransitive_SL2Z_projQQ`): the `SL₂(ℤ)`-cusp action has a single orbit.  In particular the two
endpoints of every `OrientedCuspEdge` are `SL₂(ℤ)`-translates of one another, hence are genuine
cusps of the `Gamma1_fundDomain_PSL` tiling, whose tiles are `SL₂(ℤ)`-translates of the standard
domain.  This is the coherence check that the cusp-edge boundary model and the coset-tiling model
share endpoints. -/
theorem exists_SL2Z_smul_eq_cusp (c₁ c₂ : ℙ¹ℚ) : ∃ g : SL(2, ℤ), g • c₁ = c₂ :=
  haveI := isPretransitive_SL2Z_projQQ
  MulAction.IsPretransitive.exists_smul_eq c₁ c₂

/-- The endpoints of any oriented cusp edge are `SL(2, ℤ)`-related — a direct specialisation of
`exists_SL2Z_smul_eq_cusp` to `tail` and `head`. -/
theorem OrientedCuspEdge.exists_SL2Z_smul_tail_eq_head (e : OrientedCuspEdge) :
    ∃ g : SL(2, ℤ), g • e.tail = e.head :=
  exists_SL2Z_smul_eq_cusp e.tail e.head

/-! ### The Green / Stokes boundary-period interface

The concrete fundamental-domain identification `exists_pairedBoundary_periodPairingA_eq` —
exhibiting
Shimura's period pairing `A(f, g) = (f, g) + (-1)ⁿ (g, f)` as `c · rawPairing f (B.boundaryDivisor ⊗
P)` for a `Γ₁(N)`-paired boundary `B` — is the *analytic* deliverable (deliverable 3).  It is stated
and proven in `PeterssonStokes.lean`, since its proof feeds on the per-tile region-Stokes lemma
`tile_stokes_fd` (region-Stokes over the standard `fd`-tile), which sits *above* this file in the
import graph.  This file supplies the *combinatorial* half it consumes (`PairedBoundary`,
`boundaryDivisor`, `two_smul_rawPairing_boundaryDivisor`). -/

end HeckeRing.GL2.ModularSymbols

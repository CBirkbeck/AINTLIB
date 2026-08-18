# Mathlibable assessment — `Chebotarev.ncard_index_image_frontier_le`

**Verdict: YES-but-generalise-first**

> One-line rationale: genuinely new effective boundary-cell bound, but it is hard-wired to
> the project-local `index`/chart API and a contrived constant; reshape against mathlib's
> `BoxIntegral.unitPartition` and the literature constant before landing.

---

## 0. The declaration

File: `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:203`
Qualified name (verified — `namespace Chebotarev` opens at line 51, declaration at line 203):
**`Chebotarev.ncard_index_image_frontier_le`**.

```lean
/-- **Boundary-cell count.** If `∂s` is covered by `m` images `φⱼ '' [0,1]ᵈ⁻¹` of
`M`-Lipschitz maps, the number of grid cells meeting `∂s` is `O(nᵈ⁻¹)`, with constant
`m · (2⌈M⌉₊+1)ᵈ · 2ᵈ⁻¹`. -/
theorem ncard_index_image_frontier_le {s : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0}
    {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)}
    (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (index n '' frontier s).ncard
      ≤ (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1))
          * n ^ (Fintype.card ι - 1)
```

`ι` is a `Fintype`; `index n : (ι → ℝ) → (ι → ℤ)` is `BoxIntegral.unitPartition.index` from
mathlib, identifying the cell of the `n⁻¹ℤ^ι` grid containing a point. The statement says: the
number of grid cells meeting the frontier `∂s` is `≤ C · n^(d-1)` with explicit
`C = m·(2⌈M⌉₊+1)^d·2^(d-1)` and `d = Fintype.card ι`.

**Proof shape (5 mathlib glue steps + 1 project lemma per chart):**
`index n '' ∂s ⊆ ⋃ⱼ index n '' (φⱼ '' [0,1])` (`Set.image_iUnion`, `Set.image_mono hcov`) →
`Set.ncard_le_ncard` → `Set.ncard_iUnion_le_of_fintype` → `Finset.sum_le_sum` with the
per-chart bound **`ncard_index_image_chart_le` (project)** → `(n+1)^(d-1) ≤ 2^(d-1)·n^(d-1)`
(`Nat.pow_le_pow_left`) → `gcongr`/`ring`.

It is the second-from-top node of a clean linear chain:
`ncard_index_image_le_of_diam_le` → `ncard_index_image_chart_le` →
**`ncard_index_image_frontier_le`** → (sibling) `abs_card_inter_sub_volume_mul_pow_le` →
terminal export `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`. All four helpers are
project-local (`grep` confirms no mathlib provenance).

---

## 1. Literature search

This is the **boundary-cell count** at the heart of the classical Lipschitz-class lattice-point
counting principle (Davenport → Lang → Masser–Vaaler → Widmer). The relevant standard forms:

| Source | Statement (standard generality) | Relation to our lemma |
|---|---|---|
| **Widmer**, *Lipschitz class, narrow class, and counting lattice points*, Proc. AMS **140** (2012) 677–689, Thm. 5.4 | For a lattice `Γ ⊂ ℝⁿ` with successive minima `λ₁…λₙ` and bounded `S` with `∂S ∈ Lip(n,M,L)`: `‖ |S∩Γ| − Vol(S)/det Γ ‖ ≤ M·(2√n·Ω+4)ⁿ·maxᵢ₌₀…ₙ₋₁ Lⁱ/(λ₁⋯λᵢ)` (`Ω` = orthogonality defect). | The **full error**; our `frontier_le` is its dominant **boundary-cell** ingredient, specialised to `Γ=ℤ^d` and `Ω=1`. |
| **Lang**, *Algebraic Number Theory*, 2nd ed., GTM 110, Ch. VI §3 Thm. 3, p.129 (cited in the file header) | `#(tS ∩ ℤⁿ) = Vol(S)·tⁿ + O(tⁿ⁻¹)`, error governed by the number of unit cells met by `∂(tS)`. | Our lemma is exactly the `O(tⁿ⁻¹)` cell-count step, with explicit (non-optimised) constant. |
| **Davenport**, *On a principle of Lippmann–Davenport / Note on the lattice points in a set*, Rend. Circ. Mat. Palermo (1951) | `‖ |Z∩ℤⁿ|−Vol(Z) ‖ ≤ Σⱼ₌₀ⁿ⁻¹ hⁿ⁻ʲ Vⱼ(Z)` (line-section hypothesis, not Lipschitz). | Same principle, "fibres in `≤h` intervals" hypothesis instead of Lipschitz cover. |
| **Gun–Ramaré–Sivaraman**, *Counting ideals in ray classes*, J. Number Theory **243** (2023) §3.3, §3.5 (after Debaene) (cited in the file header) | Same Lipschitz-class count, applied to ray-class ideal counting. | The application this file ultimately serves. |
| **mathlib** `BoxIntegral.unitPartition` | `tendsto_card_div_pow_atTop_volume` — the **asymptotic** `#/nᵈ → vol`, **no rate**. | Strictly weaker: no `O(nᵈ⁻¹)`, no cell-count lemma. |

**Literature-standard form** = Widmer Thm 5.4: a *single* inequality bounding
`‖ |S∩Γ| − Vol(S)/det Γ ‖` for a general lattice, with constant `M·(2√n Ω+4)ⁿ·maxᵢ Lⁱ/(λ₁⋯λᵢ)`.
The cell-count is an internal lemma there; isolating it as a named result is reasonable and
useful, but the natural mathlib home for the *whole* package is the full effective error bound,
not a lemma phrased through one particular `index`-image.

Sources:
- https://www.math.tugraz.at/~widmer/Publications/Narrow_Lipschitz.pdf (Widmer, Proc. AMS 2012)
- https://www.ams.org/proc/2012-140-02/S0002-9939-2011-10926-2/ (AMS published version)
- https://arxiv.org/pdf/1611.10103 (Thorner–Zaman, explicit ideal counting — same machinery)
- https://www.math.uzh.ch/gorodnik/papers/GN2-final.pdf (Gorodnik–Nevo survey, context)

---

## 2. Mathlib search (five methods)

- **Doc / module read** of `Mathlib/Analysis/BoxIntegral/UnitPartition.html` (authoritative,
  current): the *only* `index`/`card`/`Finite` declarations are
  `index`, `index_apply`, `mem_box_iff_index`, `index_tag`, `setFinite_index`,
  `admissibleIndex`, `mem_admissibleIndex_iff`, `tendsto_card_div_pow_atTop_volume`(`'`).
  **No** `ncard`-of-`index`-image bound; **no** `frontier` lemma; **no** quantitative rate.
- **Concept search** (WebSearch "mathlib4 … effective lattice point count Lipschitz frontier"):
  surfaces only `UnitPartition` (asymptotic) — confirms the effective version is absent.
- **`grep` over the repo**: `index`, `box`, `ncard_index_image_chart_le`,
  `ncard_index_image_le_of_diam_le`, `setFinite_index_image_of_isBounded` are all **project-local**
  to `ForMathlib/LatticePointCount.lean` (+ reused once in `ForMathlib/IdealCongruenceCount.lean`).
- **Loogle / LeanSearch**: tool backends not resolvable in this environment (noted in task);
  the mathlib-docs module read above is the authoritative substitute and is conclusive for this
  narrow file.
- **Imports inspection**: the file imports `Mathlib.Analysis.BoxIntegral.UnitPartition` and only
  reuses `setFinite_index` from it — nothing resembling the conclusion exists upstream.

**Conclusion:** mathlib has the *asymptotic* statement and the `index` primitive, but **no
effective boundary-cell count and no `O(nᵈ⁻¹)` error term**. The result is genuinely not in
mathlib (rules out `NO-mathlib-has-it`).

---

## 3. Generality analysis (vs the literature-standard form)

Measured against Widmer Thm 5.4, the project lemma is **specialised in several axes** that a
mathlib version should widen:

1. **Lattice.** Fixed to `ℤ^ι` via `index n` (the `n⁻¹ℤ^ι` grid). Widmer/Lang are for an
   arbitrary lattice `Γ` (covolume `det Γ`, successive minima `λᵢ`). Mathlib already has
   `ZLattice`/`Covolume`; the natural general statement is lattice-agnostic.
2. **Phrasing through `index`.** The conclusion counts `(index n '' frontier s).ncard`. That is
   the *cell-count surrogate*, not an intrinsic invariant — it is meaningful only inside the
   `unitPartition` development. A mathlib result is more naturally phrased as the **error term**
   `‖ Nat.card (s ∩ grid) − vol s · nᵈ ‖ ≤ …` (its own sibling
   `abs_card_inter_sub_volume_mul_pow_le` already does this — these two should likely be merged /
   re-presented as one effective theorem with the cell-count as a `private` step).
3. **Constant.** `m·(2⌈M⌉₊+1)ᵈ·2ᵈ⁻¹` with the `⌈·⌉₊` ceilings and the `2ᵈ⁻¹` slack is a
   proof-convenient, **non-canonical** constant (the `(n+1)ᵈ⁻¹ ≤ 2ᵈ⁻¹nᵈ⁻¹` step throws away a
   factor). The literature constant is `M·(2√d·Ω+4)ᵈ·maxᵢ Lⁱ/(λ₁⋯λᵢ)`. mathlib reviewers will
   want either the literature constant or at least one not carrying gratuitous slack and ceilings.
4. **`M : ℝ≥0` + `LipschitzWith`.** This axis is fine and idiomatic.
5. **Cover by `Fin m` charts of `[0,1]ᵈ⁻¹`.** Idiomatic encoding of `Lip(d,M,L)`; fine, though a
   `Set.Finite`/`Finset`-indexed cover would be marginally more general than `Fin m`.

So the *mathematical content is correct and wanted*, but the *interface* (keyed to `index`, a
bespoke constant, `ℤ^ι`-only) is below mathlib's generality bar. This is the textbook
`YES-but-generalise-first` situation: land it, but first reshape the statement.

---

## 4. Composition check (≤ 3 mathlib calls?)

**No.** There is no mathlib primitive whose ≤3-fold composition yields this. The proof needs:
- the per-chart bound `ncard_index_image_chart_le` (itself ~56 lines, resting on
  `ncard_index_image_le_of_diam_le`, ~29 lines, both **new** — a Lipschitz map sends a
  `1/n`-diameter cube into `≤(2⌈M⌉₊+1)ᵈ` cells), then
- `Set.ncard_iUnion_le_of_fintype` + `Finset.sum_le_sum` + a power inequality.

The genuinely novel mathematics lives one level down (`ncard_index_image_le_of_diam_le`:
bounded-diameter image meets boundedly many unit cells). `frontier_le` itself is the assembly
step, but it cannot exist without those new lemmas — so the *cluster* is not mathlib-composable.
Rules out `NO-composable-from-mathlib`.

---

## 5. Verdict

| Bucket | Fit |
|---|---|
| YES-add-as-is | No — interface keyed to project `index` API + non-canonical constant + `ℤ^ι`-only. |
| **YES-but-generalise-first** | **Yes** — content is new, wanted, and squarely the classical effective Lipschitz-boundary count; ship after reshaping. |
| NO-mathlib-has-it | No — mathlib has only the asymptotic `tendsto_card_div_pow_atTop_volume`. |
| NO-composable-from-mathlib | No — depends on genuinely new ≤-level lemmas. |
| BORDERLINE-needs-human | Close second (see below), but the generalise path is clear enough to call. |

**Chosen: `YES-but-generalise-first`.**

Rationale: the effective `O(nᵈ⁻¹)` boundary-cell bound is a real, citable, currently-absent
addition to mathlib's `BoxIntegral.unitPartition` story (it is the missing rate behind
`tendsto_card_div_pow_atTop_volume`). But as written it is hard-wired to project-local plumbing
(`index`-image `ncard`, the `ncard_index_image_chart_le` chain), specialised to the standard
lattice `ℤ^ι`, and carries a deliberately loose constant. The mathlib contribution should:
(a) present the **effective error bound** as the headline (folding in the sibling
`abs_card_inter_sub_volume_mul_pow_le`), with the cell-count as a supporting (possibly `private`)
lemma; (b) state it for a general `ZLattice`/`Covolume` where feasible, or at least cleanly
beside the existing `index` API; (c) use a clean/literature constant rather than the
`2ᵈ⁻¹·(2⌈M⌉₊+1)ᵈ` slack form.

**Borderline note (why not BORDERLINE):** the *whole `LatticePointCount` cluster* (six decls)
should be assessed and PR'd together — `frontier_le` in isolation has little standalone value.
A human curator owns the packaging/constant/lattice-generality decisions. But the disposition of
*this* declaration is not in doubt: it is wanted, it is new, and it needs generalisation first —
hence `YES-but-generalise-first` rather than deferring the call to a human.

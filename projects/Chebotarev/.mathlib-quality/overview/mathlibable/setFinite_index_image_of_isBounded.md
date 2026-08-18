# Mathlibable assessment — `Chebotarev.setFinite_index_image_of_isBounded`

**Verdict: YES-add-as-is**

> One-line rationale: the missing dual of mathlib's own `setFinite_index` — cells *met by* a
> bounded set are finite — phrased through the native `index` primitive with the weakest natural
> hypothesis (`IsBounded`) and a clean conclusion; drop straight into `BoxIntegral.unitPartition`.

---

## 0. The declaration

File: `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:80`
Qualified name (verified — `namespace Chebotarev` opens at line 51, `theorem` at line 80):
**`Chebotarev.setFinite_index_image_of_isBounded`**.

```lean
set_option linter.unusedFintypeInType false in
/-- The `index n`-image of a bounded set is finite: only finitely many cells of the `n⁻¹ℤ^ι`
grid meet a bounded set. -/
theorem setFinite_index_image_of_isBounded (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ι → ℝ)
  set F : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ : ι ↦ Finset.Icc (⌈-((n : ℝ) * R)⌉ - 1) (⌈(n : ℝ) * R⌉ - 1) with hF
  refine Set.Finite.subset (Finset.finite_toSet F) ?_
  rintro _ ⟨x, hx, rfl⟩
  …  -- per-coordinate: |x i| ≤ R ⟹ index n x i ∈ Icc (⌈-(n·R)⌉-1) (⌈n·R⌉-1)
```

with `variable {ι : Type*} [Fintype ι]` (lines 57) in scope.

Here `index n : (ι → ℝ) → (ι → ℤ)` is mathlib's `BoxIntegral.unitPartition.index`,
`index n x i = ⌈n·x i⌉ - 1`, the map sending a point to the index `ν` of the unit-partition cell
`box n ν` containing it (`mem_box_iff_index : x ∈ box n ν ↔ index n x = ν`). The statement: for
`T` bounded, only finitely many cells of the `n⁻¹ℤ^ι` grid are *hit* by `T`.

**Proof shape (one bounding-`Finset` + per-coordinate ceiling bound):**
`IsBounded.subset_closedBall` gives `T ⊆ closedBall 0 R`; the image lands in the explicit product
`Fintype.piFinset (fun _ ↦ Finset.Icc (⌈-(nR)⌉-1) (⌈nR⌉-1))` because `|x i| ≤ R`
(`dist_le_pi_dist` + `Real.dist_eq`) forces `index n x i = ⌈n·x i⌉-1 ∈ [⌈-nR⌉-1, ⌈nR⌉-1]`
(`Int.ceil_le_ceil`, monotone in `x i`); then `Set.Finite.subset (Finset.finite_toSet F)`.
No deep input — `dist_le_pi_dist`, `Int.ceil_le_ceil`, `Fintype.piFinset`,
`Finset.finite_toSet`, `index_apply`.

Position in the file's chain: this is a **leaf utility**, used by the unit-grid ideal-congruence
count (`ForMathlib/IdealCongruenceCount.lean`) and as a `Set.Finite` witness so the `.ncard`
bounds (`ncard_index_image_le_of_diam_le`, `ncard_index_image_frontier_le`) refer to a finite set.
It does **not** depend on the bespoke chart/constant machinery that burdens its `ncard` siblings.

---

## 1. Literature search

This is the **foundational finiteness step** of every lattice-point-counting argument: a bounded
region meets only finitely many cells of a fixed grid (equivalently, contains finitely many points
of a fixed lattice). It is the standing hypothesis that makes "`#(cells met by ∂S)`" and
"`#(S ∩ Γ)`" *well-defined finite numbers* before any rate is proved.

| Source | Statement (standard generality) | Relation to our lemma |
|---|---|---|
| **Lang**, *Algebraic Number Theory*, GTM 110, Ch. VI §3 (file header ref) | Counts of `tS ∩ ℤⁿ` and of unit cells met by `∂(tS)` are finite for bounded `S` — the unstated prerequisite of Thm 3. | Our lemma is exactly this finiteness, for the cell-index version. |
| **Widmer**, Proc. AMS **140** (2012) Thm 5.4 (sibling-report ref) | The error bound presupposes `\|S ∩ Γ\|` finite for bounded `S` with `Lip` boundary. | Same finiteness prerequisite, lattice-point version. |
| **General discrete geometry** (e.g. *Maximal lattice-free convex sets*, arXiv:1701.06543, Cor. 12) | "Every bounded set in ℝⁿ contains finitely many points of a lattice." | The lattice-point sibling of our cell-count finiteness; both are the same elementary fact. |
| **mathlib** `ZSpan.setFinite_inter` | For `Basis ι ℝ E`, proper `E`, finite `ι`, bounded `s`: `(s ∩ Submodule.span ℤ (range b)).Finite`. | mathlib **has** the *lattice-point* version; it does **not** have the *cell-index* (`index`-image) version. Different finite set (points of `s` on the lattice vs. cells hit by `s`). |
| **mathlib** `BoxIntegral.unitPartition.setFinite_index` | For null-measurable `s`, `volume s ≠ ⊤`: `{ν \| box n ν ⊆ s}.Finite` — cells *contained in* `s`. | The **dual** of our lemma (⊆ vs. ∩) and under a **stronger** hypothesis (measurable + finite volume vs. merely bounded). Not interchangeable. |

**Literature-standard form** = "a bounded set meets only finitely many cells of a fixed grid /
contains finitely many points of a fixed lattice." Our statement is precisely this, in the
cell-index encoding (`index '' T`), with the canonical weakest hypothesis `Bornology.IsBounded`.
There is no more-general *true* statement to aim for: drop boundedness and it is false; the lattice
is `ℤ^ι` because `index`/`box` are *defined* on the `ℤ^ι` grid in mathlib.

Sources:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoxIntegral/UnitPartition.html (mathlib `unitPartition` module — `index`, `setFinite_index`)
- https://leanprover-community.github.io/mathlib_docs/algebra/module/zlattice.html and the mathlib4 `Algebra.Module.ZLattice.Basic` docs (`ZSpan.setFinite_inter` — the lattice-point analogue)
- https://arxiv.org/pdf/1701.06543 (Maximal lattice-free convex sets — "bounded ⟹ finitely many lattice points", Cor. 12)
- https://www.math.tugraz.at/~widmer/Publications/Narrow_Lipschitz.pdf (Widmer, Proc. AMS 2012 — the counting principle this underlies)

---

## 2. Mathlib search (five methods)

- **Doc / module read** of `Mathlib/Analysis/BoxIntegral/UnitPartition.html` (authoritative,
  current). Exact statements retrieved:
  - `index n x i = ⌈↑n * x i⌉ - 1` (`def index`, `index_apply`) — **identical** to the project's
    usage (lines 88, 96–97), confirming `index` is the mathlib primitive, not a project redefine.
  - `setFinite_index {s} (hs₁ : NullMeasurableSet s volume) (hs₂ : volume s ≠ ⊤) :`
    `{ν : ι → ℤ | ↑(box n ν) ⊆ s}.Finite` — **cells contained in `s`**, hypotheses
    null-measurable + finite volume.
  - `mem_box_iff_index : x ∈ box n ν ↔ index n x = ν`; `admissibleIndex n B : Finset (ι → ℤ)` =
    `{ν | box n ν ≤ B}`; `tendsto_card_div_pow_atTop_volume` (asymptotic only).
  **No** lemma stating `(index n '' T).Finite`, and **no** index-finiteness lemma whose hypothesis
  is mere boundedness (the only finiteness lemma, `setFinite_index`, is the ⊆-dual under stronger
  hypotheses). Explicitly confirmed: "There is no explicit lemma stating `(index n '' T).Finite`
  for bounded `T`."
- **`ZLattice` search**: `ZSpan.setFinite_inter` (bounded ∩ `span ℤ (range b)` finite) is the
  *lattice-point* analogue — present in mathlib, but a different object (points vs. cells); see §4.
- **Concept search** (WebSearch, mathlib4 + discrete-geometry): surfaces only the lattice-point
  finiteness (`ZSpan.setFinite_inter`) and the asymptotic `unitPartition` story; the cell-index
  finiteness is absent.
- **`grep` over the repo**: `setFinite_index_image_of_isBounded` is **project-local** to
  `ForMathlib/LatticePointCount.lean`, reused in `ForMathlib/IdealCongruenceCount.lean`; no mathlib
  provenance. `index`, `box`, `setFinite_index` resolve to mathlib.
- **Loogle / LeanSearch**: backends not resolvable in this environment (noted in task); the
  mathlib-docs module read is the authoritative substitute and is conclusive for this narrow file.

**Conclusion:** mathlib has (a) the *contained-in* index finiteness `setFinite_index` (stronger
hypotheses, dual direction) and (b) the *lattice-point* finiteness `ZSpan.setFinite_inter`
(different object). It does **not** have the *cells-met-by-a-bounded-set* finiteness
`(index n '' T).Finite`. Rules out `NO-mathlib-has-it`.

---

## 3. Generality analysis (vs the literature-standard form)

This is the case where the project statement **already sits at the literature-standard generality**:

1. **Hypothesis.** `Bornology.IsBounded T` is the *weakest possible* hypothesis — the conclusion is
   false without it, and it is strictly weaker than `setFinite_index`'s `NullMeasurableSet ∧ finite
   volume`. So this lemma is *more general in hypothesis* than mathlib's existing finiteness lemma,
   and morally the correct hypothesis for an `index`-image statement (no measurability needed).
2. **Object.** `(index n '' T).Finite` is the intrinsic, idiomatic object — `index` is a mathlib
   primitive, `Set.Finite` is the canonical conclusion. No project-local surrogate, no constant,
   no chart API. (Contrast the sibling `ncard_index_image_frontier_le`, whose mathlibability is
   dragged down by a bespoke `2ᵈ⁻¹(2⌈M⌉₊+1)ᵈ` constant and the `Fin m` chart cover — none of which
   appears here.)
3. **Lattice = `ℤ^ι`.** *Not a defect.* `index`/`box`/`setFinite_index` are defined in mathlib
   exclusively on the `n⁻¹ℤ^ι` grid; a statement about `index` is *necessarily* about `ℤ^ι`. The
   general-`ZLattice` analogue is a *different* lemma (`ZSpan.setFinite_inter`, already in mathlib).
   So "specialise to a general lattice" does not apply — it would change the object, not generalise
   this one.
4. **`(n : ℕ)` with no `NeZero n`.** The lemma even holds for `n = 0` (then `index 0 x i = -1`
   constantly, image is a single point — finite), so it does *not* impose the `[NeZero n]` that
   `setFinite_index`/`admissibleIndex` carry. This is a (mild) extra generality, correctly taken.

The only blemish is cosmetic: `set_option linter.unusedFintypeInType false in`, a documented
false-positive suppression (the `Fintype ι` instance is genuinely used for the sup-metric on
`ι → ℝ`). That is a linter-interaction note for the PR, **not** a generality or interface defect.

So the statement is at the right generality with the right hypotheses and the right (mathlib-native)
vocabulary. There is nothing to widen before landing — this is `YES-add-as-is`, not
`YES-but-generalise-first`.

---

## 4. Composition check (≤ 3 mathlib calls?)

**No** — neither from the two nearby finiteness lemmas nor mechanically.

- **From `setFinite_index`?** No. It bounds `{ν | box n ν ⊆ s}` (cells *contained in* `s`), whereas
  `index n '' T ⊆ {ν | box n ν` *meets* `T}` (via `mem_box_iff_index`). Wrong direction (⊆ vs. ∩);
  and `setFinite_index` additionally demands `NullMeasurableSet`/finite volume, which we do not
  have. Not reusable in ≤3 steps.
- **From `admissibleIndex`?** One *could* pick a bounding `Box ι` `B ⊇` (`T` thickened by one cell)
  and argue `index n '' T ⊆ admissibleIndex n B`, then `Finset.finite_toSet`. But constructing a
  `Box ι` (which carries `lower i < upper i` positivity side-conditions), proving every cell *met*
  by `T` lies *inside* `B` (the one-cell enlargement), and discharging `[NeZero n]` is **more**
  work than the direct proof, not fewer than 3 mathlib calls. Not a clean composition.
- **From `ZSpan.setFinite_inter`?** No. It gives `(s ∩ span ℤ (range b)).Finite` — finiteness of
  *lattice points in `s`*, a different finite set. To reach `(index n '' T).Finite` one would
  bijection-transport via `tag n` (upper-vertex map into `n⁻¹ℤ^ι`), enlarge `T` to contain those
  tags, then apply the lemma — several non-trivial steps, no single named result. Not ≤3 calls.
- **Mechanically?** The direct proof itself is the minimal route and is already ~5 genuine steps
  (`subset_closedBall` → per-coordinate `dist_le_pi_dist` → `Int.ceil_le_ceil` monotonicity →
  `Fintype.piFinset` membership → `Finite.subset (finite_toSet …)`). There is no mathlib lemma
  "image of a bounded set under a `ℤ^ι`-cell map is finite" to call; `index` is not continuous and
  carries no boundedness/proper-map API. The fact is *elementary* but *not pre-packaged*.

So the lemma is short but not a ≤3-call corollary of existing mathlib. Rules out
`NO-composable-from-mathlib`. (It is short enough that a reviewer might inline it; but as the
named companion to `setFinite_index` it earns its place — see §5.)

---

## 5. Verdict

| Bucket | Fit |
|---|---|
| **YES-add-as-is** | **Yes** — native `index`/`Set.Finite` vocabulary, weakest hypothesis (`IsBounded`), clean conclusion; the missing companion to `setFinite_index`. |
| YES-but-generalise-first | No — already at literature-standard generality; nothing to widen (the general-lattice version is a *different*, already-present lemma `ZSpan.setFinite_inter`). |
| NO-mathlib-has-it | No — mathlib has the ⊆-dual `setFinite_index` (stronger hypotheses) and the lattice-point `ZSpan.setFinite_inter` (different object), not this `index`-image finiteness. |
| NO-composable-from-mathlib | No — not a ≤3-call corollary of either neighbour; `index` has no boundedness/proper API. |
| BORDERLINE-needs-human | No — disposition is unambiguous; no constant/packaging/lattice-generality judgement call (unlike the `ncard` siblings). |

**Chosen: `YES-add-as-is`.**

Rationale: `(index n '' T).Finite` for bounded `T` is exactly the finiteness companion that
mathlib's `BoxIntegral.unitPartition` is missing — `setFinite_index` covers cells *contained in* a
*measurable, finite-volume* set; this covers cells *met by* any *bounded* set, the hypothesis that
actually makes the unit-partition `.ncard` counts (and the asymptotic
`tendsto_card_div_pow_atTop_volume`) well-posed. It is phrased entirely in mathlib's own primitives
(`index`, `Set.Finite`, `Bornology.IsBounded`), takes the weakest reasonable hypothesis (even
allowing `n = 0`, no `[NeZero n]`), and has a short, robust proof. None of the generality concerns
that pushed its `ncard` siblings to `YES-but-generalise-first` apply here: there is no constant, no
chart interface, and the `ℤ^ι` lattice is intrinsic to `index` rather than an artificial
restriction.

The single actionable PR note is cosmetic: the `set_option linter.unusedFintypeInType false in`
guard (a documented false positive — `Fintype ι` is used for the sup-metric). On contribution this
should be raised with the linter maintainers, but it does not affect the statement and does not
downgrade the verdict.

**Packaging note:** like the rest of the `LatticePointCount` cluster, the natural home is alongside
`setFinite_index` inside `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`, ideally PR'd together
with the cluster so the effective-count story lands coherently — but, unlike the `ncard` siblings,
*this* leaf is add-as-is on its own.

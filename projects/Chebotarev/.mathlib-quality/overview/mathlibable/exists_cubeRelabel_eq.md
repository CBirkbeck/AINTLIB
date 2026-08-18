# Mathlibable assessment — `Chebotarev.exists_cubeRelabel_eq`

**Verdict: NO — composable from mathlib in ≤ 2 calls (surjectivity of `Equiv.piCongrLeft'`, restricted to the unit cube). Companion of `cubeRelabel`, which mathlib already has as `Equiv.piCongrLeft'`.**

- **Declaration:** `Chebotarev.exists_cubeRelabel_eq`
- **Location:** `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:274`
- **Namespace:** `Chebotarev` (opened L79); variable `K : Type*` `[Field K] [NumberField K]` (L124). Qualified name **confirmed** `Chebotarev.exists_cubeRelabel_eq`.
- **Earmark:** `ForMathlib/` helper, author-flagged for mathlib.
- **Date:** 2026-06-18

---

## 1. The declaration (verified from source)

```lean
theorem exists_cubeRelabel_eq {c' : {w : InfinitePlace K // w ≠ w₀} → ℝ}
    (hc' : c' ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1) :
    ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1, cubeRelabel K c = c' :=
  ⟨fun j ↦ c' (equivFinRank j), ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,
    funext fun j ↦ by simp [cubeRelabel]⟩
```

**What it says.** `cubeRelabel K` (the reindexing `c ↦ c ∘ equivFinRank.symm`, L260) restricted to
the unit cube is **surjective onto the unit cube**: every `c'` in `Icc 0 1` on the index `{w ≠ w₀}` is
`cubeRelabel K c` for some `c` in `Icc 0 1` on the index `Fin (#InfinitePlace K − 1)`. The witness is
`c = c' ∘ equivFinRank`.

**Ingredients, all from mathlib** (`open NumberField`, so unqualified):
- `NumberField.Units.equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}`
  (`…/Units/Regulator.lean:56`), with `rank K := Fintype.card (InfinitePlace K) − 1`
  (`…/Units/DirichletTheorem.lean:354`). So `Fin (Fintype.card (InfinitePlace K) − 1) = Fin (rank K)`.
- `Set.Icc`, `Pi.le_def` (pointwise order on `Pi`).
- `Chebotarev.cubeRelabel` — the only project-local symbol, itself = `⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)`
  (see the companion report `cubeRelabel.md`).

**Downstream use.** `exists_cubeRelabel_eq` is consumed only inside this file, in
`frontier_subset_frontierCoverFamily` (L322, L329): given a face image point `cubeRelabel K c' …`, it
re-expresses it as `cubeRelabel K c …` with `c` in the cube, so the clamp `clampUnit` can be undone
(`clampUnit_eq_self`). No project-specific structure rides on its concrete form — purely a "undo the
relabelling" surjectivity step.

---

## 2. Literature standard

This is the surjectivity half of "**reindexing a tuple by a bijection is a bijection**", refined to
preserve the unit cube `[0,1]^I`.

| Source / framing | Standard object | Standard generality |
|---|---|---|
| Set theory / discrete math | a bijection (here a reindexing `σ : J ≃ I` acting on `∏_i Y_i`) is **surjective**: every target value has a preimage | any bijection of index sets; any (dependent) fibers; the isomorphism *is* the content |
| Order theory | a coordinate permutation of `∏_i Y_i` is an **order isomorphism**, so it maps any product box `∏ Icc aᵢ bᵢ` onto the correspondingly-permuted box | pointwise order on `Pi`; surjectivity onto the image box is immediate |

There is **no named theorem** for this; it is the textbook fact "an equivalence is onto, and a
coordinate permutation respects pointwise order/boxes." Web search (mathlib4 `Equiv.piCongrLeft'`;
"reindexing tuple by bijection surjective preimage") returns only the generic
bijection/surjection/preimage material and the mathlib `piCongrLeft'` family — confirming there is no
specialized result to import. `exists_cubeRelabel_eq` is the special case `I = Fin (rank K)`,
`J = {w ≠ w₀}`, `σ = equivFinRank`, fibers `ℝ`, box `[0,1]`. Strictly *less* general than the standard form.

---

## 3. Mathlib search (five methods)

The reindexing map itself is in mathlib by name; its surjectivity-onto-the-cube is a 1–2 line corollary.

- **`Equiv.piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b)`**
  — `Mathlib/Logic/Equiv/Basic.lean:805`, `toFun f x := f (e.symm x)`, `@[simps apply]`. With
  `P := fun _ ↦ ℝ`, `e := equivFinRank`, **`⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank) = cubeRelabel K`
  definitionally** (verified against the local pin; the def body matches `fun j ↦ c (equivFinRank.symm j)`).
- **Surjectivity of any `Equiv`:** `Equiv.surjective : Surjective ⇑e` (`Mathlib/Logic/Equiv/Defs.lean:182`),
  and the explicit witness `Equiv.apply_symm_apply : e (e.symm x) = x` (`…/Defs.lean:250`). The proof's
  `funext fun j ↦ by simp [cubeRelabel]` is exactly `piCongrLeft'`'s `apply_symm_apply`/`piCongrLeft'_symm_apply_apply`
  (`…/Equiv/Basic.lean:826`).
- **Cube/box preservation:** pointwise order `Pi.le_def`; `c' ∘ equivFinRank ∈ Icc 0 1 ↔ c' ∈ Icc 0 1`
  because the equiv permutes coordinates. (Same one-line content as the companion lemma
  `cubeRelabel_mem_Icc`, L269.)
- **Metric/linear strengthenings** (not needed here, but present): `IsometryEquiv.piCongrLeft'`
  (`…/MetricSpace/Isometry.lean:602`), `LinearEquiv.piCongrLeft'`, `LinearIsometryEquiv.piLpCongrLeft`
  (`…/Analysis/Normed/Lp/PiLp.lean`).

Methods that hit: name search (`piCongrLeft'`, `Equiv.surjective`), local-source read
(Equiv/Basic, Equiv/Defs), "isometry/permutation of pi reindexing" grep, doc/web confirmation
(mathlib4 docs for `Equiv.piCongrLeft'`, `Mathlib.Logic.Equiv.Defs`). All converge: the map is in
mathlib; surjectivity is a one-liner.

---

## 4. Generality analysis

`exists_cubeRelabel_eq` hard-codes `equivFinRank`, fiber `ℝ`, the two specific index types, and the
specific box `[0,1]`. The literature-standard statement — and the mathlib machinery realizing it — is
parametric in the bijection `e`, the (dependent) fibers, the index types, and (for the box version)
the box endpoints. The lemma carries **no extra hypotheses or content** beyond "an `Equiv` is onto and
permutes coordinates." It is a **proper specialization**: there is nothing to *generalize and add* —
the general fact (`Equiv.surjective` of `Equiv.piCongrLeft'`, plus pointwise `Pi`-order) is already in
mathlib. (A genuinely general lemma "a `piCongrLeft'`-style coordinate permutation maps `Set.pi univ I`
onto `Set.pi univ I'`" would be the upstreamable artifact — but that, too, is a 1–2 line corollary, not
a missing primitive.)

---

## 5. Composition check (≤ 3 mathlib calls)

**Yes — the source proof already *is* the composition**, and it is short:

```lean
⟨fun j ↦ c' (equivFinRank j),                       -- witness = c' ∘ equivFinRank
 ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,                -- in Icc 0 1: pointwise Pi-order  (≈ Pi.le_def)
 funext fun j ↦ by simp [cubeRelabel]⟩              -- cubeRelabel K (c' ∘ equivFinRank) = c'  (Equiv.apply_symm_apply)
```

Two genuine mathlib facts: pointwise `Icc`-membership of a permuted tuple, and
`Equiv.apply_symm_apply` (i.e. `piCongrLeft'_symm_apply_apply`). With `cubeRelabel` itself replaced by
`Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank`, the whole lemma is:
`fun hc' ↦ ⟨_, ⟨…pointwise…⟩, by simp⟩` — **≤ 2 substantive calls**, comfortably within budget. No new
API needed.

---

## 6. Verdict

**NO — composable from mathlib** (bucket `NO-composable-from-mathlib`). `exists_cubeRelabel_eq` is the
restricted-to-the-unit-cube **surjectivity** of `cubeRelabel K`, which is just
`Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank` — so it is `Equiv.surjective` / `Equiv.apply_symm_apply`
plus a pointwise `Pi`-order box-membership, a 2-line corollary the author has in fact already written
inline. It adds nothing to mathlib and is strictly less general than the existing `Equiv.piCongrLeft'`
family. It belongs in the same disposition as its companion `cubeRelabel` (see `cubeRelabel.md`, also
NO): do **not** upstream. If the file ever drops the `cubeRelabel` wrapper for `Equiv.piCongrLeft'`,
this lemma dissolves into the equiv's surjectivity plus one pointwise-`Icc` line.

### Sources
- mathlib source (local pin): `Mathlib/Logic/Equiv/Basic.lean:805` (`piCongrLeft'`, def body + `piCongrLeft'_symm_apply_apply` L826),
  `Mathlib/Logic/Equiv/Defs.lean:182` (`Equiv.surjective`), `:250` (`Equiv.apply_symm_apply`),
  `Mathlib/Topology/MetricSpace/Isometry.lean:602` (`IsometryEquiv.piCongrLeft'`),
  `Mathlib/NumberTheory/NumberField/Units/{Regulator.lean:56, DirichletTheorem.lean:354}` (`equivFinRank`, `rank`).
- Companion assessment: `projects/Chebotarev/.mathlib-quality/overview/mathlibable/cubeRelabel.md` (verdict NO — mathlib has it).
- mathlib4 docs — `Mathlib.Logic.Equiv.Defs`: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html
- mathlib4 docs — `Mathlib.LinearAlgebra.Pi` (`LinearEquiv.piCongrLeft'`): https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Pi.html
- Bijection/surjection/preimage (standard fact, no named theorem): https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection ; https://proofwiki.org/wiki/Image_of_Preimage_of_Subset_under_Surjection_equals_Subset

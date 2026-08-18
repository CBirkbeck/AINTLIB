# Mathlibable assessment — `Chebotarev.cubeRelabel`

**Verdict: NO — mathlib already has it (`Equiv.piCongrLeft'`, packaged metrically as `IsometryEquiv.piCongrLeft'`).**

- **Declaration:** `Chebotarev.cubeRelabel`
- **Location:** `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:260`
- **Earmark:** `ForMathlib/` helper, author-flagged for mathlib.
- **Date:** 2026-06-18

---

## 1. The declaration (verified from source)

```lean
/-- Relabel cube coordinates `Fin (#InfinitePlace K - 1) → ℝ` by the non-distinguished places
`{w ≠ w₀}` via `equivFinRank`. -/
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j ↦ c (equivFinRank.symm j)
```

Ingredients, both from **mathlib** (`open NumberField`, so unqualified):

- `NumberField.Units.w₀ : InfinitePlace K` (`…/Units/DirichletTheorem.lean:73`) — a fixed distinguished place.
- `NumberField.Units.equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}`
  (`…/Units/Regulator.lean:56`), where `rank K := Fintype.card (InfinitePlace K) - 1`
  (`…/Units/DirichletTheorem.lean:354`). Hence the domain index `Fin (Fintype.card (InfinitePlace K) - 1)`
  *is* `Fin (rank K)`.

So `cubeRelabel K c = c ∘ ⇑equivFinRank.symm`: **precomposition of a function on a (finite) index
type with a fixed bijection on that index** — the generic "reindex a tuple by an equivalence."

### Accompanying lemmas (same file), all generic reindexing facts

| Lemma | Line | What it says | Generic reason |
|---|---|---|---|
| `lipschitzWith_cubeRelabel` | 265 | `LipschitzWith 1 (cubeRelabel K)` | Reindexing a tuple is an isometry for the sup (`L∞`) metric. |
| `cubeRelabel_mem_Icc` | 269 | maps `Icc 0 1 → Icc 0 1` | `Pi`-order is pointwise; reindexing permutes coordinates. |
| `exists_cubeRelabel_eq` | 274 | every `c'` is hit (preimage `c' ∘ equivFinRank`) | The map is a bijection (it is an `Equiv`). |

None of the three is used in any definitional way downstream; `cubeRelabel` appears only inside this
file, composed with `clampUnit` and the face maps in `frontierCoverFamily` (lines 288–289), with only
these three properties consumed (lines 304–305, 322, 325, 329, 337, 538). No project-specific
structure rides on its concrete form.

---

## 2. Literature standard

| Source / framing | Standard object | Standard generality |
|---|---|---|
| Linear algebra / set theory | "reindexing of a tuple by a bijection of the index set", `(x_i)_{i∈I} ↦ (x_{σ(j)})_{j∈J}` | any bijection `σ : J ≃ I`, any (possibly dependent) fibers; an isomorphism of the product |
| Metric geometry | a coordinate permutation of `∏_i Y_i` with the sup / `ℓ^∞` norm | an **isometry** (`L^p` for every `p`, in fact) |
| Functional analysis | `ℓ^p`-reindexing operator | a surjective **linear isometry** |

The literature object is the bijective reindexing of an indexed family; the regularity facts
(isometry for sup-metric, order-preservation, surjectivity) are immediate corollaries of it being
an isomorphism. `cubeRelabel` is the special case `I = Fin (rank K)`, `J = {w ≠ w₀}`, `σ =
equivFinRank.symm`, fibers `ℝ`. It is strictly *less* general than the standard form.

---

## 3. Mathlib search (five methods)

**It is already there, by name, at every structure level the literature recognizes:**

- **`Equiv.piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b)`**
  — `Mathlib/Logic/Equiv/Basic.lean:803`. `toFun f x := f (e.symm x)`. With `P := fun _ ↦ ℝ`,
  `e := equivFinRank`:
  `⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank) c = fun j ↦ c (equivFinRank.symm j) = cubeRelabel K c`.
  **Exact match of the definition** (`@[simps apply]` gives the defeq `piCongrLeft'_apply`).

- **`IsometryEquiv.piCongrLeft' (e : ι ≃ ι') : (∀ i, Y i) ≃ᵢ ∀ j, Y (e.symm j)`**
  — `Mathlib/Topology/MetricSpace/Isometry.lean:576`, for `[Fintype ι] [Fintype ι']`,
  `[∀ j, PseudoEMetricSpace (Y j)]`, `toEquiv := Equiv.piCongrLeft' _ e`. This is precisely
  "`cubeRelabel` is an isometry" (proof: `edist_pi_def` + `Equiv.iSup_comp`), which **strictly
  implies** `lipschitzWith_cubeRelabel` (`.isometry.lipschitz`) *and* the same for the inverse.

- **`LinearEquiv.piCongrLeft'`** and **`LinearIsometryEquiv.piLpCongrLeft`**
  (`Mathlib/Analysis/Normed/Lp/PiLp.lean:779`, defeq to `Equiv.piCongrLeft'` on the underlying map)
  — the linear / `L^p`-isometric strengthenings, should they ever be wanted.

Search methods that hit: name search (`piCongrLeft'`), file read (Equiv/Basic, Isometry, PiLp),
"isometry of pi reindexing" grep, doc/web confirmation (mathlib4 docs for
`Equiv.piCongrLeft'`, `IsometryEquiv.piCongrLeft`, `LinearEquiv.piCongrLeft'`). All five converge on
the same family.

Supporting facts for the three lemmas, all in mathlib:
- isometry ⟹ Lipschitz 1: `Isometry.lipschitz` (sup-metric `Pi` is `edist_pi_def`, `…/EMetricSpace/Pi.lean:38`);
- order preservation: `Pi.le_def` + `Equiv.forall_congr` / `e.symm.surjective` (pointwise);
- surjectivity: `Equiv.surjective` / `Equiv.apply_symm_apply` of `piCongrLeft'`.

---

## 4. Generality analysis

`cubeRelabel` hard-codes `equivFinRank`, the fiber `ℝ`, and the two specific index types. The
literature-standard object — and the mathlib declaration realizing it — is parametric in:
the bijection `e`, the (dependent) fibers `Y`, and the index types (any two fintypes). `cubeRelabel`
is therefore a **proper specialization**, carrying no extra hypotheses or content that the general
`Equiv.piCongrLeft'` / `IsometryEquiv.piCongrLeft'` lacks. There is nothing to *generalize and add*:
the maximally-general form is already in mathlib.

---

## 5. Composition check (≤ 3 mathlib calls)

Not merely composable — **identical to a single mathlib declaration**:

- definition: `cubeRelabel K = ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)` (1 call, defeq via `@[simps apply]`).
- `lipschitzWith_cubeRelabel`: `(IsometryEquiv.piCongrLeft' equivFinRank).isometry.lipschitz` (1–2 calls).
- `cubeRelabel_mem_Icc`: `⟨fun _ ↦ h.1 _, fun _ ↦ h.2 _⟩` reindexed — `Pi`-order, 1 call.
- `exists_cubeRelabel_eq`: surjectivity of the equiv — `⟨_, _, (piCongrLeft' …).apply_symm_apply…⟩`, 1 call.

The whole `cubeRelabel` block (def + 3 lemmas, ~20 lines) collapses to direct use of
`Equiv.piCongrLeft'` / `IsometryEquiv.piCongrLeft'` plus a one-line `Icc` membership and a one-line
surjectivity witness. Well within the budget.

---

## 6. Verdict

**NO — mathlib has it.** `cubeRelabel` is a project-local renaming of `Equiv.piCongrLeft'
(fun _ ↦ ℝ) equivFinRank`; its sole nontrivial property (1-Lipschitz) is the already-formalized
`IsometryEquiv.piCongrLeft'` (an *isometry*, strictly stronger), and the `Icc`/surjectivity lemmas
are one-liners from the equiv. It is a perfectly reasonable local convenience wrapper, but it adds
nothing to mathlib and is strictly less general than what mathlib already provides at the `Equiv`,
`Isometry`, `Linear`, and `LinearIsometry` levels. Do **not** upstream; if desired, the file could
drop the wrapper and call `Equiv.piCongrLeft'` / `IsometryEquiv.piCongrLeft'` directly.

(For consumers wanting the Lipschitz packaging without the wrapper:
`(IsometryEquiv.piCongrLeft' (Y := fun _ : {w // w ≠ w₀} ↦ ℝ) equivFinRank).symm` — note the
direction — or work from `IsometryEquiv.piCongrLeft'` and `Isometry.lipschitz`.)

### Sources
- mathlib4 docs — `Mathlib.Logic.Equiv.Basic` (`Equiv.piCongrLeft'`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Basic.html
- mathlib4 docs — `Mathlib.Topology.MetricSpace.Isometry` (`IsometryEquiv.piCongrLeft'`/`piCongrLeft`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Isometry.html
- mathlib source (local pin): `Mathlib/Logic/Equiv/Basic.lean:803`,
  `Mathlib/Topology/MetricSpace/Isometry.lean:576`, `Mathlib/Analysis/Normed/Lp/PiLp.lean:779`,
  `Mathlib/Topology/EMetricSpace/Pi.lean:38`,
  `Mathlib/NumberTheory/NumberField/Units/{Regulator.lean:56, DirichletTheorem.lean:354,73}`.

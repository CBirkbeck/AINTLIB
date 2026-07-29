# FarguesFontaine — deduplication pass

Acting on `/overview` findings. Method: two systematic scans over all 46 files
(1463 declaration bodies), plus a targeted mathlib-duplication check.

## Scan 1 — exact-duplicate proof bodies

Normalised each body (comments + whitespace stripped, own name elided) and hashed.

**Result: exactly 3 exact-duplicate groups in the whole folder** — all now fixed.
There is no other byte-equal duplication in FarguesFontaine.

## Scan 2 — primed/unprimed twin declarations

14 pairs found. Classified:

| Pair | Verdict |
|---|---|
| `biResQ{,_blocToBI,_continuous,_id,_comp}`, `theta_mem_unit` | **dead superseded orientation** — deleted |
| `not_vle_pow_p_zero`, `not_vle_pow_teichPi_zero` | **byte-identical copies** — deduped |
| `ainf_pair_spec` | **byte-identical copies** — hoisted |
| `Y_nonempty` | **pure alias** — deleted |
| `gaussTerm_teichCoeffAr_le` | primed strictly generalises → **renamed** |
| `invariant_piece_step'` | legitimate "index-flexible form" variant — keep |
| `limitFrobHom_eq_limitRestrict_pred'` | legitimate index-flexible variant — keep |
| `frobOpens_frobOpens'` | legitimate other-order roundtrip (2-line) — keep |

## What was done

### D1 — `not_vle_pow_p_zero` / `not_vle_pow_teichPi_zero`
Curve.lean carried byte-identical copies of both, existing **only** because the
YSpace originals were `private`. De-privatised the YSpace originals (added
docstrings), deleted the Curve copies, retargeted 7 call sites. −2 decls.

### D2 — `Y_nonempty`
`Curve.Y_nonempty` was a pure alias `:= Y_nonempty' p F ϖ` for the real theorem in
GaussPoint. Dropped the prime in GaussPoint, carried over Curve's much richer
docstring (the Fargues–Fontaine / Kedlaya citation), deleted the alias. −1 decl.

### D3 — `ainf_pair_spec`
Identical 19-line proof in Curve.lean and YStalks.lean, both `private`, in sibling
files. Hoisted to their common ancestor **AinfHuber.lean** (the home of `Iinf`, and
already importing `HuberRings`/`TateAlgebraTopology`) as public
`exists_pairOfDefinition_Iinf`. Curve's copy also carried a **mismatched docstring**
(it described quasicompactness); replaced with an accurate one. −2 decls, −40 lines.

### D4 — the `biResQ` orientation twin
`UniformizerEquivariance` carried two parallel families for the two interval
orientations: unprimed (`q₁ < q₂`) and primed (`q₂ < q₁`, radius-ordered). The
project runs entirely on the primed one — **the whole unprimed family was unused**,
referenced only by its own members. Deleted `theta_mem_unit`, `biResQ`,
`biResQ_blocToBI`, `biResQ_continuous`, `biResQ_id`, `biResQ_comp`: −6 decls,
−121 lines. Then dropped the now-meaningless prime from the 18 surviving
declarations (130 occurrences across 5 files).

### D5 — `gaussTerm_teichCoeffAr_le`
The primed form (Euclidean) strictly generalises the unprimed (ArCompletion) by
dropping `hx0 : Valued.v x ≠ 0` via a case split, and has 19 call sites to the
unprimed's 1 (which is inside the primed proof itself). Renamed so the general form
owns the plain name: core → `gaussTerm_teichCoeffAr_le_of_ne_zero`, general → plain.

### D6 — `comap_comp_apply` (separate commit)
FrobeniusValuation held **two** byte-identical private copies of the pointwise form
of `comap_comp`. It is a general `Spv` fact, so it moved next to `comap_comp` in
`ValuationSpectrum.lean`, derived via `congrFun` instead of re-proved by `rfl`.

## Round 2

### D7 — `NfstRPS_eq_iSup_coeffSeq` / `NsndRPS_eq_iSup_coeffSeq`
Two 37-line proofs, token-identical modulo `.1` ↔ `.2`. The entire content was the
reindexing of an `iSup` along `(Fin 1 →₀ ℕ) → ℕ`, `s ↦ s 0` — with the projection
merely carried along. Mathlib already has this as
`Function.Surjective.iSup_comp`, and crucially it is proved through `range_comp`, so
it applies to `NNReal` (only *conditionally* complete — which is exactly why the
original proofs went the long way round through `Set.range`/`sSup`).

Added `surjective_single_fin_one` next to `coeffSeq` in Presentation.lean; both
proofs became `(surjective_single_fin_one.iSup_comp _).symm`. **−60 lines.**

### D8 — `injOn_toCurve_windowU` / `injOn_toCurve_windowV`
Two 19-line proofs differing only in `windowU` ↔ `windowV`. Both used nothing but
`zsmul_window*` and `window*_disjoint`, whose signatures are exactly parallel.
Extracted `injOn_toCurve_of_wandering`, taking the family `W : ℤ → Set (Spv A_inf)`
with the equivariance and disjointness hypotheses; both theorems became two-line
applications. Line count barely moves (the abstraction costs what the copy saved) —
the win is one proof instead of two, and a lemma that states the actual reason.

### D9 — `chartTate` / `isTateRing_presheafChart`
Found by re-running the body scan with the declaration **keyword** normalised too
(the first scan missed it because one is a `theorem` and the other a
`noncomputable def`). Same statement, same proof body, in two files — and ChartVObj
already transitively imports ChartSpa, so `chartTate` was a redundant re-declaration
of an already-visible theorem. It was also a `noncomputable def` returning a `Prop`,
which is a defect in itself. Deleted; its single call site now uses the theorem.

After D9 there is **no same-body duplication left anywhere in the folder**, under
either normalisation.

### D10 — `valued_ball_mem_nhds`: one fact living in three files

The repeated-block scan flagged a 24-line block shared by `ArCompletion.lean` (×2) and
`Groebner.lean`. Following it up turned out to expose a three-way split of a single fact:

| File | What it had | Import order |
|---|---|---|
| `ArCompletion` | the ball construction **inlined twice**, inside `eventually_valued_sub_le` and `eventually_valued_sub_le_of_tendsto` | earliest |
| `Groebner` | `valued_ball_mem_nhds_zero` — the construction, centred at `0` | via Euclidean |
| `IntervalRing` | `valued_ball_mem_nhds` — the general centre, derived from the `0` case by translating along `w ↦ w - z` | via Groebner |

ArCompletion inlined the argument twice **because the named lemma lived in files that
come after it**. The fix inverts the dependency: the construction is done once, for a
general centre, in ArCompletion (the earliest of the three), and the two special cases
become corollaries.

* `ArCompletion.valued_ball_mem_nhds` — the general statement, proved directly.
* `Groebner.valued_ball_mem_nhds_zero` — now `by simpa using valued_ball_mem_nhds …`
  (42 lines → 6). Its 5 consumers are untouched.
* `IntervalRing.valued_ball_mem_nhds` — deleted as redundant; its 6 consumers now
  resolve to ArCompletion's identical statement.
* ArCompletion's two theorems became 2-line and 1-line term proofs.

Two things worth remembering from this one:

1. **The first attempt deleted an unrelated theorem.** The replacement range spanned
   both target theorems, but `tendsto_gaussTerm_teichCoeffAr` sits *between* them. The
   build caught it. Ranges spanning more than one declaration must be split.
2. **The lemma already existed under the name I was about to introduce.** IntervalRing's
   `valued_ball_mem_nhds` has a byte-identical statement, in the same namespace — a
   silent collision. Always grep the intended name across the folder before adding it,
   not just the concept.

## Scan 3 — repeated blocks *inside* proofs

Whole-declaration scans miss copy-paste that lives inside proof bodies. Indexed every
6-line window across all 46 files, kept substantial ones, grew each match to maximal
length, and de-overlapped.

**Result: ~682 redundant lines in repeated blocks.** Top findings:

| Lines | Copies | Location |
|---|---|---|
| **73** | 2 | `Euclidean.lean:598` and `:1481` — inside `digit_sub_le` and `valued_sub_sub_PhiHatK_le` |
| 9 | 8 | `RobbaPresentation.lean` ×8 (1714, 1891, 3205, 3356, 3476, …) |
| 7 | 8 | `RobbaPresentation.lean` ×8 (1910, 2025, 2121, 2240, 3616, …) |
| 24 | 3 | `ArCompletion.lean:1320`, `:1448`, **`Groebner.lean:59`** — cross-file |
| 7 | 6 | `RobbaPresentation.lean` ×6 (4889, 5004, 5100, 5219, 5311, …) |
| 11 | 4 | `RobbaPresentation.lean` (859, 1536, 1677, 6369) |
| 32 | 2 | `RobbaPresentation.lean:2177`, `:5156` |
| 10 | 4 | `ArCompletion.lean:471`, `:1327`, `:1455`, **`Groebner.lean:66`** — cross-file |
| 14 | 3 | `ArCompletion.lean:225`, `:300`, `:1276` |
| 26 | 2 | `RobbaPresentation.lean:2092`, `:5071` |

The 73-line block is the single biggest win: a limit-transfer preamble (reconstruct
`x`/`y` from `PhiHatK`, convergence of the prefix sequences, and the uniform bound
`hPNval`) copied verbatim between two of the file's longest proofs. Extracting it is
`/decompose-proof` work — the statement of the extracted lemma needs choosing, so it
is deliberately not done blind.

The `ArCompletion` ↔ `Groebner` cross-file repeats (24×3 and 10×4) are the most
interesting: shared setup living in two files that should almost certainly be one
lemma in the earlier one.

## Remaining — structural duplication (NOT yet done; needs a design decision)

These are *moral* duplications (`/overview` Step 5): parallel proofs that differ only
in which component/branch they address. Unifying them means introducing a parametric
lemma, i.e. a real refactor rather than a deletion.

| Twin | Lines each | Differs only in |
|---|---|---|
| `NfstRPS_eq_iSup_coeffSeq` / `NsndRPS_eq_iSup_coeffSeq` | 37 | `.1` vs `.2` |
| `kerSolElt_coe_fst` / `kerSolElt_coe_snd` | 31 | component index |
| `coeffSeq_GeltElt_mul_fst` / `_snd` | 30 | component index |
| `valued_blocToBI_teichPowGen_fst` / `_snd` (and the `₂` pair) | 15 ×4 | component index |
| `injOn_toCurve_windowU` / `injOn_toCurve_windowV` | 19 | `windowU` vs `windowV` |
| `KGE_smul_iff` / `KLE_zpow_smul_iff` | 14 | `KGE` vs `KLE` |
| `teichCoeff_sum_range_add` (GaussNorm) / `teichCoeffF_sum_range_add` (WittF) | 28/32 | `OF F`-Witt vs generic Witt — a **generalisation** opportunity |

The `Nfst/Nsnd` pair is the cleanest win: both proofs are entirely the
`(Fin 1 →₀ ℕ) ≃ ℕ` reindexing of an `iSup`, with the projection merely carried
along. Extracting that reindexing (mathlib has the equiv as
`Finsupp.equivFunOnFinite.trans (Equiv.funUnique (Fin 1) ℕ)`) should collapse both to
a few lines and is a mathlib-API improvement as well.

## Gate

Every step verified by a separate `lake build '«Adic spaces»'` run before commit;
zero new `sorry`; new/moved declarations `#print axioms`-checked.

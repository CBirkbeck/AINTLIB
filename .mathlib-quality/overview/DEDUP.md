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

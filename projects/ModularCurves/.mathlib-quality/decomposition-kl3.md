# /develop --decompose — [KL-3] flat-locus spreading (Stacks 07RF/00RC), CHARTER-FP-2

**CLAIM (fable-FP, 2026-07-11, rule-5; board v10.141a).** The GF7/T-DEV lane is unstaffed;
the flat-locus-spreading residual tree is fleet-unowned and claimed. Target: close the two
sorry-carriers `NoethApprox.exists_subalgebra_flat_baseChange` (07RF/00R6) and
`FlatLocus.flatLocus_spreads_of_flat` (00MK/00RB), which feed `exists_noetherian_descent_flat`
⟹ KL-3 (`SpreadData.exists_flat_stage` in `FinitePresentationDescent.lean`).

## 1. Reconnaissance — the tree is 95% done (GF7 lane)

The GF7 lane built a **major multi-file homological development**, largely PROVEN and
axiom-clean:
- `Grade.lean` — `isOpen_gradeGE_locus`, `rees_core`, `gradeGE_localize`: **fully proven,
  axiom-clean** (file states `#print axioms isOpen_gradeGE_locus → [propext, Classical.choice,
  Quot.sound]`).
- `FittingIdeals.lean` — `idealOfMinors` API (map, antitone, McCoy rank, eq_bot_iff): PROVEN.
- `Depth.lean` — `HasDepthGE` + Stacks 00LW/00LX/00LD (Ext-characterization, the three SES
  depth inequalities, `depth≥1 ⟺ 𝔪∉Ass`, `depth(Rⁿ)=depth R`): **PROVEN** (the "skeleton"
  docstring is stale — the lemmas carry full Ext-long-exact-sequence proofs).
- `LocalCriterion.lean` — `Module.free_of_flat_of_fibre_free` (00MH) + `exists_fibre_adapted_
  surjection`: PROVEN (snake engine + Nakayama).
- `BuchsbaumEisenbud.lean` — `buchsbaumEisenbud_acyclic` (00N1), `be_forward`/`be_backward`,
  `localAcyclicity_block/shift`, the whole acyclicity criterion: PROVEN **modulo the 2
  T-BE-TAIL sorries** below.
- `HilbertSyzygy.lean`, `FiniteFreeResolution.lean`, `Acyclicity.lean`: the resolution +
  global-dimension substrate.

## 2. The frontier — exactly 6 sorries + 2 consumers

Attack order is bottom-up (the docstrings ARE the GF7 decomposition; execute them):

**Tier 0 — T-BE-TAIL (inside `localBE_homology_disjunction`, BuchsbaumEisenbud:770), the
strong-induction closure of `buchsbaumEisenbud_acyclic`:**
- **[KL3-a]** L846: split top differential (`idealOfMinors = ⊤` ⟹ ψ(e-1) is a split
  injection, Stacks 00MW; peel it, IH at e-1). Template: the proven `htz` trailing-zero case
  (825-840) + the proper-ideal case (847-856).
- **[KL3-b]** L858: gap truncation (∃ j∈[i,e), rk j=0 ⟹ modify `rk' i := if i<j then rk i
  else 0`, ψ unchanged below j / 0 above; IH at e'=j). Same IH-application shape as `htz`.

**Tier 1 — the two-term local criterion (foundational for 00MI):**
- **[KL3-c]** `local_criterion_twoTerm` (00ME, BuchsbaumEisenbud:110): `ū` injective ⟹ `u`
  injective ∧ `coker u` R-flat. Snake engine `lTensor_injective_of_exact_of_exact_of_rTensor_
  injective` (as in `free_of_flat_of_fibre_free`) for injectivity + Nakayama on `ker`; the
  cokernel flatness is the Tor₁-vanishing half — verify via the `Flat.of_shortExact_of_flat_
  flat` (PROVEN, :76) + the fibre-injectivity, NOT the general local criterion.

**Tier 2 — the geometric leaves (consume BE + openness):**
- **[KL3-d]** `fibreExact_spreads` (00RB, :1138): fibre-exact at 𝔮 ⟹ basic-open of fibre-exact.
  Translate `FibreExactAt` via `buchsbaumEisenbud_acyclic` over the fibre ring to the
  `idealOfMinors`/`gradeGE` disjunction, then spread by `isOpen_gradeGE_locus` (PROVEN) +
  minor-ideal non-containment loci (open = zeroLocus complement).
- **[KL3-e]** `coker_flat_of_specialFibreExact` (00MI, :1156): special-fibre-exact ⟹ coker
  R-flat. Induction on `e` from [KL3-c] (00ME base case).

**Tier 3 — assembly:**
- **[KL3-f]** `flatLocus_spreads_reduce_to_polynomial` (:1176): reduce to `P=R[x]` via `P↠S`;
  needs a `flatLocus` comap-under-surjection functoriality lemma (`M_{𝔮ᴾ}≅M_𝔮` as R-modules).
- **[KL3-g]** `flatLocus_spreads_of_flat_viaBE` (:1200): the final assembly per its docstring
  (free resolution → dévissage → syzygy free (`free_of_flat_of_fibre_free`) → freeness spreads
  (`Module.basicOpen_subset_freeLocus_iff`, mathlib) → [KL3-d] → [KL3-e]).

**Wiring (Tier 4):**
- `FlatLocus.flatLocus_spreads_of_flat := flatLocus_spreads_of_flat_viaBE` (un-private / cite).
- `NoethApprox.exists_subalgebra_flat_baseChange`: the pointwise descent (via the now-closed
  00MK openness) + the cofiltered-limit collapse (mathlib `01Z2/01Z3/01Z4` + my
  `IsFilteredAlgColimit` ring-colimit-into-scheme-limit wiring).
- Then `exists_noetherian_descent_flat` is sorry-free ⟹ bridge into KL-3
  `SpreadData.exists_flat_stage` (my banked bridge: `exists_noetherian_descent_flat A B` +
  generator-lift of R₀ to a stage + spread the descent-iso).

## 3. Notes
- All Stacks tags are in the in-file docstrings (verbatim intended proofs); the GF7 lane's
  decomposition is authoritative — this artifact is the execution map.
- Deepest/riskiest: [KL3-c] (00ME local criterion) and [KL3-a/b] (00MW/gap strong-induction).
  [KL3-d]/[KL3-f]/[KL3-g] are assembly of proven pieces.
- House rules: no `set_option maxHeartbeats`; commit-early + push; single-target builds;
  axiom-verify each closed leaf (`sorryAx` must retreat).

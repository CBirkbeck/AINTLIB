# Step 4 — Mathlib API Audit (Chebotarev)

Scope: every `def`/`abbrev` in the project (38 found by `grep`, after excluding doc-string false
positives) plus the project's core concepts and the 5 `ForMathlib/` files. Search tooling: mathlib
docs via `WebSearch` (confirmed `AddChar.sum_eq_zero_of_ne_one`, `Submodule.map_span` /
`LinearMap.map_span`, `Asymptotics.IsEquivalent` + `isEquivalent_iff_tendsto_one`,
`LipschitzWith.projIcc`, `lipschitzWith_circleMap`, `CommGroup.monoidHomMonoidHomEquiv`); plus the
def bodies read directly from source. `lean_loogle`/`lean_leansearch`/`lean_local_search` were not
available in this worker, so each "no equivalent found" lists the search terms tried.

Legend for each entry: **Action** = REPLACE (exact mathlib match) / GENERALISE (mathlib has more
general) / USE-MATHLIB-API (API-richer abstraction) / KEEP (genuinely new) / RENAME.

---

## Definitions to Replace with Mathlib

These are exact or near-exact matches: the project def is a thin wrapper around an existing mathlib
declaration and the wrapper should be deleted (inline the mathlib def) or replaced by it.

### `charEval` (`ZetaProduct.lean:248–251`) — **REPLACE**
- Project: `private def charEval {G} [CommGroup G] [Finite G] (σ : G) : (G →* ℂˣ) →* ℂˣ :=
  (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ`.
- The body **is literally** `(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ` — the canonical
  double-dual / Pontryagin evaluation map already in mathlib (`CommGroup.monoidHomMonoidHomEquiv`,
  in `Mathlib.GroupTheory.FiniteAbelian.Duality`, which this project already imports).
- **Action: REPLACE.** Delete `charEval`/`charEval_apply`; use
  `(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm` directly (its `_apply` is
  `monoidHomMonoidHomEquiv_symm_apply_apply`, which `charEval_apply` just re-states). `charEval_ker_card`
  (`|ker| = |G|/orderOf σ`) is the only piece worth keeping — and it should be restated about the
  evaluation hom directly, see "evaluation-character kernel" under API Choice.

### `lipschitzWith_exp_ofReal_mul_I` (`ForMathlib/NormLeOneLipschitz.lean:369–375`) — **REPLACE**
- Project: `LipschitzWith 1 (fun t : ℝ ↦ Complex.exp ((t:ℂ) * Complex.I))`; proof rewrites the
  function to `circleMap 0 1` and applies mathlib `lipschitzWith_circleMap 0 1`.
- This is `circleMap 0 1` up to `funext`; mathlib `lipschitzWith_circleMap (c R)` already gives
  `LipschitzWith ‖R‖₊ (circleMap c R)`, i.e. exactly this with `R = 1`.
- **Action: REPLACE** call sites with `lipschitzWith_circleMap 0 1` after rewriting `exp (t*I) =
  circleMap 0 1 t` (a one-line `simp [circleMap]`). At most keep a 1-line `@[simp]` bridge; do not
  ship it to mathlib as a new lemma.

### `map_span_int_linearEquiv` (`ForMathlib/IdealCongruenceCount.lean:646–649`) — **REPLACE**
- Project: `(f : E ≃ₗ[ℝ] F) (S) : f '' (span ℤ S) = span ℤ (f '' S)` — proof is
  `Submodule.map_span (f.restrictScalars ℤ)` + `congrArg SetLike.coe`.
- Mathlib `Submodule.map_span` / its alias `LinearMap.map_span` is exactly the submodule-level
  statement; the project lemma is the `SetLike.coe`-image restatement for an `≃ₗ` after
  `restrictScalars ℤ`.
- **Action: REPLACE** with `Submodule.map_span (f.restrictScalars ℤ)` at the ~5 call sites
  (`exists_latticeEquiv_image_idealLattice`, `span_image_basisFun_eq`, `chart_lattice_eq_map`,
  `smul_chart_lattice_eq`). It is too trivial to upstream.

### `dist_mul_le_norm_mul_dist` (`ForMathlib/NormLeOneLipschitz.lean:360–367`) — **REPLACE / search-first**
- Project: `(a b u v : α) [NormedField α] : dist (a*u) (b*v) ≤ ‖a‖*dist u v + ‖v‖*dist a b`.
- Generic normed-field product-distance estimate; the inventory already flags it as "very plausibly
  already in mathlib." Search terms tried: `dist_mul_le`, `nndist mul`, `norm_mul_sub`,
  `Asymptotics`/`NormedRing` product bounds. Did not positively locate an identical lemma, but the
  proof is `norm_add_le` + `norm_mul` + `ring` on `a*u − b*v = a*(u−v) + (a−b)*v` (3 lines).
- **Action: USE-MATHLIB-API / inline.** If the exact lemma is not found at PR time, inline the
  3-line proof at its single transitive call site (`dist_mul_exp_phase_le`) rather than carrying a
  named ForMathlib lemma; or upstream as `dist_mul_le_…` to `Mathlib.Analysis.Normed.Field.Basic`.

---

## API Choice Improvements (API-poor → API-rich abstraction)

The project chose a hand-rolled construct where mathlib offers a richer, better-supported
abstraction. These are the **highest-impact** findings (the task's core question).

### Character orthogonality: `ForMathlib/CharacterOrthogonality.lean` → mathlib `AddChar` API
The four public theorems are textbook finite-abelian orthogonality / Fourier inversion, stated for
the **multiplicative** dual `G →* ℂˣ`. Mathlib's first-class abstraction is `AddChar` (with a rich
orthogonality + Fourier API), reachable from `G →* ℂˣ` via `MonoidHom.toAddChar` / `Additive`.
- `sum_char_self_eq_zero_of_ne_one` (`∑ g, χ g = 0` for `χ ≠ 1`) — **REPLACE.** mathlib
  `AddChar.sum_eq_zero_of_ne_one` is exactly this (sum over the group of a nontrivial character
  vanishes, target a domain). **Action: REPLACE** with `AddChar.sum_eq_zero_of_ne_one` after the
  `MonoidHom ↔ AddChar` translation; keep at most a thin `ℂˣ`-flavoured restatement.
- `sum_char_apply_eq_zero_of_ne_one` (`∑ χ : G →* ℂˣ, χ g = 0` for `g ≠ 1`) — column orthogonality,
  i.e. the **dual-side** sum. Mathlib's `AddChar` orthogonality is primarily row-side; the
  dual-side sum is exactly the same statement applied to the double dual (every `g ≠ 1` is a
  nontrivial character of `Ĝ` under `G ≃ Ĝ̂`, valid since `ℂ` has enough roots of unity). **Action:
  GENERALISE/derive** — obtain it as `AddChar.sum_eq_zero_of_ne_one` on `Ĝ` through
  `CommGroup.monoidHomMonoidHomEquiv` (the same `charEval` evaluation map above), rather than the
  bespoke `sum_eq_zero_of_mulLeft_mul_const_aux` translation trick.
- `card_mul_eq_sum_of_sum_char_mul_eq_zero` / `eq_of_sum_char_mul_eq_zero` (Fourier inversion ⇒
  `f` constant) — **USE-MATHLIB-API.** These are consequences of `AddChar` Fourier inversion
  (`AddChar.inv_apply`, the Fourier transform on a finite abelian group). Search terms:
  `AddChar Fourier inversion`, `AddChar.sum_apply_eq_card`, `MonoidHom.sum_apply`. No verbatim
  match for the "all nontrivial moments vanish ⇒ constant" packaging, so it may stay, but it should
  be **rebuilt on the `AddChar` orthogonality lemmas** instead of the private aux engine.
- `sum_eq_zero_of_mulLeft_mul_const_aux` (private) — the generic "scaling by a non-`1` constant ⇒
  sum 0 over a finite group" engine. Genuinely general (`Group` + `IsRightCancelMulZero` semiring)
  and plausibly mathlib-worthy on its own; but if the four theorems above are rebased onto `AddChar`,
  this aux is **no longer needed**. Search: `Finset.sum_eq_zero_of_…_smul`, `Fintype.sum_bijective`
  consequences. **Action: KEEP-or-drop** depending on the `AddChar` rebase.

### `tendsto_ratio_one_of_div_atTop_pm_bounded` (`ForMathlib/LogOneDivSubOne.lean:60–72`) → `Asymptotics.IsEquivalent`
- Project: generic additive-perturbation squeeze `g→+∞`, `|f−g|≤C` eventually ⇒ `f/g → 1`.
- Mathlib's `Asymptotics.IsEquivalent` is the API-rich home: `isEquivalent_iff_tendsto_one`
  packages `u/v → 1` as `u ~[l] v`, and `IsLittleO.isEquivalent` builds `~` from `f − g = o(g)`.
  The two-sided additive bound `|f−g| ≤ C` with `g → +∞` gives `f − g = o(g)` directly. The file's
  own docstring already cites `isLittleO_one_left_iff`, `IsLittleO.isEquivalent`,
  `isEquivalent_iff_tendsto_one`.
- **Action: USE-MATHLIB-API.** Re-derive via `IsEquivalent` (`(f-g) = o(g)` from
  `Asymptotics.isBigO_const_of_eventually_le`-style bound + `IsBigO.trans_tendsto`/`isLittleO`), so
  the lemma becomes a 1–2 line corollary of mathlib. The downstream caller
  (`tendsto_ratio_one_of_log_pm_bounded`, `primeIdealZetaSum_univ_tendsto_log`) only needs the
  `Tendsto (f/g) → 1` form, which `isEquivalent_iff_tendsto_one` provides. Keep the elementary `∃C,∀ᶠ`
  *interface* if caller hypotheses are shaped that way, but the *proof* should route through
  `IsEquivalent`.

### `clampUnit` + `lipschitzWith_clampUnit` (`ForMathlib/NormLeOneLipschitz.lean:86–110`) → `LipschitzWith.projIcc`
- Project: coordinatewise `Set.projIcc 0 1` retraction of `ι → ℝ` onto the unit cube, shown
  `1`-Lipschitz via the private `lipschitzWith_one_of_edist_apply_le` + `LipschitzWith.projIcc`.
- Mathlib already has `LipschitzWith.projIcc` (the `1`-Lipschitz interval projection) and the pi
  Lipschitz API. `clampUnit` is the `Pi`-packaging; the only missing piece is "pi of `projIcc` is
  `1`-Lipschitz", which is `LipschitzWith.projIcc` composed through `LipschitzWith.pi`.
- **Action: USE-MATHLIB-API.** Keep `clampUnit` as a convenience def if needed, but prove
  `lipschitzWith_clampUnit` directly from `LipschitzWith.pi (fun i ↦ LipschitzWith.projIcc …)`
  instead of the bespoke `lipschitzWith_one_of_edist_apply_le`. Consider whether a packaged
  "project onto `pi`-`Icc`" belongs in mathlib (search: `LipschitzWith.projIcc pi`,
  `Set.pi Icc projection` — no packaged pi-version found, so a small mathlib addition is reasonable).

### `lipschitzWith_one_of_edist_apply_le` (private, `NormLeOneLipschitz.lean:98–105`) → `LipschitzWith.pi`/`.eval`
- Generic "1-Lipschitz into a finite pi from coordinatewise `edist` bound". Mathlib has
  `LipschitzWith.pi` (build pi-Lipschitz from coordinatewise) and `edist_pi_def`/`edist_le_pi_edist`.
- **Action: USE-MATHLIB-API.** Expressible as `LipschitzWith.pi` with each coordinate
  `LipschitzWith.of_edist_le`. Two call sites (`lipschitzWith_clampUnit`, `lipschitzWith_cubeRelabel`)
  can use `LipschitzWith.pi` directly; the private helper can likely be deleted.

### `realizedResidues` (`ZetaProduct.lean:1014–1035`) — hand-rolled `Subgroup` — **KEEP (verify only)**
- A genuine `Subgroup (ZMod m)ˣ` (the residues realized as `N𝔟 mod m`). Built as the range/closure
  of the norm-residue map. **Action: USE-MATHLIB-API check** — confirm it is not more cleanly
  `MonoidHom.range`/`Subgroup.closure` of the norm-residue hom; the structure-field construction
  (unit via `⊤`, inverse via `𝔟^{ord−1}`) suggests it could be `Subgroup.closure (range …)` or the
  range of a monoid hom into `(ZMod m)ˣ`. Search: `MonoidHom.range`, `Subgroup.closure_range`.
  Otherwise mathematically project-specific; KEEP.

### Density predicates `HasDirichletDensity`/`Upper`/`Lower` (`Density.lean:60–92`) — **KEEP, but note `limsup`/`liminf` API**
- `HasUpperDirichletDensity := limsup … = δ`, `…Lower := liminf … = δ`, `HasDirichletDensity :=
  Tendsto … (𝓝 δ)`. These are the right mathlib-flavoured definitions (no hand-rolled limits; they
  use `Filter.Tendsto`/`limsup`/`liminf` directly). **Action: KEEP.** Only flag: mathlib has no
  "Dirichlet density of a set of primes" notion, so these are genuinely new (Sharifi 7.1.13);
  they are good upstream candidates verbatim. The `of_upper_eq_lower` sandwich is
  `tendsto_of_liminf_eq_limsup` (already used) — correct API choice.

---

## Hand-Rolled Patterns to Replace

Patterns inside proofs / small defs that duplicate mathlib API or use `Set.Finite` where
`Finset`/`Fintype` is idiomatic, etc.

### `Set.Finite` counts pushed through `Nat.card`/`ncard` — **mostly idiomatic, one note**
The geometry-of-numbers files (`LatticePointCount`, `IdealCongruenceCount`) consistently use
`Set.ncard`/`Nat.card` of subtypes with `Set.Finite`/`Finite` instances. This is the modern mathlib
idiom (matches `BoxIntegral.unitPartition.setFinite_index`, `tendsto_card_div_pow_atTop_volume`), so
**no blanket `Set.Finite → Finset` change is warranted.** The `index`-image counting refinements
(`setFinite_index_image_of_isBounded`, `ncard_index_image_*`) belong directly beside mathlib's
existing `unitPartition.index` API. **Action: KEEP**, contribute next to `unitPartition`.

### Effective `O(N^{1−1/d})` ⇒ ratio limit — `tendsto_div_atTop_of_sub_mul_rpow_le`, `exists_sub_mul_rpow_le_of_div` (`IdealCongruenceCount.lean`) — **USE-MATHLIB-API**
Purely-analytic "`|f N − κ·N| ≤ C·N^{1−1/d}` ⇒ `f N / N → κ`" and its floor-division transfer. No
number theory. **Action: USE-MATHLIB-API** — should route through `squeeze_zero'` +
`tendsto_rpow_neg_atTop` (already do) but are candidates to live in `Mathlib.Analysis` as standalone
asymptotic lemmas; check `tendsto_div_of_…`, `Asymptotics.IsLittleO` ratio forms before duplicating.

### `measureReal_biUnion_box` (`LatticePointCount.lean:261–272`) — **inline**
Real volume of a finite disjoint union of grid boxes = `#t/nᵈ`. Thin specialisation of mathlib
`volume_box` + `measureReal_biUnion_finset`. **Action: inline** at its single call site rather than
ship as a ForMathlib lemma.

### Elementary `ℕ`/`ZMod` arithmetic helpers — **search-first, do not upstream as-is**
- `natCast_eq_iff_mul_natCast_eq` (`IdealCongruenceCount.lean:568–573`): `m ≡ a [c] ↔ m·NJ ≡ a·NJ
  [c·NJ]`. Generic `ZMod`/`Nat.ModEq` scaling. **Action: search** `ZMod.natCast_mul`,
  `Nat.ModEq.mul_right`, `Nat.mul_mod_mul_right`; likely composable from existing lemmas — inline.
- `Nat.le_iff_le_mul_div_of_dvd` (`IdealCongruenceCount.lean:2112–2116`): generic `Nat`
  divisibility/floor fact, **AND declared in the `Nat.` namespace** — clobber risk. **Action:
  RENAME** out of `Nat.` (e.g. `le_iff_le_mul_div_of_dvd`) and search `Nat.le_div_iff_mul_le`,
  `Nat.mul_div_le` for an existing form before keeping.
- `prod_eq_neg_one_pow_card_mul_prod_abs` (`IdealCongruenceCount.lean:462–472`): generic `Finset.prod`
  sign identity `∏ f = (−1)^{#neg}·∏|f|`. **Action: search** `Finset.prod_abs`,
  `Finset.prod_neg`/`prod_attach` sign lemmas; if absent, upstream to `Mathlib.Algebra.BigOperators`.
- `mem_span_int_basisFun_iff` (`IdealCongruenceCount.lean:887–891`): `v ∈ span ℤ (range basisFun) ↔
  ∀ i, ∃ n:ℤ, v i = n`. **Action: search** `Pi.basisFun`/`Basis.mem_span_iff_repr_mem`,
  `mem_span_range`; standard-lattice membership — likely thin, candidate for `Pi.basisFun` API.

### Ideal-norm / lattice number-theory bridges — **KEEP, contribute beside `Ideal.absNorm`/`ZLattice`**
- `relIndex_mul_ideal_eq_absNorm`, `relIndex_idealLattice_eq_absNorm`,
  `absNorm_coprime_of_isCoprime_span`, `covolume_image_basisFun_eq_abs_det`,
  `exists_mk0_eq_absNorm_coprime`, `crt_single_coset`, `natCast_algebraNorm_add_nsmul_mul`,
  `norm_eq_prod_real_emb_mul_prod_complex`: natural `Ideal.absNorm` / `ZLattice.covolume` /
  `ClassGroup` / `Algebra.norm` facts. The inventory flags each as a mathlib-overlap candidate.
  **Action: search-then-KEEP** — these are genuinely useful, generically-stated number-theory
  lemmas (some, like `crt_single_coset` and `exists_mk0_eq_absNorm_coprime`, are textbook); they
  should be checked against existing `Ideal.absNorm`/`ZLattice.covolume_eq_det`/`ClassGroup` API and,
  if absent, contributed to the relevant mathlib file with the `Chebotarev` namespace stripped.

---

## Definitions audited — verdict table (concept-bearing defs)

| Def (file) | Verdict | Mathlib target / note |
|---|---|---|
| `charEval` (ZetaProduct) | REPLACE | `CommGroup.monoidHomMonoidHomEquiv` (literal body) |
| `lipschitzWith_exp_ofReal_mul_I` (NormLeOne…) | REPLACE | `circleMap 0 1` + `lipschitzWith_circleMap` |
| `map_span_int_linearEquiv` (ICC) | REPLACE | `Submodule.map_span`/`LinearMap.map_span` |
| `dist_mul_le_norm_mul_dist` (NormLeOne…) | REPLACE/inline | normed-field `norm_add_le`+`norm_mul` |
| `sum_char_self_eq_zero_of_ne_one` (CharOrth) | REPLACE | `AddChar.sum_eq_zero_of_ne_one` |
| `sum_char_apply_eq_zero_of_ne_one` (CharOrth) | GENERALISE | `AddChar` orthogonality via double dual |
| `card_mul_eq_…`/`eq_of_sum_char_…` (CharOrth) | USE-MATHLIB-API | `AddChar` Fourier inversion |
| `tendsto_ratio_one_of_div_atTop_pm_bounded` (LogOne…) | USE-MATHLIB-API | `Asymptotics.IsEquivalent` |
| `clampUnit` / `lipschitzWith_clampUnit` (NormLeOne…) | USE-MATHLIB-API | `LipschitzWith.projIcc` + `LipschitzWith.pi` |
| `lipschitzWith_one_of_edist_apply_le` (NormLeOne…) | USE-MATHLIB-API | `LipschitzWith.pi`/`.eval` |
| `realizedResidues` (ZetaProduct) | KEEP (verify) | maybe `MonoidHom.range`/`Subgroup.closure` |
| `tendsto_div_atTop_of_sub_mul_rpow_le`, `exists_sub_mul_rpow_le_of_div` (ICC) | USE-MATHLIB-API | `squeeze_zero'`/`IsLittleO`; → `Mathlib.Analysis` |
| `cardNormLeResidue`/`…Class`/`…ClassDvd` (ICC) | KEEP | `Nat.card` of residue subtype — fine; new |
| `idealNormMultiplicity`, `NonzeroIdeal` (NFEuler) | KEEP | `Nat.card` count / subtype — idiomatic, new |
| `insertPiEquiv` (NFEuler) | KEEP | `subtypeInsertEquivOption`∘`piOptionEquivProd` — already mathlib-composed, fine as private |
| `primeFactorsOf` (NFEuler) | KEEP | `normalizedFactors.toFinset` packaging — fine |
| `galoisCharacter` (abbrev, ZetaProduct) | KEEP | `Gal(L/K) →* ℂˣ` — correct, no `AddChar` needed at def site |
| `galoisCharacterOnIdeal`, `frobeniusIdeal`, `galoisCharacterCoeff`, `artinDirichletSeries` (ZetaProduct) | KEEP | Artin L-series coefficients — project-specific, new |
| `twistedPrimeSum` (Cyclotomic) | KEEP | `tsum` over unramified primes — new |
| `UnramifiedIn`, `frobeniusClass` (Frobenius) | KEEP | new NT predicates (mathlib has `IsArithFrobAt`/`arithFrobAt` but not these packagings) |
| `faceMapZero/Side`, `cubeRelabel`, `frontierCoverFamily`, `mixedCubeEquiv`, `liftToMixed` (NormLeOne…) | KEEP | `expMapBasis`/`mixedEmbedding`-specific frontier-cover machinery — the real contribution |
| `underUP`, `fiberUnderEquiv`, `unramifiedFlatten/ramifiedFlattenEquiv` (ZetaProduct) | KEEP | bespoke subtype bookkeeping for `sigmaFiberEquiv`; project-local, fine as private |
| `badPart`, `goodPart`, `IsBadPart`, `primeFactorsOf`, `realizedResidues` | KEEP | L2-partition infra; project-specific |

### `exists_phase_mem_Icc_mul_exp` (NormLeOne…:419–436) — note
Polar form `z = ‖z‖·exp((2πθ−π)i)`, `θ∈[0,1]`. Core is mathlib `Complex.norm_mul_exp_arg_mul_I`;
the `[0,1]`-normalised arg packaging is project-specific. **Action: KEEP**, but the
interval-normalisation could be generalised; the modulus×phase split is already mathlib.

---

## Summary of highest-impact actions (for the orchestrator)
1. **`charEval` → `CommGroup.monoidHomMonoidHomEquiv`** — delete the def + `charEval_apply`; the body is the mathlib map verbatim.
2. **`CharacterOrthogonality.lean` → mathlib `AddChar`** — `sum_char_self_eq_zero_of_ne_one` IS `AddChar.sum_eq_zero_of_ne_one`; rebase all four theorems + drop the private aux. Biggest dedup win.
3. **`tendsto_ratio_one_of_div_atTop_pm_bounded` → `Asymptotics.IsEquivalent`** (`isEquivalent_iff_tendsto_one`).
4. **`clampUnit`/Lipschitz-pi helpers → `LipschitzWith.projIcc` + `LipschitzWith.pi`**, and **`lipschitzWith_exp_ofReal_mul_I` → `lipschitzWith_circleMap`**.
5. **`map_span_int_linearEquiv` → `Submodule.map_span`**; inline `measureReal_biUnion_box`, `dist_mul_le_norm_mul_dist`; **RENAME `Nat.le_iff_le_mul_div_of_dvd`** out of `Nat.`.

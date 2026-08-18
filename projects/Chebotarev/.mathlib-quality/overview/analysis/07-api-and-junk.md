# Steps 7 + 8 — API Design Review & Junk Identification: Chebotarev

Scope: 14 files, 441 declarations. Inputs: `inventory/*.md` + source `CebotarevDensity/`.
Search: cross-file `grep` of duplicated lemma names + verbatim proof comparison.
Local Lean build unavailable; mathlib-existence claims are flagged "verify" where not certain.

This project is a near-complete Chebotarev development with a large `ForMathlib/` upstreaming
surface. Most "unused in file" declarations are **terminal public exports** consumed by sibling
files — these are catalogued explicitly as *keep (public API)* and are NOT junk.

---

## PART A — API Improvements

### A.1 Missing NEW project lemmas (extract repeated patterns)

**API-1 (HIGH) — Shared `two_le_absNorm` (nonzero prime ⇒ N ≥ 2). 3 copies + 1 inline.**
Confirmed duplicates, all the same proof (`absNorm_eq_zero_iff` / `absNorm_eq_one_iff` + `lia`):
- `Density.two_le_absNorm_of_prime` (ℝ-valued, `(2:ℝ) ≤ (N𝔭:ℝ)`) — `Density.lean:293`
- `Cyclotomic.two_le_absNorm_prime` (ℕ-valued) — `Cyclotomic.lean:434`
- `ZetaProduct.two_le_absNorm` (**most general**: any `IsDedekindDomain R`, `Module.Free/Finite ℤ R`) — `ZetaProduct.lean:2470`
- `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` and `Density.absNorm_rpow_neg_lt_one` /
  `FixedFieldDensity.absNorm_rpow_neg_le_under_sq` re-derive `N𝔭 ≥ 2` inline.
**Action:** keep the general `ZetaProduct.two_le_absNorm` form, move to a shared `Common/`
location, and have the other two + the inline derivations call it. This is *also* a strong
**mathlib** candidate (a nonzero prime of any Dedekind ℤ-finite-free ring has `absNorm ≥ 2`); verify
mathlib `Ideal.absNorm` API does not already have `Ideal.one_lt_absNorm`/`two_le_absNorm`.

**API-2 (HIGH) — Shared `smul_algebraMap_eq` + `isArithFrobAt_restrictNormal` (Frobenius descent).**
Verbatim-equivalent pairs (verified by side-by-side read):
- `CyclotomicNormResidue.smul_algebraMap_eq` (`IntermediateField K L` form) ↔
  `Abelian.smul_algebraMap_eq_repl` (abstract tower `K ⊆ L ⊆ M`) — same proof body.
- `CyclotomicNormResidue.isArithFrobAt_restrictNormal` ↔ `Abelian.isArithFrobAt_restrictNormal_repl`.
The Abelian docstrings already call themselves "replica of a private `CyclotomicNormResidue` lemma".
**Action:** keep ONE tower-form `(K L M)` version in `Common/` (the abstract tower subsumes the
`IntermediateField` case via `IntermediateField.isScalarTower_mid'`), delete the `_repl` copies.
Both are mathlib candidates (`AlgEquiv.restrictNormal` intertwines the integer-ring embedding; the
arith-Frobenius descent `IsArithFrobAt.restrictNormal`) — verify against
`Mathlib.RingTheory.Frobenius` / `AlgEquiv.restrictNormal_commutes` neighbourhood.

**API-3 (HIGH) — Shared "cyclotomic coprime-norm ⇒ unramified" different-ideal lemma. 3 variants.**
- `Main.unramifiedIn_cyclotomic_of_coprime` (`Main.lean:275`, ~48-line proof) — docstring explicitly
  says "self-contained replica of a private lemma from `ZetaProduct.lean`".
- `ZetaProduct.unramifiedIn_of_coprime_absNorm` (`ZetaProduct.lean:614`, ~55 lines).
- `ZetaProduct.coprime_absNorm_of_unramified_of_finrank_eq_one` (`:1654`, the converse direction for
  `[K:ℚ]=1`, ~53 lines) — different statement but shares the Eisenstein/different-ideal machinery.
**Action:** the first two are the SAME theorem (verbatim-replica per docstring) — keep one in
`Common/`, delete the Main copy and import. The whole "ramification in `K(μ_m)` is detected by the
different ideal via `conductor_mul_differentIdeal` + `minpoly ∣ X^m−1`" argument is mathlib-worthy
(`IsCyclotomicExtension.Rat.ramificationIdx` exists for `ℚ`-base; the general-base coprime-norm
criterion looks new — verify, then upstream).

**API-4 (HIGH) — General "Dirichlet ratio → 1 when complement is finite" lemma. ≥3 sites.**
Verified structurally identical proofs (split `univ` = good `G` ⊔ finite-bad `B`, bad-ratio → 0 via
bounded-numerator/`log→∞`, subtract from `primeIdealZetaSum_univ_tendsto_log`, reassemble with
`primeIdealZetaSum_union_of_disjoint` + `primeIdealZetaSum_eq_univ_of_forall_prime_mem`):
- `Cyclotomic.primeIdealZetaSum_unramified_div_log_tendsto_one` (`Cyclotomic.lean:690`, ~42 lines)
- `CyclotomicNormResidue.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` (`:353`, ~49 lines)
- `Abelian.ratioSum_frobeniusFibres_tendsto_one` (`:1377`, ~57 lines) uses the same skeleton with a
  finite ramified complement and a pairwise-disjoint family.
**Action (NEW project lemma, `Density.lean`):**
`primeIdealZetaSum_div_log_tendsto_one_of_finite_primeCompl (G : Set (Ideal (𝓞 K)))
  (hfin : {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ 𝔭 ∉ G}.Finite) : Tendsto (fun s ↦ Σ_G s / log(1/(s-1))) (𝓝[>]1) (𝓝 1)`.
Collapses each of the 3 proofs above to a 1-line application (supply the finite-complement witness).
This is the single highest-value extraction in the project (~120 lines of near-duplicate squeeze code).

**API-5 (MED) — `primeIdealZetaSum` inclusion–exclusion / sdiff helper is over-local.**
`Main.primeIdealZetaSum_eq_add_sub_sdiff` (`Main.lean:179`) is a clean `Σ_T = Σ_S + Σ_{T∖S} − Σ_{S∖T}`
identity but private to `Main`. The symmetric-difference density-invariance it powers
(`hasDirichletDensity_of_finite_symmDiff`, also private in `Main`) is a generally-useful
Dirichlet-density fact. **Action:** relocate both to `Density.lean` next to `HasDirichletDensity`
and make public — `hasDirichletDensity_of_finite_symmDiff` is exactly the kind of lemma other
density consumers will want, and it currently sits orphaned in the AP-theorem file.

**API-6 (MED) — Fibre-counting `tsum` helpers are duplicated 3× in FixedFieldDensity.**
`tsum_comp_eq_card_fibre_smul` (ℝ, equal fibres), `tsum_comp_le_card_fibre_mul` (ℝ≥0∞, bounded
fibres), `tsum_real_comp_le_card_fibre_mul` (ℝ, bounded fibres) — `FixedFieldDensity.lean:696/860/875`.
These are pure `tsum`/`HasSum.tsum_fiberwise` glue with no number theory. **Action:** they are
mathlib-flavoured (fibrewise `tsum` counting); keep but consolidate into one `Common/` file and check
mathlib `HasSum.tsum_fiberwise` / `tsum_fiberwise` neighbourhood for an existing constant-fibre form.

### A.2 Missing instances / coercions

**API-7 (MED) — Duplicated/ad-hoc `Fintype`/`Finite` instances.**
- `NumberFieldEulerProduct.instFintypeSym` (`Fintype (Sym α n)` from `Finite`) — generic, plausibly
  already in mathlib (`Sym.instFintype`?); verify, likely deletable.
- `galoisCharacter.instFintype` (`ZetaProduct.lean:2430`, **local** `Fintype (Gal(L/K) →* ℂˣ)`) vs the
  repeated explicit `[Fintype (galoisCharacter K L)]` hypotheses threaded through `Cyclotomic.lean`
  (`character_orthogonality_*`, `sum_charTwist_*`). **Action:** promoting the local instance (or a
  `Common/` one) to non-local would let the `Cyclotomic` lemmas drop their `[Fintype …]` binders.
- `NumberFieldEulerProduct.instFiniteAbsNormFiber` ↔ `ZetaProduct.finite_nonzeroIdeal_absNorm_eq`
  (`ZetaProduct.lean:2108`) are the SAME fact ("norm-`n` fibre of nonzero ideals is finite"); one is
  an `instance`, the other a `theorem`. **Action:** keep the instance form, delete the theorem, use
  the instance.

### A.3 Completeness gaps (`@[simp]` / equation companions)

**API-8 (LOW) — `@[simp]` asymmetry on the prime-evaluation equation lemmas.**
`ZetaProduct.frobeniusIdeal_apply_prime` IS `@[simp]` but the parallel
`ZetaProduct.galoisCharacterOnIdeal_apply_prime` (`:104`) is NOT, despite identical shape
("value on a nonzero prime = …"). Likewise `galoisCharacterOnIdeal_one` is `@[simp]` (good).
**Action:** consider `@[simp]` on `galoisCharacterOnIdeal_apply_prime` for consistency (it has an
`h𝔭 : 𝔭 ≠ ⊥` hypothesis, so it is a conditional-simp; matches `frobeniusIdeal_apply_prime` which
has the same hypothesis and IS marked).

**API-9 (LOW) — `frobeniusIdeal`/`galoisCharacterOnIdeal` lack `_pow` companions.**
Both have `_one` and `_mul` (completely-multiplicative API) but no `_pow` lemma; several proofs
(`autToPow_frobeniusIdeal`, `weight_prod_primePow`) re-derive `w(𝔭^k)=(w𝔭)^k` by induction inline.
**Action (LOW):** a `frobeniusIdeal_pow` / `galoisCharacterOnIdeal_pow` companion would tidy those.
Marginal; only worth it if the inline inductions recur.

**API-10 (NOTE) — `orderOf_eq_finrank_of_isArithFrobAt` is a genuine documented mathlib API gap.**
`Frobenius.orderOf_eq_finrank_of_isArithFrobAt` (`:212`) — "the order of the arithmetic Frobenius =
residue degree `f`" — is flagged in its own docstring as missing from mathlib (mathlib lacks
"Frobenius generates the decomposition group `D_𝔓`"). This is an *additive-to-mathlib* gap, not a
project cleanup; record for the `/mathlibable` pass. No project action.

---

## PART B — Junk / Removable

**Methodology:** Every decl flagged "unused in file" was cross-checked against the inventory "Used by"
notes and the module docstrings. The vast majority are **terminal public exports** consumed by
sibling files (the `ForMathlib/` upstream surface + the cross-file Chebotarev API spine). Those are
listed as *keep (public API)*. Genuine removables are duplicates and one superseded decl.

### B.1 REMOVE / REPLACE — genuine duplicates (the real junk)

| # | Decl | Verdict | Reason |
|---|------|---------|--------|
| J-1 | `Density.two_le_absNorm_of_prime`, `Cyclotomic.two_le_absNorm_prime` | **REPLACE** → `ZetaProduct.two_le_absNorm` (relocate to `Common/`) | 3 verbatim copies of the same 3-line proof (API-1). Keep the most-general; delete the other two. |
| J-2 | `Abelian.smul_algebraMap_eq_repl` | **REMOVE** (use one tower-form shared lemma) | Verbatim replica of `CyclotomicNormResidue.smul_algebraMap_eq` per its own docstring (API-2). |
| J-3 | `Abelian.isArithFrobAt_restrictNormal_repl` | **REMOVE** (use shared lemma) | Verbatim replica of `CyclotomicNormResidue.isArithFrobAt_restrictNormal` (API-2). |
| J-4 | `Main.unramifiedIn_cyclotomic_of_coprime` | **REMOVE** (import `ZetaProduct.unramifiedIn_of_coprime_absNorm`, relocated to `Common/`) | Docstring: "self-contained replica of a private lemma from `ZetaProduct.lean`" (API-3). ~48 dup lines. |
| J-5 | `NumberFieldEulerProduct.instFiniteAbsNormFiber` **or** `ZetaProduct.finite_nonzeroIdeal_absNorm_eq` | **REMOVE one** (keep the `instance`) | Same fact ("norm-`n` ideal fibre finite") stated twice, once as instance once as theorem (API-7). |

### B.2 REMOVE — superseded / genuinely dead

| # | Decl | Verdict | Reason |
|---|------|---------|--------|
| J-6 | `Abelian.H_n_over_H_tends_to_one` (public, `:1193`, ~60 lines) | **REMOVE** | Inventory + docstring: "superseded by `ratio_card_dvd_orderOf_tendsto_one`, which is the variant actually fed to `liminf_ratio_ge_inv_card_G`." It is public but has NO consumer (in-file or cross-file) — the sequence-of-moduli variant replaced it. ~60 dead lines. **Verify** no other project imports it before deleting. |
| J-7 | `Abelian.cyclic_subgroup_meets_G_times_one_trivially` (public, `:90`) | **REMOVE or privatise** | Inventory: the concrete `Gal`-realisation `zpowers_inf_fixingSubgroup_eq_bot_aux` "re-derives the same fact directly; cited in docstrings of C3 but not invoked." Abstract `G × H` version is never applied. Either delete (concrete version is self-contained) or keep as a `private` general lemma if judged reusable. |

### B.3 INLINE candidates (1–3 mathlib-call wrappers) — LOW priority

| # | Decl | Verdict | Reason |
|---|------|---------|--------|
| J-8 | `NumberFieldEulerProduct.instFintypeSym` | **REPLACE** if mathlib has `Sym.instFintype` | One-line `Fintype.ofFinite (Sym α n)`; verify mathlib coverage, else keep. |
| J-9 | `LatticePointCount.measureReal_biUnion_box` | **KEEP** (inventory-flagged inline candidate, but NOT a clean wrapper) | Inventory calls it "a thin specialisation [of `volume_box`+`measureReal_biUnion_finset`], may be inlineable" — but it bundles disjointness + finite-measure side-conditions over the box family, so inlining at its one call site (`abs_card_inter_sub_volume_mul_pow_le`) would bloat an already-72-line proof. Keep as a named helper. |
| J-10 | `Frobenius.UnramifiedIn.ne_bot` (`hunr.1`) | **KEEP** | Trivial projection wrapper, BUT it is the canonical accessor used by ~6 call sites and reads far better than `.1`. Keep — idiomatic API, not junk. |

Note on J-8/J-9: these are the *only* "thin wrapper" candidates in the inventory, and both are
borderline. The project has very few gratuitous wrappers — most short decls are legitimate named
projections (`UnramifiedIn.ne_bot`, `.ramificationIdx_eq_one`) or equation lemmas
(`primeIdealZetaSum_def`, `*_apply_prime`) that earn their names.

### B.4 KEEP — "unused in file" but PUBLIC API (NOT junk — do not remove)

These are flagged "unused in file" by the inventory but are intended cross-file/upstream exports.
Confirmed via "Used by" notes and module docstrings. **Do not touch.**

- **`ForMathlib/` upstream exports** (root-namespace, author-earmarked for mathlib):
  `LogOneDivSubOne.tendsto_ratio_one_of_log_pm_bounded`;
  `CharacterOrthogonality.sum_char_self_eq_zero_of_ne_one`, `.eq_of_sum_char_mul_eq_zero`;
  `LatticePointCount.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`;
  `NormLeOneLipschitz.normLeOne_frontier_lipschitz_cover`, `.normLeOne_frontier_lipschitz_cover_index`;
  `IdealCongruenceCount`'s 4 public terminals (`exists_card_coset_inter_smul_sub_volume_mul_rpow_le`,
  `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le[_uniform]`,
  `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`).
- **Cross-file Chebotarev spine** (consumed by sibling modules):
  `Frobenius.{card_primesAbove_mul_orderOf_eq, finite_ramifiedIn, finite_badPrimes}`;
  `CyclotomicNormResidue.{autToPow_frobeniusClass_out, subgroup_eq_top_of_forall_frobenius_mem}`;
  `Cyclotomic.chebotarev_cyclotomic_lowerDensity_ge` (consumed by `Abelian`);
  `FixedFieldDensity.density_lift_through_fixedField` (consumed by `Main`/`Abelian`);
  `Abelian.chebotarev_abelian` (consumed by `Main`);
  `ZetaProduct.artinLSeries_one_ne_zero` (LF5, consumed by `Cyclotomic`);
  the `Density.HasDirichletDensity.*` API surface (10 "unused-in-file" lemmas, all downstream API);
  `NumberFieldEulerProduct.{dedekindZeta_eq_tprod_primeIdeal, dedekindZeta_re_pos_of_one_lt,
  hasSum_nonzeroIdeal_absNorm_cpow}` (consumed by `Density`/`ZetaProduct`).
- **Top-level theorems** (the project deliverables): `Main.{chebotarev_density,
  chebotarev_density_of_comm, infinite_setOf_frobenius_class, density_split_completely,
  dirichlet_primes_in_AP}`.
- **Resolved-by-typeclass-search instances** (no explicit reference is expected):
  `Frobenius.faithfulSMul_galois`, `ZetaProduct.{finite_L2, finite_ramifiedAbove,
  galoisCharacter.instFintype}`, `NumberFieldEulerProduct.{instFintypeSym, instFiniteAbsNormFiber}`.

---

## Summary counts

- **API suggestions: 10** (A.1: 6 — 4 HIGH extractions, 2 MED relocations; A.2: 1 instance/coercion
  group [3 sub-items]; A.3: 3 completeness — 2 LOW simp/`_pow`, 1 NOTE documented mathlib gap).
- **Genuine junk (REMOVE/INLINE/REPLACE): 7** — J-1 REPLACE (folds 2 copies), J-2/J-3/J-4 REMOVE
  (verbatim replicas), J-5 REMOVE (one of an instance/theorem dup pair), J-6 REMOVE (superseded dead
  `H_n_over_H_tends_to_one`), J-7 REMOVE/privatise (unapplied abstract lemma). Plus J-8 conditional
  INLINE/REPLACE and J-9/J-10 evaluated-and-kept.
- **False-positive "unused but public": ~30+** terminal exports (full list in B.4) — all KEEP.
- **Top duplication root causes:** (1) the log-asymptotic squeeze [API-4, ~120 dup lines across 3
  decls — the single biggest win], (2) `two_le_absNorm` [J-1, 3 copies], (3) the Frobenius-descent
  pair `smul_algebraMap_eq`/`isArithFrobAt_restrictNormal` [J-2/J-3, replicated for the compositum
  tower], (4) the cyclotomic coprime-norm⇒unramified different-ideal lemma [J-4, replica].

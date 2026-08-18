# Step 6 — Generalization Analysis — Chebotarev (`CebotarevDensity`)

Scope: find results stated **too specifically** that mathlib would want in their most general
form. Priority: the 5 author-earmarked `ForMathlib/` files. Local build unavailable — all
signatures reasoned from the source `.lean` + the mathlib doc API (no `lean_local_search`).

Search tooling note: `lean_loogle`/`lean_leansearch` were **not** available in this environment;
findings rest on `WebSearch` + `WebFetch` of the mathlib4 doc pages (`FiniteAbelian/Duality`,
`EMetricSpace/Lipschitz`, `MetricSpace/Lipschitz`, `Normed/Field/Basic`, `ProjIcc`,
`SpecialFunctions/Log/Basic`, `Asymptotics/AsymptoticEquivalent`) and the literature.

Legend for each entry: **Current** (the statement as written) / **proof-only-uses** (the
structure the *proof* actually consumes) / **Literature** (the textbook-standard generality) /
**Mathlib** (relevant existing API) / **Action** (proposed generalised signature) /
**Difficulty** (Low / Med / High).

---

## A. `ForMathlib/CharacterOrthogonality.lean` — hard-wired `ℂ`, only needs `HasEnoughRootsOfUnity`

This file is the headline finding: all four public results are textbook finite-abelian character
orthogonality / Fourier inversion, but every one fixes the target ring to `ℂ`. The proof of the
generating column lemma already routes through
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, whose **verified** mathlib signature is

```
theorem CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
  (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent G)] {a : G} (ha : a ≠ 1) :
  ∃ φ : G →* Mˣ, φ a ≠ 1
```

— i.e. it needs only `CommMonoid M` + `HasEnoughRootsOfUnity M (Monoid.exponent G)`, **not** `ℂ`,
**not even a field**. `ℂ` enters the project solely as a source of `HasEnoughRootsOfUnity ℂ _`
(via `IsAlgClosed`). Confirmed via `WebFetch` of `Mathlib/GroupTheory/FiniteAbelian/Duality.html`:
**no** orthogonality-sum lemma exists upstream, so these are genuinely new — and should be added
in their general form.

### 1. `sum_char_apply_eq_zero_of_ne_one` (column orthogonality) — generalise `ℂ → R`

- **Current**: `{G} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) :`
  `∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0`.
- **proof-only-uses**: the separating character from
  `exists_apply_ne_one_of_hasEnoughRootsOfUnity G R hg`, then the private aux
  `sum_eq_zero_of_mulLeft_mul_const_aux` over a `Semiring` with `IsRightCancelMulZero`. The scalar
  `c = χ₀ g ≠ 1` and the cancellation `eq_zero_of_mul_eq_self_left`. Nothing complex-specific:
  the value lands in `R` via `((χ g : Rˣ) : R)`; the engine only needs `R` to be a right-cancellative
  (mul-by-nonzero) semiring and the separating character to exist.
- **Literature**: column orthogonality holds for characters into any field (or integral domain)
  containing enough roots of unity — Conrad, *Characters of finite abelian groups* §4;
  Washington, *Cyclotomic Fields* ch. 3. The complex case is the textbook default but never the
  natural level of generality.
- **Mathlib**: `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`,
  `HasEnoughRootsOfUnity`, `IsRightCancelMulZero`, `eq_zero_of_mul_eq_self_left`,
  `Group.mulLeft_bijective`. (`IsAlgClosed ⇒ HasEnoughRootsOfUnity` supplies the `ℂ` instance.)
- **Action**: generalise to a commutative ring/field `R` with enough roots of unity:
  ```
  theorem sum_char_apply_eq_zero_of_ne_one {G R : Type*} [CommGroup G] [Finite G]
      [CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]
      [Fintype (G →* Rˣ)] {g : G} (hg : g ≠ 1) : ∑ χ : G →* Rˣ, ((χ g : Rˣ) : R) = 0
  ```
  (`IsDomain` gives `IsRightCancelMulZero`; an even weaker `[Semiring R] [IsRightCancelMulZero R]`
  form is possible if the roots-of-unity hypothesis can be phrased there — `IsDomain` is the safe,
  literature-matching choice.) The project's `ℂ` callers recover it by instance resolution.
- **Difficulty**: **Med** (mechanical hypothesis swap + check the `Units` coercion/`HasEnoughRootsOfUnity`
  instance plumbing typechecks over general `R`; the proof body is unchanged).

### 2. `sum_char_self_eq_zero_of_ne_one` (row orthogonality) — generalise `ℂ → R`

- **Current**: `{G} [CommGroup G] [Fintype G] {χ : G →* ℂˣ} (hχ : χ ≠ 1) :`
  `∑ g : G, ((χ g : ℂˣ) : ℂ) = 0`.
- **proof-only-uses**: a separating *element* `g₀` with `χ g₀ ≠ 1` (from `DFunLike.ne_iff`, no
  roots-of-unity needed here at all), then the same `sum_eq_zero_of_mulLeft_mul_const_aux`. The
  only requirement on the codomain is the right-cancellative-semiring of the aux lemma.
- **Literature**: same as #1; row orthogonality is even more elementary (needs only that the
  character is nontrivial), so it generalises further than the column version — **no**
  `HasEnoughRootsOfUnity` required.
- **Mathlib**: `DFunLike.ne_iff`, `IsRightCancelMulZero`, `eq_zero_of_mul_eq_self_left`.
- **Action**: generalise to any monoid `M` whose unit-coercion lands in a right-cancellative
  semiring `R`:
  ```
  theorem sum_char_self_eq_zero_of_ne_one {G R : Type*} [CommGroup G] [Fintype G]
      [Semiring R] [IsRightCancelMulZero R] {χ : G →* Rˣ} (hχ : χ ≠ 1) :
      ∑ g : G, ((χ g : Rˣ) : R) = 0
  ```
  (Strictly weaker hypotheses than #1 — keep them minimal; this is the maximally general form.)
- **Difficulty**: **Low** (pure hypothesis relaxation; proof body verbatim).

### 3. `card_mul_eq_sum_of_sum_char_mul_eq_zero` (Fourier inversion) — generalise `ℂ → field R`

- **Current**: `{G} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (f : G → ℂ)`
  `(hf : ∀ χ ≠ 1, ∑ s, χ s · f s = 0) (u) : (#(G →* ℂˣ) : ℂ) · f u = ∑ s, f s`.
- **proof-only-uses**: column orthogonality (#1) for the indicator `horth`, `Finset.sum_comm`,
  `map_mul`/`Units.val_mul`, `Finset.sum_eq_single_of_mem`. The *equality* statement itself uses no
  division — it only needs `R` to be a commutative (semi)ring in which #1 holds. So this lemma
  generalises to the **same** hypotheses as #1.
- **Literature**: finite Fourier inversion over any field with enough roots of unity (the
  "average value" identity), Conrad §4, Serre *Linear Representations* §6.
- **Mathlib**: #1 (generalised), `Finset.sum_comm`, `Finset.sum_eq_single_of_mem`,
  `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` (`Nat.card (G →* Mˣ) = Nat.card G`).
- **Action**: same `R` hypotheses as #1:
  ```
  theorem card_mul_eq_sum_of_sum_char_mul_eq_zero {G R : Type*} [CommGroup G] [Fintype G]
      [CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]
      [Fintype (G →* Rˣ)] (f : G → R)
      (hf : ∀ χ : G →* Rˣ, χ ≠ 1 → ∑ s, ((χ s : Rˣ) : R) * f s = 0) (u : G) :
      (Fintype.card (G →* Rˣ) : R) * f u = ∑ s, f s
  ```
- **Difficulty**: **Med** (depends on #1; proof body unchanged once #1 is general).

### 4. `eq_of_sum_char_mul_eq_zero` (vanishing Fourier ⇒ constant) — generalise `ℂ → field R`

- **Current**: `{G} [CommGroup G] [Fintype G] (f : G → ℂ) (hf …) (u u') : f u = f u'`.
- **proof-only-uses**: #3 at `u` and `u'`, then `mul_left_cancel₀` with `(#(G →* ℂˣ) : ℂ) ≠ 0`
  (`Fintype.card_ne_zero`). The **only** place a field (cancellation by the nonzero cardinality) is
  needed: requires `R` to have no zero divisors and `(#dual : R) ≠ 0`. With
  `HasEnoughRootsOfUnity` + `IsDomain` + `CharZero` (or any setting where `#G` is invertible /
  nonzero in `R`), this holds. Over `ℂ` `CharZero` makes `(#dual : ℂ) ≠ 0` automatic.
- **Literature**: the constancy criterion, same references.
- **Mathlib**: #3, `mul_left_cancel₀`, `Fintype.card_ne_zero`, `CharZero`/`Nat.cast_ne_zero`,
  `card_monoidHom_of_hasEnoughRootsOfUnity`.
- **Action**:
  ```
  theorem eq_of_sum_char_mul_eq_zero {G R : Type*} [CommGroup G] [Fintype G]
      [Field R] [HasEnoughRootsOfUnity R (Monoid.exponent G)] [CharZero R]
      (f : G → R) (hf …) (u u' : G) : f u = f u'
  ```
  (Or keep `[CommRing R] [IsDomain R]` and add an explicit `(hcard : (Fintype.card (G →* Rˣ) : R) ≠ 0)`
  hypothesis to avoid baking in `CharZero` — cleaner for non-`CharZero` targets such as finite
  fields where `#G` is coprime to the characteristic. The explicit-`hcard` form is the
  maximally-general one.)
- **Difficulty**: **Med** (needs the `(#dual : R) ≠ 0` side-condition routed correctly; small).

### 5. `sum_eq_zero_of_mulLeft_mul_const_aux` (private engine) — ALREADY maximally general ✅

- **Current**: `{H} [Group H] [Fintype H] {M₀} [Semiring M₀] [IsRightCancelMulZero M₀] …`.
- Already stated over an arbitrary finite group and the weakest sensible ring class
  (`Semiring` + `IsRightCancelMulZero`). **No generalisation needed** — this is the reference for
  how general #1–#4 *should* be. (It is itself plausibly mathlib-worthy as a standalone
  "scaling by a non-one factor forces the sum to zero" lemma.)
- **Difficulty**: n/a (no action).

---

## B. `ForMathlib/NormLeOneLipschitz.lean` — generic metric/normed helpers over-specialised

The bulk of this file (`expMapBasis`/`faceMap*`/`frontierCoverFamily`/`liftToMixed`/the three
`normLeOne_frontier_lipschitz_cover*`) is genuinely number-field-specific (heavy `paramSet`,
`compactSet`, `normAtAllPlaces`, `mixedEmbedding.stdBasis`) and correctly so. But four small helpers
are stated more narrowly than their proofs need.

### 6. `lipschitzWith_one_of_edist_apply_le` (private) — generalise `1 → K`; mathlib gap

- **Current**: `{α κ} {β : κ → Type*} [PseudoEMetricSpace α] [∀ j, PseudoEMetricSpace (β j)]`
  `[Fintype κ] {F : α → ∀ j, β j} (h : ∀ c d j, edist (F c j) (F d j) ≤ edist c d) : LipschitzWith 1 F`.
- **proof-only-uses**: `LipschitzWith.of_edist_le` + `edist_pi_def` + `Finset.sup_le`. The constant
  `1` is hard-coded but never used as `1` — the same proof gives `LipschitzWith K F` from
  `edist (F c j) (F d j) ≤ K * edist c d`.
- **Literature**: the standard "a map into a finite product is `K`-Lipschitz iff each coordinate
  is" fact. The codomain-pi companion of `LipschitzWith.eval`.
- **Mathlib**: `LipschitzWith.eval` (1-Lipschitz *projection from* a finite pi) **exists**
  (`Mathlib/Topology/EMetricSpace/Lipschitz`), but — **verified by WebFetch** — there is **no**
  `LipschitzWith.pi` / `lipschitzWith_pi` proving a map *into* a finite pi is Lipschitz from
  coordinatewise bounds. So this fills a real gap and should be added in the general `K` form.
- **Action**:
  ```
  theorem LipschitzWith.pi {α κ} {β : κ → Type*} [PseudoEMetricSpace α]
      [∀ j, PseudoEMetricSpace (β j)] [Fintype κ] {K : ℝ≥0} {F : α → ∀ j, β j}
      (h : ∀ j, LipschitzWith K (fun a => F a j)) : LipschitzWith K F
  ```
  (state it via per-coordinate `LipschitzWith K` to match `LipschitzWith.eval`'s phrasing; keep the
  current `edist`-bound form as a corollary). Name it `LipschitzWith.pi` and contribute next to
  `LipschitzWith.eval`. Current callers (`lipschitzWith_clampUnit`, `lipschitzWith_cubeRelabel`)
  use `K = 1`, recovered trivially.
- **Difficulty**: **Low** (proof is the same three lines with `K` threaded through `Finset.sup_le`).

### 7. `dist_mul_le_norm_mul_dist` — already general (`NormedField`) but verify against mathlib

- **Current**: `{α} [NormedField α] (a b u v : α) : dist (a*u) (b*v) ≤ ‖a‖ * dist u v + ‖v‖ * dist a b`.
- **proof-only-uses**: `dist_eq_norm`, the algebraic split `a*u − b*v = a*(u−v) + (a−b)*v`,
  `norm_add_le`, `norm_mul`. **Only uses** `norm_mul` (submultiplicativity as equality) — so it
  already works over any `NormedRing`/`NormedDivisionRing`, not just `NormedField`; `NormedField` is
  marginally too strong (`norm_mul` equality holds in `NormedDivisionRing`; even `‖a*b‖ ≤ ‖a‖‖b‖`
  of a `NormedRing` suffices to get a `≤`).
- **Literature**: standard product-perturbation estimate, valid in any normed ring.
- **Mathlib**: **verified by WebFetch** — no two-variable product-distance bound
  (`dist (a*u) (b*v) ≤ …`) exists in `Normed/Field/Basic`. Related: `norm_mul`, `dist_eq_norm`,
  `norm_add_le`. Genuinely contributable; widen the class first.
- **Action**: relax to a normed ring (keeping the equality-form bound needs `‖·*·‖ = ‖·‖‖·‖`, i.e.
  `NormedDivisionRing`; the `≤`-form generalises to `NormedRing`):
  ```
  theorem dist_mul_le_norm_mul_dist {α} [NormedDivisionRing α] (a b u v : α) :
      dist (a * u) (b * v) ≤ ‖a‖ * dist u v + ‖v‖ * dist a b
  ```
- **Difficulty**: **Low** (swap the class; proof unchanged — `norm_mul` holds in
  `NormedDivisionRing`). First confirm no near-duplicate at PR time.

### 8. `lipschitzWith_exp_ofReal_mul_I` — thin specialisation of `lipschitzWith_circleMap`

- **Current**: `LipschitzWith 1 (fun t : ℝ ↦ Complex.exp ((t:ℂ) * Complex.I))`.
- **proof-only-uses**: identifies the map with `circleMap 0 1` and applies
  `lipschitzWith_circleMap 0 1` (`|R| = 1`). So it is *already* a one-line consequence of mathlib.
- **Literature**: the unit-circle parametrization is `circleMap 0 1`; nothing more general to say.
- **Mathlib**: `lipschitzWith_circleMap (c R) : LipschitzWith R.nnabs (circleMap c R)` **exists**
  (`Mathlib/MeasureTheory/Integral/CircleIntegral`). This is dedup, not generalisation.
- **Action**: do **not** contribute as-is; either inline at the single call site
  (`lipschitzWith_phase`) or, if a named `t ↦ exp(t·I)` lemma is wanted, add it as a trivial
  `simp`-backed corollary of `lipschitzWith_circleMap`. (Flag for the dedup lane rather than the
  generalise lane.)
- **Difficulty**: **Low** (it is already proved from mathlib; this is a keep-or-inline call).

### 9. `clampUnit` / `lipschitzWith_clampUnit` — hard-wired unit cube `[0,1]`; generalise to a box

- **Current**: `clampUnit (ι) (c : ι → ℝ) : ι → ℝ := fun i ↦ Set.projIcc 0 1 zero_le_one (c i)`;
  `lipschitzWith_clampUnit (ι) [Fintype ι] : LipschitzWith 1 (clampUnit ι)`.
- **proof-only-uses**: coordinatewise `Set.projIcc 0 1`, `LipschitzWith.projIcc`,
  `edist_le_pi_edist`, and (#6). The endpoints `0`/`1` are never used as anything but interval
  endpoints — the construction works for an arbitrary box `Icc a b` (`a b : ι → ℝ`, `a ≤ b`).
- **Literature**: the nearest-point retraction onto a box / pi-Icc — a standard order-theoretic
  projection.
- **Mathlib**: `Set.projIcc` + `LipschitzWith.projIcc` (scalar, 1-Lipschitz) **exist**
  (`Mathlib/Order/Interval/Set/ProjIcc`); **verified by WebSearch** there is **no** pi/box version
  (`Set.piIcc` / a packaged `clampUnit`). A general "project onto `Icc a b` in `ι → ℝ`" def is a
  reasonable small addition.
- **Action**: generalise the def to arbitrary endpoints and keep the unit cube as the `a=0,b=1`
  instance:
  ```
  def projPiIcc {ι} (a b : ι → ℝ) (h : ∀ i, a i ≤ b i) (c : ι → ℝ) : ι → ℝ :=
    fun i ↦ Set.projIcc (a i) (b i) (h i) (c i)
  theorem lipschitzWith_projPiIcc {ι} [Fintype ι] (a b …) : LipschitzWith 1 (projPiIcc a b h)
  ```
  (`clampUnit ι = projPiIcc 0 1 _`.) Names should drop the `Chebotarev`-leaf style for a mathlib
  `Set`/`Pi` namespace.
- **Difficulty**: **Low** (mechanical; the only subtlety is the `h : ∀ i, a i ≤ b i` argument and a
  membership-lemma `projPiIcc_mem_Icc`).

### 10. `exists_phase_mem_Icc_mul_exp` — keep; interval-normalization is the specific part

- **Current**: `(z : ℂ) : ∃ θ ∈ Icc (0:ℝ) 1, (‖z‖:ℂ) * exp((2πθ − π)·I) = z`.
- **proof-only-uses**: `Complex.norm_mul_exp_arg_mul_I` (mathlib) + the affine renormalization
  `θ = (arg z + π)/(2π)` to land in `[0,1]`.
- **Literature**: polar form; the `[0,1]`-normalization is a packaging choice for the cube-cover
  caller, not a general statement.
- **Mathlib**: core is `Complex.norm_mul_exp_arg_mul_I`; the `[0,1]` repackaging is
  Chebotarev-shaped. Low generalisation value.
- **Action**: keep as-is (or, if upstreamed, present as a corollary of
  `Complex.norm_mul_exp_arg_mul_I`). Not a generalisation target.
- **Difficulty**: n/a (no action recommended).

---

## C. `ForMathlib/LatticePointCount.lean` — `Fintype ι` already; one real axis (concrete lattice)

These decls are stated for `ι : Type*` `[Fintype ι]` over the sup-metric `ι → ℝ` — already the
right level for a `BoxIntegral.unitPartition`-adjacent contribution. The `Chebotarev` namespace
must be stripped on contribution, but that is naming, not generality. Two genuine observations:

### 11. Concrete standard lattice `span ℤ (range (Pi.basisFun ℝ ι))` → abstract `ZLattice`?

- **Current**: `abs_card_inter_sub_volume_mul_pow_le` /
  `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` count points of
  `(n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))` — the *standard* integer lattice.
- **proof-only-uses**: the `BoxIntegral.unitPartition` `index`/`tag`/`box` API, which is itself
  built around the standard lattice and the unit grid (`tag_mem_smul_span`, `index_tag`,
  `mem_box_iff_index`, `volume_box`, `setFinite_index`). The argument is **intrinsically** tied to
  the standard cubical grid; an arbitrary `ZLattice` would require an affine change of variables.
- **Literature**: Lang GTM 110 Ch. VI §3 and Gun–Ramaré–Sivaraman §3.5 state the boundary-cell
  count for a general lattice via the linear map carrying it to `ℤ^d` (the count picks up a
  `covolume` factor). The downstream `IdealCongruenceCount.lean` already performs exactly this
  change of variables (`map_span_int_linearEquiv`, `covolume_image_basisFun_eq_abs_det`,
  `smul_chart_lattice_eq`) **on top of** these standard-lattice lemmas.
- **Mathlib**: `ZLattice`, `ZLattice.covolume`, `Pi.basisFun`, `BoxIntegral.unitPartition.index`,
  `tendsto_card_div_pow_atTop_volume` (the rate-free version, also stated for the standard grid).
- **Action**: **keep the standard-lattice statement** for these `unitPartition`-level lemmas (they
  belong beside the existing standard-grid `index` API), and — if a general-`ZLattice` effective
  count is wanted in mathlib — add it as a *separate* wrapper that conjugates by the basis
  `LinearEquiv` (mirroring `IdealCongruenceCount`'s own transfer), rather than re-stating these.
  Listed here for completeness; **not** a forced change.
- **Difficulty**: **High** (the abstract-lattice version is real new work — a change-of-variables
  layer — not a hypothesis swap; better as a follow-up lemma than a generalisation of these).

### 12. `ceil_natCast_mul_le_ceil_natCast_mul_add`, `abs_sub_le_one_div_of_ceil_natCast_mul_eq` — keep

- **Current**: ceiling-subadditivity (`a ≤ b+r ⇒ ⌈n·a⌉ ≤ ⌈n·b⌉+⌈n·r⌉`) and the `1/n`-cell-diameter
  bound, both for `n : ℕ`, reals.
- **proof-only-uses**: `Int.ceil_le_ceil`, `Int.ceil_add_le`, `Int.le_ceil`, `Int.ceil_lt_add_one`,
  `Nat.cast_nonneg`. The `n : ℕ` is used only for `(n:ℝ) ≥ 0`; could be a general nonneg real
  scalar `(0 ≤ t)` instead of `(n:ℝ)`.
- **Literature**: elementary ceiling arithmetic.
- **Mathlib**: `Int.ceil_add_le`, `Int.ceil_le_ceil` (these are the general ceiling lemmas).
- **Action**: optionally generalise the scalar `(n:ℝ)` to an arbitrary `0 ≤ t : ℝ` (then the
  `n`-instances are special cases), but the gain is marginal and the names are `n`-specific by
  design. Low priority; flag only if these are contributed standalone (likely they are inlined).
- **Difficulty**: **Low** (scalar generalisation), but **low value** — recommend keep/inline.

All other `LatticePointCount` decls (`setFinite_index_image_of_isBounded`,
`ncard_index_image_le_of_diam_le`, `ncard_index_image_chart_le`, `ncard_index_image_frontier_le`,
`measureReal_biUnion_box`, `index_mem_image_frontier_of_box_meet_not_subset`) are appropriately
general (`Fintype ι`, sup-metric `ι → ℝ`) and need only namespace-stripping — no generalisation.

---

## D. `ForMathlib/LogOneDivSubOne.lean` — elementary squeeze vs `IsEquivalent` (dedup, not generalise)

### 13. `tendsto_ratio_one_of_div_atTop_pm_bounded` — could generalise, but author chose elementary form

- **Current**: `{l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop)`
  `(h_le : ∃ C, ∀ᶠ s in l, f s ≤ g s + C) (h_lower : ∃ C, ∀ᶠ s in l, g s − C ≤ f s) :`
  `Tendsto (fun s ↦ f s / g s) l (𝓝 1)`.
- **proof-only-uses**: `tendsto_bdd_div_atTop_nhds_zero`, `add_div_eq_mul_add_div`,
  `hg.eventually_gt_atTop 0`. Purely `ℝ`-ordered-field arithmetic.
- **Literature**: this is `f ~[l] g` (`Asymptotics.IsEquivalent`) under a divergent denominator;
  `isEquivalent_iff_tendsto_one` packages `u ~ v ↔ Tendsto (u/v) l (𝓝 1)`.
- **Mathlib**: `Asymptotics.IsEquivalent`, `isEquivalent_iff_tendsto_one`,
  `tendsto_bdd_div_atTop_nhds_zero`, `isLittleO_one_left_iff` — **the file's own docstring already
  cites these** and explains the deliberate choice of the elementary `∃C, ∀ᶠ` form to match
  caller-produced hypotheses.
- **Action**: **not a generalisation target** — it is a (mild) restatement/dedup question. Two
  options at PR time: (a) keep the elementary form (author's stated rationale) and contribute it as
  a convenience lemma feeding `IsEquivalent`; or (b) prove it *via* `IsEquivalent` to reduce the
  proof. A genuine generality axis exists (replace `ℝ` codomain by a `LinearOrderedField` with the
  right order-topology, or state over `𝓝[>]`-agnostic `g`), but the value is low and the
  `tendsto_bdd_div_atTop_nhds_zero` dependency is `ℝ`-flavoured. Recommend: leave to the dedup lane.
- **Difficulty**: **Med** if routed through `IsEquivalent` (restructure); **Low** if kept. Not
  primarily a generalisation.

### 14. `tendsto_log_one_div_sub_one_atTop`, `tendsto_ratio_one_of_log_pm_bounded` — keep (thin composites)

- Both are very specific (`log(1/(s−1))` at `1⁺`) and are thin composites of existing mathlib
  (`Real.tendsto_log_atTop`, `Tendsto.inv_tendsto_nhdsGT_zero` — both **confirmed** in
  `SpecialFunctions/Log/Basic` / the order-field topology API) plus #13. No generalisation; the
  specialisation is the point. (Mathlib-overlap/dedup question, not generality.)
- **Difficulty**: n/a (no generalisation action).

---

## E. `ForMathlib/IdealCongruenceCount.lean` — mostly number-field-specific; helpers already general

This 3400-line file is ~73 `private` helpers driving the class-field-theory-free Chebotarev count.
The **inventory's own caveat** (lines 1068–1071) already flags the right principle: several private
helpers are stated only for `index K → ℝ` / specific number-field charts but are mathematically
generic (lattice / `Submodule` / `Finset` / analysis level). Spot-checking the candidates:

- `crt_single_coset` (`{ι} [Finite ι]`, abstract `Submodule ℤ (ι → ℝ)`, coprime-order CRT) —
  **already general** (`Finite ι`, abstract submodules); only the ambient `ι → ℝ` is concrete, and
  the proof uses `QuotientAddGroup`/`nsmul_right_bijective` generically. Could move from `ι → ℝ` to
  an arbitrary `ℝ`-module / additive group, but value is low (it is a private CRT step). **Low**.
- `exists_lipschitz_cover_union`, `exists_lipschitz_cover_iUnion` (`{ι} [Fintype ι]`,
  `{γ} [Finite γ]`) — **already general** in `ι`, `γ`; concrete only in the `ι → ℝ` cube cover,
  which is intrinsic to the `LatticePointCount` `hlip` interface they feed. No change.
- `frontier_signOrthant_subset` (`{ι κ} [Finite κ]`, arbitrary index map `g : κ → ι`) —
  **already general**. No change.
- `span_image_basisFun_eq`, `covolume_image_basisFun_eq_abs_det`, `image_range_basisFun_eq`,
  `smul_chart_lattice_eq` (`{ι} [Finite ι]`/`[Fintype ι]`) — generic linear-algebra/`ZLattice`
  facts already at `Fintype ι`; the `Pi.basisFun` concreteness matches their purpose. Candidates to
  generalise to an abstract basis, but they are private plumbing for the standard chart. **Low /
  low-value**.
- The `natCast_algebraNorm_*`, `norm_eq_prod_real_emb_*`, `relIndex_*_eq_absNorm`,
  `prod_eq_neg_one_pow_card_mul_prod_abs` family — generic `Algebra.norm` / `Ideal.absNorm` /
  `InfinitePlace` identities; flagged by the inventory as "check for existing forms." That is a
  **dedup/mathlibable** question (does mathlib already have them?), not a generality one.

**Net for this file**: no high-value *generalisation* opportunities beyond namespace/`Fintype`
hygiene already noted; the private helpers are either already maximally general for their role or
are dedup candidates. The real generalisation wins live in files A and B.

---

## Summary

**Total generalisation opportunities: 11 actionable** (entries 1–4, 6, 7, 9 as primary;
12, 13 marginal; 11 as a high-effort follow-up; plus entries 5, 8, 10, 14 explicitly assessed as
**no-action** / dedup — listed for completeness).

Split by difficulty (actionable only):
- **Low: 5** — #2 (row orthogonality `ℂ→R`), #6 (`LipschitzWith.pi`, `1→K`), #7
  (`dist_mul_le` `NormedField→NormedDivisionRing`), #9 (`clampUnit`→general box `projPiIcc`),
  #12 (ceiling scalar `n→t`, low value).
- **Med: 5** — #1 (column orthogonality `ℂ→R`), #3 (Fourier inversion `ℂ→R`), #4 (constancy
  `ℂ→R`), #13 (ratio-squeeze via `IsEquivalent`, mostly dedup).
- **High: 1** — #11 (`LatticePointCount` standard lattice → abstract `ZLattice`; a
  change-of-variables layer, better as a new wrapper than a restatement).

**Top 5 (all ForMathlib):**
1. **#1 `sum_char_apply_eq_zero_of_ne_one`** — drop `ℂ`, use `[CommRing R] [IsDomain R]`
   `[HasEnoughRootsOfUnity R (Monoid.exponent G)]`. The proof already calls the general
   `exists_apply_ne_one_of_hasEnoughRootsOfUnity`; `ℂ` is used only for the instance. **Med.**
2. **#2 `sum_char_self_eq_zero_of_ne_one`** — even weaker: any `[Semiring R] [IsRightCancelMulZero R]`
   (row orthogonality needs no roots of unity). Verbatim proof. **Low.**
3. **#6 `lipschitzWith_one_of_edist_apply_le` → `LipschitzWith.pi`** — generalise `1→K`; fills a
   confirmed mathlib gap (only `LipschitzWith.eval` exists, not the into-pi direction). **Low.**
4. **#3 + #4 Fourier inversion** (`card_mul_eq_sum_…`, `eq_of_sum_char_mul_eq_zero`) — same `ℂ→R`
   generalisation as #1, with #4 needing an explicit `(#dual : R) ≠ 0` side-condition for the
   maximally-general (non-`CharZero`) form. **Med.**
5. **#7 `dist_mul_le_norm_mul_dist`** + **#9 `clampUnit`** — two clean Low-difficulty normed/metric
   additions: relax `NormedField → NormedDivisionRing`; lift the unit-cube clamp to a general box
   `projPiIcc` (mathlib has scalar `LipschitzWith.projIcc` but no pi/box version). **Low.**

**Cross-cutting recommendation**: items #5, #8, #10, #14 are **not** generalisation work —
#8/#14 are dedup against `lipschitzWith_circleMap` / `IsEquivalent` (route to the dedup lane), and
#5/#10 are already optimal. The character-orthogonality block (A) is the single highest-value
target: four new-to-mathlib theorems currently pinned to `ℂ` that the proofs show need only
`HasEnoughRootsOfUnity`.

**Output path**:
`/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/Chebotarev/.mathlib-quality/overview/analysis/06-generalization.md`

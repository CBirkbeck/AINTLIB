# Decomposition — BB-QF `mulByHom_locallyQuasiFinite` (Torsion.lean) — STREAM-G0

**Re-run 2026-07-14 (adversarial `--decompose`, v10.219 de-confliction).** Target:
`LocallyQuasiFinite (E.mulByHom N)` for `N ≠ 0`, ANY base `S`, ANY characteristic. This re-run
supersedes the optimistic 7-leaf pass (QF-L1..L7, in git history): it **banks the mathlib-criterion
reduction as real proved code**, and it re-classifies the geometric leaf against verified mathlib
coverage.

**De-confliction constraint (owner v10.219):** G0 owns quasi-finiteness + flatness; KM owns the exact
`deg = N²` (`mulByHom_finrank`, Torsion.lean, sorry). This decomposition **must not** route through
`mulByHom_finrank`. It does not (the only degree-free nonconstancy source is HasseWeil's torsion
witness — see QF-NONCONST attack log).

## Skeleton location (Step 2.5 — written + `lake build`-clean, sorries-only)
`projects/ModularCurves/ModularCurves/EllipticCurve/Torsion.lean`:
- **`mulByHom_finite_fibres (N) [NeZero N] (x : E.E) : (⇑(E.mulByHom N).base ⁻¹' {x}).Finite := by sorry`**
  — the GATED geometric leaf (QF-FIBFIN). The single remaining BB-QF sorry.
- **`mulByHom_locallyQuasiFinite (N) [NeZero N] : LocallyQuasiFinite (E.mulByHom N)`**
  — **PROVED** (reduction half). Body: `LocallyQuasiFinite.of_finite_preimage_singleton _
  (fun x => E.mulByHom_finite_fibres N x)`. Zero sorry in its own body; `#print axioms` =
  {propext, Classical.choice, Quot.sound, **sorryAx**} where sorryAx is transitively from the leaf.
  File-wide `lean_diagnostic_messages severity=error` → **empty** (verified 2026-07-14).

## Plain-English proof (KM 2.3.1 fibre route, transcribed)
KM 2.3.1 proves `[N] : E → E` is finite locally free of rank `N²`. Quasi-finiteness (the BB-QF
slice) is the fibre input of that proof: `[N]` is proper (an `S`-endomorphism of the proper `E/S`),
so by ZMT `finite ⟺ quasi-finite`; quasi-finiteness is checked **geometric fibre by geometric
fibre** — on `E_{k̄}` (an elliptic curve over an algebraically closed field) `[N]` is **nonconstant**
for `N ≥ 1`, and a nonconstant morphism of proper smooth curves has finite (`0`-dimensional) fibres.
In mathlib terms: `[N]` is locally of finite type (proper ⟹ lft), so LQF ⟺ every topological fibre
`[N]⁻¹{x}` is finite (`locallyQuasiFinite_iff_finite_preimage_singleton`); the fibre sits inside the
curve `E_s` (`s = π x`), on which `[N]_s` is a proper (closed) nonconstant map, so the fibre is a
proper closed subset of an integral dim-1 scheme, hence dim `≤ 0`, hence artinian, hence finite.

**Source note:** the KM PDF (`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, 526 pp.) has
**no text layer** (djvu-derived; `pdftotext` yields zero matches), so a copy-paste verbatim quote is
not extractable. The project's source-of-record transcription of KM 2.3.1's proof is quoted verbatim
per leaf below (from `black-box-plan.md` §BB-QF and the Torsion.lean docstrings — the established
in-repo authority for this box).

## Leaf tree (re-classified)

### [QF-REDUCE] (leaf, mathlib) — **DISCHARGED, banked in Torsion.lean**
- Lean: `mulByHom_locallyQuasiFinite` (proved) consuming `mulByHom_finite_fibres`.
- Discharged by (verified via `lean_multi_attempt` + file-wide error-free diagnostic):
  - `AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton`
    (QuasiFinite.lean:296): `[LocallyOfFiniteType f] → (∀ x, (f ⁻¹' {x}).Finite) → LocallyQuasiFinite f`.
  - `LocallyOfFiniteType (E.mulByHom N)` — **free by `inferInstance`**: `IsProper` *extends*
    `LocallyOfFiniteType` (mathlib `Proper.lean:42`), and `mulByHom_isProper` is an `instance`.
- Source-of-record quote (Torsion.lean docstring, KM 2.3.1 first reduction): *"Because `E` is proper
  over `S`, any `S`-endomorphism of `E` is proper."* Lean↔source: `mulByHom_isProper` is exactly this;
  the extends-chain hands us `LocallyOfFiniteType` for the criterion.
- **Attacks attempted:**
  - [1] Discharge attack: `of_finite_preimage_singleton` type checked by editing the real body and
    reading `lean_diagnostic_messages` — `mulByHom_locallyQuasiFinite` elaborates with **no error**,
    confirming both the instance resolution and the fibre-notation unification
    `(⇑(E.mulByHom N).base ⁻¹' {x})` ≡ criterion's `f ⁻¹' {x}`. SURVIVED.
  - [2] Instance attack: is `LocallyOfFiniteType` really free? `Proper.lean:42`
    `class IsProper extends IsSeparated, UniversallyClosed, LocallyOfFiniteType` — yes, extends-instance.
    `mulByHom_isProper` is `instance`, not `theorem` — synthesises. SURVIVED.
  - [3] Hypothesis attack: `of_finite_preimage_singleton` needs only `[LocallyOfFiniteType]` (NOT
    `[QuasiCompact]`, unlike the `iff` form at :318) — so the reduction needs strictly less. Minimal.
    SURVIVED.
- Verdict: **true leaf, discharged from mathlib, banked as real proved code.**

### [QF-FIBFIN] (internal — the substance) `mulByHom_finite_fibres` — **GATED (not ready)**
`∀ x, ([N]⁻¹{x}).Finite`. Decomposes into a dimension/finiteness half (now largely mathlib-backed)
and a **nonconstancy half that is the decisive wall**.

- Source-of-record quote (`black-box-plan.md` §BB-QF, verbatim):
  > "on an elliptic curve over a field, `[N]` is nonconstant, hence has finite fibres; so `[N] : E → E`
  > is locally quasi-finite."
  and its route: *"1. `[N]` over an algebraically closed field is nonconstant for `N ≥ 1` … 2.
  nonconstant morphism of curves ⟹ finite fibres … 3. spread out to `LocallyQuasiFinite` via the
  fibre criterion … **Depends on** T-B6 (fibre comparison, stream-B)."*
- Lean↔source: `mulByHom_finite_fibres` is step-2's "finite fibres"; `[QF-REDUCE]` is step 3;
  steps 1–2's geometric content is the sub-leaves below.

#### [QF-DIM] (sub-leaf, dimension/finiteness) — **BOUNDED, mathlib-backed (refined this pass)**
"A proper closed subset of an integral Noetherian dim-1 scheme over a field is finite." The prior
pass feared this a "ringKrullDim mathlib-hunt"; **verified this pass that mathlib already carries the
scaffolding**:
- `AlgebraicGeometry.IsArtinianScheme.finite` : `[IsArtinianScheme X] → Finite X`.
- `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero` :
  `[IsLocallyNoetherian X] → topologicalKrullDim X ≤ 0 → IsLocallyArtinian X`.
- `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible`,
  `isArtinianRing_iff_krullDimLE_zero`.
- **Attacks attempted:**
  - [1] Existence attack: all five decls returned by `lean_leansearch` at the stated types. SURVIVED.
  - [2] Composition attack: chaining these gives "Noetherian dim-0 ⟹ finite". The gap is the INPUT
    `topologicalKrullDim ([N]⁻¹{x}) ≤ 0`, which needs (a) `E_s` integral of dim 1 and (b) the fibre a
    PROPER closed subset. (a) needs a **relative-dim-1 ⟹ fibre-dim-1 bridge** (`SmoothOfRelativeDimension
    1 E.π` ⟹ `topologicalKrullDim (E_s) = 1`) — partial mathlib support, a real but bounded assembly;
    (b) is nonconstancy = the wall below. So QF-DIM is bounded ONLY relative to QF-NONCONST. FLAW: not
    standalone. Recorded.
  - [3] Edge attack: `N = 1` ⟹ `[1] = id`, fibres singletons (finite) — consistent. Char `p ∣ N`: the
    topological argument is char-uniform (no separability used). SURVIVED.
- Verdict: **bounded (mathlib scaffolding present + a rel-dim→fibre-dim bridge), but consumes
  QF-NONCONST.**

#### [QF-NONCONST] (sub-leaf, nonconstancy witness) — **WALL: gated on T-B6**
`[N]_s` is nonconstant, i.e. the fibre `[N]⁻¹{x}` is a PROPER subset of `E_s` (not all of it).
Equivalently `[N]_s ≠ 0`, i.e. `∃ P ∈ E_s, N·P ≠ 0`.
- **Only two sources of this witness exist, and both are walls under the constraints:**
  1. **The degree** `mulByInt_degree = N² ≠ 0 ⟹ [N] ≠ 0` (KM's `mulByHom_finrank`) — **FORBIDDEN by
     de-confliction** (KM's box).
  2. **HasseWeil's torsion witness** `card_torsion_ellPow_nat` / `torsion_ellPow_finite`
     (`#E[ℓⁿ] = ℓ²ⁿ`, `ℓ ≠ char`, `TorsionPowStructure.lean` **0-sorry**) ⟹ `∃ P, N·P ≠ 0` — degree-free
     (**satisfies de-confliction**), stated for `WeierstrassCurve.Point` over a field. Transporting it to
     `E_s` needs a **pointed** comparison `E_s ↔ modelEllipticCurve W_s` carrying scheme-`[N]` →
     model-`[N]`. **WALL-BREAK (2026-07-14, correcting an earlier "gated" verdict):** a *pointed*
     comparison does NOT need the sorried existence box `abelEnrichment_exists` — it needs only
     **uniqueness/rigidity**, which IS proven: `abelEnrichment_unique_of_isLocallyNoetherian`
     (`Rigidity.lean:1577`, PROVEN) + GIT 6.4 `isMonHom_of_one_comp_eq'` (PROVEN, used
     `EndomorphismDegree.lean:70`) upgrades any pointed morphism of group objects to a monoid hom, and
     `mulBy_comp_of_isMonHom` (**PROVEN**, `MulByHomFibres.lean`) conjugates `[N]`. The pointed iso itself
     is `localModel` (real atlas field, `ModelRecord.lean:76 := locallyWeierstrass_projModel W`). So the
     transport is **sound with proven foundations — no existence box, no stream-B T-B6.**
- Source-of-record quote (`black-box-plan.md` §BB-DIFF L-B, verbatim): *"a group-compatible scheme-fibre
  ↔ `WeierstrassCurve k̄` comparison `E.baseChange t ≅ projModel W_k̄` carrying scheme-`[N]`→Weierstrass-`[N]`.
  Does not exist anywhere … the group-compat leg is transitively gated on the sorried
  `abelEnrichment_exists` … This is the registered T-B6 fibre-comparison box (stream-B)."*
- **Attacks attempted:**
  - [1] "Third source" attack: can nonconstancy come from `SmoothOfRelativeDimension 1` directly? A
    constant `[N]_s` would force `E_s = E_s[N]`; but "`E_s[N]` finite" is exactly `torsionπ_isFinite`
    ⟸ `mulByHom_isFinite` ⟸ this very LQF — **CIRCULAR**. Attack fails to find a third source. WALL holds.
  - [2] "Avoid transport" attack: can I run the whole fibre argument WITHOUT the model iso, using only
    `[N]_s` a group-scheme endo? Nonconstancy of an abstract group-scheme endo is not derivable without
    either its degree or a point-witness; the point-witness lives in the model (HasseWeil). No dodge.
    WALL holds.
  - [3] `mulByHom_surjective` attack: it is proved (`MulByHomDegree.lean:180`) and degree-free-ish
    (`one_le_finrank_iff_surjective`), giving nonconstancy at field/model level. Applying it to `E_s`
    needs the SAME pointed transport — which the wall-break above supplies. Consistent.
  - **[4] WALL-BREAK (the attack that succeeded against my own "gated" verdict):** the "T-B6 transport"
    was assumed to need the sorried `abelEnrichment_exists`. FALSE for a *pointed* comparison — rigidity
    (`abelEnrichment_unique_of_isLocallyNoetherian` + GIT 6.4, both PROVEN) suffices, and
    `mulBy_comp_of_isMonHom` (PROVEN) conjugates `[N]`. Foundations verified 0-sorry (see source-2 bullet).
- Verdict: **NOT a wall. `QF-NONCONST` has a SOUND degree-free route with proven foundations (pointed
  comparison via rigidity, not existence). What remains is a real multi-lemma BUILD (the model
  fibre-count + the transport assembly), tracked in `MulByHomFibres.lean` — not a gate.**

## Confidence gate (Step 5) — **DOES NOT PASS**
1. Every leaf discharged/gap-classified: ✓ (`QF-REDUCE` mathlib-discharged; `QF-DIM` bounded-mathlib;
   `QF-NONCONST` T-B6-gated).
2. Skeleton compiles: ✓ (`lake build`/diagnostics error-free; sorries only).
3. Verbatim source quote per leaf: ✓ (source-of-record; KM PDF text-layer absent — noted).
4. Adversarial pass every node: ✓ (attack logs above).
5. Prior-B2 log: no BB-QF entry by name/shape (`b2_log.jsonl` checked).
6. Mirrors source structure: ✓ (KM 2.3.1 fibre-by-fibre; `black-box-plan.md` "**Depends on T-B6**").
7. Single-conclusion: ✓.
- **STATUS (corrected 2026-07-14): no T-B6 gate.** `QF-REDUCE` banked; `QF-NONCONST` + `QF-DIM` are a
  sound degree-free BUILD (foundations proven/verified 0-sorry) tracked in `MulByHomFibres.lean` — a
  real multi-lemma frontier (model fibre-count + transport), NOT a gated/REVIEW-PENDING leaf. Ready for
  ticket creation as a build (not blocked on another stream).

## Feasibility verdict (CORRECTED 2026-07-14 — supersedes the "gated" reading)
**BB-QF is dischargeable in-project via a sound degree-free route; a real multi-lemma build remains,
but it is NOT gated on another stream.** The earlier verdict this pass ("gated on T-B6, rooted in the
sorried `abelEnrichment_exists`") was **wrong** — it conflated the *existence* box with the *pointed
comparison* the fibre argument actually needs. Corrected picture, foundations all verified 0-sorry:
1. **`QF-REDUCE`** — banked as proved code (`mulByHom_locallyQuasiFinite`); `IsProper`⟹`LocallyOfFiniteType`.
2. **The pointed field-fibre comparison** `E_s ↔ modelEllipticCurve W_s` intertwining `[N]` needs only
   **rigidity** (`abelEnrichment_unique_of_isLocallyNoetherian` PROVEN + GIT 6.4 PROVEN) +
   power-naturality (`mulBy_comp_of_isMonHom` PROVEN) + `localModel` (real atlas field) — **NO existence
   box, NO stream-B T-B6.**
3. **The model fibre-count** is field-level and degree-free: HasseWeil `card_torsion_ellPow_nat` (0-sorry)
   ⟹ `[N]`-image infinite ⟹ fibres proper closed in the integral `zChart` curve (dim ≤ 1, Krull PIT) ⟹
   finite (`IsArtinianScheme.finite`; `topologicalKrullDim → IsLocallyArtinian → Finite`, mathlib-present).
**Remaining work = a genuine multi-lemma BUILD** (the model fibre-count [Krull-PIT dim≤1 + Jacobson +
HasseWeil density] and the transport assembly), being built in `MulByHomFibres.lean` (power-naturality
already landed). This is G0-ownable frontier, not a cross-stream block — it **refutes** the
`black-box-plan.md` GATING CORRECTION's claim that BB-QF needs stream-B's T-B6 to land. On completion,
`mulByHom_finite_fibres` closes ⟹ the banked `QF-REDUCE` gives `mulByHom_locallyQuasiFinite` axiom-clean
⟹ the whole E[N]-finiteness trail (`mulByHom_isFinite` → `torsionπ_isFinite`).

## Consumers on discharge
Discharging `mulByHom_finite_fibres` makes `mulByHom_locallyQuasiFinite` axiom-clean, which closes
`mulByHom_isFinite` (Torsion.lean, proper + LQF via ZMT) ⟹ `torsionπ_isFinite` real ⟹ the E[N]
finite-locally-free package + the SIGNAL/Y₀(N) finiteness trail auto-clean (BB-QF eliminated from the
register). BB-QF and BB-FLAT (G0) + BB-DEG (KM) then jointly retire the T-B4 = KM-2.3.1 assumption.

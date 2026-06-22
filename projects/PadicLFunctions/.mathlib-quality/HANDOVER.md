# HANDOVER — §13.2 Vandiver IMC (RJW arXiv:2309.15692), `dev/padic`

*Written 2026-06-22, at the close of the §13.2 Galois-foundation work cycle. Supersedes the
2026-06-10 handover (the pre-AINTLIB sequential §3–§4 cycle; that history lives in git + `tickets.md`).
Read this top to bottom before touching anything.*

**Goal of this effort:** a *faithful* Lean formalization of RJW §13.2 + **Theorem 13.11** (Iwasawa
Main Conjecture for Vandiver primes): `X⁺_∞ ≃ₗ[Λ(Γ⁺)] Λ(Γ⁺)/I(Γ⁺)ζp`.

**Binding constraints (do NOT break — these are the user's explicit, repeated directives):**
- Build the **REAL** Galois/analytic objects. **No `Type*` placeholders, no structures that bundle the
  theorem's hard content as hypotheses.** Reference the RJW source, not memory; no shortcuts.
- **Exactly ONE** class-field-theory result may be assumed: **TG5 / Prop 13.13** (the units SES). Nothing
  else gets assumed wholesale. Standard structural facts (normality, ramification) are *proven*.
- You are a **PRODUCER** on `dev/padic` (see root `CLAUDE.md`). Prove theorems; leave `sorry` only as
  honest WIP. Do not golf/dedup/bump — that is done centrally on `main`. PR to `main` when a ticket is done.

---

## 1. CURRENT STATE — the §13.2 Galois foundation is COMPLETE (sorry-free, axiom-clean)

All in **`projects/PadicLFunctions/PadicLFunctions/Iwasawa/GaloisFoundation.lean`** (~1000 lines,
`lake build` clean, `lean_verify` = `[propext, Classical.choice, Quot.sound]` only on the headline
decls). **Do not re-derive any of this.** What's proven:

- **Objects (genuine, over `Ω = AlgebraicClosure ℚ`):** `Fcyc`/`F` (cyclotomic layers), `FPlus` (`F⁺ₙ`),
  `Finf`/`FinfPlus` (`F∞`/`F∞⁺`), `Gamma`/`GammaPlus` (= `Gal(F∞/ℚ)`, `Gal(F∞⁺/ℚ)`), `IsUnramifiedOutsideP`,
  `IsAdmissibleM`/`IsAdmissibleL`, `MPlusN`/`LPlusN`/`MinfPlus`/`LinfPlus`, `XinfPlus` (= `Gal(M∞⁺/F∞⁺)`),
  `YinfPlus` (= `Gal(L∞⁺/F∞⁺)`).
- **Keystone:** `isMulCommutative_iSup` (compositum of abelian-Galois extensions is abelian; was missing
  from mathlib).
- **TG1 (Remark 13.7):** `instMulDistribMulActionGammaPlusXinfPlus : MulDistribMulAction (GammaPlus p)
  (XinfPlus p)` — the Γ⁺-action by conjugation of lifts. Built from `normal_MinfPlus`, `restrToGammaPlus`
  (`Gal(M∞⁺/ℚ) ↠ Γ⁺`), `baseChangeEquiv`, `ker_restrToGammaPlus`, `xinfEquivKer`, `gammaPlusActionHom`
  (conjugation descent via `QuotientGroup.lift` + `quotientKerEquivOfSurjective`).
- **TG3:** `isMulCommutative_YinfPlus` (Y∞⁺ abelian).
- **TG4:** `restrXtoY`, `restrXtoY_surjective`, `ker_restrXtoY` (the Galois SES `0→Gal(M∞⁺/L∞⁺)→X∞⁺→Y∞⁺→0`),
  + over-F∞⁺ normality (`instNormalMinfPlusOverFinf`, `instNormalLinfPlusOverFinf`).
- **TG2 (carrier half):** `instCommGroupXinfPlus` ⟹ `Additive X∞⁺` is the ℤ[Γ⁺]-module carrier.
- **`normal_MinfPlus` (M∞⁺/ℚ normal)** — fully proven, including the analytic core `isAdmissibleM_map`
  ("admissibility is σ-invariant for σ : Ω →ₐ[ℚ] Ω"): helpers `finrank_sigmaL`,
  `finiteDimensional_sigmaL`, `isGalois_sigmaL`, `mulComm_sigmaL`, and the unramified core
  `isUnramifiedOutsideP_sigmaL` (the worked base-moving-ramification pattern — see §6).

**ONE vendored lemma to clean up later:** `isUnramifiedAt_bot_charZero` (top of the namespace) is copied
from **open mathlib PR #40886** (`feat: add Algebra.IsUnramifiedIn`), per CB's pointer — it discharges the
`⊥` (generic-fibre) case in char 0. Flagged "remove when the daily bump brings `Algebra.isUnramifiedAt_bot`
into mathlib"; then delete the copy and use the mathlib one.

---

## 2. ARCHITECTURE & THE KEY DECISION (already made by CB — do not relitigate)

- **§13 (this file) lives in `Ω = AlgebraicClosure ℚ`.** §12 (the analytic/units side) lives in **`ℂ_[p]`**:
  `globalUnits`, `localUnits`, `NormCompatUnits`, the E/U/C unit towers, `IwasawaAlgebra := PowerSeries 𝒪`,
  `Gamma := OneUnits p ≅ ℤp` — in `…/Iwasawa/{GPlusDecomp,CyclotomicUnits,LocalUnits,…}.lean` and
  `…/StructureTheory/IwasawaAlgebra.lean`.
- **DECISION (CB): bridge the two ambients by embedding `Ω ↪ ℂ_[p]`** (fix one prime above p), transport
  the §13 Galois objects into ℂ_[p], reuse §12 directly. Alternatives (rebuild §12 over Ω; an abstract
  interface) were considered and **rejected** — embedding keeps every object real with no extra assumptions.
- Theorem 13.11 inherently connects the Galois side (X∞⁺, over Ω) and the analytic side (Λ/I·ζp, over
  ℂ_[p]); the bridge is the content, not avoidable.

---

## 3. THE REMAINING PLAN — critical path TG2-Lambda → TG6 → TG9

Full tickets (statement / sketch / mathlib lemmas / RJW source line-refs / generality decision) are in
**`projects/PadicLFunctions/.mathlib-quality/tickets.md`** under "§13 VANDIVER IMC — AUTHORITATIVE
CONSOLIDATED BOARD". The remaining tickets, in dependency order:

- **[TG2-Lambda]** Λ(Γ⁺) = ℤp[[Γ⁺]]-module structure on X∞⁺, and `GammaPlus p ≃* §12.Gamma (= OneUnits p ≅
  ℤp)`. This is the cyclotomic character at the limit: `Gal(F∞⁺/ℚ) ≅ lim (ℤ/pⁿ)ˣ⁺ ≅ ℤp`. mathlib has the
  finite-level `IsCyclotomicExtension.autEquivPow` but NOT the inverse-limit version — build it, or route
  through §12's `galEquiv` + `gplusHomeo`. **Do the Ω↪ℂ_[p] embedding FIRST.** Expect to split into
  sub-tickets (embedding; char-at-finite-level; inverse limit; Λ-action transport).
- **[TG5]** *The single permitted CFT assumption* (Prop 13.13): the SES
  `0 → E∞,₁⁺ → U∞,₁⁺ → Gal(M∞⁺/L∞⁺) → 0` of Λ(Γ⁺)-modules, stated about the REAL objects (§12 unit towers +
  `ker_restrXtoY` from TG4 = Gal(M∞⁺/L∞⁺)). State as a hypothesis/`variable`, NOT a bundled-isos structure.
- **[TG6]** Cor 13.14: splice TG4 (Galois SES) with TG5 via the third isomorphism theorem.
- **[TG7a–d]** Cor 13.16 (Vandiver), with **Prop 13.15 PROVED** (CB: not assumed): TG7a `Yₙ⁺≅Cl(Fₙ⁺)⊗ℤp`
  (reuse **FltRegularBernoulli `HilbertPClassField`**), TG7b coinvariants `(Y∞⁺)_{Γₙ⁺}≅Yₙ⁺`, TG7c `Y∞⁺=0`
  + `p∤hₙ⁺`, TG7d `E∞,₁⁺/C∞,₁⁺ = 0`.
- **[TG8]** Thm 11.9 wiring: `U∞,₁⁺/C∞,₁⁺ ≅ Λ(Γ⁺)/I(Γ⁺)ζp` (from §12's `iwasawa_theorem`; the Λ-linear
  upgrade is the disclosed gap).
- **[TG9]** **Theorem 13.11** (the milestone): assemble TG6 + TG7 + TG8.

---

## 4. REUSABLES — don't reprove (`grep -r` the workspace + mathlib, then `import`)

- **mathlib `RamificationInertia/{Unramified,Ramification,Galois}`**: `isUnramifiedAt_iff_of_isDedekindDomain`
  (`IsUnramifiedAt ↔ ramIdx = 1`), `ramificationIdx_algebra_tower'`, `ramificationIdx_comap_eq`/`_map_eq`,
  **`ramificationIdx_eq_of_isGaloisGroup`** (equal ram-idx over a fixed prime in a Galois ext — the
  `MulSemiringAction (Gal L/K) (𝓞 L)` + `IsGaloisGroup ℤ (𝓞 L)` instances resolve AUTOMATICALLY from
  `IsGalois`), `IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver`, `Ideal.under_ne_bot`.
  `RingOfIntegers.mapAlgEquiv`/`mapRingEquiv`, `Algebra.FormallyUnramified.{of_isSeparable,comp}`.
- **AINTLIB sibling projects** (same Lake workspace, directly importable):
  - **FltRegular** (`projects/FltRegular`): `NumberTheory.Unramified`, ramification in cyclotomic fields.
  - **FltRegularBernoulli**: `HilbertPClassField` (`Gal(Hp/L) ≃* ClassGroupModP`) — the cited CFT input for
    TG7a; `ComponentUnramifiedCyclicDegreePExtension`.
  - **Chebotarev** (`projects/Chebotarev/CebotarevDensity/Frobenius.lean`): `UnramifiedIn`,
    `inertiaGroup_trivial_of_unramified`, Frobenius/decomposition — the Galois-action-on-`𝓞` pattern.
- **§12 in THIS project**: `IwasawaAlgebra` (`= PowerSeries 𝒪`), `Gamma` (`= OneUnits p`), `GPlus`,
  `gplusHomeo` (`GPlus ≃ₜ Δ × Γ`), `iwasawa_theorem`, the unit towers — in `…/Iwasawa/*.lean`.
- **RJW notes**: `refs/PadicLFunctions/RJW.txt` (LOCAL ONLY, gitignored; symlink `refs` into the worktree:
  `ln -s ../AINTLIB/refs refs`). Line refs: Rmk 13.7 @6726, Prop 13.13 @6796, Cor 13.14 @6826, eq 13.2
  @6874, Prop 13.15 @6879, Cor 13.16 @6891, Thm 13.11 @6764, final proof @7002.

---

## 5. HOW TO WORK

- **Worktree:** this lives in a git worktree `../aintlib-padic` off the shared clone, on branch `dev/padic`.
  (Different machine → `git clone CBirkbeck/AINTLIB`, `git checkout dev/padic`.)
- **Build:** from the workspace ROOT (`aintlib-padic/`, NOT `projects/PadicLFunctions/`):
  `lake exe cache get` once, then `lake build PadicLFunctions.Iwasawa.GaloisFoundation`. Builds are
  incremental. **Never** put `2>/dev/null` next to a `lake`/`lean` command (a guardrail blocks it; use `2>&1`).
- **Push:** `LEAN4_GUARDRAILS_BYPASS=1 git push origin dev/padic` (the worktree push needs the env flag).
- **Process skills:** `/develop` plans (writes tickets with statement + sketch + sources), `/beastmode`
  executes (picks the next open ticket with met deps, works it to DONE, spawns focused sub-tickets for gaps,
  never stops on "hard"/"long"/"multi-session"). The ticket board + plan live in `.mathlib-quality/`.
  Everything in `.mathlib-quality/`, `docs/`, `blueprint/` stays on `dev/padic` (process, not merged to `main`).
- **LSP-first:** use `lean_diagnostic_messages` / `lean_goal` / `lean_multi_attempt` for fast iteration;
  reserve full `lake build` for checkpoints; verify axiom-cleanliness with `lean_verify`.

---

## 6. GOTCHAS / LESSONS (these cost real time — heed them)

- **Timeouts are encoding bugs, not walls** (CB's binding correction). Fix by (1) breaking into smaller
  top-level lemmas with algebra/tower instances as EXPLICIT hypotheses (clean elaboration context), or
  (2) passing implicit variables explicitly (`@`-apply / `(R := …)`). It always worked.
- **The ℚ-algebra diamond.** `↥(K : IntermediateField ℚ _)` carries `DivisionRing.toRatAlgebra`, but generic
  lemmas expect `IntermediateField.algebra'`. Syntactic `rw` fails. **Bridge with `refine ….mpr`/`.mp`
  (defeq), pass the instance explicitly, or `rw [show LHS = RHS from lemma …]`.**
- **`⨆`-base heavy defeq.** Building a concrete `AlgEquiv` over the base `↥(FinfPlus p)` (a big `⨆`) via
  `comap` + `AlgHom.codRestrict` TIMES OUT. Use mathlib's light primitives:
  **`IntermediateField.restrict` / `restrict_algEquiv`** (and `extendScalars`).
- **Base-moving (β-semilinear) ramification.** `σ : Ω →ₐ[ℚ] Ω` moves `F⁺ₙ` by `β = σ|F⁺ₙ`, so fixed-base
  ram-idx lemmas don't apply directly. The clean route is the **ℤ-tower**: over ℤ, `σ` IS fixed-base
  (`ramificationIdx_comap_eq` via `eOI` as a ℤ-AlgEquiv), use tower multiplicativity
  (`ramificationIdx_algebra_tower'`), and `ramificationIdx_eq_of_isGaloisGroup` for the base primes
  (auto Galois-action instances), then `Nat.eq_of_mul_eq_mul_left` to cancel. See `isUnramifiedOutsideP_sigmaL`.
- **Syntax:** `open … in` / `set_option … in` must come BEFORE the docstring, not between docstring and decl.
- **`obtain ⟨…⟩ := h`** *consumes* `h`; use `obtain … := id h` if you still need `h` later.
- **`IsMulCommutative` is a Prop, not a `CommGroup`** — upgrade with the `CommGroup` constructor + `mul_comm`
  (from `isMulCommutative_iff.mp`) before using `Additive`.
- **Identifiers:** combining marks (e.g. `σ̃`) are NOT valid Lean identifiers; use plain names (`eOIz`).
- **Vendoring across mathlib versions:** PR proofs may use newer signatures; adapt arg structure (e.g. my
  `isAlgebraic_of_isFractionRing` has `{R S}` implicit, `(K L)` explicit).

---

## 7. FIRST MOVES for the new worker

1. `cd` to the worktree root, `lake exe cache get`, `lake build PadicLFunctions.Iwasawa.GaloisFoundation` —
   confirm green baseline (should be clean, 0 sorries).
2. `ln -s ../AINTLIB/refs refs` (if not already), so `refs/PadicLFunctions/RJW.txt` is readable.
3. Read `tickets.md` (the board) — especially the **TG2-Lambda** ticket and the §12 file inventory.
4. Run `/beastmode` (the sentinel is removed at this handoff; `/beastmode` re-arms it). It will pick up
   TG2-Lambda. The first sub-step is the **Ω ↪ ℂ_[p] embedding**; then the finite-level cyclotomic
   character; then the inverse limit `Γ⁺ ≅ ℤp`; then transport the Λ-action onto `Additive X∞⁺`.

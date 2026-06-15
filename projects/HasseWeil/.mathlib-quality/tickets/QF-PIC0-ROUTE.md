# QF witness — committed route (Pic⁰ / restricted dual additivity)

**Committed 2026-05-26** per expert-review reply (`../expert-review/2026-05-26/`). This is
the primary critical path for the `qf_nonneg` HasseWitnesses field (Silverman III.6.3). The
V.1.3 witness is tracked separately (the F.1/B(ii)–(iv) geometric bridge, already
decomposed and dispatchable). Route 3 (explicit Walls A/B) is **parked** — fallback only.

Irreducible target: **`(rπ − s)^ = rV − s` on ℤπ + ℤ** (restricted dual additivity). With it
plus `φ̂∘φ = [deg φ]`, the chain `(rV−s)∘(rπ−s) = [deg(rπ−s)]` and the point-map expansion
`= [q·r²−t·r·s+s²]` force `deg(rπ−s) = q·r²−t·r·s+s² ≥ 0`, uniformly in (r,s).

**⭐ MAJOR SCOPING UPDATE 2026-05-26.** The Pic⁰ keystone is **already shipped axiom-clean**:
`picZeroIsoE : Pic⁰(E) ≃+ E.Point` (over `[IsAlgClosed F]`, `[NeZero 2]`, `[NeZero 3]`,
Dedekind/integrally-closed coordinate ring), with a `picZeroIsoE (W.baseChange L)` form for
the descent. Dual-via-Pic⁰ functoriality (pushforward/pullback on Pic⁰, diagram-commute
`φ_*(κ P)=κ(φ P)`) is wired. So **T-QF-PIC0-ISO is effectively DONE** (modulo dropping
[IsAlgClosed]/[NeZero] via base-change). Remaining QF chain to pin & prove:
(i) **dual additivity in the morphism** `(φ+ψ)_* = φ_* + ψ_*` on Pic⁰ (additivity of the
pushforward in the ISOGENY, not just the divisor — verify if shipped, else prove);
(ii) transport across `picZeroIsoE` to get `(rπ−s)^ = rV−s` on ℤπ+ℤ over K̄;
(iii) degree descent K̄→𝔽_q (degree base-change invariant — `isogeny_degree_baseChange_eq`
shipped, L12b) so `deg(rπ−s)=N` holds over 𝔽_q; (iv) `qf_nonneg` close.
Char 2/3 + non-closed-field handled in the base-change/descent layer (Q5: never in the QF
proof). The exact leaf chain (i)–(iv) is being pinned by a scoping pass before the prover.

**⭐ T9 CONFIRMED AXIOM-CLEAN 2026-05-26** (`#print axioms HasseWeil.verschiebung_dual_exists`
→ [propext, Classical.choice, Quot.sound]). So the Verschiebung-is-dual-of-Frobenius
existence (∃ V, IsDualOf V π) is DONE, not sorry-tainted — the leaf-chain's identified
bottleneck is already solved. Also confirmed: `genuineIsogSmulSub_degree_eq_quadratic_form`
has a clean body (only its witnesses are the gap). **QF keystone now = discharge the sorry
skeleton `genuineIsogSmulSub_degree_eq_quadratic_form_minimal` (QuadraticForm.lean:374)** by
supplying V (T9) + trace identity (T4, shipped hom-level) and routing the single-(r,s)
degree identity through either the witness-parametric form (needs V-side addIsog data = the
parked Wall A/B) OR the shipped Pic⁰ degree machinery `isogPicPullback_comp_pushforward`
(φ*∘φ_* = [deg α], IsogenyBaseChange.lean:331) which may bypass Wall A/B. The prover
determines which; if dual-additivity-at-isogeny-level is the irreducible leaf, that becomes
the next focused target via Pic⁰ pushforward additivity.

**⭐ ROUND-2 REVIEWER DECISION 2026-05-26 (route resolved).** The shipped Pic⁰ dual is
degree-blind (placeholder pullback). Route = **B-narrow primary + C supporting**:
- **B (primary, narrow):** construct, for `β = rπ−s` ONLY, a genuine dual `β_dual = rV−s`
  with a *real pullback* (comorphism) and `β_dual∘β = [N]` at the function-field/degree level
  = the leaf `genuineIsogSmulSub_pivot_witness` (QuadraticForm.lean) / `genuineIsogSmulSub_
  degree_eq_signed` (GapSpines, the consumed twin). NOT the full Picard-functor stack; NOT
  the explicit addition-pullback (Wall A, ruled out).
- **C (supporting accelerator):** `genuine_isogeny_ext_of_geometric_pointMap_eq` — genuine
  morphisms equal on E(K̄) ⟹ equal pullback. Shortens the pullback-equality once genuine maps
  exist; NOT a replacement for B; depends on B in practice. (This supersedes/retargets the
  old T-QF-EXT entry below: it must be over E(K̄), supporting, not primary.)
- **RULED OUT:** D (deg_s·deg_i — detour); Weil-pairing/torsion-determinant (major new
  branch); explicit-coordinate Route 3 (V-side pole obstruction real).
- **Next concrete target (reviewer):** `frobeniusPlane_genuine_dual (r s : ℤ) : ∃ β βdual,
  β.toPointMap = r•π−s•id ∧ βdual.toPointMap = r•V−s•id ∧ β.IsGenuine ∧ βdual.IsGenuine ∧
  βdual.comp β = mulByInt(N)`, then extract `degree β = N`. β=rπ−s already genuine; construct
  the genuine βdual. Round-2 record: `expert-review/2026-05-26-2/`.

**⭐ ROUND-3 REVIEWER DECISION 2026-05-26 — QF splits into two layers.** Genuine `rV−s`'s
addIsog route is obstructed at the pole bound; the reviewer routes the POLE BOUND through the
LIGHT formal-group argument (NOT Pic⁰, NOT VII.2):
- **Layer 1 (local genuineness):** `rV−s ≠ 0 ⟹ ord_O((rV−s)*x) < 0` via the formal group law
  `F(T₁,T₂)=T₁+T₂+…` preserving `𝔪 = {ord > 0}` (positive-order series sum stays positive-order;
  nonzero positive-order parameter ⟹ `x ∼ t⁻²` pole). Bypasses the 3-way coordinate tie. Discharges
  `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole` → genuine `rV−s`. Build the MINIMAL
  5-lemma formal-neighbourhood package (IV.1–IV.3 style; NOT VII.2; NOT mathlib `Reduction`
  (coefficient-level) — define E₁ via t-adic order): (1) `𝔪={ord>0}`; (2)
  `formalGroup_preserves_positive_order : 0<ord u → 0<ord v → 0<ord (F u v)`; (3) inverse preserves
  it; (4) isogeny-fixing-O ⟹ series ∈ T·K[[T]]; (5) `addPullback_x_has_pole_of_formalSeries_positive_order`.
  Caveat: nonzero branch only (rV−s=0 separate, like L8z); watch `rπ−s≠0 ⟹ rV−s≠0` transfer.
- **Layer 2 (degree/duality):** Pic⁰ comorphism OR K̄-extensionality / restricted dual additivity
  → `(rπ−s)^ = rV−s` → qf_nonneg. Separate from Layer 1 (Pic⁰ ≠ formal-group).
- **Next target:** `formalGroup_preserves_positive_order` (foundational, self-contained).
- Round-3 record: `expert-review/2026-05-26-3/`.

Status legend: O open · P in-progress · B blocked · R review · D done.

---

## [T-QF-EXT] Genuine-isogeny extensionality by point-map
- **Status**: O   **Parallel**: yes (no deps)   **Type**: lemma + corollary   **Priority**: HIGH
- **Depends on**: none
- **Statement (math)**: if φ, ψ : E → E′ are *genuine* isogenies (real function-field
  pullbacks, not placeholders) that agree as maps on E(K̄), then their pullbacks agree on
  K(E′); consequently `deg φ = deg ψ`.
- **Reviewer Lean shape**: `genuine_isogeny_ext_of_pointMap_eq (φ ψ : Isogeny E E')
  (hφ : φ.IsGenuine) (hψ : ψ.IsGenuine) (hpt : ∀ P, φ.toPointMap P = ψ.toPointMap P) :
  φ.pullback = ψ.pullback`, then `degree_eq_of_pointMap_eq`.
- **Why**: removes the Wall-B friction project-wide — lets shipped point-map identities
  (`π + V = [t]`, `(rV−s)∘(rπ−s) = [Q]`) transfer to the pullback/degree level for genuine
  maps. Reusable far beyond Hasse.
- **Caveat**: must be restricted to genuine isogenies; placeholder isogenies are the
  counterexamples. Does NOT by itself close qf_nonneg — the dual identification remains.
- **Source**: a morphism of curves over an algebraically closed field is determined by its
  effect on points (the function-field pullback is the comorphism); Silverman II.2.
- **⚠ FINDING 2026-05-26 (scoping)**: the hypothesis must be over **geometric points
  E(K̄)** (`PointOverAlgClosure`), NOT `W.Point = E(𝔽_q)` — the latter is finite and cannot
  determine a map on the function field (the reviewer's Q4 shape already used
  `E.PointOverAlgClosure`). Consequence: the shipped trace identity `π+V=[t]` is only at the
  𝔽_q level (Lagrange), so it is **not** directly valid input to this lemma; it would need a
  K̄-level lift. Cleaner alternative recast (purely algebraic, no point-density): "two
  AlgHoms K(E)→K(E) agreeing on the generators x_gen, y_gen are equal" — true and avoids the
  finiteness trap, but its input is generator-values, not point-maps. **Net: the
  extensionality shortcut is more delicate than the brief implied; Pic⁰ (Route 1, geometric)
  is the robust primary and does not depend on it. Demoted to genuinely-secondary; needs its
  own decomposition (K̄ point-map vs generator-recast) before any proof worker.**
- **Sub-decomposition (from scoping)**: T2 — x_gen,y_gen generate K(E) as F-algebra; T3 —
  an AlgHom K(E)→K(E) is determined by its action on x_gen,y_gen; T4 — assemble. `IsGenuine`
  predicate does not yet exist (Isogeny carries `pullback` + `toAddMonoidHom` as independent
  data; degree is finrank of the pullback). Define `IsGenuine` only if the generator-recast
  needs it.

## [T-QF-PIC0-ISO] Pic⁰(E) ≅ E  (activate picard stack keystone)
- **Status**: O (existing picard tickets)   **Parallel**: yes   **Type**: theorem
- **Depends on**: the `tickets/picard/` stack (Abel–Jacobi / Miller principal-divisor
  lemmas — shipped under [IsAlgClosed],[NeZero 2],[NeZero 3]; the σ̄/κ isomorphism tickets).
- **Statement (math)**: the Abel–Jacobi map P ↦ class of (P) − (O) is a group isomorphism
  E(K̄) ≅ Pic⁰(E).
- **Note**: this is the Pic⁰ keystone the reviewer's route rests on. Activate and complete
  the existing picard tickets (`T-PIC-F-002-pic-zero-iso-equiv` and its dependency chain)
  as primary, not background.
- **Source**: Silverman III.3.4.

## [T-QF-DUAL-VIA-PIC0] Dual isogeny via Pic⁰ functoriality
- **Status**: O   **Parallel**: no   **Type**: def + theorems
- **Depends on**: T-QF-PIC0-ISO
- **Statement (math)**: define φ̂ as the functorial pullback φ* : Pic⁰(E) → Pic⁰(E)
  transported across Pic⁰ ≅ E. Establish `φ̂∘φ = [deg φ]` and **additivity**
  `(φ+ψ)^ = φ̂ + ψ̂` (free from functoriality of pullback on Pic⁰).
- **Source**: Silverman III.6.1 (existence), III.6.2 (additivity via Pic⁰).

## [T-QF-DUALADD] Restricted dual additivity on ℤπ + ℤ
- **Status**: B (on T-QF-DUAL-VIA-PIC0; T-QF-EXT for the lift)   **Type**: theorem (★ keystone)
- **Depends on**: T-QF-DUAL-VIA-PIC0, T-QF-EXT
- **Statement (math)**: `(rπ − s)^ = rV − s` for all r, s ∈ ℤ, where V = π̂ (shipped). A
  direct specialisation of additivity + `1̂ = 1`, `π̂ = V`.
- **Note**: this is the §5.4 keystone. With T-QF-DUAL-VIA-PIC0's general additivity it is a
  one-step specialisation; T-QF-EXT promotes the point-map identities to the pullback level
  where degree lives.

## [T-QF-CLOSE] qf_nonneg from the dual identification
- **Status**: B (on T-QF-DUALADD)   **Type**: theorem (the HasseWitnesses field)
- **Depends on**: T-QF-DUALADD
- **Statement (math)**: `0 ≤ q·r² − t·r·s + s²` for all r, s ∈ ℤ. Proof: from T-QF-DUALADD,
  `(rV−s)∘(rπ−s) = (rπ−s)^∘(rπ−s) = [deg(rπ−s)]`; the point-map expansion (shipped algebra
  from V∘π=[q], π+V=[t]) gives this `= [q·r²−t·r·s+s²]`; equate and use `[m]=[n] ⟺ m=n` and
  `deg ≥ 0`.
- **Note**: most of the consumer wiring already exists in witness-parametric form
  (`qf_nonneg_universal_of_polarisation_witness`, `qf_nonneg_via_frobenius_polarisation`,
  the `_of_qf_nonneg_witnesses` chain). This ticket supplies the polarisation/degree witness
  unconditionally and discharges the `HasseWitnesses.qf_nonneg` field.

---

## [T-QF-PIVOT-FULL] Genuine `(r,s)` Pic⁰ pivot witness (full-isogeny dual)
- **Status**: O (NEW — single irreducible leaf for the keystone)   **Parallel**: no   **Type**: theorem (★ keystone leaf)
- **Depends on**: T-QF-DUAL-VIA-PIC0 (full-isogeny, not just point-map) + Wall A/B content, OR the Pic⁰ dual-additivity-at-isogeny-level route over K̄ + degree descent.
- **Lean shape** (shipped as `sorry`-skeleton 2026-05-26, `HasseWeil/Hasse/QuadraticForm.lean`,
  `genuineIsogSmulSub_pivot_witness`):
  ```
  theorem genuineIsogSmulSub_pivot_witness (W) [IsElliptic] (hq) (r s) (hr hs hrK hsK) :
    ∃ β_dual : Isogeny W.toAffine W.toAffine,
      IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK) ∧
      β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) = mulByInt W.toAffine N ∧
      0 < (genuineIsogSmulSub W r s hr hs hrK hsK).degree ∧ N ≠ 0
  ```
  where `N = q·r² − t·r·s + s²`.
- **Statement (math)**: for the genuine `β = r·π − s`, there is a genuine dual `β_dual`
  (morally `r·V − s`) with `IsDualOf β_dual β` and the **full-isogeny** (pullback-bearing)
  composition `β_dual ∘ β = [N]`, plus `0 < deg β`, `N ≠ 0`. Silverman III.6.2(b/c).
- **Why this is the irreducible leaf (deep-pass finding 2026-05-26)**: `Isogeny.degree` is
  `finrank` of the *pullback* only (`Basic.lean:91`); the point map `toAddMonoidHom`
  determines only `sepDegree` (kernel cardinality over K̄), and `r·π − s` is generically
  *inseparable*, so its point map never pins down its full degree. Hence **Route B (Pic⁰
  degree bypass) is mathematically blocked, not merely import-blocked**: the entire Pic⁰
  stack (`isogPicPullback_comp_pushforward`, `dualViaPicZero`) operates on `AddMonoidHom`s
  on Pic⁰, and `dualViaPicZero`/`dualOfPicZeroPullback` build the dual with a **placeholder**
  `pullback := α.pullback` (`IsogenyBaseChange.lean:148`). The hom-level identity
  `(rV−s)∘(rπ−s) = [N]` is shipped (`cross_compose_zPi_witness`, `IsogenyBaseChange.lean:191`)
  but it is degree-blind. Route A hits **Wall A** (V-side pole bound
  `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`,
  `Verschiebung/Genuine.lean:1091`, itself an open `sorry`).
- **Discharge path**: the full-isogeny composition `β_dual ∘ β = [N]` is exactly the parked
  Wall A/B content. The Pic⁰ route would build `β_dual` over `K̄ = AlgebraicClosure K` (where
  `picZeroIsoE` + dual-via-Pic⁰ functoriality live), establish the composition there, and
  descend the degree to `K` via `degree_eq_of_finrank_eq` (`IsogenyBaseChange.lean:92`) — but
  only once dual-additivity ships **at the pullback (isogeny) level** `(φ+ψ)^ = φ̂ + ψ̂`, NOT
  merely on Pic⁰ point-maps. That isogeny-level additivity is the genuine next sub-ticket
  (cf. T-QF-DUAL-VIA-PIC0 "additivity"; `pushforwardProjectiveDivisor_add`
  (`Curves/PicZeroPushforward.lean:55`) is additivity in the *divisor*, not the *morphism*).
- **Consumes-into**: `genuineIsogSmulSub_degree_eq_quadratic_form_minimal`
  (`QuadraticForm.lean`, now `sorry`-free in its own body, axioms
  `[propext, sorryAx, Classical.choice, Quot.sound]` with `sorryAx` traced solely to this leaf)
  via the shipped axiom-clean `signed_degree_of_genuine_dual_pair`
  (`DegreeQuadraticForm.lean:233`, Wall C `mulByInt` injectivity on the pullback).
- **Critical-path twin**: the *consumed* sorry on the actual bound path is
  `genuineIsogSmulSub_degree_eq_signed` (`GapSpines.lean:553`) — identical statement, gates
  `degree_quadratic_exists_skeleton_nonzero` → `qf_nonneg_skeleton` → Hasse bound. It is an
  open `sorry` **despite** having T9 (`verschiebung_dual_exists`), T4
  (`pi_plus_V_eq_isogTrace_addMonoidHom`), the V-side genuine isogeny chain and the full Pic⁰
  stack all in scope — confirming the gap is irreducible against the entire shipped codebase.
  Discharging `genuineIsogSmulSub_pivot_witness` here (it is statement-portable to GapSpines)
  closes BOTH.

---

## Parked (Route 3 — fallback only, do not pursue as primary)

- Wall A (V-side pole order) — `v-side-pole-bound-obstruction.md`
- Wall B (explicit double-Vieta pullback) — `decomposition-WallB-y-side-2026-05-25.md`
- L2 char-divisible edges — `decomposition-L2-char-divisible-2026-05-25.md`

Route 1 moots all three: dual additivity is uniform in (r,s) (no V-side pole bound, no
explicit coordinate formula, no char-divisible split).

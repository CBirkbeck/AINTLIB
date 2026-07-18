# Upstream candidate ledger — [T-UPSTREAM-TRIAGE] (v10.30)

Owner: beastmode-A, 2026-07-08. **Deliverable only — no external PRs opened** (publishing to
mathlib is an owner action). Each entry: verified against *current* mathlib (searched, not
assumed), ranked `shortens-existing > fills-cited-gap > nicety`, target file named, PR draft
staged. Verification method per entry noted.

Ranking summary (verified candidates, strongest first):

| # | Lemma | Class | Target mathlib file | Status |
|---|-------|-------|---------------------|--------|
| 1 | `Functor.map_zpow'` | fills-gap (sibling of existing) | `CategoryTheory/Monoidal/Cartesian/Grp.lean` | READY |
| 2 | `AdjoinRoot.isDomain_of_monic_of_map` (+2) | shortens-existing + fills-gap | `RingTheory/AdjoinRoot.lean` (+ Polynomial) | READY |
| 3 | `IdealSheafData.comap_mul`/`comapMonoidHom`/`comap_prod` | fills-gap (API completion) | `AlgebraicGeometry/IdealSheaf/Functorial.lean` | READY |
| 4 | `IdealSheafData.exists_factor_comap_iff` | fills-gap | `AlgebraicGeometry/IdealSheaf/Functorial.lean` | READY |
| 5 | `OverPullbackMul` (grpObjMkPullbackSnd…) | nicety / needs-owner | `CategoryTheory/Monoidal/Cartesian/Over.lean` | OWNER-INPUT |
| 6 | D2 homological suite (≈8 files) | fills-gap (specialized) | RingTheory/homological | VERIFY-PASS |
| 7 | P3b3 bridge pieces | — | — | NO-CANDIDATE |

---

## 1. `Functor.map_zpow'` — STRONGEST (clean sibling)

- **Source**: `ForMathlib/FunctorMapZpow.lean`.
- **Statement**:
  ```lean
  @[to_additive]
  lemma CategoryTheory.Functor.map_zpow' (f : X ⟶ G) (n : ℤ) :
      F.map (f ^ n) = (F.map f) ^ n := map_zpow (Functor.homMonoidHom F) f n
  ```
  (`F` a monoidal functor, `G` a group object; `open scoped CategoryTheory.Obj`.)
- **Verified**: mathlib has **`Functor.map_inv'`** at `Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean:191`
  (the `inv` companion) and uses `map_zpow (Functor.homMonoidHom …)` inline at Grp.lean:166 — but there
  is **no `Functor.map_zpow'`**. This is the exact missing `zpow` sibling of `map_inv'`.
- **Class**: fills-cited-gap (natural API companion — obvious mathlib fit, next to `map_inv'`).
- **Target**: `Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean`, immediately after `Functor.map_inv'`.
- **PR draft**: drop-in; the `map_zpow (Functor.homMonoidHom F)` proof already matches the Grp.lean:166
  inline usage, so the inline use there can be replaced by `F.map_zpow'` (a minor shortening bonus).
  Keep `@[to_additive]`. No new imports.

## 2. `AdjoinRoot.isDomain_of_monic_of_map` — shortens an existing mathlib proof

- **Source**: `ForMathlib/MonicQuotientDescent.lean` (a 3-lemma cluster).
- **Statements**:
  ```lean
  theorem Polynomial.dvd_of_monic_of_map_dvd_map [Nontrivial A] [IsDomain B] …   -- line 30
  def AdjoinRoot.mapRingHom : AdjoinRoot f →+* AdjoinRoot (f.map φ)               -- line 54
  theorem AdjoinRoot.mapRingHom_injective [Nontrivial A] [IsDomain B] (hf : f.Monic) … -- line 67
  theorem AdjoinRoot.isDomain_of_monic_of_map [Nontrivial A] [IsDomain B] (hf : f.Monic)
      (hφ : Function.Injective φ) [IsDomain (AdjoinRoot (f.map φ))] : IsDomain (AdjoinRoot f)  -- line 79
  ```
- **Verified**: grep of `Mathlib/RingTheory/AdjoinRoot.lean` finds **no `isDomain_of_monic_of_map`**
  and no `dvd_of_monic_of_map_dvd_map`. The **shortening target** is
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:194-197`:
  ```lean
  instance [IsDomain R] : IsDomain W'.CoordinateRing :=
    have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
      AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
    (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain
  ```
  This IS the abstract `isDomain_of_monic_of_map` trick spelled inline (monic `polynomial`, inject via
  `FractionRing`). Upstreaming the abstract lemma lets this instance read
  `AdjoinRoot.isDomain_of_monic_of_map monic_polynomial (IsFractionRing.injective …)`.
- **Class**: shortens-existing (the CoordinateRing instance) + fills-gap (general monic `IsDomain` descent).
- **Target**: `isDomain_of_monic_of_map` + `mapRingHom`(+`_injective`) → `Mathlib/RingTheory/AdjoinRoot.lean`;
  `dvd_of_monic_of_map_dvd_map` → `Mathlib/Algebra/Polynomial/…` (a Monic/Map file; verify exact home).
- **PR draft**: two PRs (Polynomial dvd lemma first, then AdjoinRoot cluster depending on it). Note the
  `[Nontrivial A] [IsDomain B]` hypotheses match the `FractionRing` use. `isDomain_away`
  (HomogeneousLocalization, same file) is a SEPARATE candidate — the `IsDomain` sibling of
  `Proj.isReduced_away`; verify against `Mathlib/…/HomogeneousLocalization` before staging.

## 3. `IdealSheafData.comap_mul` / `comapMonoidHom` / `comap_prod` — API completion

- **Source**: `ForMathlib/IdealSheafComapMul.lean`.
- **Statements**:
  ```lean
  theorem IdealSheafData.comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
      (I * J).comap f = I.comap f * J.comap f                                     -- line 185
  noncomputable def IdealSheafData.comapMonoidHom (f : X ⟶ Y) :
      Y.IdealSheafData →* X.IdealSheafData                                        -- line 255
  lemma IdealSheafData.comap_prod (s : Finset ι) (K : ι → Y.IdealSheafData) (f) :
      (∏ i ∈ s, K i).comap f = ∏ i ∈ s, (K i).comap f                            -- line 265
  ```
- **Verified**: `Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean` has `comap_mono` (127),
  `comap_top` (144), `map_gc` — but **no `comap_mul`/`comap_prod`/`comapMonoidHom`**. The
  multiplicativity of `comap` is a genuine missing piece of the comap API.
- **Class**: fills-cited-gap (completes the `comap` monoid structure alongside `comap_mono`/`comap_top`).
- **Target**: `Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean`.
- **PR draft**: bundle the three. Note the file also has a `_of_isAffine` stepping-stone
  (`comap_mul_of_isAffine`, line 145) + `comap_ideal_top_of_isAffine` (34) that the general `comap_mul`
  reduces to affine-locally — keep those as private/aux or inline. Verify `SetLike`/`GradedRing`
  instance assumptions match mathlib's `IdealSheafData` API before staging.

## 4. `IdealSheafData.exists_factor_comap_iff` — the comapIso factoring dictionary

- **Source**: `ForMathlib/IdealSheafComapMul.lean:273` (mine, from T-D6a-ii L4).
- **Statement**:
  ```lean
  lemma IdealSheafData.exists_factor_comap_iff (I : Y.IdealSheafData) (f : X ⟶ Y) (g : T ⟶ X) :
      (∃ h : T ⟶ (I.comap f).subscheme, h ≫ (I.comap f).subschemeι = g) ↔
        (∃ h : T ⟶ I.subscheme, h ≫ I.subschemeι = g ≫ f)
  ```
- **Verified**: not in `Functorial.lean`; the `comapIso` (there, line 43) exists but the factoring-through
  dictionary does not. Genuinely missing.
- **Class**: fills-cited-gap.
- **Target**: `Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean`, after `comapIso`.
- **PR draft**: 6-line proof via `comapIso_hom_fst`/`comapIso_inv_subschemeι` + pullback universal
  property — self-contained.

## 5. `OverPullbackMul` (fable-P4) — needs owner input

- **Source**: `ForMathlib/OverPullbackMul.lean`: `monObjMkPullbackSnd_mul_left_fst`,
  `grpObjMkPullbackSnd_mul_left_fst` (the pullback-snd projection intertwining the Mon/Grp-object
  multiplication).
- **Assessment**: the CONTENT (base change / `Over.pullback` preserves group-object structure) overlaps
  mathlib's monoidal `Over.pullback` + `mapGrp` (`Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean`,
  `…/Grp.lean`). The specific `grpObjMkPullbackSnd` naming is project-tied; whether the upstreamable
  general form already follows from `mapGrp` functoriality needs fable-P4's context. **OWNER-INPUT**:
  fable-P4 to confirm what is genuinely absent vs derivable from mathlib's `Over.pullback` monoidal API.
- **Class**: nicety-or-gap (undetermined without owner).

## 6. D2 homological-algebra ForMathlib suite — VERIFICATION PASS NEEDED

- **Candidate files** (D2's commutative-algebra/homological territory; exact 8 to be confirmed by D2):
  `Acyclicity.lean`, `BuchsbaumEisenbud.lean`, `HilbertSyzygy.lean`, `Depth.lean`, `FinrankExact.lean`,
  `FiniteFreeResolution.lean`, `FittingIdeals.lean`, `FinitePresentationCancel.lean`.
- **Verified (this pass)**: **Buchsbaum–Eisenbud acyclicity** and **Hilbert syzygy** are BOTH ABSENT
  from current mathlib (`grep` of all of `Mathlib/` — empty). These are genuine, high-value classical
  gaps. **HOWEVER**: D2's B-E is **actively mid-construction** (recent commits: homology-localization
  transport, `freeLocEquiv`, "B-E backward residual" pieces — the backward direction is not finished),
  so `BuchsbaumEisenbud.lean`/`Acyclicity.lean` are **NOT upstream-ready** — they carry live sorries /
  in-flight scaffolding. **RECOMMENDATION**: defer #6 until D2 completes B-E, then a dedicated D2-owned
  verify-pass on the finished, sorry-free lemmas (the gap is real and worth upstreaming — B-E acyclicity
  and Hilbert syzygy would both be new to mathlib — but staging drafts now is premature). The lower-level
  helpers in the suite (`FinrankExact`, `Depth`, `FiniteFreeResolution`, `FittingIdeals`) may have
  sorry-free, independently-upstreamable pieces; a per-file `#print axioms` scan by D2 identifies them.

## 7. P3b3 bridge pieces — NO CLEAR CANDIDATE

- Scanned `ComparisonBridge.lean`/`ComparisonInjective.lean`: no `ForMathlib`/`upstream` markers; the
  helpers (`coordRingCongr`, `pointedIsoCoordEquiv_congr`, the `away_mk_*` decompositions) are
  project-specific coordinate-ring transport, not upstream-shaped. **OWNER-INPUT**: P3b3 to name any
  intended upstream piece; none identified by triage.

## 8. Confirmed mathlib GAPS surfaced by the T-W7.8 route-a survey (future candidates, NOT staged)

*Added 2026-07-09 (beastmode-A, route-a ground-truth survey — two independent agents, file:line
verified against the pinned mathlib). Not code yet; recorded so future work lands upstream-shaped.*

- **Absolute noetherian approximation (Stacks `01ZA`)** — "every qcqs scheme is a cofiltered limit
  of finite-type-ℤ schemes with affine transitions". Confirmed ABSENT: `AffineTransitionLimit.lean`
  cites 01YT in prose but claims only tags 01Z2–01Z6 + 01ZC (all *given-a-limit* lemmas); no
  existence theorem. High-value, self-contained; the affine case (`Spec R = lim Spec Rⱼ`, `Rⱼ` the
  finite-type-ℤ subalgebras) is a bounded first PR (foundations exist: `Subalgebra.coe_iSup_of_directed`,
  `Algebra.FiniteType.isNoetherianRing`, `Ring/FinitePresentation.lean` colimit API, `Scheme.Spec`
  preserves limits).
- **Property-descent along cofiltered limits (Stacks `081D`/`081E`/`01ZP`/`01ZQ`/`04AI`)** — descending
  {isomorphism, closed immersion, separated, flat, proper, étale, …} from the limit to a finite stage.
  Confirmed ABSENT (`grep` of `Morphisms/` for `of_isLimit` forms: empty). This is route-a's L4c and
  the natural big upstream contribution if route-a is ever completed (`RigiditySpreadingOut.lean`
  skeleton, commit 590984cce, holds the consumer + decomposition).

---

### Next actions (owner)
- Stage PRs #1–#4 (READY, verified) in priority order; #1 (`map_zpow'`) is the cleanest first.
- Request fable-P4 (#5) and P3b3 (#7) owner-input; commission a D2 verification sub-pass (#6).
- §8 gaps: no action now — they become PR-shaped only if route-a resumes (T-W7a fallback).
- This triage is interruptible/droppable; 0h (on 0c-ii landing) preempts it.

# HANDOVER — after the KM 4.7.0 engine landed (what's done, what remains)

*Written 2026-07-22 for the incoming worker. Branch `dev/modular-curves`, HEAD `55feda6a3`
(synced with origin, `0 0`). Everything below is verified against the tree at this commit —
`lake build`s and `#print axioms` runs, not memory. The full library builds green.*

---

## 0. TL;DR — read this first

The previous handover (`HANDOVER-receipts.md`) described the 7 KM 4.7.0 "receipts" as blocked by
two walls (B2 `legendreDeltaGAction`, B3 Oort–Tate). **Both walls are gone and the KM 4.7.0
engine is complete and axiom-clean.** What that did and did *not* finish:

- ✅ **The KM 4.7.0 Scholie engine** — `representable_of_affineOverEll_of_rigidNoeth`
  (`Moduli/EngineWiring.lean`) is **axiom-clean** (`{propext, Classical.choice, Quot.sound}`,
  no `sorryAx`). It reduces representability of *any* moduli problem to
  (affine-over-Ell ∧ relatively representable ∧ rigid-noeth). This is the hard general machine
  (KM pp. 112–116) including the a5-P-loc semilocal Weierstrass-model mouth core.
- ✅ **Y(N)** (full level, N ≥ 3 invertible): `gammaFullNaive_rigid_and_representable`,
  `gammaFullDrinfeld_rigid_and_representable` (`Moduli/GammaHClosure.lean`) — **unconditional,
  axiom-clean.** These are `(hN : 3 ≤ N)(hinv : IsUnit N) → Rigid ∧ Representable`, no other hyps.
- ✅ **Y₁(N)** (Drinfeld Γ₁, N ≥ 4 invertible): `gammaOneDrinfeld_rigid_and_representable`
  (`GammaHClosure`) — **unconditional, axiom-clean.**
- ⚠️ **Y₀(N) and general Y_H(N): NOT done, but close — gated on exactly TWO focused hypotheses**
  (`hbase` + `hH`, §2 below). The quotient-problem-data construction and the engine are done and
  axiom-clean; what's missing is a geometric separatedness lemma and a per-H rigidity argument.

So "all 7 receipts axiom-clean" is **true** (no `sorryAx`) but does NOT mean "all modular curves
representable" — three of the seven are conditional theorems, and Y₀(N) is not among the finished
ones. The honest one-line status: **the engine + Y(N) + Y₁(N) are done; Y₀(N)/Y_H(N) need two
lemmas.**

---

## 1. What is done (decl-by-decl, all axiom-clean unless noted)

| Result | Declaration | File | Status |
|---|---|---|---|
| KM 4.7.0 engine | `ModuliProblem.representable_of_affineOverEll_of_rigidNoeth` | `Moduli/EngineWiring.lean:106` | ✅ axiom-clean |
| D(2) leg (level-4) | `representable_baseChange_two` | `Moduli/EngineWiring.lean` | ✅ |
| D(3) leg (level-3) | `representable_baseChange_three` | `Moduli/EngineWiring.lean` | ✅ |
| recollement (KM 4.7.1) | `representable_of_baseChange_cover` | `Moduli/Recollement.lean` | ✅ |
| mouth core (a5-P-loc) | `MouthCharts.exists_invariant_away_presentation` | `Moduli/EngineMouthCharts.lean` | ✅ |
| ℰ₄ machine | `naiveLevelFour_representable_by_affine` | `Moduli/UniversalLevelFour.lean` | ✅ |
| level-4 torsor | `exists_levelFourTorsorData_ulift` | `Moduli/LevelFourTorsor.lean` | ✅ |
| Y(N) naive | `gammaFullNaive_rigid_and_representable` | `Moduli/GammaHClosure.lean` | ✅ unconditional |
| Y(N) Drinfeld | `gammaFullDrinfeld_rigid_and_representable` | `Moduli/GammaHClosure.lean` | ✅ unconditional |
| Y₁(N) Drinfeld | `gammaOneDrinfeld_rigid_and_representable` | `Moduli/GammaHClosure.lean` | ✅ unconditional |
| Y(N) étale | `levelSpaceΓπ_etale` | `Moduli/GammaHRepresentability.lean:3498` | ✅ |
| **qpd constructor** | `gammaH_relativelyRepresentable` | `Moduli/GammaHRepresentability.lean:3553` | ✅ axiom-clean **modulo `hbase`** |
| Y_H representable | `gammaH_representable_of_orderOf` | `Moduli/GammaHMaster.lean:1094` | ✅ axiom-clean, **takes `qpd` + `hH`** |
| Drinfeld invertible-N boxes | `…smul_eq_zero_of_factors_of_invertible`, `…nsmul_ne_zero_of_field` | `LevelStructure/ExactOrderInvertible.lean` | ✅ |

**New files created this workstream** (all axiom-clean, zero `sorry`): `Moduli/UniversalLevelFour.lean`,
`Moduli/LevelFourTorsor.lean`, `Moduli/EngineMouthCharts.lean`, `Moduli/EngineDescentCore.lean`,
`LevelStructure/ExactOrderInvertible.lean`, `ForMathlib/{AffineCechH0, SemilocalUnitCocycleSplit,
SemilocalVariableChangeSplit, MaximalSpectrumOrbit}.lean`.

---

## 2. The remaining math — Y₀(N) / Y_H(N) is TWO hypotheses away

`gammaH_representable_of_orderOf` (`GammaHMaster.lean:1094`) proves `qpd.prob.Representable` given
`(qpd : QuotientProblemData (gammaHAut R N H))` + `(hH : <per-H finite-order pin>)`. To turn this
into an **unconditional** Y_H(N) (and Y₀(N) = Y_H at H = Borel), discharge both inputs:

### Gate 1 — `hbase` (produces the `qpd`) — geometric, likely the easier one

`gammaH_relativelyRepresentable (N)(H)(hinv) (hbase) : Nonempty (QuotientProblemData (gammaHAut R N H))`
is **already proven axiom-clean** (verified: `#print axioms` = clean triple). Its ONLY open
hypothesis is

```lean
hbase : ∀ X : EllObj R, IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X.base))
```

i.e. every `EllObj` base has **affine diagonal over `Spec ℤ`** (equivalently: is separated with
affine diagonal). The `QuotientProblemData` structure it builds (`GammaHRepresentability.lean:139`)
has all 6 fields — `prob`, `proj`, `proj_invariant`, `relRep` (KM 7.1.3(1) finite-étale rel-rep),
`couniversal`, `geom_surjective`, `geom_orbits` — proven via the landed `[GHB7]`
`ModuliProblem.exists_quotientProblemData` + `gammaFullNaive_freeAction` (:3431) +
`gammaFullNaive_equivariantRelRepData` (:3529). **All of that is done.**

TASK: prove `hbase` (or restrict the `EllObj` category to bases where it holds and thread it).
For affine/separated elliptic-curve bases it should hold; the diagonal of a separated scheme is a
closed immersion, and closed immersions are affine — so `IsSeparated X.base` (over `Spec ℤ`)
suffices. Search mathlib for `IsSeparated`/`diagonal`/`IsAffineHom` API
(`AlgebraicGeometry.IsSeparated`, `diagonal_isClosedImmersion`, `IsClosedImmersion → IsAffineHom`).
Then Y_H(N) representability is `gammaH_representable_of_orderOf N hN H hinv
(gammaH_relativelyRepresentable N H hinv hbase).some hH`.

### Gate 2 — `hH` (per-H rigidity) — the harder one, the "keystone"

```lean
hH : ∀ (k)[Field k][IsAlgClosed k] (sm) (E) (e : EllObj-iso), e.hom.baseHom = 𝟙 _ →
       e ≠ Iso.refl _ → ∀ γ : ↥H,
       isoPow e (orderOf (γ : GL₂(ZMod N))) = Iso.refl _ → False
```

"No non-trivial base-identical automorphism `e` of `(E, level-H structure)` can be `orderOf γ`-torsion
for `γ ∈ H`." This is the KM 2.7.2 rigidity, per-`H`. Status of the two extreme cases:
- **H = ⊥** (Y(N)): discharged outright — `gammaFullNaive_hfree_bot` (`GammaHMaster.lean`, used by
  `gammaBot_rigidNoeth`). So the H=⊥ `hH` is FREE.
- **General H** (incl. **Borel = Y₀**): the docstring at `GammaHMaster.lean:1069` frames it as the
  "CM-unit/`H` intersection" condition — a base-identical iso has `e^(orderOf γ) = refl` for
  `γ ∈ H`, killed by the CM-unit argument. For H = Borel this is the classical Γ₀(N) rigidity
  (Aut of a Γ₀-structure is ±1 for N ≥ 3, and the Borel-fixed condition forces triviality). This
  needs the per-H endomorphism/CM argument — the genuine remaining mathematics. Look at how the
  full-level `hfree_bot` is proven and generalise the orbit-freeness to the H-twisted setting
  (the `geom_orbits`/`isoPow` machinery is all present).

**Recommended first target: Y₀(N).** Define H = Borel (upper-triangular) ⊂ GL₂(ℤ/N), discharge
`hbase` (Gate 1, geometric), and prove the Borel `hH` (Gate 2). That gives Y₀(N) representable +
smooth affine over ℤ[1/N] via the engine — the headline the previous handover was aiming at.

*(Note: `GammaHClosure.lean` already assembles `gammaFullNaive`/`gammaOneDrinfeld` unconditionally;
add a `gammaH_representable` there that takes only `(N)(hN)(H)(hinv)` once both gates land, by
supplying `hbase` and the per-H `hH` internally — mirroring how `gammaOneDrinfeld_rigid_and_representable`
discharges its `hbound` via `hbound_of_kvc`.)*

---

## 3. Engineering debt to clean (not blocking any math)

1. **Pre-existing `maxHeartbeats` bumps** (NOT from this workstream): 1 in
   `Moduli/EngineDescentCore.lean:322` + 1 in `Moduli/EngineDescent.lean:1628`, both from the older
   T-W7 group-law work (the file-split just relocated one). Every file THIS workstream created is
   **zero-bump** (verified). **The ℰ₃ machine `Moduli/UniversalLevelThree.lean` almost certainly
   carries the same spurious over-provisioned bumps** the ℰ₄ machine did — a *triage pass* (strip
   ALL bumps, build, see the ≤2 that actually fail at 200k) would likely clear most of them, same
   as `UniversalLevelFour` (26 → 0). See §4 for the technique.
2. **One dead `sorry`** — `isFinite_etale_of_comp_of_finite_etale_surjective`
   (`GammaHRepresentability.lean:720`): a `[GH-DESC-GAP]` marker, **consumed by nothing** (its
   docstring says the primary route landed via `SchemeAction.quotient_desc_finite_etale`). Close it
   (needs Chevalley "affine descends along finite surjective", absent from mathlib) or upstream it;
   it blocks nothing.
3. **Quarantined Legendre subtree** (`Moduli/LegendreTorsor.lean`, `Moduli/SqrtCoverGlue.lean`):
   documented non-goals (banner cites `b2_log` `B2-DECISION`). The level-4 rigidifier superseded
   them; only touch if you deliberately want the Legendre route (you don't).
4. **Over-ℤ `ExactOrder` boxes** (`LevelStructure/ExactOrder.lean:117/849/917/948`): statement-
   protected future work (general-base Oort–Tate / Deligne order-kills). The invertible-N receipts
   route around them via `ExactOrderInvertible.lean`; they block nothing at invertible N.

---

## 4. Discipline / hard-won lessons (read before touching heavy files)

- **`maxHeartbeats` is banned** (owner rule). If a proof times out it is almost never "hard" — it's
  `kabstract`/`whnf` on concrete scheme/localization/curve terms. Fixes that WORK (used to reach
  zero bumps in the mouth core AND `UniversalLevelFour`): (a) replace `set x := <heavy> with hx` by
  `obtain ⟨x, hx⟩ : ∃ x, x = <heavy> := ⟨_, rfl⟩` (zero-kabstract binding — often 2–3× alone);
  (b) hoist heavy steps as **barrier lemmas over a VARIABLE ring/curve** and apply at the concrete
  type (keeps localized coefficients atomic — they `whnf` once, not per-rewrite); (c) pass implicits
  explicitly; (d) `congrArg`/`calc` term-mode + `eqToHom` instead of `rw`/`simp` on scheme-typed
  products; (e) `set_option backward.isDefEq.respectTransparency false in` is ALLOWED (transparency
  hint, not a bump). **Measure elaboration cost with `set_option debug.skipKernelTC true` +
  `#count_heartbeats`** — bare `#count_heartbeats` also counts kernel-TC (millions) that the build
  does NOT limit, which is misleading. A **triage build** (strip every bump, build, read the errors)
  tells you which few decls genuinely need work — most bumps are spurious.
- **Heavy-instance imports regress slow proofs.** Importing anything that transitively pulls
  `EllipticCurve/InvariantDifferential` into a file with heavy proofs blows their budget. Fix =
  FILE-SPLIT the consumer downstream (that's why `EngineDescentCore.lean` exists), don't decompose
  the slow proofs.
- **`open CategoryTheory.MonObj` now carries a `notation "γ"`** (from mathlib `Monoidal/Mod.lean`,
  pulled in via the engine). If your file has `γ` binders, do NOT `open MonObj` — reproduce η
  locally: `local notation "η[" M "]" => CategoryTheory.MonObj.one (X := M)` (see the top of
  `GammaHMaster.lean`).
- **Verify builds yourself.** Under machine contention subagents repeatedly mis-report "green" from
  scratch-only type-checks — always run the real `lake build <Module>` + `grep -nE "error[:(]"` +
  `#print axioms` before trusting a completion. `grep "error:"` misses `error(lean.…):` — use
  `grep -nE "error[:(]"`. Never `2>/dev/null` next to a `lake`/`lean` call (guardrail blocks it).
- **Discipline:** atomic pathspec commits; `git fetch` + `rev-list --left-right` before every push;
  push with `LEAN4_GUARDRAILS_BYPASS=1` after verifying green; `.mathlib-quality/` is dev-branch
  process (not merged to `main`).

---

## 5. Artifacts to read (in order)

1. This file.
2. `.mathlib-quality/decomposition-e4.md` — the STREAM-E4 decomposition: verbatim KM quote bank
   (§0), the ℰ₄ ring design (§2), the mouth-core route (§5), the Drinfeld cone census (§7).
3. `.mathlib-quality/tickets.md` — board entries v10.342 → v10.344-FIN (the full narrative of this
   workstream, with the reusable engineering findings inline).
4. `.mathlib-quality/b2_log.jsonl` — the `B2-DECISION` entry (why level-4, why Legendre is
   quarantined) and the earlier B2 refutations.
5. Memory: `modular-curves-km470-engine-complete.md`, `modular-curves-b2-adjudication-level4.md`.

*— end of handover. Sync at write: HEAD `55feda6a3`, `0 0` vs `origin/dev/modular-curves`,
full library green.*

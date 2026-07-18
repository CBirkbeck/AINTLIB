# Black-box decomposition plan

**Owner directive (2026-07-09): only `BB-RR` (Riemann–Roch) may be assumed. Every other
registered black box must be planned out and proved.**

This document decomposes the eight non-RR boxes. Each is classified **BOUNDED** (a real
but finite development, route through existing mathlib / in-repo code) or **MAJOR-INFRA**
(needs a published-paper-scale sub-project — the infrastructure does not exist in mathlib
and must be built). RR stays assumed per the directive.

Mathlib coverage was surveyed 2026-07-09 (see the per-box "mathlib" lines).

**v8 staging correction (2026-07-06 expert review; see `tickets.md` §"Amendments v8"):**
the reviewer's Weierstrass-atlas / quotient-stack route removes the *abstract-side* boxes
from the critical path to the open modular curves. Concretely: **BB-COHBC** (coherent
cohomology & base change) and the *abstract-side* use of **BB-RR** now block ONLY the
abstract-vs-locally-Weierstrass comparison (`T-W-cmp`), the Hodge bundle / modular forms, and
compactification — **not** `Y(N)`/`Y₁(N)`/`Y(ρ̄,p)`. They form a parallel, non-blocking **COH
stream**. The construction-side spine instead uses `LocallyWeierstrass` (T-A8) + the
quotient-stack atlas `[U/G]` (Stream W), where the group law comes from mathlib's Weierstrass
charts + descent (`T-W7`) rather than Abel/Pic⁰ — so **T-A6** (canonicity) also leaves the
critical path. BB-FLAT / BB-DELIGNE / BB-DIFF (the `[N]`/`E[N]` rank+killing boxes) remain
genuine construction-side gaps as classified below; the atlas route does not retire them.

---

## Tier 1 — BOUNDED (discharge in-project, routes verified)

### BB-QF — `[N]` is (locally) quasi-finite  ·  consumer T-B4x / T-B4
- **Statement (KM 2.3.1 fibre input):** on an elliptic curve over a field, `[N]` is
  nonconstant, hence has finite fibres; so `[N] : E → E` is locally quasi-finite.
- **mathlib / in-repo:** in-repo `HasseWeil/Foundation/DegreeQuadraticForm.lean` already
  proves `mulByInt` has degree `N²` (the isogeny-degree quadratic form); a nonconstant
  isogeny has finite fibres.
- **Route (decomposition):**
  1. `[N]` over an algebraically closed field is nonconstant for `N ≥ 1` (HasseWeil
     `mulByInt_degree = N² ≠ 0`, so `[N] ≠ 0`).
  2. nonconstant morphism of curves ⟹ finite fibres (mathlib
     `Scheme.Hom.finite_preimage` for finite morphisms, or quasi-finiteness of a
     nonconstant map between 1-dim varieties).
  3. spread out to `LocallyQuasiFinite (E.mulByHom N)` via the fibre criterion
     (`QuasiFinite.lean` is fibrewise-checkable).
- **Sub-tickets:** T-BB-QF-1 (import HasseWeil degree; nonconstancy over `k̄`), T-BB-QF-2
  (fibrewise ⟹ locally quasi-finite). **Depends on** T-B6 (fibre comparison, stream-B).
- **Effort:** BOUNDED (cross-project import + fibre spread-out).

### BB-DEG — `deg [N] = N²`  ·  consumer T-B4
- **Statement (Silverman III.6.2(d)):** `[N]` on an elliptic curve has degree `N²`.
- **in-repo:** HasseWeil `DegreeQuadraticForm.lean` `mulByInt_degree` — **already proved**
  over a field. This box is essentially "import + fibre comparison".
- **Route:** fibre rank of `E[N] → S` at `s` = `deg [N]` on the geometric fibre = `N²`
  (HasseWeil), transported by T-B6.
- **Sub-tickets:** T-BB-DEG-1 (rank-at-fibre = HasseWeil degree, via `finrank_pullback_snd`
  which is already used in `torsion_rank`). **Depends on** T-B6.
- **Effort:** BOUNDED (the hard math is done in HasseWeil).

### BB-FLAT — `[N]` is flat / fibrewise-flatness (miracle flatness)  ·  consumer T-B4
**(RECLASSIFIED MODERATE→MAJOR after 2026-07-09 survey: mathlib has NO `Module.depth`
and no packaged local-flatness criterion — see the corrected note below.)**
- **Statement (EGA IV 11.3.10 / AK-1 V.3.6):** `[N]` finite between regular schemes of
  equal dimension ⟹ flat (KM's own route); or the general fibrewise-flatness criterion.
- **mathlib:** `RingTheory.Flat` basics + **`RingTheory/Regular/ProjectiveDimension.lean`**
  (Auslander–Buchsbaum machinery: `projectiveDimension`, the `quotSMulTop` recursion).
  NO packaged miracle-flatness or scheme-level fibrewise criterion yet.
- **Route (miracle flatness — the cleaner one):**
  1. over a regular local ring `R` of dim `d`, a finite `R`-module `M` with
     `depth M = d` has `projectiveDimension M = 0` (Auslander–Buchsbaum: `pd + depth =
     dim`), hence `M` is free, hence flat.
  2. the universal Weierstrass base is regular; `[N]`-pushforward is finite;
     equal-dimension ⟹ full depth ⟹ pd 0.
  3. base-change to arbitrary `S` (flatness is base-change-stable — already have the
     scheme instance).
- **Sub-tickets:** T-BB-FLAT-1 (ForMathlib: `Module.Flat` from `projectiveDimension = 0`
  via Auslander–Buchsbaum — check what `Regular/ProjectiveDimension` already gives),
  T-BB-FLAT-2 (miracle-flatness statement: finite + equidimensional + regular ⟹ flat),
  T-BB-FLAT-3 (apply to `[N]` over the universal base).
- **CORRECTION (2026-07-09 survey):** Auslander–Buchsbaum is NOT present — mathlib has
  `projectiveDimension` but **no `Module.depth`** and no A-B theorem (`pd + depth = dim`),
  and no general local-criterion-of-flatness for finite modules over noetherian local
  rings. So BOTH routes need substantial NEW commutative-algebra infra (depth theory +
  A-B, or `Tor₁(M, R/𝔪)=0 ⟹ flat`). `Module.Flat.of_free` exists, so the last step is
  free; the gap is getting `Free`/`flat` from the finiteness+regularity data.
- **Effort:** **MODERATE-to-MAJOR** — a real commutative-algebra development (depth + A-B,
  OR the local flatness criterion). Upstream-candidate, but not a quick discharge.

### BB-DESC — torsor / fppf descent of levelled curves  ·  consumer T-E8/E10
- **Statement:** (i) fppf covers are epimorphisms of schemes [**ALREADY DISCHARGED** this
  session — `Flat.epi_of_flat_of_surjective`, used in T-E11]; (ii) effectivity of the
  descent datum for a levelled curve along a finite-group torsor (GME 2.6.7 form).
- **mathlib:** `AlgebraicGeometry/Morphisms/FlatDescent.lean`, `Sites/Fpqc.lean`,
  `CategoryTheory/Sites/Descent` — the descent framework EXISTS.
- **Route (ii):** in the rigidified situation the cocycle is automatic (Aut = {1});
  descend via the relatively-ample invariant differential `ω` (or the ideal-at-zero
  embedding) ⟹ reduce to MODULE descent, which mathlib's `FlatDescent` provides, then
  reconstruct via `Proj`.
- **Sub-tickets:** T-BB-DESC-0 (survey `Sites/Descent` API), T-BB-DESC-1 (levelled-curve
  ⟶ module-descent datum via `ω`), T-BB-DESC-2 (effectivity from mathlib FlatDescent),
  T-BB-DESC-3 (reconstruct the curve).
- **Effort:** BOUNDED-to-MODERATE (framework exists; the `ω`-embedding reduction is real
  work). **Depends on** BB-COHBC-lite (existence of relatively-ample `ω` — see below).

### BB-DIFF — `[N]` formally unramified when `N` invertible  ·  consumer T-B5y  ·  **owner CHARTER-P3B3**
- **Statement:** `mulByHom_formallyUnramified` (`Torsion.lean:228`): `NIsInvertible S N → FormallyUnramified (E.mulByHom N)`.
- **ROUTE SUPERSEDED (2026-07-08):** the invariant-differential route (`[N]^*ω = Nω` via a scheme-level
  relative-`Ω¹` sheaf + group-translation invariance) is a **mapped DEAD END** — mathlib has no scheme
  `Ω¹` sheaf and this project won't build it. Replaced by the **`E[N]`-torsor route** (KM §2.3,
  non-circular, HasseWeil-anchored): decomposition in `decomposition-km2.3-b5d.md`. MASTER =
  `mulByHom_formallyUnramified'` = L-A ∘ L-BC (assembled, `EllipticCurve/MulByHomUnramified.lean`).
- **STATUS:**
  - **L-A DONE** — `formallyUnramified_mulByHom_of_torsionπ` (`FormallyUnramified (torsionπ N) →
    FormallyUnramified (mulByHom N)`, via `E[N]`-torsor / `of_hom_ext`→`hom_ext`) **PROVED axiom-clean,
    PR #5223** (branch `dev/modular-curves-b5da`).
  - **L-BC TODO** = `formallyUnramified_torsionπ` (`torsionπ` unramified, non-circular) = **T-DISC ∘ L-B**:
    - **T-DISC BANKING (2026-07-08)** — `AlgebraicGeometry.FormallyUnramified.of_finite_fiberToSpecResidueField`
      (finite + all residue-field fibres unramified ⟹ unramified) in NEW
      `ForMathlib/FormallyUnramifiedFibre.lean`. Algebra core
      `Algebra.FormallyUnramified.of_forall_residueField_fiber` **PROVED axiom-clean** (no flatness:
      `tensorKaehlerEquivBase` + `mem_support_iff_nontrivial_residueField_tensorProduct` Nakayama);
      scheme wrapper mirrors `SmoothFiber.lean` (in progress). **DUAL-USE**: also discharges the
      "finite-étale-iff-unramified-fibrewise" input of **T-D6c** ((3)⟺(4)) and **T-D7-bridge**
      (`orderDivisor_etale_iff_geometric`).
    - **L-B = T-B6′ = the WALL (stream-B's box).** Geometric fibres `E[N]_k̄` étale ⟸ a
      **group-compatible scheme-fibre ↔ `WeierstrassCurve k̄` comparison** `E.baseChange t ≅ projModel W_k̄`
      carrying scheme-`[N]`→Weierstrass-`[N]`. **Does not exist anywhere** (no `E.baseChange t ≅ projModel W`;
      the group-compat leg is transitively gated on the *sorried* `abelEnrichment_exists`, GroupLaw.lean —
      geometry→group-law extraction). This is the registered **T-B6 fibre-comparison box (stream-B / T-D8-bridge
      "glued to T-B6")** — several-hundred-LOC, NOT a bounded charter leaf; owned by stream-B, not CHARTER-P3B3.
      HasseWeil supplies the field-level content (`mulByInt_isSeparable`, `torsion_genN_linearEquiv`,
      `mulByInt_degree` — all `Point`/function-field level, **nothing scheme-level**), so T-B6′ is purely the
      transport bridge.
- **UPSTREAM CANDIDATE (mathlib-gap filler, flag for a mathlib PR):**
  `AlgebraicGeometry.isNilpotent_ker_SpecMap (φ : R ⟶ S) (RingHom.ker φ.hom ^ 2 = ⊥) :
  IsNilpotent (Spec.map φ).ker` (`ForMathlib/NilpotentKerSpecMap.lean`) — the elim-side companion of
  `FormallyUnramified.of_hom_ext` (which supplies ring-level `ker φ ^ 2 = ⊥`) for
  `FormallyUnramified.hom_ext` (which asks for `IsNilpotent i.ker` on the scheme-theoretic
  `Scheme.Hom.ker`). mathlib has no such lemma; genuinely general.
- **Effort / verdict (2026-07-08, CHARTER-P3B3 decomposition):** L-A done; **T-DISC banking** (dual-use);
  **L-B = T-B6′ is a WALL** — not a bounded leaf but stream-B's group-compatible fibre-comparison box, rooted
  in the sorried `abelEnrichment_exists`. **Milestone 1 (BB-DIFF discharged) is BLOCKED on stream-B's T-B6.**
  CHARTER-P3B3's max non-blocked contribution to the cascade = **L-A (PR #5223) + T-DISC (banking)**; L-BC then
  closes as `L-A ∘ T-DISC ∘ (stream-B's T-B6)` the moment T-B6 lands. The whole charter étale cascade
  (items 2–4: T-D6b flip, `torsionFixed_of_fixesLevel`, T-D8-bridge) likewise consumes the T-B6 landing.

---

## Tier 2 — MAJOR-INFRASTRUCTURE (published-paper-scale; must be planned as sub-projects)

These three are NOT in mathlib in any form. Per the directive they must still be planned,
but the honest scope is a multi-week development each. Recommend flagging to the owner as
their own workstreams (not blockers for the level-structure spine, which can consume their
*statements* while the proofs are developed in parallel).

### BB-DELIGNE — finite locally free comm. group scheme of rank `N` is killed by `N`
- **Consumer:** T-D5 (exact order ⟹ killed).
- **mathlib:** **NO finite-flat-group-scheme theory** (no `GroupScheme`, no Cartier dual,
  no order/norm argument). Big gap.
- **Decomposition (Deligne's norm argument, per the register):**
  1. finite-locally-free commutative group scheme `G/S` vocabulary (a `GrpObj` in
     `Over S` that is finite locally free) — NEW.
  2. the "norm" / order endomorphism: `N_G : G → G` via the group-algebra `O_S[G]`.
  3. Deligne's lemma: `N · id_G = 0` for `G` of rank `N` (the norm argument).
  Some of this can reuse `Algebra.norm` + FltRegular's norm lemmas (register note).
- **Sub-project:** T-SG (scheme-group vocabulary) → T-OT (Oort–Tate/Deligne). **MAJOR-INFRA.**

### BB-COHBC — coherent cohomology & base change; `Γ(E,𝒪)=Γ(S,𝒪)`; `Rⁱf_*`
- **Consumer:** the Abel canonicity chain (T-A6), relative Picard, and BB-DESC's `ω`.
- **mathlib:** coherent cohomology of schemes is **essentially absent** (only étale/ℓ-adic
  sites). The relevant lane numbers were tracked (#36345/#36218) — coordinate, don't build.
- **Decomposition (GME 1.10.4 / 1.9.12):** `Rⁱf_*` for proper flat `f` + cohomology-and-
  base-change (Grothendieck) + `f_*O_E = O_S` for genus-1 with a section.
- **Sub-project:** **MAJOR-INFRA.** Recommend: coordinate with the mathlib coherent-
  cohomology effort rather than build in-project; keep the *statements* (`Γ=Γ`, `Rⁱf_*`
  base-change) as the interface the Abel chain consumes.

### BB-IRR — geometric irreducibility of `Y(N)`, `Y(ρ̄)`
- **Consumer:** T-F5.
- **mathlib:** absent.
- **Decomposition:** algebraic route (KM Ch. 10 — components via `T[N]`, Tate-curve/cusp
  degeneration — ⧗KM, do-not-formalize-from-memory) OR analytic route (uniformisation,
  hooks LeanModularForms). Buzzard sanctioned sorrying this ("see 1980s").
- **Sub-project:** **MAJOR-INFRA**, latest-phase. Plan both routes; likely stays a
  registered assumption longest, but is now *scheduled*, not permanent.

---

## Summary for the owner

| Box | Effort | Route status | First sub-ticket |
|-----|--------|-------------|------------------|
| BB-QF | BOUNDED | HasseWeil import + fibre | T-BB-QF-1 |
| BB-DEG | BOUNDED | HasseWeil (done over field) + fibre | T-BB-DEG-1 |
| BB-FLAT | MODERATE-MAJOR | needs depth+A-B OR local flatness criterion (NEITHER in mathlib) | T-BB-FLAT-0 (build infra) |
| BB-DESC | MODERATE | mathlib FlatDescent + `ω`-embedding | T-BB-DESC-0 |
| BB-DIFF | MODERATE | relative `Ω¹` sheaf + group induction | T-BB-DIFF-0 |
| BB-DELIGNE | MAJOR-INFRA | group-scheme theory + Deligne norm | T-SG / T-OT |
| BB-COHBC | MAJOR-INFRA | coherent cohomology (coordinate w/ mathlib) | — |
| BB-IRR | MAJOR-INFRA | KM Ch.10 or analytic | — (latest phase) |

**GATING CORRECTION (2026-07-09 survey):** BB-QF and BB-DEG are bounded on the *math*
(HasseWeil has the field-level degree) but **gated on T-B6** (the E[N]-geometric-fibre
comparison, stream-B) to transport to scheme fibres. BB-FLAT needs new comm-alg infra
(above). So NO black box is fully dischargeable in-project *today* without either stream-B
(T-B6) landing or building mathlib infrastructure. The plan below stands; the *order* is:
land T-B6 → BB-DEG/BB-QF fall out → then the infra boxes.

**Recommendation:** the five Tier-1/moderate boxes are genuine in-project work and should
be ticketed now (BB-QF, BB-DEG, BB-FLAT are the highest-leverage — they retire the T-B4
KM-2.3.1 assumptions). The three MAJOR-INFRA boxes are multi-week sub-projects; the spine
should keep consuming their *statements* while they are developed in parallel (or, for
BB-COHBC, coordinated with the mathlib coherent-cohomology effort). Only BB-RR remains a
permanent assumption, per the directive.

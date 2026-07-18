# /develop --decompose — [STREAM-FP] stretch (i): [KM-FMT-FLAT], the First-Main-Theorem flatness gate

*fable-FP, 2026-07-08 (same session as [A711-FP]/[FP-B], see `decomposition-a711-fp.md`).
Gate ledger entry (decomposition-nisog.md §4): "[Γ₁(N)]/[Γ₀(N)]/[N-Isog] flat over ℤ (KM
5.1.1/6.6.1/6.8.1) — powers every universal-case reduction; the single most-shared gate
(L9, L16, L19, L22, L24, L26)". Discipline: v10.8/v10.24/v10.35b.*

## Scoping verdict — what the gate actually is

The six gated NISOG leaves consume ONE pattern, KM's step-(ii)→(iii)→(iv) pipeline
(decomposition-nisog.md §1): *statement true after inverting N* + *ambient moduli space
flat over ℤ* + *locus of truth closed* ⟹ *statement true*. The pattern splits cleanly:

- **[FMT-0] the reduction engine** (THIS charter's bounded deliverable, ForMathlib,
  provable NOW): a closed universal locus (`Scheme.IdealSheafData`, the T-D15 interface
  shape) through which the basic open `D(N) = S[1/N]` factors is ALL of `S`, provided the
  section `N` is regular (a nonzerodivisor) on `S` — i.e. **`S[1/N]` is schematically
  dense in `S` when `S` has no `N`-torsion**. ℤ-flatness enters only as "torsion-free ⟹
  every `N ≠ 0` is regular".
- **[FMT-1/2/3] the flatness instances** for `[Γ₁(N)]`/`[Γ₀(N)]`/`[N-Isog]` over ℤ —
  each a THEOREM OF ITS OWN SCALE (KM 5.1.1 = the Ch. 5 regularity machinery; 6.6.1
  descends from 5.1.1 via A-K VII 4.8; 6.8.1 = Axiomatic Finite Flatness 6.8.2 +
  Serre–Tate 6.8.4 + the one-equation lifting locus 6.8.6). These CANNOT be built today —
  their subject spaces are still under construction by the representability streams
  (Y1/YFULL/GH; the gate ledger already assigns them to the T-E9/T-H9 lineage). They stay
  **tracked interface gates**: the [FMT-0] engine is *parametric* in a regularity/flatness
  hypothesis, so each consumer plugs its space's instance the day it exists.

This is the v10.24(b) opaque-interface move: NISOG's M3 wave binds to [FMT-0]'s signature
now; no leaf waits on KM Ch. 5.

## Sources (all banked verbatim already — cited, not re-fetched; rule 4 honored)

1. **KM 5.1.1 First Main Theorem** (print p. 129, PDF 140) — banked at tickets.md:7611:
   *"Each of the four moduli problems [Γ(N)], [Γ₁(N)], [bal.Γ₁(N)], and [Γ₀(N)] is
   relatively representable over (Ell). Each is finite and flat over (Ell) of constant
   rank ≥ 1, and regular (necessarily of dimension two). Each tensored with Z[1/N] is
   finite etale over (Ell/Z[1/N])."* — flatness-over-ℤ of the total spaces follows from
   the REGULARITY clause (KM's Ch. 5 machinery), which is [FMT-1/2]'s real content.
2. **KM 6.6.1** (print p. 166) — banked verbatim at decomposition-nisog.md:167 (RR-core
   sentence + (Ell)-global clauses: degree `N·∏(1+1/p)`, `[Γ₁]→[Γ₀]` finite flat of rank
   φ(N), *"regularity descends from [Γ₁(N)] (5.1.1) since it is finite flat 'under' it,
   [A-K VII 4.8]"*).
3. **KM 6.8.1 engine** — banked at decomposition-nisog.md:262: *"[N-Isog] finite flat over
   (Ell) via the Axiomatic Finite Flatness Theorem 6.8.2 + Drinfeld's Serre–Tate theorem
   6.8.4 + the one-equation lifting locus 6.8.6"* (marked out-of-stream there; stays a
   tracked gate here).
4. **KM's reduction usage exemplar** (6.7.5, decomposition-nisog.md:189–192): *"universal
   case = [Γ₁(N)] ×_{[Γ₀(N)]} [Γ₁(N)], finite flat over [Γ₀(N)] of degree φ(N)² by 6.6.1,
   hence flat over ℤ), (iii) (physically obvious when N invertible), (iv)"* — the exact
   (ii)/(iii)/(iv) shape [FMT-0] packages.
5. **Consumer interface** (in-project, PROVEN): `ModularCurves.exists_factor_subschemeι_iff`
   (Incidence.lean:846): factoring through `Z.subscheme` ⟺ `Z ≤ t.ker`; T-D14/T-D15
   universal loci are `S.IdealSheafData`.
6. **Mathlib substrate** (verified on the pin): `Scheme.Hom.ker = ofIdeals (fun U ↦
   RingHom.ker (f.app U))` with `Hom.ideal_ker_le` (IdealSheaf/Basic.lean:692–697);
   `IsLocalization.map_eq_zero_iff`; `Module.Flat.torsion_eq_bot`
   (RingTheory/Flat/TorsionFree.lean:84); `IsAffineOpen.isLocalization_basicOpen`.

## Prose proof of the [FMT-0] engine

Let `S` be a scheme, `s ∈ Γ(S, O_S)` a global section that is a nonzerodivisor on `Γ(U)`
for every affine open `U`, and `Z ⊆ S` a closed subscheme (ideal sheaf `I`) such that the
open immersion `D(s) ↪ S` factors through `Z`. Factoring gives `I ≤ ker(res : O_S → O_{D(s)})`
(kernel as ideal sheaves, computed on affine opens). On an affine `U`, `U ∩ D(s) = D(s|_U)`
and `Γ(D(s|_U)) = Γ(U)[1/s|_U]` (localization away from `s|_U`), whose kernel of
localization is the `s`-power torsion `{x | ∃ n, sⁿx = 0}` — zero because `s|_U` (hence
each power) is a nonzerodivisor. So `I(U) = 0` on all affine opens, i.e. `Z = S`. ∎
Bridge: if `Γ(U)` is ℤ-flat (S flat over ℤ), it is torsion-free (`Flat.torsion_eq_bot`),
so every integer `N ≠ 0` is a nonzerodivisor — the KM hypothesis "flat over ℤ" implies the
engine's hypothesis for `s = N`.

## Ordered leaves ([FMT-0] file: NEW `ForMathlib/RegularSectionDensity.lean`)

- **[FMT-0a]** `IsLocalization.Away.ker_algebraMap_eq_bot` — kernel of `R → R[1/f]` is `⊥`
  for `f` a nonzerodivisor. *Match*: the affine heart of "D(s) schematically dense";
  Stacks-level content: 01Z* territory kernel-of-localization = `s`-power torsion via
  `IsLocalization.map_eq_zero_iff` + `IsSMulRegular.pow`.
- **[FMT-0c]** `isSMulRegular_natCast_of_flat` — `Module.Flat ℤ R` + `N ≠ 0` ⟹
  `IsSMulRegular R (N : R)`. *Match*: "flat over ℤ" ⟹ torsion-free
  (`Module.Flat.torsion_eq_bot`) ⟹ `N` regular; this is the ONLY place ℤ-flatness is
  consumed — everything else is `s`-regularity.
- **[FMT-0b-i]** `Scheme.ker_basicOpenι_eq_bot` — `(S.basicOpen s).ι.ker = ⊥` for `s`
  affine-locally regular. *Match*: per-affine-open reduction of the prose proof;
  `Hom.ideal_ker_le` + `IsAffineOpen.isLocalization_basicOpen` + [FMT-0a].
- **[FMT-0b]** `Scheme.IdealSheafData.eq_bot_of_basicOpenι_factors` — THE GATE INTERFACE:
  a universal locus `Z` through which `(S.basicOpen s).ι` factors is `⊥`. *Match*: KM
  (ii)+(iii)+(iv) packaged; consumers apply their T-D15-shaped locus + their space's
  [FMT-i] flatness instance (via [FMT-0c]) + their elementary-over-ℤ[1/N] check (iii) as
  the factoring hypothesis.

Gates OUT of this file (tracked, interface-only): **[FMT-1]** `[Γ₁(N)]` flat/ℤ (KM 5.1.1
regularity stream), **[FMT-2]** `[Γ₀(N)]` flat/ℤ (6.6.1, descends from FMT-1), **[FMT-3]**
`[N-Isog]` flat/ℤ (6.8.1/6.8.2 Serre–Tate stream). Each waits on its space existing
(representability streams) — boarded as gate tickets, not leaves.

## Adversarial block ([FMT-0], ≥3)

1. **"Schematic density needs qcqs/noetherian"**: NO — the factoring hypothesis is
   through a CLOSED subscheme given by an `IdealSheafData` (per-affine-open data), so the
   argument is purely affine-local; no global finiteness is used. (The classical
   "scheme-theoretic image" subtleties arise for non-qc opens in non-affine targets; we
   never form an image, we test against a given `Z`.)
2. **"ker ≤ vs =" trap**: `Hom.ker` is `ofIdeals` of the app-kernels, and mathlib only
   gives `ideal_ker_le` (≤). The proof needs exactly the ≤ direction (`Z.ideal U ≤
   ker(app U) = ⊥`), so the completion subtlety is harmless. Attack fails.
3. **"U ∩ D(s) vs D(s|_U)" defeq trap**: `Scheme.basicOpen_res`-style lemmas make the
   identification propositional, not defeq; the localization instance is stated for
   `U.basicOpen (res s)` — budget a rewrite chain, and if elaboration crawls, split per
   v10.24 (private helper per identification).
4. **Wrong-hypothesis attack (regular on ⊤ vs on all affines)**: global regularity of
   `s ∈ Γ(S,⊤)` does NOT imply regularity on every `Γ(U)` for general `S` (sections don't
   inject into products of affine sections without separatedness-ish hypotheses... they
   DO inject for any scheme via the affine cover sheaf condition — but the RESTRICTION
   maps need not be injective). The hypothesis is therefore quantified over affine opens
   (the form ℤ-flatness delivers pointwise anyway via [FMT-0c] per-`U`). Interface pins
   this; consumers holding "flat over ℤ" hold it per-`U` for free.
5. **Consumer-shape attack**: NISOG leaves test loci against arbitrary `T → S`
   (T-D15 ∀-⦃T⦄ form). [FMT-0b] concludes `Z = ⊥`, whence `Z ≤ t.ker` for every `t` —
   i.e. every `t` factors (`exists_factor_subschemeι_iff`), recovering the ∀-form. ✓

## Skeleton & status — ★ SUPERSEDED SAME SESSION: ALL FOUR LEAVES PROVEN

`ForMathlib/RegularSectionDensity.lean` went skeleton→green→**sorry-free in one session**
(2026-07-08T15:43Z): [FMT-0a], [FMT-0c], [FMT-0b-i], [FMT-0b] all proven, `#print axioms`
= [propext, Classical.choice, Quot.sound] on each, 2579 jobs green. Proof notes vs. the
adversarial block: attack 3's eqToHom fear didn't materialize — the whole opens
identification is `image_preimage_eq_opensRange_inf` + `opensRange_ι` + `basicOpen_res` +
`inf_comm`, and mathlib's `IsAffineOpen.isLocalization_of_eq_basicOpen` ties the
localization structure to `(S.presheaf.map i.op).hom.toAlgebra` directly (the `letI` +
type-ascribed `haveI` pattern forces the defeq at elaboration; instance-search alone
fails at reducible transparency — fleet-reusable note). Root registration deferred
(sweep hazard), file enters the graph when its first consumer imports it.

## Board

Leaves boarded §v10.44b as [FMT-0a/0b/0b-i/0c] (claimed + DONE, fable-FP); gates
[FMT-1/2/3] registered unclaimed with their banked sources.

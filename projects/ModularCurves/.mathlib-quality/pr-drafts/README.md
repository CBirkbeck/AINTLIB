# Upstream PR drafts — staged locally (DRAFTS ONLY)

**These are not open PRs.** Submitting to mathlib is an **owner action**; this directory
just stages the mathlib-ready extracts so the owner can submit them with zero re-derivation.
Each file opens with a `PR DRAFT` metadata block (target mathlib file, placement, shortening
opportunity, import notes) that the owner strips before submission.

Ranking and verification: see `../upstream-ledger.md` (the T-UPSTREAM-TRIAGE deliverable).
Every candidate below was checked against *current* mathlib (searched, not assumed) and is
axiom-clean in-project.

**Re-verified 2026-07-09** (v10.94 staging pass): all four drafts compile clean standalone
(`lake env lean`, exit 0 each) on the current toolchain/mathlib pin — no bump rot. Ledger
gains §8 (two confirmed mathlib gaps from the route-a survey; future candidates, not staged).

| File | Lemma(s) | Target mathlib file | Class |
|------|----------|---------------------|-------|
| `01-Functor-map_zpow.lean` | `Functor.map_zpow'` | `CategoryTheory/Monoidal/Cartesian/Grp.lean` | sibling of `map_inv'` |
| `02-AdjoinRoot-isDomain_of_monic_of_map.lean` | `Polynomial.dvd_of_monic_of_map_dvd_map`; `AdjoinRoot.mapRingHom(_injective)`; `AdjoinRoot.isDomain_of_monic_of_map`; `HomogeneousLocalization.isDomain_away` | `RingTheory/AdjoinRoot.lean` (+ Polynomial, + HomogeneousLocalization) | shortens `EllipticCurve/Affine/Point.lean:194` + fills-gap |
| `03-IdealSheafData-comap_mul.lean` | `comap_mul`, `comapMonoidHom`, `comap_prod` (+ affine-local supporting lemmas) | `AlgebraicGeometry/IdealSheaf/Functorial.lean` | completes the `comap` monoid API |
| `04-IdealSheafData-exists_factor_comap_iff.lean` | `exists_factor_comap_iff` | `AlgebraicGeometry/IdealSheaf/Functorial.lean` | factoring corollary of `comapIso` |

## Submission order (owner)

1. **#1** `map_zpow'` — cleanest; a one-declaration sibling PR. Start here.
2. **#2** as **two PRs** in dependency order: the `Polynomial` dvd lemma first, then the
   `AdjoinRoot` cluster that depends on it. `isDomain_away` is a **third, independent** PR
   (different subject — HomogeneousLocalization).
3. **#3 + #4** can share one PR (same target file, `Functorial.lean`) or ship separately;
   #4 is a 6-line self-contained corollary either way.

## Not staged (need owner/other-worker input — see ledger §5–§7)

- **#5** `OverPullbackMul` (fable-P4) — content overlaps mathlib's `Over.pullback` monoidal
  API; needs fable-P4 to confirm what's genuinely absent. OWNER-INPUT.
- **#6** D2 homological suite (Buchsbaum–Eisenbud, Hilbert syzygy) — genuinely absent from
  mathlib and high-value, but B-E is mid-construction (live sorries). Defer to a D2-owned
  verify-pass once B-E is sorry-free.
- **#7** P3b3 bridge pieces — project-specific coordinate-ring transport; no upstream shape
  identified. OWNER-INPUT.

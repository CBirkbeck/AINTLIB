# Ecosystem survey — 2026-07-05 (three agents: mathlib PRs, external repos, AINTLIB rescan)

*Full agent reports archived in the session; this file is the actionable digest.
BINDING coordination policy at the end.*

## Reuse / coordinate / watch table

| Item | Where | Impact on our board |
|---|---|---|
| **Tate normal form PR #25218 (kckennylau)** + #26078 | mathlib PR, open | **T-E1/T-E2 overlap directly.** Before working them: check PR state; either review/complete the PR upstream or align statements verbatim. OWNER ACTION: coordinate on the Zulip "Modular curves" thread (we are participants). |
| Universal elliptic curve #41300 (alreadydone) | mathlib PR, active 2026-07-03 | Supersedes NagellLutz `Universal.lean` upstream; our elementary-families tickets consume whichever lands. |
| Group scheme structure on Weierstrass curves #35151 + Zulip blueprint (Junyan Xu, Feb 2026) | mathlib PR (draft) | **Alternative discharge of the `EllipticCurve` group field for the locally-Weierstrass case** via Bosma–Lenstra complete addition laws — a second route to `abelEnrichment_exists` that avoids Pic⁰ for Weierstrass models. Track; do not duplicate. |
| Hopf ≌ affine group schemes #40500 (YaelDillies et al., FLT/toric labels) | mathlib PR, active | DS3 wiring (T-B2) and stream OT's vocabulary. Build against it. |
| **YaelDillies/toric** `GroupScheme/{Diagonalizable,Character,Torus}`, `Hopf/*` | external repo, Apache-2.0, current toolchain, upstreaming live | `Diag(ℤ/n) = μ_n` + character/Cartier-duality material for diagonalizable groups: **T-B2 and AG-CD should import/align, not rebuild.** |
| Sheaf cohomology: merged `Sheaf.H`, Čech; open #36345 (affine vanishing), #36218 (LES), #35790, #35073 (Riou/Nugent) | mathlib | COH-3 lane exists and is owned. **Do not build cohomology foundations.** Our COH stream = the UNCLAIMED layer: `R^i f_*`, COH-1 (base change), COH-2 (`π_*O = O_S`). Coordinate with Riou/Nugent before cutting COH tickets. |
| Descent: merged descent-data + property-descent; **effectivity #24434** (Riou–Merten, infra merged, PR stale-ish); #34015 (schemes affine over base) | mathlib | DESC stream: framework reusable now; effectivity for schemes = watch #24434; torsors unclaimed. Our `ellipticCurve_fppf_descent` route (relatively-ample embedding) may reduce to affine-morphism effectivity = #34015's territory. |
| Weil-divisor → RR pipeline: #38472/#38953/#41198 (**Raph-DG**, very active) | mathlib | **Do not touch Weil divisors.** Effective *Cartier* divisors are unclaimed = OURS (streams D0/D). Coordinate naming with Raph-DG on Zulip before D0 tickets close. |
| Flatness criteria | mathlib: nothing open | **FLAT stream is genuinely ours** (fibrewise criterion [A-K 1, V 3.6] / EGA IV 11.3.10; local criterion). Cleanest "must prove" item; mathlib has the local-ring free/flat lemmas as substrate. |
| **SmwYin/XYin** (modular polynomials, X₀(N) function-field model, Cox Ch. 11 route; uses `.mathlib-quality` tickets!) | external repo, NO LICENSE, 61 sorries | Complementary route to X₀(N) (function-field, not moduli). OWNER ACTION: contact author re licence + coordination (the repo builds on your modular-forms work; `dual` branch from SmwYin already exists in OUR repo remotes!). |
| loefflerd/ModularFormDimensions (`OpenModularCurve Y(𝒢) = 𝒢\ℍ`, 0 sorries) | external repo, no licence | The analytic Y(Γ) object for the phase-3 comparison + IRR analytic route. Small; likely upstreamed by author; statement-mine. |
| FLT repo | external | `GroupScheme/FiniteFlat.lean` + `TateCurve/TateCurve.lean` are ZERO-CODE stubs; FLT `knownin1980s`-sorries Mazur et al. **No collision; FLT is a downstream consumer of our KM programme.** Coordinate on the two stub files (offer to fill them from streams OT/Tate). |
| WenrongZou/FormalGroupLaws (heights, Lubin–Tate; mathlib `RingTheory/FormalGroup` upstreaming started) | external, no licence | OT/char-p side; build against mathlib's `FormalGroup` + HasseWeil's; watch upstream. |
| Vacuums confirmed (nobody anywhere): | | EC over schemes as such, Weil pairing, **Tate curve**, finite-flat group scheme theory proper, p-divisible groups, eff. Cartier divisors, `R^i f_*`+base change, fppf torsors, KM moduli. = exactly our programme; no redo risk. |

## AINTLIB rescan — incremental reuse for the de-black-boxed streams

1. **OT/killed-by-N**: FltRegular `Hilbert92.lean` norm-of-units machinery
   (`Units.map (RingOfIntegers.norm)`, `norm_eq_prod_pow_gen`, `norm_map_zpow`) = the
   Deligne-norm-argument substrate; + HasseWeil `FormalGroup/{CharP,Height,MulByNat}`
   (`[p](T) = g(T^p)`, height additivity) for the char-p analysis; + fibre anchor
   `NTorsion/TorsionPow` (`E[ℓⁿ]` killed by `ℓⁿ`).
2. **DESC**: HasseWeil `Isogeny/{Dual/Descent, GroupHom/Descend}.lean` —
   "descends ⟺ Galois-fixed" + base-change-then-descend engines; FltRegular
   `Hilbert94.lean` (cyclic Galois descent of ideals/units via mathlib Hilbert 90).
3. **COH/Picard**: `HasseWeil.ClassGroup.relNorm` (Pic-pushforward over arbitrary
   Dedekind extensions — fully relativised); `Pic0/ToClassSurjective` shows the
   Pic⁰ ≅ E theory is ClassGroup-structured (relativisation-friendly inputs).
4. **FLAT substrate**: `CurveMapBaseChange.lean` free/flat base-change plumbing;
   `FiniteOverKx.lean` (F[C] free rank 2 over F[X]); FltRegular
   `IsIntegralClosure.finite`.
5. **IRR**: no Tate-curve/algebraic-q-expansion material anywhere in AINTLIB (dev
   worktree NOT ahead); the analytic hook is LeanModularForms
   `DimGenCongLevels/NormTransfer.lean` + cusp machinery. Algebraic route source =
   GME 2.5.2–2.5.3 + 2.9.3 (in hand).

## BINDING coordination policy (added to the board's standing rules)

- Before starting T-E1, T-E2, T-B2, any D0 ticket, or any COH ticket: check the
  named PR/lane above; if live, align statements with it and record the
  decision in the ticket's log. Duplicating a live mathlib PR is a B2-grade offence
  (AINTLIB's cardinal sin, extended to the ecosystem).
- OWNER ACTIONS (Chris): (a) post the KM-programme plan summary to the Zulip
  "Modular curves" thread; (b) licence/coordination ping to SmwYin (XYin) — note
  their `dual` branch already sits in our remotes; (c) optional: offer FLT the
  FiniteFlat/TateCurve stub fills.

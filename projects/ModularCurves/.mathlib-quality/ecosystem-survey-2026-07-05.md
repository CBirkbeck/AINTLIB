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

## BINDING reuse policy (v2 — "copy by default, with discipline")

Three tiers, by licence:

**Tier 1 — COPY NOW (Apache-2.0 / mathlib code, incl. open PR branches):**
mathlib PRs #25218 (Tate normal form), #41300 (universal curve), #35151 (Weierstrass
group law), #40500 (Hopf ≌ affine group schemes); YaelDillies/toric
(Diag/μ_n/Character); FLT infrastructure. Mechanics (the **VENDOR register**):
- vendored code goes under `ModularCurves/ForMathlib/`, one file per source, with a
  provenance header: source repo/PR#, commit, licence, and the rule
  `DELETE WHEN UPSTREAM LANDS`;
- every vendored file is listed in the VENDOR table below; the daily-bump worker and
  every `[CLEANUP-*]` ticket check the table: if the upstream PR merged, delete the
  vendored file and switch imports to mathlib (this is the ONLY reason copying an
  in-flight PR needs care: AINTLIB bumps mathlib daily, so PRs are future upstream);
- adapt-don't-fork: keep names as close to the source as possible so the
  delete-and-switch is mechanical.

| Vendored file | Source | Delete when |
|---|---|---|
| `ModularCurves/ForMathlib/TateNormalForm.lean` | mathlib PR #25218 (kckennylau/tatenf @ 8b7741e0), Apache-2.0 | PR #25218 merges (then switch T-E1 to mathlib's `toTateNF` and offer our `toTateNF_unique` + `Ψ₃_eval_X` additions on the PR thread) |
| (next candidates: toric `Diag` → T-B2) | | |

**Tier 2 — RESOLVED by author permission (owner, 2026-07-05):** XYin (owner's
student) and loefflerd/ModularFormDimensions — copying permitted; treat as Tier 1
(vendor with provenance headers crediting the author; best practice: get the OK in
writing / a LICENSE file added before anything ships in a public release, since
AINTLIB redistributes). erdOne/QuasiCoherent stays read-only (mathlib staging; will
land upstream anyway).

**Needs-assessment (2026-07-05, so nobody vendors for the sake of it):**
- *Loeffler/ModularFormDimensions*: unique delta vs AINTLIB = the quotient object
  `Y(𝒢) = 𝒢\ℍ` with divisors/orders on the quotient. Consumed only in **phase 3**
  (analytic comparison `Y(N)(ℂ) ≅ Γ(N)\ℍ`, stream IRR analytic route). Vendor then,
  not now.
- *WenrongZou/FormalGroupLaws*: **nothing needed** — HasseWeil's FormalGroup/ already
  covers the programme's formal-group uses (height, [n], char-p `[p](T)=g(Tᵖ)`),
  sorry-free; Wenrong's extras (Lazard universal FGL, Lubin–Tate) are out of scope.
  Only relevance: his defs are becoming mathlib's `FormalGroup` API — future
  AINTLIB-wide dedup item (HasseWeil ↔ mathlib) at some daily bump; track, don't copy.
- *XYin*: the genuinely useful pieces are the Φ_m modular-polynomial/function-field
  model of X₀(N), the Kronecker congruence, and integral q-expansions of Δ, j —
  phase 2–3 (Γ₀/N-Isog cross-checks, cusps/q-expansions) and phase 4 (KM Ch. 12/
  Igusa-adjacent). Vendor per-need with provenance.

**Tier 3 — COORDINATE-THE-DESIGN (active mathlib lanes owned by others):** COH
`R^i f_*` lane (Riou/Nugent), Weil divisors (Raph-DG), descent effectivity (#24434).
Here the point is not permission but that mathlib's eventual API wins by default in a
daily-bumped monorepo — steer it (Zulip) or track it; do not silently diverge. Posting
the KM plan to the Zulip modular-curves thread is an optimisation of this, not a gate.

Owner-level items reduced to: (a) licence pings to SmwYin + Loeffler (Tier 2 unlock);
(b) optional Zulip post (Tier 3 steering). Everything in Tier 1 is workable now by
any agent following the VENDOR register discipline.

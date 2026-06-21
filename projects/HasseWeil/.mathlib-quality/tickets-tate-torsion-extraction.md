# Ticket board — Tate-torsion extraction → mathlib

Dev-side piece of the main-branch extraction **epic #2546** (GitHub). The N-torsion structure, Tate
module, and Weil pairing are already **proven on `main`** (files cleaned); mathlib has **none** of it
(`Mathlib/AlgebraicGeometry/EllipticCurve/` has no torsion structure / Tate module / Weil pairing), so
this is a genuine upstream contribution.

## Already exists on main (do NOT re-prove)
- `torsion_ellPow_linearEquiv` — `E[ℓⁿ] ≃ₗ[ZMod ℓⁿ] (Fin 2 → ZMod ℓⁿ)`  (`TateModule/TorsionPowStructure.lean`)
- `torsion_ell_linearEquiv` — `E[ℓ] ≃ₗ[ZMod ℓ] (Fin 2 → ZMod ℓ)`  (`WeilPairing/TorsionModule.lean`)
- `tateModule`/`tateCompat`, `rhoTateGL`  (`TateModule/`); Weil pairing + non-degeneracy (`WeilPairing/Pairing*.lean`)

## The ONE dev ticket (genuinely new math)

**T-TATE-GENN — general-`N` torsion structure.** Prove
`E[N] ≃ₗ[ZMod N] (Fin 2 → ZMod N)` for arbitrary `N` (with `N` invertible in the alg-closed base),
by CRT over the prime-power factorisation — the only piece NOT yet on main (we have only `E[ℓⁿ]`):
1. `ZMod N ≃+* ∏ ZMod (pᵢ^kᵢ)` (mathlib `ZMod.chineseRemainder` / `Nat.factorization`).
2. `E[N] ≅ ⨁ E[pᵢ^kᵢ]` — torsion of pairwise-coprime orders splits as a direct sum.
3. Assemble the `ZMod N`-linear equiv from the existing prime-power `torsion_ellPow_linearEquiv`.

**Acceptance:** sorry-free; `#print axioms` = only `propext`/`Classical.choice`/`Quot.sound`;
`lake build HasseWeil` green **and** `lake build HasseWeil.<NewModule>` (by name — it'll be an orphan
until imported). This is the headline statement for the mathlib PR (GitHub **#2549**).

## NOT dev work (tracked on main, GitHub — do not duplicate here)
Isolating the minimal dependency cut + mathlib-style restatement of the EXISTING results is
extraction/packaging, not new math: GitHub **#2547** (E[ℓⁿ]), **#2548** (E[ℓ] + Weil pairing), **#2550**
(Tate module). Those are `mathlib:pr` tracking tickets on the main side.

## Protection (already in place)
`TateModule/*` and `WeilPairing/{Torsion,Pairing}*` are listed in `docs/worker-prompts/protected-paths.txt`
on `main`, so the cleanup/generalise/decompose fleet will **not** touch them while this extraction is
active — `main` stays stable under you and this branch won't be churned on rebase. Remove those lines
(and close #2546) once the extraction lands.

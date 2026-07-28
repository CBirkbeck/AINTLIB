# HRW sub-campaign decomposition — head-localization reducedness (BGR 7.3.2/10)

Opened 2026-07-28 on user authorization ("open the BGR work").  Adjudication and
route analysis: `chatgpt-review-2026-07-28.md` § "The wall" (4-lemma structure,
counterexamples to the shortcut routes, char-2 truth confirmation).  Goal: discharge

  `HeadLocsReduced K w : ∀ N (DH : RationalLocData (WPHead K w N)), DH.IsRational →
    IsReduced (presheafValue DH)`

— the quarantined hypothesis of endpoints (3).  Classical source: BGR 7.3.2/10 via
the completed-local comparison + analytic unramifiedness; we follow the reviewer's
head-specific plan, with the graph model `QHead` as the concrete localization.

## Skeleton
`projects/AdicSpaces/Adic spaces/WP/HeadReduced.lean` (statements sorried, builds).

## The four lemmas (reviewer-adjudicated structure)

### HRW-L2 `isReduced_of_forall_completedLocal_reduced` (mathlib-grade; EASIEST — start here)
Noetherian `R` with all completed local rings at maximal ideals reduced is reduced.
Prose: let `x` be nilpotent.  For each maximal `𝔪`, its image in `R_𝔪` is nilpotent;
the map `R_𝔪 → (R_𝔪)^` (adic completion at the maximal ideal) has kernel
`⋂ (max)ⁿ = 0` by Krull intersection (`Ideal.iInf_pow_eq_bot_of_isLocalRing`,
VERIFIED in mathlib, Filtration.lean:34/426 area; `R_𝔪` noetherian local), so the
image of `x` in the reduced completion is 0 forces `x/1 = 0` in `R_𝔪`; vanishing at
all maximal localizations forces `x = 0` (`Ideal.mem_of_localization_maximal` at
`J = ⊥`, VERIFIED LocalProperties/Basic.lean:539).
Leaves: (i) kernel-of-completion = ⋂ powers (state as: `x ∈ ⋂ 𝔪ⁿ` from vanishing
image — via `AdicCompletion.of` and its coefficientwise characterization; if the
kernel lemma is absent, prove membership in every `𝔪ⁿ` directly from the completion
vanishing at level `n`); (ii) the two cited mathlib lemmas.  All-mathlib; no WP
dependence.  Sizing: reviewer gives the proof in 3 sentences; expect ~80 LOC.

### HRW-L1 `qHead_completedLocal_comparison` (deps: W15, W16 — the QHead layer)
For a head datum `DH` and a maximal `𝔮 ⊂ QHead DH` with `𝔭 := 𝔮.comap (headToQ DH)`:
`((WPHead)_𝔭)^ ≅ ((QHead DH)_𝔮)^` (completed local rings at the maximal ideals of
the localizations).  Reviewer's sketch: "Prove this first for the graph
presentation, using that the denominator becomes a unit and that modulo every power
of the maximal ideal the restricted-series variables evaluate uniquely.  Then pass
to inverse limits."  Decomposition:
- L1.a `headToQ` (the canonical hom head → QHead = quotient ∘ polyToP ∘ C) + `𝔭`
  maximal (Tate-scope: the fibre argument — s ∉ 𝔮 since s is a unit; standard).
- L1.b mod-𝔮ⁿ evaluation: `(QHead DH)/𝔮ⁿ ≅ (WPHead)_𝔭-side/𝔭ⁿ`-comparison: in the
  quotient by `𝔮ⁿ` the variables `T_i` are determined (`T_i = f_i/s`, `s` invertible
  mod every power since `s ∉ 𝔮`), and restricted series collapse to polynomials mod
  each power (coefficients below any ϖ-power vanish in the artinian quotient —
  uses that `ϖ ∈ 𝔮`?? NO — ϖ is a UNIT; the collapse is: mod 𝔮ⁿ the ideal 𝔮 is
  nilpotent and the graph relations make T_i integral-rational — the honest leaf is
  the surjectivity + kernel computation of `(head-polynomials in T)/(graph,𝔭ⁿ-side)
  → QHead/𝔮ⁿ`; state carefully at skeleton refinement).
- L1.c inverse limits: `AdicCompletion` functoriality along the compatible tower.
Frontier flag: L1.b is genuinely new mathematics (no mathlib precedent for
Tate-graph completed-local comparisons); it is however finite-level COMMUTATIVE
ALGEBRA (artinian quotients), not analysis.

### HRW-L3 `head_completedLocal_reduced` (THE frontier)
Every completed local ring of the head at a maximal ideal is reduced.  Case split
on `WaHead ∈ 𝔭`:
- **L3.a, `W ∉ 𝔭`** (Z-elimination): in `(WPHead)_𝔭`, `W` is a unit and
  `Z_i = W^{−2w i}·Y_i²`, so the local ring is a localization of (the head with the
  Z's eliminated) = the FULL Tate algebra `K⟨W, U_{≤N}⟩` localized at the pulled-back
  maximal (`A_N[1/W] = K⟨W,U_{≤N}⟩[1/W]`, an equality of subrings of the ambient —
  provable by the support model: `U_n = W^{−w n}·Y_n`).  The leaf becomes: completed
  locals of the FULL Tate algebra `K⟨X_0,…,X_N⟩` at maximals are reduced — classical
  regularity of Tate algebras.  Sub-frontier with a standard route: residue fields
  of maximals are finite over `K` (affinoid Nullstellensatz — CHECK the 828b layer's
  7.51/7.52 artifacts first: `exists_hSpa_points_*` machinery may contain the needed
  finiteness) and the completed local is then a formal power-series ring over a
  finite extension (Cohen-style, but constructible by hand here: regular system of
  parameters `X_i − a_i` after base change... state the leaf as
  `tateAlgebra_completedLocal_reduced` and sub-decompose when reached).
- **L3.b, `W ∈ 𝔭`** (the quadratic tower at the singular point): then every
  `Y_i ∈ 𝔭` (from `Y_i² = W^{2w i}Z_i ∈ 𝔭`, primality).  The completed local ring
  is the `(W,Y,…)`-adic completion of the local quadratic tower; reviewer: "one must
  analyze the formal relations themselves" (char-2-safe).  Plan of attack when
  reached: the explicit monomial model gives the completed local ring an explicit
  description as a sub-power-series ring (the support condition localized); reuse
  the Φ-style embedding into a formal domain to kill nilpotents — the analogue of
  `isReduced_tailC0` one level down.  This is the deepest leaf of the whole
  campaign; expect its own decomposition round when its ticket opens.

### HRW-L4 `headLocsReduced` (assembly; deps L1+L2+L3 + W16 headLocEquiv)
`P := presheafValue DH ≅ QHead DH` (W16); `QHead` noetherian (W15 layer + 828b
machinery); by L2 it suffices that all completed locals of `QHead` are reduced; by
L1 those agree with completed locals of the head; by L3 the latter are reduced.
Then endpoints: `weightedParity_chainReduced_unconditional` etc. in Main.lean (NEW
theorems; the conditional forms stay).

## Adversarial notes
- L2 attack (composition): does reducedness really localize upward? — yes:
  `x/1 = 0` in ALL `R_𝔪` ⇒ `x = 0` is exactly mem_of_localization_maximal at ⊥;
  and nilpotents localize to nilpotents (ring-hom images).  SURVIVED.
- L1 attack: is `𝔭 := comap` maximal (not just prime)?  For Tate rings the
  localization map is NOT finite; maximality of the contraction is a genuine claim —
  in rigid geometry it holds for affinoid subdomain maps (max-spec functoriality,
  BGR 7.2.2/1-ish).  FLAGGED: L1.a must not assume it silently; if hard, weaken L2
  to "completed locals at all PRIMES pulled from maximals" or restate L1/L3 over
  the primes that occur.  The decomposition keeps `𝔭` as *the contraction* and L3
  quantifies over ALL maximals of the head PLUS (if needed) the contracted primes —
  L3's statements therefore take `[𝔭.IsPrime]` with local-ring completion, NOT
  IsMaximal, wherever the proof allows.  (Krull intersection needs only
  noetherian-local ✓ works at primes.)
- L3.a attack: `A_N[1/W] = K⟨W,U⟩[1/W]` is an ALGEBRAIC localization statement —
  fine — but the completed local comparison then needs the two rings' localizations
  at the SAME maximal to agree: they do, as the rings agree after inverting W ∉ 𝔭.
  SURVIVED (as algebra; the Tate-regularity leaf remains).

## Ticket chain (appended to the main board)
HRW-1 (L2) → HRW-2 (L1.a headToQ + maximality-or-primality) → HRW-3 (L1.b/c
comparison) → HRW-4 (L3.a Z-elimination + Tate-local leaf) → HRW-5 (L3.b tower) →
HRW-6 (L4 assembly + unconditional endpoints).  HRW-1 is dispatchable immediately
(pure mathlib); HRW-2+ gated on W15/W16 (the QHead layer) which sit on the main
board's critical path anyway.

# Decomposition — `presheafValue D` strongly noetherian (faithful t.f.t. route)

`/develop` 2026-06-05. Source read in full: Wedhorn §6.6 (Def 6.28–Prop 6.35, `wedhorn.txt:2568`–
`2672`) + §6.7 (Prop+Def 6.36, Remark 6.37, Example 6.38, `wedhorn.txt:2674`–`2707`).

## Goal
`IsStronglyNoetherian (presheafValue D)` (= `O_X(V)` again strongly noetherian Tate; the Prop 8.30
base step), for `A` strongly noetherian Tate, `D : RationalLocData A`. NO noetherian ring of
definition.

## Source proof (transcribed, NOT invented)

**Example 6.38** (`wedhorn.txt:2700`–`2707`): "If `A` is a strongly noetherian Tate ring … In
particular, `Â⟨T/s⟩` is again strongly noetherian." The justification is:

**Remark 6.37(1)** (`wedhorn.txt:2682`): "If `A` is a strongly noetherian Tate ring, then every Tate
ring topologically of finite type over `A` is **strongly noetherian** by Proposition 6.33."

combined with **Example 6.32(2)** (`wedhorn.txt:2637`–`2641`) / Example 6.38 (`2695`): "the canonical
homomorphism `A → Â⟨T/s⟩` is **topologically of finite type**."

**Prop+Def 6.36** (`wedhorn.txt:2675`–`2680`): `A` strongly noetherian ⟺ **(i)** `Â⟨X₁..Xₙ⟩`
noetherian ∀n ⟺ **(ii)** every Tate ring t.f.t. over `A` is noetherian. "follows immediately from
6.34."

### What the chain actually needs (traced to the bottom)

`IsStronglyNoetherian (presheafValue D)` = `∀ m, (presheafValue D)⟨Y₁..Yₘ⟩` noetherian. For each `m`:

1. `(presheafValue D)⟨Y₁..Yₘ⟩` is **strictly topologically of finite type over `A`** — there is a
   **surjective** continuous `A`-algebra hom `Â⟨Z₁..Z_{n+m}⟩ ↠ (presheafValue D)⟨Y₁..Yₘ⟩`
   (`Zᵢ ↦ tᵢ/s` for `i ≤ n`, `Z_{n+j} ↦ Yⱼ`), `n = |D.T|`. [Def 6.28, Example 6.32(2) generalised to
   the relative target.]
2. `Â⟨Z₁..Z_{n+m}⟩ = restrictedMvPowerSeriesSubring (n+m) A` is **noetherian** — directly from `A`
   strongly noetherian (Def 6.36(i)), NO Fubini, NO ring of definition.
3. **A quotient of a noetherian ring is noetherian** (`isNoetherianRing_of_surjective`) — this is the
   *clean half* of Def 6.36 (i)⟹(ii): `B` strictly t.f.t. ⟹ `Â⟨Z⟩ ↠ B` ⟹ `B` noetherian.

### ★ KEY SIMPLIFICATION (faithful, verified by reading the full §6.6)

The route needs **only** Def 6.36 (i)⟹(ii)'s *quotient-of-noetherian* step (3 above), which is just
`isNoetherianRing_of_surjective`. It does **NOT** need the deep §6.6 machinery:
- NOT Def 6.29's four-way equivalence (i)⟺(ii)⟺(iii)⟺(iv) (and its external (iii)⟹(iv) = [Hu1] 2.3.25);
- NOT Prop 6.33 t.f.t. **composition** (whose strict-t.f.t. case needs the restricted-PS Fubini
  `Â⟨X_n⟩⟨Y_m⟩ ≅ Â⟨X_{n+m}⟩` — the flagged trap);
- NOT Prop 6.34 (t.f.t. ⟺ strict t.f.t. over Tate).

Because we attack the **specific** target `(presheafValue D)⟨Y_m⟩` with the **direct** `(n+m)`-variable
surjection, the source `Â⟨Z_{n+m}⟩` is already noetherian by Def 6.36(i) *directly* — we never compose
two t.f.t. maps, so Prop 6.33 (the Fubini-bearing step) never enters. This is strictly more faithful
AND avoids the trap.

This confirms the **existing** `presheafValue_isStronglyNoetherian_faithful` (Wedhorn828) is the
correct faithful minimal decomposition: `refine ⟨fun m => ?_⟩; … isNoetherianRing_of_surjective _ _ φ hφ`
where `φ` is the relative surjection. Steps 2–3 are PROVEN; the single residual is step 1.

## The single API gap — `presheafValue_mvRestricted_surjection`

**Leaf:** `∃ φ : restrictedMvPowerSeriesSubring (D.T.card + m) A →+* restrictedMvPowerSeriesSubring m (presheafValue D), Function.Surjective φ`.
This is "(presheafValue D)⟨Y_m⟩ is strictly t.f.t. over A" (RING-surjectivity suffices — Def 6.36(i)⟹(ii)
only needs the ring quotient; openness NOT needed, since `isNoetherianRing_of_surjective` is purely
algebraic, and `mvEvalHomBounded` builds the hom from `Continuous g` alone).

**Source quote** (Example 6.32(2), `wedhorn.txt:2637`): *"Let `A` be an f-adic ring … `Ti·A` open …
Then the canonical homomorphism `A → A⟨T₁/s₁,…,Tₙ/sₙ⟩` is topologically of finite type."* — our
relative target `(presheafValue D)⟨Y_m⟩ = Â⟨T/s, Y_m⟩` is of this form (the `Y` are free unit-disc
variables, `Tᵢ = {1}`), so it is t.f.t. over `A`; the strictly-t.f.t. presentation gives the surjection.

**Proof route (template = the PROVEN `example638_evalHom_surjective`):**
- The map `φ` is `mvEvalHomBounded (A → (presheafValue D)⟨Y_m⟩) (tuple (t/s) ⊕ Y)` — straightforward.
- Surjectivity mirrors `example638`: `ker φ` is closed (Prop 6.17 `MvTateAlgebra.mvTate_isClosed_ideal`
  at `n+m` over the strongly-noetherian `A` — APPLIES, source is over `A`), so `A⟨Z_{n+m}⟩/ker` is
  complete; a backward completion-extension right-inverts the injective factorisation.

**Sub-decomposition (the deep content):**
- **AG-1**: `(presheafValue D)⟨Y_m⟩` expressed as a `UniformSpace.Completion` of a dense subring
  (so `Completion.extensionHom` can build the backward map). The `example638` machinery uses
  `presheafValue D = Completion (Localization.Away D.s)`; the relative target is
  `restrictedMvPowerSeriesSubring m (presheafValue D)`, a subring of `MvPowerSeries`, NOT presented as
  a completion. Needed: `restrictedMvPowerSeriesSubring m B ≅ Completion(B[Y_m])` (restricted-mv-PS =
  completion of polynomial ring, for the Gauss topology) — **NOT in the repo** (no univariate template
  either, verified 2026-06-05). This is the genuine new infrastructure.
- **AG-2**: the relative `kerLift` + `quotBackward` + round-trip (mirroring `example638_kerLift`,
  `example638_quotBackward`, `example638_kerLift_comp_backward`, retargeted via AG-1), yielding
  surjectivity.

**Difficulty (honest, grounded):** `example638`'s univariate completion-comparison is ~700 lines
(`Example638.lean`) + the `kerLift`/`quotBackward` chain ~120 lines (`Wedhorn828:1640`–`1817`). The
relative version reuses the *pattern* but needs AG-1 (the restricted-mv-PS = completion-of-polynomial
iso) which has no repo template. Estimate: AG-1 ~150 LOC, AG-2 ~120 LOC. Bounded, but a genuine
multi-session build — NOT a quick close (correcting the earlier "lower-risk templated" estimate).

## Attacks attempted (adversarial)
- **[1] Counterexample / falsity:** the leaf is TRUE (Wedhorn states it, Example 6.38). The conclusion
  `∃ surjective φ` is a presentation that exists by Example 6.32(2). No counterexample.
- **[2] Edge cases:** `m = 0` → `φ : A⟨X_n⟩ → presheafValue D` = the PROVEN `example638_evalHom`
  (surjective ✓). `n = 0` (whole space, `s=1`) → degenerates to the univariate case. Both consistent.
- **[3] Hypothesis test:** needs `A` strongly noetherian only to make the SOURCE `A⟨Z_{n+m}⟩` noetherian
  (step 2) — but the *surjection itself* (this leaf) is a presentation that holds for any f-adic `A`
  (Example 6.32(2) assumes only `Tᵢ·A` open). So `[IsStronglyNoetherian A]` on the leaf is harmless
  over-decoration carried from the theorem; not load-bearing for the surjection. (Kept for uniformity.)
- **[4] Source-drift:** the Lean `∃ φ surjective` vs Example 6.32(2)'s "t.f.t." — t.f.t. via Def 6.28
  IS "∃ surjective continuous open `Â⟨Z⟩ ↠ B`". We drop "open" because only ring-surjectivity feeds
  `isNoetherianRing_of_surjective`. Faithful WEAKENING (we prove less than full t.f.t., enough for
  noetherian). No false strengthening.
- **[5] Discharge attack:** `isNoetherianRing_of_surjective` — exists, used at Wedhorn828:1881 ✓.
  `mvEvalHomBounded` exists (Wedhorn828:996), produces a ring hom from `Continuous g` ✓. `mvTate_isClosed_ideal`
  exists (MvTateAlgebraTopology:1028), needs `[IsStronglyNoetherian A]` (have) ✓. AG-1 (restricted-mv-PS
  = completion-of-poly) has NO repo discharge — genuine API gap, correctly flagged.
- **Verdict:** SURVIVED. The leaf is a true, faithful, minimal residual; its sub-content (AG-1/AG-2) is
  a genuine bounded API gap, not a false/fabricated leaf.

## Prior-B2 consultation
`b2_log.jsonl` entry `T-Q4-STRONGNOETH-FIX` (the FALSE `isStronglyNoetherian_of_isNoetherianRing_isTateRing`)
— ADDRESSED: this decomposition replaces that false bare-implication with the faithful surjection route;
the residual is the honest relative surjection, not the false noeth⟹strongly-noeth.

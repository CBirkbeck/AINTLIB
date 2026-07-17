# M9 pre-plan: [FJP] Cor 5.5 (strong sheafiness) + §6 (the A_d family) — audit & sizing

Status: PRE-PLAN (scope decision pending owner). Sources read in full: Cor 5.5 proof
(fjp.txt:1384-1400), §6/Cor 6.1 proof (fjp.txt:1440-1490), Lemma 4.1 statement+proof
(fjp.txt:610-635), Lemma 5.2 statement (fjp.txt:1190-1200), Thm 5.3 proof (1363-1372).

## What the paper's proofs actually are

* **Cor 5.5** (fjp.txt:1385-1399, one paragraph): "For every n ≥ 0, Lemma 4.1 gives a
  canonical strict isomorphism 𝓐⟨Z₁..Zₙ⟩ ≅ B⟨Z⃗⟩ ×_{D⟨Z⃗⟩} C⟨Z⃗⟩ (5.11). The right map
  remains a strict surjection and the three comparison vertices remain strongly
  noetherian. … Now Proposition 4.5 and Lemma 4.6 apply to every rational localization
  of the extended square. The comparison vertices satisfy the topological sheaf
  condition by Huber's theorem, as in Theorem 5.3. Applying Lemma 5.2 proves that every
  𝓐⟨Z₁,…,Zₙ⟩ is sheafy."
* **Cor 6.1** (fjp.txt:1445-1489, one page): defines B_d = k⟨W,Q⟩/(Q^d), C_d, D_d,
  A_d = B_d ×_{D_d} C_d; support monoid S_d ⟹ uniform Tate domain "exactly as in
  Lemma 2.2"; chart A_d⟨W/ϖ⟩ ≅ k⟨X,Q⟩/(Q^d) by "the same density argument as in
  Proposition 3.1" (nonuniform target via λQ^{d-1}, square-zero since 2d−2 ≥ d);
  sheafiness: "The parameter-free localization theorem Proposition 4.5 therefore gives
  the strict rational pullback for every datum and every d ≥ 2, naturally under
  refinement by Lemma 4.6 … Lemma 5.2 proves sheafiness"; strong sheafiness by
  Lemma 4.1 again; non-noetherianity via K_d·J_d = Q^{d+1}C_d, J_d/K_dJ_d ≅ k⟨W,W⁻¹⟩.

Both proofs are one paragraph BECAUSE the paper's §4–§5 theorems (Prop 4.5, Lemmas 4.1,
4.6, 5.1, 5.2) are stated **parametrically over an arbitrary strict Milnor square** of
affinoid k-algebras. The corollaries just re-instantiate the machine.

## What our formalization actually is (audit, 2026-07-17)

| Layer | File(s) | Lines | Genericity |
|---|---|---|---|
| Graph-Koszul / flatness (§4.1-4.2) | FiniteJetGraphKoszul | 1976 | **fully generic** (0 Jet-mentions; over `[NormedCommRing E][IsUltrametricDist E]`) |
| Pods `P R m` | GraphKoszul.P | — | **generic in R** ✓ |
| Strict localization (§4.3-4.7) | FiniteJetStrictLocalization | 1044 | **instantiated at the four d=2 Jet rings** (29 Jet-mentions; the (4.12)-(4.16) chase itself is written parameter-free, inputs = square data + constants) |
| Covariant pushes + bridges (§5.1) | FiniteJetFunctoriality | 2580 | mixed: `presheafValueMapOfHom` section generic; bridges concrete (191 mentions) |
| Transfer (§5.2-5.3) | FiniteJetSheafTransfer | 705 | concrete (54 mentions) |
| Model + chart (§2-§3) | Rings/UniformDomain/Chart | 3143 | concrete d=2 (`DualNumber` = TrivSqZeroExt throughout) |
| Huber's theorem | isSheafy_of_stronglyNoetherian_828b | — | **generic** ✓ |
| `IsStronglyNoetherian` | RestrictedPowerSeries:238 | — | exists: `∀ k, IsNoetherianRing (restrictedMvPowerSeriesSubring k A)` — the mirror `IsStronglySheafy` is the natural new definition |

## Verdict on the "easy refactor" premise

**True at the paper's level; false for the code as it stands.** Our §4.3–§5 machine
(~4.3k lines) and the whole §2–§3 model layer (~3.1k lines) are instantiated at d = 2
with no Tate variables. Neither corollary is reachable by instantiation:

1. Cor 5.5 quantifies over ALL n — the machine must be **abstracted over a
   strict-Milnor-square interface** (the paper's own (5.7)-hypothesis list) and then
   instantiated at the Z-extended squares via a formalized Lemma 4.1. No shortcut: n is
   a variable, so per-instance copies are impossible.
2. Cor 6.1 needs a **d-parametric model layer**: a truncated-jet-algebra construction
   `J_d(R) = R[Q]/(Q^d)` with the sup norm (mathlib has only the d = 2 case,
   `TrivSqZeroExt`/`DualNumber`; our JetDualNumberNorm generalizes to `Fin d → R` with
   truncated convolution), then the §2 support/uniform/domain arguments, the §6.3
   chart (d-component density roundtrips), and the K_d/J_d non-noetherianity — all
   currently written with two-component (`fst`/`snd`) bookkeeping.

Also needed for 5.5 regardless: the topological pair package on `A⟨Z₁..Zₖ⟩`
(Tate/Huber/T2/complete/maximal-plus/IsRingOfIntegralElements instances on the
restricted power-series ring over a Tate base) — real infrastructure, partially
available in the Wedhorn 6.x vendor.

## Scope options (grounded sizing; anchors = the d=2 campaign's actual line counts)

* **M9a — machine abstraction** (needed by BOTH goals): define `StrictMilnorSquare`
  bundling the paper's (5.7) interface (four complete Tate k-algebras, three bounded
  maps, strict surjection with norm-κ section, strictness/pullback constants ρ,
  strongly-noetherian comparison vertices, pod data); port §4.3–§5 (~4.3k lines) onto
  it; re-instantiate at the d=2 square (regression: `isSheafy_JetA` re-derived).
  Anchor: the original §4-§5 formalization took the M5+M6 campaigns; porting
  parameter-free proofs is cheaper than discovery, estimate ½–⅔ of that effort.
* **M9b — strong sheafiness** (Cor 5.5, needs M9a): `IsStronglySheafy` definition;
  `A⟨Z⃗ₖ⟩` pair package; Lemma 4.1 (paper proof: 1 paragraph, coefficientwise — builds
  on the V4c restricted-Fubini/isometry vendor); instance of the interface at the
  extended square; `finiteJet_isStronglySheafy`. 
* **M9c — the A_d family** (Cor 6.1, needs M9a for its sheafiness clause): truncated
  jet algebra + norms; d-parametric §2 (uniform Tate domain, non-noetherian via
  K_d/J_d); d-chart + `not_isStablyUniform`; square instance; the five A_d claims +
  (6.3). The d=2 model layer is 3.1k lines; the d-general version is comparable plus
  Fin-d bookkeeping.
* **Option C (cheap partial, no M9a)**: A_d model + uniform + domain + non-noetherian +
  d-chart + not-stably-uniform ONLY (everything in Cor 6.1 except the two sheafiness
  clauses. These are §2/§3/§6-computational and reuse the generic Koszul/Laurent/
  Gauss-norm layers directly).

Total for everything (A = M9a+b+c): a campaign on the order of the original M1–M6 —
multi-week of marathon sessions, roughly 8–15k lines new or ported.

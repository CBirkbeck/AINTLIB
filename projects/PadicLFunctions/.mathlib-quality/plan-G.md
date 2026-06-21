# Development Plan: §13 Stage G — Galois Λ-modules + the Vandiver IMC

## STATUS (audited & corrected 2026-06-21) — §13 CAPSTONE RETRACTED; foundation rebuild started

**The earlier "capstone" was NOT a faithful proof of RJW Thm 13.11 and has been removed.** It
quantified over abstract `Type*` variables `X⁺_∞, Y⁺_∞, U⁺` (never constructed — the real objects are
`Gal(𝓜⁺_∞/F⁺_∞)` etc.) and bundled the connecting maps/isos (the Galois SES, the CFT iso, `𝓔⁺=𝓒⁺`,
Thm 11.9 in Λ-linear form) as `structure`/hypothesis fields (`IwasawaGaloisData`, `CFTUnitsData`,
`VandiverData`) — i.e. it assumed essentially the whole theorem. `#print axioms` cleanliness is
irrelevant: `(h:P)→Q` is axiom-clean whatever `P` assumes. Deleted: the three structures + the capstone
files (`MainConjecture`, `Capstone`, `CapstoneConcrete`, `CharIdealConjunct`, `Galois/{Modules,Sequence,
Coinvariants,ClassFieldTheory}`). PR #2361 retracted.

**Project audit verdict**: the bundling was ISOLATED to the §13 capstone. The rest is genuine — only
`structure` left is the real `NormCompatUnits`; no `axiom`s; the headline kept theorems
(`iwasawa_theorem`, `iwasawa_exact_sequence`, `col_image_cycloTower1_eq_zetaIdeal`, `charIdeal_quotient`,
`charIdealGroup_quotient`, `isotypicIdempotent_sum_eq_one`, `carrierBridgeFull`) are all axiom-clean and
about genuinely-constructed objects; the only `sorry`s are confined to the deliberately-bypassed
structure theorem (`fg_pseudoIso_canonical`), one `PseudoIso` lemma, and the openly-flagged
`GaloisAction` bodies — none taint a headline result. Caveat: `iwasawa_theorem` is the *additive* iso
(Λ-linear refinement open; docstring discloses).

**Foundation rebuild (chosen direction)**: construct the real Galois objects of §13.2 ground-up
(`Iwasawa/GaloisFoundation.lean`). The wall: mathlib has infinite Galois + finite-extension ramification
(`IsUnramifiedAt`) + `maximalRealSubfield`, but NO "maximal abelian extension unramified outside `S`".
So `Mₙ/Lₙ` and `Xₙ=Gal(Mₙ/Fₙ)` must be built as quotients of the absolute Galois group (max pro-`p`
abelian, killed by inertia at primes ∤ `pₙ`), then `X∞=lim Xₙ` with the Remark-13.7 `Λ(Γ)`-action — a
substantial mathlib-PR-scale build. Brick 1 (DONE, axiom-clean): the base tower `Fₙ=ℚ(μ_{pⁿ})`.

KEPT, real, axiom-clean (orphaned from the deleted capstone; reusable):
- **Structure theory**: `charIdeal` (length-theoretic), `charIdeal_quotient` (`Ch(Λ/(f))=(f)` via
  `Ring.ord`/`ord_eq_addVal` + UFD), isotypic decomposition, `charIdealGroup_quotient`,
  `charIdealGroup_of_quotientEquiv`, both `charIdeal`/`charIdealGroup` iso-invariances.
- **Galois side**: `IwasawaGaloisData`, the Nakayama Vandiver vanishing `yPlus_subsingleton`
  (+ `vandiver_yPlusFin_subsingleton` from `p∤h₁⁺`), the four-term collapse `xPlus_equiv_uModCPlus`.
- **Carrier bridge Φ** (`carrierBridgeFull`, fully assembled): measure functoriality
  (`pushforwardRingEquiv`, `mahlerPushforwardRingEquiv`), `finiteProductRingEquiv`, the Teichmüller
  decomposition `𝒢⁺ ≅ Δ×Γ` (`gplusMulEquiv`→`gplusHomeo` via compact→T2), and the logarithm iso
  `Γ ≅ ℤ_p` (`logCM`/`expCM` + the 4 laws, continuity from the log/exp isometries).
- **Isotypic completeness** `∑_ω e_ω = 1` (`isotypicIdempotent_sum_eq_one`): the "extend L"
  assumption discharged from `HasEnoughRootsOfUnity ℤ_[p] (exponent Δ)` (Teichmüller roots) +
  character duality; all `Δ` typeclass instances (`Fintype`, `Invertible |Δ|`) derived.

UPDATE (2026-06-21): **§12 is DONE.** `iwasawa_theorem` (`𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≃+ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`),
`col_image_cycloTower1_eq_zetaIdeal`, and `iwasawa_exact_sequence` are all **PROVED and axiom-clean**
in `IwasawaProof/Main.lean` (orchestrator-verified: `#print axioms` = the standard three, no sorryAx;
Main.lean sorry-free). They were closed via the **faithful plus/minus Route-P** (`col_mem` splits
`Col u` into the `c`-plus part — handled by the proved `col_mem_zetaIdeal_of_mem_cycloTower1Plus` —
and the `c`-minus part `∈ ℤ_p(1) = ker Col`), NOT the density route; the entire `[T1220–T1225]`
density chain is therefore **SUPERSEDED** (its `_of_density` route was unsound at the free level-0
coordinate, T1220 B2-logged). The board had been stale (`+sorryAx`).

REMAINING (genuinely bundled-by-necessity / off the plan's chosen path):
- **CFT** (`CFTUnitsData`'s `cft` field, the `Gal(𝓜⁺/𝓛⁺) ≅ 𝒰⁺/𝓔⁺` identification) — global class
  field theory, **not in mathlib** (verified: no `RayClassGroup`/Artin reciprocity), so bundled by
  necessity per plan + expert review; building it is a multi-week paper-scale development (B3-scale).
- The **Λ(𝒢⁺)-linear refinement** of `iwasawa_theorem` (it is proved as an *additive* iso; the
  `Λ`-linear upgrade needs the `Col`-`smul` intertwining ≡ the deliberately-absent `Continuous(Col)`,
  which the whole §12 Coleman pipeline was built to AVOID). So the capstone's `h12` (stated `≃ₗ[Λ]`)
  takes the Λ-linear form as part of the bundle; §12 supplies its additive core.
- The Λ-module **structure theorem** `fg_pseudoIso_canonical` — deliberately BYPASSED by the
  length-theoretic `charIdeal` reroute (not needed for the capstone).

## Goal

Formalise RJW §13.2–§13.3 (arXiv:2309.15692): the Galois-theoretic side of the Iwasawa
Main Conjecture, culminating in **the IMC for Vandiver primes** (`thm:vandiver`, TeX 3762):

```
theorem iwasawa_main_conjecture_vandiver (hp : Vandiver p) :
    Nonempty (𝒳⁺_∞ ≃ₗ[Λ(𝒢⁺)] Λ(𝒢⁺) ⧸ zetaIdealPlus) ∧
    charIdealGroup 𝒳⁺_∞ = zetaIdealPlus
```

## Scope decision (binding — surfaced for user approval)

RJW prove the IMC in two regimes:
- **Vandiver primes** (§13.3): `𝒳⁺_∞ ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, **Iwasawa's original conditional
  proof**, via the CFT exact sequences + §12 (`iwasawa_theorem`, already DONE). Self-contained
  within these notes.
- **All primes**: the full IMC, which RJW **do not prove** — they cite Mazur–Wiles (`MW84`)
  and the Euler-system route (Kolyvagin–Rubin–Thaine, `CS06`) (TeX 3882).

**Stage G targets the Vandiver case.** This makes Stage E (Euler system / Thaine) **not
required** for an RJW-faithful IMC — it would be a separate, far larger project formalising
Mazur–Wiles or Rubin. The board's S13-E/S13-M should be re-scoped accordingly (proposal below).

## CFT-input decision (REVISED after full-monorepo search — surfaced for user approval)

**We do NOT need to build or axiomatise full class field theory.** My first pass searched only
mathlib + `.lake`; searching the whole **monorepo** found substantial real, sorry-free CFT /
class-group infrastructure in sibling projects that Stage G can `import` (the point of the monorepo):

- **Hilbert 94** — `FltRegular/FltRegular/NumberTheory/Hilbert94.lean`: `dvd_card_classGroup_of_unramified_isCyclic`
  (unramified cyclic ext of odd prime degree ⟹ `[L:K] ∣ |Cl(𝓞 K)|`), `exists_not_isPrincipal_and_isPrincipal_map`. Sorry-free.
- **Hilbert p-class field iso** — `FltRegularBernoulli/.../HilbertClassField.lean`: `ClassGroupModP L p`,
  `HilbertPClassField L p` (`Gal(H_p(L)/L) ≃* Cl(𝓞 L)/Cl^p`), bundled data structure.
- **Class-group ±-structure** — `TotallyRealSubfield/ClassGroup.lean`: `classGroupMap : Cl(𝓞 K⁺) →* Cl(𝓞 K)`
  injective, `hMinus`, `h = h⁺·h⁻`; `p ∣ h⁻ ⟺ p ∣ Bernoulli`. Sorry-free.
- **Galois action on Cl + units, eigenspace projectors** (`Reflection/ClassGroupModP/GalAction.lean`,
  `UnitQuotient/DeltaAction.lean`); **Hilbert 90** for K/K⁺ (`FLT37/Hilbert90.lean`); cyclotomic/circular
  units + index `[𝒱:𝒟]`; **Vandiver proven p=37** (`FLT37/VandiverProven.lean`). All sorry-free.
- **Chebotarev density** — `projects/Chebotarev/` (`chebotarev_density`, `dirichlet_primes_in_AP`). Sorry-free.
- **Cyclotomic tower foundation** — already in PadicLFunctions: `Fglobal(Plus)`, `globalUnits(Plus)`,
  `localUnits(One)(Plus)`, `𝒢≅ℤ_p^×`, `Λ(𝒢)=PadicMeasure`, ±-decomposition, `𝒞_∞`. Sorry-free. Plus
  mathlib `Representation.Coinvariants` + Nakayama.

So **G1 (unramified CFT) and G-VANDIVER REUSE real monorepo proofs**, not axioms. **G3** builds on the
existing tower + mathlib `Coinvariants` (the Iwasawa-specific coinvariant/norm assembly is the new proof).
The Euler-system machinery (`FltRegularBernoulli/Thaine/`) is *also* present (finite-level), so a future
full-IMC (Stage E) is less out-of-reach than first stated.

**The ONE genuinely-missing classical input is G2 — ramified CFT** (Washington Cor 13.6): the exact
sequence for `Gal(𝓜⁺_∞/𝓛⁺_∞)`, the maximal abelian p-extension unramified *outside p*. Ray class groups,
the Artin reciprocity map, conductors, and ramified-abelian-extension Galois theory are **absent from the
entire monorepo and mathlib** (the Hilbert class field is unramified *everywhere* — a different object).
This single input is axiomatised as one field of `IwasawaGaloisData` (citing Washington Cor 13.6), exactly
as RJW cite it (TeX 3767, 3790); Chebotarev supplies prime-existence but not the full reciprocity sequence.

Net: instead of "axiomatise CFT", the plan is **reuse the monorepo for G1 / G-VANDIVER / the tower, prove
G3 / G4 / G-IMC, and axiomatise only the single ramified-CFT sequence (G2).**

### Post-expert-review refinement (2026-06-18): assume *general* CFT, derive the special case

An Iwasawa-theory specialist reviewed the above (`expert-review/2026-06-18/`). Conclusions: there is **no
Coleman-only/Chebotarev-only shortcut** (the kernel = closure of global units *is* p-ramified global
reciprocity); the bespoke sequence is **not intrinsic**, but *some* global bridge is; for the Vandiver
milestone, assuming the CFT input is "overwhelmingly the right engineering decision". Acting on the
reviewer's "more reusable black box" and on the design goal *depend on the stable interface a future
global-CFT library will expose, not a bespoke specialisation*:

- **The assumed boundary is the general, classical theorem of global CFT** (ray-class / ideal-theoretic
  form), for arbitrary number fields: **Artin reciprocity** `Cl_K(𝔪) ≅ Gal(H_𝔪/K)` + **existence**
  (every finite abelian `L/K` lies in some `H_𝔪`, `𝔪` divisible by the conductor) + **conductor–
  ramification** ("unramified outside `S`" ↔ modulus supported in `S`). Bundled as a `structure
  ClassFieldTheory` (or marked axioms). This is exactly what mathlib's eventual global CFT will provide,
  so discharge later = *instantiate the structure*, with nothing downstream changing.
- **Derived (PROVEN) from the interface**: the bespoke CFTunits1 sequence (apply the interface to
  `K = F_n^+`, `S = {𝔭,∞}`). Most of the unwinding is **elementary** (the ray-class/units/class-group
  exact sequence is the *definition* of the ray class group — no CFT); the only irreducible CFT content
  is the Artin iso itself. The inverse-limit passage is a Mittag–Leffler proof.

So the irreducible assumed surface is **one general classical theorem (Artin reciprocity + existence)**,
not a cyclotomic-tower specialisation. The deduction + ray-class API is reusable by every monorepo project.

### Eventual axiom-elimination (deferred, separate project)

Per the reviewer, the genuine non-ray-class route to the *full* IMC is **tower-level class-group Euler
system (reuse `FltRegularBernoulli/Thaine`) + Kummer pairing/reflection (NSW Thm 11.4.3 / Washington
Prop 13.32) + the Iwasawa adjoint** — replacing ray-class reciprocity by global Kummer duality (itself a
global theorem ≈ degree-one Poitou–Tate). This is ≈ the full Main Conjecture and is **not** a shortcut for
Vandiver (it concerns reflected *odd* components, where the irregularity lives). Recorded as `G2-DISCHARGE`.
The Greenberg/Selmer reformulation (Q5) is cleanest in the abstract but **larger** than the CFT black box
now (needs local Tate duality + Poitou–Tate) — not pursued at this stage.

### Added references (from the review)
- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Thm 11.4.3 (Kummer pairing).
- Washington, *Cyclotomic Fields* 2nd ed., Prop 13.32 (Kummer pairing), Cor 13.6 (the finite-level
  ramified sequence), Ch. 15 (Thaine–Kolyvagin–Rubin + an MC proof).
- Aoki, "The Iwasawa Main Conjecture and Gauss Sums" (minus-side Euler system of Gauss sums).
- [Selecta Math.] "Fitting ideals of p-ramified Iwasawa modules over totally real fields" (Selmer-complex
  treatment).

## Mathlib / project inventory

| Concept | Status | Action |
|---|---|---|
| `ClassGroup (𝓞 K)`, finiteness | mathlib ✓ | USE for G1 (`Cl(F⁺_n)`) |
| `Representation.Coinvariants ρ` | mathlib ✓ | USE for G3 |
| `groupCohomology.H1/H2`, Hilbert 90 | mathlib ✓ | available; Hilbert 94 ABSENT |
| `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` (Nakayama) | mathlib ✓ | USE for G-VANDIVER(i) |
| `IsMittagLeffler`, finite inverse limits | mathlib ✓ (Type-level) | USE for inverse limits; exactness-of-lim ABSENT (axiomatise per-use) |
| Global CFT, Hilbert 94, ramified ab. ext., ℤ_p-tower Gal | ABSENT | AXIOMATISE (G1 iso, G2) |
| `iwasawa_theorem` (𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p) | project ✓ `IwasawaProof/Main.lean` | USE for G-IMC |
| `localUnitsOnePlus`,`globalUnitsPlus`,`Fglobal(Plus)` | project ✓ | USE for unit objects |
| `zetaIdealPlus`, `projPlus`, `GPlus` | project ✓ | USE for the target ideal / Λ(𝒢⁺) |
| `charIdealGroup`, `IwasawaAlgebraGroup`, `IsPseudoIso` | project ✓ (Stage S) | USE for the char-ideal conclusion |

## File structure

- `IwasawaProof/Galois/Modules.lean` — `IwasawaGaloisData` structure (objects + axiomatised CFT
  fields), 𝒳⁺_∞/𝒴⁺_∞ accessors, Λ(𝒢⁺)-actions. [G-DEF, G1, G2]
- `IwasawaProof/Galois/Coinvariants.lean` — G3 (coinvariants), G-VANDIVER. [proven]
- `IwasawaProof/Galois/Sequence.lean` — G4 (CFTunits2). [proven]
- `IwasawaProof/MainConjecture.lean` — G-IMC milestone (the Vandiver theorem + char-ideal). [proven]

## Dependency graph

```
S13-S5 (charIdealGroup) ─┐
§12 iwasawa_theorem ─────┤
                         ▼
   G-DEF (IwasawaGaloisData: objects + axiomatised G1-iso, G2, Galois-SES)
        │           │              │
        ▼           ▼              ▼
   G3 coinvariants  G4 CFTunits2   (G1 class-group side: 𝒴⁺_n := Cl(F⁺_n)⊗ℤ_p)
        │           │
        ▼           ▼
   G-VANDIVER (Cor Iw1) ──────────► G-IMC (thm:vandiver + charIdealGroup = zetaIdealPlus)
```

## Generality decisions

- Work over the standing `𝒪 = ℤ_p` / `Λ(𝒢⁺)` of the project (not abstract), since the objects are
  the specific cyclotomic Galois modules; the Stage-S char-ideal API it calls is already general.
- `IwasawaGaloisData` is a `structure` (bundling the classical inputs) rather than scattered
  axioms, so the axiomatised surface is explicit, auditable, and discharge-able later if mathlib
  gains global CFT.

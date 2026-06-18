# Development Plan: §13 Stage G — Galois Λ-modules + the Vandiver IMC

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

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

## CFT-input decision (binding — surfaced for user approval)

Global class field theory is **absent from mathlib**: no Artin reciprocity, idele/ray class
groups, conductors, Hilbert 94, ramified abelian extensions, Galois cohomology of global fields,
ℤ_p-extension Galois theory, or principal-unit filtrations of the cyclotomic local tower
(verified by exhaustive search). FltRegular is **not vendored**.

RJW themselves "omit the proofs of some more classical auxiliary results" and follow CS06 §4.5
(TeX 3767). Mirroring this, the **CFT inputs are introduced as axiomatised hypotheses**, bundled
in a `structure IwasawaGaloisData` whose fields are exactly the classical CFT facts RJW cite to
Washington. The **Iwasawa-theoretic content is proven** on top of that data. This is the
"axiomatise" option the board already flagged for G2. Every axiomatised field carries its precise
Washington/CS06 citation.

Split:
- **Axiomatised inputs** (fields of `IwasawaGaloisData`): G1 (Hilbert-94 iso `𝒴⁺_n ≅ Cl(F⁺_n)⊗ℤ_p`
  — the *iso to the unramified Galois group*; the class group side is real mathlib), G2 (CFTunits1
  ramified-CFT SES, Washington Cor 13.6), the Λ(𝒢⁺)-module structures, and the Galois SES
  `0→Gal(𝓜⁺_∞/𝓛⁺_∞)→𝒳⁺_∞→𝒴⁺_∞→0`.
- **Proven** from the data: G3 (coinvariants `(𝒴⁺_∞)_{Γ⁺_n}=𝒴⁺_n`), G4 (CFTunits2 4-term SES),
  G-VANDIVER (Cor Iw1), G-IMC (the Vandiver theorem) — using §12's `iwasawa_theorem` and Stage-S
  `charIdealGroup`.

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

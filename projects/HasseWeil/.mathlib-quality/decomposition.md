# Decomposition — Route-1 Hasse bound remaining (qf_nonneg / Leaf 1)

**Date**: 2026-06-02. **Mode**: `/develop --decompose` (adversarial, source-faithful).
**Source**: Silverman, *Arithmetic of Elliptic Curves* (GTM 106), in-repo PDF
(`HasseWeil/Silverman-Arithmetic_of_EC.pdf`, offset = book page + 18).

## Top result

`hasse_bound_skeleton` (`HasseWeil/HasseWeilSkeleton.lean:27`) — `|#E(F_q)−q−1| ≤ 2√q`.
Assembled; carries `sorryAx` **only** via `qf_nonneg_skeleton` (`GapSpines.lean:2142`).
Everything else on Route 1 is axiom-clean: V.1.3 (`isogOneSub_negFrobenius_degree_eq_pointCount`),
`pc_sep`, `pc_fin`, `ker_deg_skeleton`, `verschiebungV`+`IsDualOf V π`+`[q]⊆π`, π-side `genuineIsogSmulSub`.

## Silverman's ACTUAL proof of the Hasse bound (transcribed, V.1.1 + III.6)

V.1.1 (Hasse, book p.138) proves `|a| ≤ 2√q` (a = q+1−#E) from:
- **Cor III.6.3 (p.85)**: `deg : Hom(E₁,E₂) → ℤ` is a **positive-definite quadratic form**; then
  Cauchy–Schwarz on the associated bilinear form applied to `(1, φ)`, φ = Frobenius.
- Cor 6.3's proof: `⟨φ,ψ⟩ = deg(φ+ψ)−deg φ−deg ψ` is bilinear because `[⟨φ,ψ⟩] = φ̂∘ψ + ψ̂∘φ`
  (via III.6.2(c)), linear in each slot by III.6.2(c) again.
  > (verbatim p.85) "Everything is clear except for the fact that the pairing ⟨φ,ψ⟩ = deg(φ+ψ) − deg(φ) − deg(ψ) is bilinear. … = φ̂∘ψ + ψ̂∘φ from (III.6.2c). Using (III.6.2c) a second time, … linear in both φ and ψ."
- **KEY LEAF — III.6.2(c) (p.83), the dual is additive:**
  > (verbatim p.83) "(c) Let ψ : E₁ → E₂ be another isogeny. Then **(φ+ψ)^ = φ̂ + ψ̂.**"
- III.6.2(c)'s proof (p.84) IS the **theorem of the square / Abel** argument:
  > (verbatim p.84) "Now consider the divisor `D` … The definition of φ+ψ implies that **D sums to O, so (III.3.5) tells us that D is linearly equivalent to 0.** … Since this is the divisor of a function, it sums to O, so using (III.6.1b), … the point `(φ+ψ)^(x₂,y₂) − φ̂(x₂,y₂) − ψ̂(x₂,y₂)` does not depend on (x₂,y₂) … Putting (x₂,y₂)=O shows that it is equal to O."
  Footnoted char-0; char-p via Exercise 3.31, but the *D-sums-to-O ⟹ principal* (Abel) core is char-free over a perfect base.

```
V.1.1 (Hasse)
└─ Cor III.6.3 — deg is a positive-definite quadratic form   [formal: Cauchy–Schwarz]
   └─ III.6.2(c) — dual additivity (φ+ψ)^ = φ̂ + ψ̂           [THE key leaf]
      └─ theorem of the square: div D sums to O ⟹ principal   [Abel III.3.5; char-free over F̄]
```
**Single irreducible source leaf = the theorem of the square (`σ(Δ_Q)=O`), Silverman III.6.2(c)/III.3.5.**

## Two project routes — one source-faithful, one INVENTED

| | Route A: Pic⁰ / theorem of the square | Route B: double-Vieta / V-side pole |
|---|---|---|
| Files | `Pic0/RouteCAddFormula.lean`, `RouteCTheoremOfSquareDiv.lean`, `RouteCAssembly.lean` | `GapSpines.lean` (`genuineIsogSmulSub_degree_eq_signed`), `WallA/VSideDual.lean`, `Verschiebung/Genuine.lean` |
| Source-faithful? | **YES** — IS Silverman III.6.2(c)'s divisor argument (`sigma_delta`, `sigma_delta_eq_zero_iff`) | **NO — invented.** Silverman never computes `deg(rπ−s)` via a V-side `r·V−s` pole match |
| Direct sorries | 0 in the RouteC files | `GapSpines`:2013 + `Verschiebung/Genuine` V-side pole sorry |
| Bottoms at | `DualAddMulByIntResidual` ⟺ `∀Q, σ(Δ_Q)=O` (theorem of the square) | `ord_O(φ*x) = −2·deg_i(φ)` V-side ramification (see `decomposition-intDegree-WallA-2026-05-25.md`) |
| Machinery present | Abel `projIsPrincipal_of_degZero_of_sigma_eq_zero` (used clean in Route 2A), `sigma_delta` PROVEN | π-side pole clean; V-side pole an open curve-specific (ordinary vs supersingular) computation |

Per source-faithfulness (rules 1, 3 quote-or-delete, 4): **the double-Vieta is an artifact** — chosen
because it connects to existing `genuineIsogSmulSub` machinery, not transcribed from Silverman; no
source passage proves `deg(rπ−s)` via a V-side pole. Silverman proves the *additivity* and gets the
quadratic form formally.

## Source-faithful leaf — adversarial pass

**Leaf: `σ(Δ_Q)=O` (theorem of the square / dual additivity), Silverman III.6.2(c) p.84.** Project form
`DualAddMulByIntResidual` (`RouteCAddFormula.lean:267`) ⟺ `∀Q, σ(Δ_Q)=O` (`sigma_delta_eq_zero_iff`,
`RouteCTheoremOfSquareDiv.lean:170`); reduces `qf_nonneg` generic via `RouteCAssembly` + proven `sigma_delta`.

- [1] Counterexample: theorem of the square is foundational (all abelian varieties); `D` sums to O **by the definition of `φ+ψ`** (group law), not an extra hypothesis. No counterexample.
- [2] Edge cases: φ/ψ constant → trivial (proof's first line); `[m]` slot → III.6.2(d) `[m]^=[m]`.
- [3] Char-p drift: p.84 proof is char-0, but `D`-sums-to-O ⟹ principal is char-free over perfect base; `RouteCAddFormula` is "char-free over F̄ (perfect)" (line 108). The char-0 caveat is the field-of-definition trick (footnote), sidestepped by the F̄/Abel route.
- [4] Citation drift: re-read p.83-85 — III.6.2(c)=`(φ+ψ)^=φ̂+ψ̂`, Cor 6.3="positive-definite quadratic form" with pairing `φ̂ψ+ψ̂φ`; project `DualAddMulByIntResidual`/`sigma_delta` match. No drift.
- [5] Discharge: `sigma_delta` (`RouteCTheoremOfSquareDiv.lean:155`) PROVEN; Abel `projIsPrincipal_of_degZero_of_sigma_eq_zero` PROVEN (axiom-clean, used in Route 2A). Residual `σ(Δ_Q)=O` is the genuine content (= dual additivity), NOT yet discharged, but it is the **standard** theorem of the square with the Abel machinery present.
- Verdict: SURVIVED. Source-faithful, char-free-adaptable, machinery present.

## Prior-B2 log

`b2_log.jsonl` (155 KB) records many B2s on the **double-Vieta / V-side** route
(`genuineIsogSmulSub_degree_eq_signed`, V-side pole) — corroborates that it is the artifact (it has
repeatedly hit scope errors). The theorem-of-the-square route has far fewer — consistent with it being
the source's actual route.

## Feasibility

Route-1 Hasse, decomposed faithfully to Silverman, reduces to the **single standard leaf `σ(Δ_Q)=O`**
(theorem of the square, III.6.2(c)) via the project's already-built, 0-direct-sorry Pic⁰ machinery
(`RouteCAddFormula`/`RouteCTheoremOfSquareDiv`/`RouteCAssembly` + proven `sigma_delta` + Abel). FEASIBLE
— a foundational char-free EC fact with machinery in place, not exotic infrastructure. The **double-Vieta
/ V-side route (the current Wall-A work) is an invented artifact** bottoming at a harder curve-specific
ramification computation Silverman never does; per source-faithfulness it should be **abandoned** for the
theorem-of-the-square route. The char-divisible edges (`decomposition-L2-char-divisible-2026-05-25.md`)
route through `[p]=V∘π` + the SAME dual additivity, so they also close once `σ(Δ_Q)=O` ships.

## Next step

Source-faithful target = **`σ(Δ_Q)=O` (DualAddMulByIntResidual)** via the Pic⁰ theorem-of-the-square
machinery — NOT the double-Vieta. Re-point the Wall-A effort from `Verschiebung/Genuine` (V-side pole)
to `Pic0/RouteCTheoremOfSquareDiv` (`σ(Δ_Q)=O`).

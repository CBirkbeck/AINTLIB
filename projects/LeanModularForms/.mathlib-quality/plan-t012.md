# Plan — T012: the reverse old-space inclusion (gap #4, unconditional 4.6.12)

*`/develop --decompose` ADVERSARIAL planning-only, 2026-05-27, branch `hecke-ring`. NEW file
(does not touch the `-adjoint` artifacts). No `lake build` run; LSP unavailable (concurrent
`AdjointTheory/FDTransport.lean` edit). Full leaf logs + source quotes: `decomposition-t012.md`.*

## Goal

Make `HeckeRing.GL2.strongMultiplicityOne_constMul` (Miyake Thm 4.6.12) provable
**UNCONDITIONALLY** — without the "Mitigation B" extra hypothesis
`g ∈ cuspFormsOldChar ⊔ cuspFormsNew`. The blocker is the reverse old-space inclusion.

## Minimal target (Option B, NOT Option A)

```lean
theorem cuspFormsOld_inf_charSpace_le_cuspFormsOldChar
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOldChar N k χ.toUnitHom χ.conductor
```

This is exactly what the assembly needs: the project's PROVEN
`cuspFormsOld_isCompl_cuspFormsNew` decomposes `g = oldPart g + newPart g` with
`oldPart g ∈ cuspFormsOld`; since `g ∈ charSpace χ` and the projection is diamond-equivariant,
`oldPart g ∈ cuspFormsOld ⊓ charSpace χ`; the target then lands it in `cuspFormsOldChar`, feeding
`oldPart_eq_zero_of_shared_eigenvalues` (the existing `:= by sorry` consumer). Option A
(`IsCompl (cuspFormsOldChar) (cuspFormsNew)`) is strictly stronger, circular-prone
(reduces to `cuspFormsOldChar = cuspFormsOld` via the project's `cuspFormsNew = (cuspFormsOld)⊥`),
and not consumed by the assembly. **Ship B; A is a ~15-line follow-on if ever wanted.**

## References (verbatim quotes in `decomposition-t012.md` §1)

- **[Miy]** Modular Forms 2e §4.6. S_k^♭(N,χ) def + Lemma 4.6.9(1)(2)(3) (p. 162); Thm 4.6.8
  "by induction on the factors of l" engine (p. 162); Thm 4.6.12 (pp. 163-164). PDF page = book + 9.
- **[DS]** A First Course §5.6. Def 5.6.1 (old = Σ_p i_p(S_k(N/p)²)); "Exercise 5.6.2: all divisors
  = prime divisors makes no difference"; Prop 5.6.2 (old/new stable under T_n, ⟨n⟩) (pp. 187-188).
- **Cross-check verdict:** both sources confirm the recursive old = span-of-V-images-of-lower-levels
  structure. The reverse inclusion (DS-style char-agnostic-full old space = Miyake-style χ-new old
  space) is the **Atkin–Lehner–Li** content; neither book states it as one lemma (each gets old⊕new
  from an orthocomplement *definition*). It is project-specific because the project defines
  `cuspFormsOldChar` by Miyake's generating set but `cuspFormsNew` by DS's orthocomplement.

## Induction (spine)

- **Variable:** `N`, via `Nat.strong_induction_on` (≡ Ω(N), strong induction on the level).
- **Base:** `N` with no proper-divisor generator (`cuspFormsOld N k = ⊥`) ⇒ `⊥ ⊓ _ ≤ _` by `bot_le`.
- **Step:** `f = Σ_j c_j V_{d_j}(g_j)` (generators, `1<d_j`, `d_j M_j = N`). Per generator split
  `g_j = old(M_j) + new(M_j)`:
  - **new piece** → `cuspFormsOldChar` via conductor fact (Miyake 4.6.4, ALREADY PROVEN) ⇒ `m_χ ∣ M_j`,
    then 4.6.9(2) (proven). [global χ-isotypic vanishing via proven `iSupIndep` drops bad-ψ pieces]
  - **old piece** → IH at `M_j < N` gives `old(M_j) = Σ_i V_{e_i}(h_i)`; **levelRaise associativity**
    (NEW leaf L2) folds `V_{d_j}(V_{e_i}(h_i)) = V_{d_j e_i}(h_i)`, a single raise to N ⇒ generator.
  - sum (mathlib `sum_mem`).

## Mathlib / project inventory (grep/Read-verified — see decomposition-t012.md §2)

| Concept | Status | Action |
|---------|--------|--------|
| per-level old⊕new `cuspFormsOld_isCompl_cuspFormsNew` | EXISTS sorry-free (`Newforms/Basic.lean:309`) | USE |
| forward `cuspFormsOldChar_le_cuspFormsOld` | EXISTS sorry-free (`StrongMultiplicityOneFull.lean:271`) | USE (the reverse twin) |
| 4.6.9(2) `levelRaise_cuspFormsNew_le_cuspFormsOldChar` | EXISTS sorry-free (`…Full.lean:227`) | USE |
| χ-decomp + indep of old/new (`…iSup_inf_charSpace`, `…iSupIndep…`, `exists_finsupp…`) | EXISTS sorry-free (`Newforms/MainLemma.lean:63-150`) | USE |
| diamond-stable old/new | EXISTS sorry-free (`LevelRaiseComm.lean:944,976`) | USE |
| **conductor fact 4.6.4** `conductor_theorem_dichotomy_cuspForm_strong` + Case A charSpace bundle | EXISTS sorry-free (`ConductorTheorem.lean`) | USE (the "m_χ ∣ M" fact — NOT a new leaf) |
| `levelRaise` = `→ₗ[ℂ]`; `levelRaiseFun_injective`; `levelRaise_mem_cuspFormCharSpace` | EXISTS (`LevelRaise.lean:231,367`, `ConductorTheorem.lean:1001`) | USE |
| **`levelRaise` associativity `V_d∘V_{d'}=V_{dd'}`** | NOT present (grep-confirmed) | **BUILD (L2, ~50 LOC)** |
| `oldPart` commutes with diamond | NOT present | BUILD (~10 LOC, T013 side) |

## File structure

- New `LeanModularForms/SMOObligations/Lemma4_6_9.lean` (imports `LeanModularForms.SMOObligations`)
  — holds L3 + the induction workhorse + the public target. Strictly downstream of SMO (no cycle).
- ~50 LOC into `LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean` — the new associativity leaf L2
  (`levelRaiseMatrix_mul`, `levelRaise_levelRaise`) near the `levelRaise` def at :231.
- The consumer edits (assembly of `strongMultiplicityOne_constMul` to drop Mitigation B) land in
  `StrongMultiplicityOneFull.lean` — those are the existing `oldPart_eq_zero_of_shared_eigenvalues`
  / `strongMultiplicityOne_constMul` sorries, NOT part of T012 proper.

## RISK section

1. **L2 transport hell (the only real Lean-mechanics risk).** `heq ▸` on the bundled iterated
   `levelRaise` is the classic pain point. **Mitigation (proven pattern):** prove the FUNCTION-level
   associativity via `levelRaiseFun_apply` (= `f(α_l • τ)`, `LevelRaise.lean:315`) and
   `α_d•(α_{d'}•τ)=α_{dd'}•τ`, then re-bundle via `qExpansion_ext2`/`CuspForm.ext` (exactly the
   `MainLemma.lean:288-295` pattern). Dodges the transport entirely. **Bounded.**
2. **ATTACK-χ: global isotypic vanishing.** The char-agnostic `cuspFormsNew M k` in the Lean def
   means the "which ψ survives" argument must be GLOBAL (assemble the full sum, drop ψ≠χ pieces via
   `iSupIndep`), not generator-local. This interleaves L1+L3+L6 into one combined argument — the LOC
   bulk. Every ingredient is proven (`cuspFormsOld_iSupIndep_inf_charSpace`, finsupp χ-decomp). The
   char-agnostic def is in fact a FEATURE: it makes 4.6.9(2) easy to satisfy (takes agnostic-new `g`).
   **Bounded but intricate.** This is the piece the prior pass called "open hard part" without
   resolving; it IS resolvable from proven infrastructure.
3. **Conductor descent bundle ≅ algebraic `g_j`.** Conductor theorem gives a bundle `F` with `⇑F=f`;
   bridging to the specific `old(M_j) g_j` needs `levelRaise` injectivity — `levelRaiseFun_injective`
   EXISTS (`LevelRaise.lean:367`), so the bundled wrapper is ~5 LOC. **Bounded.**
4. **Conductor invariance under descent:** `m_{χ_{M_j}} = m_χ` — standard `DirichletCharacter.conductor`
   invariance under `FactorsThrough`-lowering. **Bounded (mathlib API).**
5. **Heartbeats:** the induction workhorse + L3 are the biggest. Per project memory,
   `set_option maxHeartbeats` is FORBIDDEN — split into the named helper lemmas (L1-L6 are already
   separate) if any exceeds budget. No single leaf is large enough to threaten the default budget.

## Verdict

**BOUNDED, ~276 LOC** (floor ~195), one new file + ~50 LOC into `LevelRaise.lean`. The conductor
fact (Miyake 4.6.4) is ALREADY PROVEN (major de-risk vs the prior "OPEN/HARD" rating). The one
genuinely-absent piece is `levelRaise` associativity (elementary, ~50 LOC). No leaf hides an
unproven mathematical theorem; no `mainLemma`(sorry'd) or spectral-theorem dependency. This upgrades
the prior pass's "side-step via Mitigation B" to a **dischargeable, bounded unconditional 4.6.12**.

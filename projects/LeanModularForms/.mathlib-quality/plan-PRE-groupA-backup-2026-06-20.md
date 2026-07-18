# Development Plan: Miyake Theorem 4.6.12 (Strong Multiplicity One, full constant-multiple form)

*`/develop` Phase 1, 2026-05-26, branch `hecke-ring`. Supersedes the prior `plan.md`
(backed up to `plan-PRE-4612-backup-2026-05-26.md`, which covered the broader Hecke-ring
bridge program).*

## Goal

Formalise the FULL Miyake Theorem 4.6.12 (constant-multiple Strong Multiplicity One),
building on — and never modifying — the existing same-level normalised-newform uniqueness
`HeckeRing.GL2.strongMultiplicityOne_axiom_clean`.

Target Lean statement (top of the new file, stated `:= by sorry`):

```lean
theorem strongMultiplicityOne_constMul
    (f : Newform N k) (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n)
    (h_chi_factor : …) :   -- Miyake's character-conductor restriction, inherited from route-B 4.6.8
    ∃ c : ℂ, g.toCuspForm = c • f.toCuspForm
```

Miyake (p. 163): "Let f ∈ S_k^♯(N,χ) and g ∈ S_k(N,χ). If f and g are common
eigenfunctions of T(n) with the same eigenvalue for each n prime to some L, then g is a
constant multiple of f." Here `f : Newform` (new + normalised), `g : Eigenform` (full
χ-space common eigenfunction), `S` generalises "primes dividing L".

## References

- **[Miy]** Miyake, *Modular Forms*, 2nd ed., 2006. Statement Thm 4.6.12 p. 163; proof
  pp. 163–164; supports 4.5.15 (p. 149), 4.6.2 (p. 157), Thm 4.6.8 (pp. 159–162),
  4.6.9 (p. 162), 4.6.10 (p. 163), 4.6.11 (p. 163). PDF `docs/Toshitsune Miyake.pdf`
  (PDF page = book page + 9).
- **[DS]** Diamond–Shurman, *A First Course in Modular Forms*, GTM 228, 2005, §5.6–5.8.
- Full proof transcription + per-leaf source quotes: `.mathlib-quality/decomposition.md`.

## Mathlib / project inventory

| Concept | Status | Action |
|---------|--------|--------|
| Old⊕new decomposition (`cuspFormsOld`, `cuspFormsNew`, `oldPart`/`newPart`, `oldPart_add_newPart`, `mem_cuspForms{Old,New}_iff_…`) | EXISTS sorry-free (`Newforms/Basic.lean`) | USE |
| 4.6.10 stability `heckeT_n_preserves_cuspForms{Old,New}` | EXISTS sorry-free (`Newforms/LevelRaiseComm.lean:922,966`) | USE |
| Route-B Main Lemma 4.6.8 `mainLemma_charSpace_routeB` | EXISTS sorry-free (`SMOObligations.lean:232`) | USE |
| Same-level SMO `strongMultiplicityOne_axiom_clean`, `newform_unique_routeB` | EXISTS axiom-clean (`SMOObligations.lean:397,258`) | USE (template + dependency); NEVER modify SMO |
| `Newform`/`Eigenform` + `eigenvalue`, `isEigen`, `eigenvalue_eq_coeff`, `eigenvalue_coprime_mul` | EXISTS sorry-free (`Newforms/{Basic,MainLemma,CoeffSeq}.lean`) | USE |
| `levelRaise` = V_l, `heckeT_n_levelRaise_comm` | EXISTS sorry-free (`LevelRaise.lean:231`, `LevelRaiseComm.lean:883`) | USE (4.6.2) |
| `fourierCoeff_heckeT_n_period_one` (a₁(Tₙf) building block) | EXISTS sorry-free (`FourierHecke.lean:864`) | USE (4.5.15) |
| Eigenbasis / spectral `exists_simultaneous_eigenform_basis`; orthogonality `eigenforms_orthogonal_of_ne_eigenvalues` (private) | EXISTS sorry-free (`AdjointTheoryPetersson.lean:880,810`) | USE; de-privatise orthogonality |
| `DirichletCharacter.conductor`, `conductor_dvd_level`, `validSourceLevels` (m_χ\|M\|N) | EXISTS (`MainLemma.lean`, `LevelEmbed.lean:93`) | USE |
| 4.5.15(1) un-normalised (`aₙ = a₁ λₙ` for Eigenform) | NOT formalised | BUILD (T001) |
| 4.6.11 for `cuspFormsNew`-eigenform (`a₁ ≠ 0`) | NOT formalised | BUILD (T002) |
| 4.6.2 eigenvalue corollary | NOT formalised | BUILD (T003) |
| Miyake χ-refined old space `S_k^♭(N,χ)` + 4.6.9(1)(2)(3) | NOT formalised | BUILD (T005–T009) — **gap #4** |
| Decomposition `S_k(N,χ) = S_k^♭ ⊕ S_k^♯` for the χ-refined space | NOT formalised | BUILD/DECIDE (T012) — **RISK** |
| Bare `mainLemma` (no h_chi_factor), L-series eigenvalue lemmas | sorry'd, NOT used | AVOID (route B) |

## File structure

- `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean` — the entire new
  development (skeleton already written; `import LeanModularForms.SMOObligations`;
  namespace `HeckeRing.GL2`). One file suffices: the transitive import closure of
  `SMOObligations` already provides every dependency (AdjointTheoryPetersson, LevelRaise,
  LevelRaiseComm, Newforms.*, LevelEmbed) — verified by import-closure BFS (107 modules).
- **No cycle:** nothing in the project imports `LeanModularForms.SMOObligations` from
  outside the `SMOObligations/` cluster (verified by grep), so the new file is strictly
  downstream and SMO cannot depend on it.
- If `cuspFormsOldChar` + 4.6.9 grow large, optionally split into
  `SMOObligations/Lemma4_6_9.lean` (the χ-refined old space) imported by
  `StrongMultiplicityOneFull.lean`. Decide during execution (split-file at >1500 lines).

## Dependency graph

```
                 fourierCoeff_heckeT_n_period_one (∃)   Eigenform.isEigen (∃)
                              \                          /
T001 (4.5.15(1) un-norm) ──────●─────────────────────────
   │                                  \
   │                                   \── mainLemma_charSpace_routeB (∃)  cuspFormsOld_disjoint (∃)
   ▼                                            \            /
T002 (4.6.11) ───────────────────────────────────●─────────
   │
   ├──────────────► T005 (def cuspFormsOldChar)
   │                     │
T003 (4.6.2) ◄── heckeT_n_levelRaise_comm (∃)     │
   │                     ├── T006 (4.6.9(2))
   │                     ├── T007 (4.6.9(1) — empty index ⟹ ⊥)
   │                     ├── T008 (4.6.9(3)+eigen) ◄── T003, 4.6.10(∃), exists_simultaneous_eigenform_basis(∃), T011
   │                     └── T009 (bridge ≤, easy dir) ◄── cuspFormsOld(∃)
   │
T011 (L_indep public) ◄── eigenforms_orthogonal_of_ne_eigenvalues (∃, de-privatise)
   │
T004 (L5 new part = b₁f) ◄── T001, T002, newform_unique_routeB(∃ template)
T010 (L6 old part = 0)   ◄── T008, T001, T002, T006, T009, T011, route-B 4.6.8
   │
T012 (decomp codisjoint: S_k = oldChar ⊕ new) — RISK; or Mitigation B (extra hypothesis)
   │
T013 (T4.6.12 assembly) ◄── T004, T010, oldPart_add_newPart(∃), [T012 OR Mitigation B]
```

## Generality decisions

- **Level/weight:** keep the project's fixed `(Gamma1 N).map (mapGL ℝ)` and `k : ℤ`,
  `[NeZero N]` — matches every existing decl; no gain from abstracting the group here.
- **Nebentypus:** χ as `(ZMod N)ˣ →* ℂˣ` (the project's `cuspFormCharSpace` convention),
  with `m_χ := (Newform.dirichletLift χ).conductor` (or `χ.conductor` when a
  `DirichletCharacter` is in hand). The route-B `h_chi_factor` is carried verbatim from
  `strongMultiplicityOne_axiom_clean` — NOT weakened (it is mathematically necessary so long
  as the sorry-free Main Lemma is route B; the bare `mainLemma` is unproved).
- **"Prime to L":** generalised to "coprime to N and ∉ (S : Finset ℕ)", matching the
  existing SMO interface and `eigenvalues_eq_all_coprime_of_eq_off_finite` (which already
  upgrades "off finite S" to "all coprime"). Strictly more general than a single integer L.
- **`g` as `Eigenform`** (not a bare predicate): reuses `Eigenform.eigenvalue`/`isEigen`
  and keeps the eigenvalue bookkeeping uniform with `f : Newform`. The full-space membership
  is `hgχ` + (for the old part) the decomposition; `Eigenform` does not assume new/old.
- **`cuspFormsOldChar`** stated over an explicit `m_χ : ℕ` argument (rather than computing
  the conductor internally) so callers control which conductor is meant and so the def is
  reusable; the 4.6.9(1) lemma binds `m_χ := χ.conductor`.

## RISK section

1. **Gap #4 — the χ-refined old space (DOMINANT RISK).** Miyake's `S_k^♭(N,χ)` (span of
   `V_l` of **new** spaces `S_k^♯(M,χ)`, `m_χ | M | N`, `M ≠ N`) is **not** the project's
   `cuspFormsOld N k` (span of `levelRaise` of **full** spaces over all proper divisors,
   character-agnostic). The skeleton introduces `cuspFormsOldChar` = Miyake's definition.
   - **Forward leaves are bounded and mostly easy:** 4.6.9(2) (T006, subset_span),
     4.6.9(1) (T007, *trivial* under the span definition: the index set `{M : m_χ=N ∣ M ∣ N,
     M ≠ N}` is empty by `Nat.dvd_antisymm`, so the span is `⊥` — the "depth" Miyake
     describes lives in the orthocomplement equivalence, which 4.6.12 does not need),
     4.6.9(3) (T008, span-induction + existing eigenbasis), bridge `cuspFormsOldChar ≤
     cuspFormsOld` (T009, span_mono).
   - **THE OPEN PART (T012):** the assembly R needs `g`'s old part to live in
     `cuspFormsOldChar` (not merely `cuspFormsOld`). Two honest resolutions:
     - **(A) structural:** prove `IsCompl (cuspFormsOldChar N k χ m_χ) (cuspFormsNew N k)`,
       reducing (via finite-dim nondegenerate Petersson) to "same orthocomplement as
       `cuspFormsOld`", i.e. essentially `cuspFormsOldChar = cuspFormsOld` — **hard,
       potentially open-ended** (it is the formal content of the master plan's unproven
       identification at `docs/plans/strong-multiplicity-one.md:617`).
     - **(B) hypothesis (recommended, bounded):** state 4.6.12 with
       `hg : g.toCuspForm ∈ cuspFormsOldChar N k χ m_χ ⊔ cuspFormsNew N k` as an explicit
       hypothesis (matching the master plan's `hg1` and Miyake's framing `g ∈ S_k(N,χ) =
       S_k^♭ ⊕ S_k^♯`). Then no reverse bridge is needed; the theorem is faithful to Miyake
       modulo making the ambient-space-equals-direct-sum a *hypothesis* rather than a
       theorem. **This keeps the development bounded.**
   - **Recommendation:** build everything through T010 + the forward 4.6.9 leaves
     (bounded), then ship 4.6.12 under Mitigation B first (a complete, honest theorem),
     and pursue T012/(A) as a follow-on if the structural equivalence proves tractable.
2. **Privacy of `eigenforms_orthogonal_of_ne_eigenvalues`** (`AdjointTheoryPetersson.lean:810`):
   needs a public wrapper or a 1-line de-privatise. Low risk (T011).
3. **χ-eigenspace refinement of `cuspFormsNew M k`** (the caveat in `decomposition.md`):
   the project's new space at level M ignores χ; faithful 4.6.9 may need
   `cuspFormsNew M k ∩ cuspFormCharSpace_M (χ mod M)` (valid since `m_χ | M`). Folded into
   T005/T006; medium risk but local (conductor-descent of χ is supported by
   `DirichletCharacter.conductor` API).
4. **Heartbeats:** L4.3 (T008) and L6 (T010) are the largest proofs (~120–150 LOC). Per
   project memory, `set_option maxHeartbeats` is forbidden — decompose into helper lemmas
   if they exceed budget (split-proof cadence).

**Overall feasibility:** the new-part half, both supporting lemmas (4.5.15(1), 4.6.11),
4.6.2, and the forward 4.6.9 leaves are **bounded and well-grounded** in existing sorry-free
infrastructure. The **only** open-ended risk is the decomposition codisjointness for the
χ-refined old space (T012); it is cleanly isolated and **side-steppable via Mitigation B**,
which yields a complete and faithful 4.6.12. Verdict: **bounded development under
Mitigation B; gap #4's structural form (T012) is the sole open-ended item and is optional.**

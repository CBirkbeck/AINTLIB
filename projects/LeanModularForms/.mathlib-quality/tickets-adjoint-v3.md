# Tickets (v3, ADVERSARIAL) — leaf 2 verdict OPEN

**Supersedes** `tickets-adjoint-v2-PRE-leaf2.md` (which had 6 BUILD tickets under a BOUNDED
verdict — **WRONG**; see `decomposition-adjoint.md`).

## Verdict: OPEN — there is ONE genuine open obligation, in three guises

`petN_heckeT_p_RHS_aggregate_eq` (leaf 2, ConcreteFamily.lean:5461),
`SigmaQPermResidual_M_infty` (5198), and `SigmaQPermResidual_upper` (5201) all encode the SAME
irreducible content: `h_HeckeFD_swap ⟺ petN(T_p f,g) = petN(⟨p⟩f,T_p g)` (the symmetric form).
Proven via `lean_goal` @5550 (post-leaf1+aggregate goal == leaf2 verbatim) and via the two-way
equivalence at ConcreteFamily 1966 (`symm` from swap) + 2300 (swap from `symm`).

**There are NO BUILD tickets that close leaf 2 from existing code.** The v2 A1–A3/B1–B3 tickets
are withdrawn. What remains is a single multi-week analytic development ticket, or a decision to
park.

---

## The ONE open obligation: DS 5.5.2(a) over the conjugate-intersection group Γ_p(α)

### O1 (OPEN, multi-week) — per-rep change-of-variables over Γ_p(α_j)
The binding leaf. Build, in order:

1. **`smul_Gamma_p_α_fundDomain_PSL_ae_eq_adjoint_FD`** (NEW, ~150–250 LOC, OPEN core)
   Skeleton signature (NOT yet added; would live in FDTransport near 957):
   ```lean
   theorem smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain
       (α : GL (Fin 2) ℚ) (hα : 0 < ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ).det.val) :
       IsFundamentalDomain
         (ConjAct.toConjAct ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) •
           ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R))
         (((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) • Gamma_p_α_fundDomain_PSL (N := N) α)
         μ_hyp := by sorry
   ```
   This is the FD-image identification `α•(FD of α⁻¹Γα∩Γ)` ↦ FD of the conjugate group. Hard
   because det α = p (α not a PSL(2,ℝ) Γ₁-symmetry). Substrate: `measurePreserving_glPos_smul`
   (SummandAdjoint:896), `IsFundamentalDomain.smul`-style transport, mathlib FD API. **This is the
   piece DS Lemma 5.5.1(a,b) packages and that the repo has NOT built.**

2. **`peterssonInner_slash_adjoint_over_Gamma_p_α`** (NEW, ~60–120 LOC)
   Instantiate `peterssonInner_slash_adjoint` (AdjointTheory:770) at `D = Gamma_p_α_fundDomain_PSL`
   and feed (1) to rewrite the `α•D` domain into the adjoint-group FD. Yields the genuine
   `⟨Γ_p(α)-FD⟩(f∣α) g = ⟨adjoint-FD⟩ f (g∣α′)`.

3. **`heckeFD_swap_from_per_rep_Gamma_p_α`** (NEW, ~120–220 LOC)
   Sum (2) over the family `{M_∞}⊔{T_p_upper b}`, reconcile the `[Γ₁:Γ_p(α_j)]` indices against
   `c_N` via `sum_SL_Gamma_p_α_*` (FDTransport 1104/1137/1169) and the cross-block
   `Gamma1QuotEquivOfGamma0` reindex. **The cross-block reindex is false per-block (id d6e58f26)
   and only closes after the whole-double-coset sum** — this is the combinatorial heart.

4. Wire (3) → `h_HeckeFD_swap` → `petN_heckeT_p_diamond_shift_core_from_HeckeFD_swap` (1898) to
   discharge `petN_heckeT_p_symmetric_form` (5185), retiring sorries 5198/5201; then leaf 2 (5461)
   follows by the equivalence, retiring the global skeleton.

**Estimated size: several hundred LOC of NEW measure-theory/FD-combinatorics. NOT bounded.**

### Alternative (recommended if O1 is not funded): PARK
- Mark `petN_heckeT_p_symmetric_form`, `heckeT_p_adjoint`, and
  `exists_simultaneous_eigenform_basis`'s axiom-cleanliness as OPEN (analogous to T024 in MEMORY).
- Keep the proven leaf1 (5403), aggregate (122/202), leaf3 (5470), and the per-alpha forms
  (DeltaBSystem 1436/1525) as honest infrastructure — they are correct and reusable as the
  substrate for O1.

---

## Withdrawn (v2 tickets — based on the false BOUNDED verdict)
- ~~A1 `aggregate_HeckeFD_measure_hyps`~~ — actually PROVEN already (5470), but it only feeds the
  aggregate, which is the trivial LHS expansion. Keep as-is; it discharges nothing of substance.
- ~~A2 `petN_heckeT_p_LHS_eq_aggregate`~~ — PROVEN (5403); trivial LHS rewrite.
- ~~A3 `petN_heckeT_p_RHS_aggregate_eq` (leaf 2) as "assembly + relIndex"~~ — **this IS the goal**;
  not assembly. Reclassified as O1 (OPEN).
- ~~B1 global assembler~~ — already written (5537); it is the circular route. Leave its leaf-2
  `sorry` in place; it is the honest open obligation.
- ~~B2 repoint + delete~~ — do NOT repoint `heckeT_p_adjoint` to the global route (it bottoms out
  in the same open leaf). Do NOT delete the split sorries claiming the global route supersedes
  them — it does not.
- ~~B3 verify axiom-clean~~ — cannot succeed; `sorryAx` remains until O1.

---

## DO-NOT (unchanged + reinforced)
Do NOT claim the global aggregate route proves the symmetric form (circular). Do NOT try to prove
`SigmaQPermResidual_M_infty/upper` per-block (FALSE, id d6e58f26). Do NOT touch the 4.6.12 board,
`strongMultiplicityOne_axiom_clean`, `miyake_4_6_14_delta_slash_sum_coeff_zero`, or the signatures
of `heckeT_p_adjoint` / `exists_simultaneous_eigenform_basis` / `petN_heckeT_p_symmetric_form`.
No `native_decide`, no `set_option maxHeartbeats`, no custom `axiom`.

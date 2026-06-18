# Route 1 (primary, over K) — precise status (2026-06-02)

ASSEMBLED bound: `hasse_bound_skeleton` (HasseWeilSkeleton.lean) carries sorryAx ONLY via `qf_nonneg_skeleton`.
DONE axiom-clean: V.1.3 (sepDegree_oneSub_eq_pointCount / isogOneSub_negFrobenius_degree_eq_pointCount),
pc_sep (isogOneSub_negFrobenius_isSeparable), pc_fin (isogOneSub_negFrobenius_finiteDimensional),
ker_deg_skeleton, verschiebungV + IsDualOf V π + [q]⊆π subset (verschiebungV / mulByInt_q_pullback_subset_frobenius),
π-side genuineIsogSmulSub (rπ−s).

REMAINING = qf_nonneg_skeleton's 3 sorries, ALL bottoming at the V-side double-Vieta:
1. genuineIsogSmulSub_degree_eq_signed (GapSpines:2013, generic deg(rπ−s)=QF = Wall A).
2-3. degree_quadratic_exists_edge_r/s_char_divisible (L6Witnesses ~695,706; reduce to deg([a]−[b]V)=a²−abt+b²q via [p]=V∘π — SAME V-side content).

Wall-A scaffold SHIPPED: HasseWeil/WallA/VSideDual.lean (builds, no direct sorry, but carries sorryAx via the V-side pole):
- betaDualV = r·V−s constructible (addIsog GENERALISES to V via genuineIsogSmulSubV_universal_unconditional).
- genuineIsogSmulSub_degree_eq_signed_closed: reduces Wall A (via genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain) to 4 inputs:
  * h_sum_trace (π+V=[t]) — point-map level; likely trivial over E(F_q) (π=id, #E·P=0 ⟹ id+[q]=[t]). NOT geometric.
  * h_N_ne (N≠0) — arithmetic.
  * h_pullback_eq ((β_dual∘β)*=[N]*) — the GEOMETRIC double-Vieta pullback match. IRREDUCIBLE.
  * h_isDual_pair (IsDualOf β_dual β) — geometric.
- The V-side pole bound `genuineIsogSmulSubV_universal_unconditional` (Verschiebung/Genuine.lean:1632) carries sorryAx — the V-side pole analysis (π-side analog is CLEAN). = the double-Vieta core.

HONEST: Route 1's irreducible remaining = the V-side double-Vieta (r·V−s pole bound + (β_dual∘β)* pullback match) — the dual-additivity wall, the user's ACTIVE work. NOT a quick finish; both routes have a deep geometric core. Route 1 is maximally scaffolded so the double-Vieta closes the whole bound.

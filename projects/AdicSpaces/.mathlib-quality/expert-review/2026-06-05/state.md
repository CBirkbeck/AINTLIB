# Expert-review session state

- Generated: 2026-06-05
- Audience: Senior expert in adic spaces / Huber–Tate rings / non-archimedean functional analysis (Wedhorn, Huber, BGR assumed)
- Goal of brief: Route-faithfulness check — does our decomposition mirror Wedhorn's actual proof of Thm 8.28(b), and where does it diverge?
- Scope: Whole of Theorem 8.28(b) (both the embedding/separation half and the gluing/acyclicity half)
- Reply received: true (2026-06-05)
- Reply integrated: true (2026-06-05)

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | (decomposition faithfulness) Is splitting sheafiness into (a) the per-cover topological embedding O_X(base) ↪ ∏ O_X(Uᵢ) (injectivity from Cor 8.32 faithfully-flat; strictness from Prop 6.18(2)) + (b) q≥1 acyclicity via Lemma 8.34 → A.3/A.4 the right formalisation of Wedhorn's "sheaf of complete topological rings"? Is factoring q=0 through faithful flatness Wedhorn's intended route, and is the topological half genuinely Prop 6.18(2), or does Wedhorn get strictness more cheaply? |
| Q2 | (quasi-compactness keystone, no height-1) To get Spa A quasi-compact (closed in Spv A) without assuming all valuations height-1, is the route the Spv(A, I·A)-spectral description Cont(A) = {v : v(a)<1 ∀a∈I} (Thm 7.10) ∩ A⁺-conditions, realised as closed cylinders in the patch topology — with the correct cut quantifier the A₀-ideal of definition I, NOT its A-extension I·A? Or is there a cleaner standard route (e.g. Huber's spectral-space theorem directly)? |
| Q3 | (Banach/inducing/Huber external inputs) We treat Prop 6.17, 6.18 ("Proof. Missing" in Wedhorn), 7.48 (=[Hu2] 3.9), 7.54 (=[Hu3] 2.6) as external inputs. (i) Right call, or some provable inline in Tate generality? (ii) For 6.17/6.18 (the open-mapping content), what is the cleanest self-contained reference for a Tate ring (NOT σ-compact, so classical Banach OMT fails verbatim)? Henkel zero-sequence-of-units OMT (arXiv:1407.5647), or a [BGR] §2.8 statement? |
| Q4 | (hypothesis hygiene / ℂ_p test) We claim (b) needs ONLY "A strongly noetherian Tate" — no noetherian ring of definition, no domain, no global height-1 (test: A=ℂ_p⟨X⟩ has no noeth ring of def). (i) Agree this is the exact hypothesis set, and any noeth-ring-of-def on the case-(b) path is a defect? (ii) Is "O_X(V) strongly noetherian" legitimately derivable, or must it come from Example 6.38 propagating A's strong-noetherianity (since noeth+Tate ⟹ strongly-noeth is FALSE)? Is our section-ring promotion sound? |

## Ticket-board snapshot at brief time (from §7 of the brief)

| Mathematical statement | Status | Depends on |
|---|---|---|
| O_X(base) → ∏ O_X(Uᵢ) injective (Cor 8.32) | structure done, rests on 8.30 residual | Prop 8.30, Lemma 7.45, Prop 7.48 |
| same map topological-inducing (Prop 6.18(2)) | open (noeth-of-def → ring-noeth rewire) | Prop 6.18 (external) |
| Prop 8.30 flat | engine done; Remark 7.55 chain open | Ex. 6.38, Lemma 8.31, Remark 7.55 |
| Lemma 8.31 (3 parts) | done | Remark 8.29 |
| Remark 8.29 (µ_M bijective) | done modulo Prop 6.18(1)(2) (external) | Prop 6.18 |
| O_X(V) noetherian (Ex. 6.38) | done | Prop 6.17 (external), Mv-Tate topology |
| O_X(V) strongly noetherian | done via a noeth+Tate ⟹ strongly-noeth step — see Q4 | Ex. 6.38 |
| Lemma 7.45 (analytic point dominates non-open prime) | in progress (Wedhorn proves it) | Thm 7.10, Prop 7.41 |
| Spa point extension (Lemma 7.46 / Prop 7.48) | open, honest sorry | Prop 7.48 = [Hu2] 3.9 (external) |
| Lemma 8.34 (T-cover acyclic) | open (assembly) | Lemma 8.33, A.3(1)(2)(3), Cor 7.32 |
| Lemma 8.33 (2-elt Laurent exact) | open (diagram chase) | Cor 8.32, Ex. 6.38/6.39 |
| Lemma 7.54 (cover refines to rational T-cover) | open | [Hu3] 2.6 (external) |
| Prop A.3 / A.4 (Čech reductions) | done | — |
| Spa quasi-compact, no height-1 (keystone) | open | Wedhorn 7.5/7.10/7.12/7.30 |

(Live board: .mathlib-quality/tickets.md — the P0–P4 faithfulness-migration tasks + the M1 keystone finding.)

## Stuck points (from §8 of brief)

1. The three deepest leaves (Prop 6.17, 6.18, 7.48, Lemma 7.54) coincide with Wedhorn's OWN external citations ("Proof. Missing" / [Hu2] 3.9 / [Hu3] 2.6) — treated as external inputs; 6.17/6.18 = the non-archimedean open-mapping circle, discharged via a zero-sequence-of-units OMT (NOT σ-compact Banach).
2. The no-height-1 quasi-compactness keystone: Spa = {v ∈ Spv(A, I·A) : v(a)<1 ∀a∈I} ∩ {v(f)≤1 ∀f∈A⁺}; cut over A₀-ideal I (NOT I·A — just-fixed bug); ambient Spv(A,I·A) spectral; the cofinality coordinate constraint is the open content the hArch blanket wrongly assumes away.
3. Internal residuals Wedhorn proves and we should: Lemma 7.45, the Remark 7.55 geometric chain (Prop 8.30), Lemma 8.34 assembly, Lemma 8.33 diagram chase.
4. Hypothesis-hygiene worry: section-ring "strongly noetherian" promotion possibly via the false noeth+Tate ⟹ strongly-noeth — needs Example 6.38 propagation instead.

## Reference list (from §2.2 of brief)

- [Wedhorn] Adic Spaces (primary)
- [Hu1] Huber, Continuous valuations, Math. Z. 212 (1993)
- [Hu2] Huber, A generalization of formal schemes…, Math. Z. 217 (1994) — 7.48 = Prop 3.9
- [Hu3] Huber, Étale cohomology of rigid analytic varieties and adic spaces, Vieweg (1996) — 7.54 = Lemma 2.6
- [BGR] Bosch–Güntzer–Remmert, Non-Archimedean Analysis (1984) — open-mapping circle for 6.17/6.18
- [God] Godement, Topologie algébrique… — Cartan's theorem (A.4)
- [Henkel] arXiv:1407.5647 — zero-sequence-of-units open-mapping theorem (candidate for 6.18)

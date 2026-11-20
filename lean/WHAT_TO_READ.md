# What to read in the distance-product proof

Start with [the theorem audit](AUDIT.md). Each row links to the declaration and names any analytic facts supplied as hypotheses. [The paper correspondence](CLAIM_MAP.tsv) locates each declaration in the paper or identifies its role as a helper. [The audit notes](AUDIT_NOTES.md) explain the hypotheses of the main results.

| Question | Where to read |
|---|---|
| Which placements maximize the volume of the ordinary distance-product solid? | In every dimension d ≥ 3, take any n ≥ 1 marks and the set of points whose product of distances to the marks is at most 1. Under the six named capacity and equilibrium-measure hypotheses, this set has finite volume at most the volume of the unit d-ball. Equality holds exactly when all marks coincide. [Full statement and proof](ErdosVolume/Paper/TwoMarkSlices.lean#L401) |
| What does the bound give in three dimensions? | The maximum is 4π/3 for every n ≥ 1, attained exactly when all marks coincide. [Three-dimensional specialization](ErdosVolume/Paper/Statements.lean#L112) |
| Which planar result does the two-mark slice proof use? | Lean assumes the open unit sublevel from Erdős–Herzog–Piranian (1958), p. 134. Pólya’s original zweite Mitteilung (1928), Satz II, pp. 280–282, states the closed bound for every positive threshold. For two marks, Lean proves the boundary has area zero and rescales the result. [Lean hypothesis](ErdosVolume/Paper/TwoMarkSlices.lean#L108) · [Erdős–Herzog–Piranian, p. 134](https://users.renyi.hu/~p_erdos/1958-05.pdf#page=10) · [DOI 10.1007/BF02790232](https://doi.org/10.1007/BF02790232) · [Pólya, p. 280](https://archive.org/download/sitzungsbericht1928preu/page/n311_w900.jpg) |
| How does the capacity argument bound volume and characterize equality? | `volume_capacity` in [Capacity.lean](ErdosVolume/Capacity.lean) uses six named capacity and equilibrium-measure facts. The separate flux argument, `Flux.direct_bound_eq`, uses eight named facts in [Flux.lean](ErdosVolume/Flux.lean). |
| Which part of the inradius estimate is sharp? | [Sharpness.lean](ErdosVolume/Sharpness.lean) gives the two-mark ratio limit in `pair_ratio_limit` and the counterexamples to every smaller coefficient in `sharp_coefficient`. |
| How general is the upper bound? | `Paper.uniform_upper_given` in [Conditional.lean](ErdosVolume/Paper/Conditional.lean) covers all compactly supported source probabilities at each positive threshold under its seven named premises. |
| What happens along a sequence of positive deficits tending to zero? | At unit threshold the upper limit of fractional inradius loss divided by deficit is at most one. The trial-cost estimate first holds at each sufficiently small fixed annulus width δ, with positive denominator 1/6 − Cδ. Both statements use the same seven stability hypotheses. [Inradius limit](ErdosVolume/Paper/StabilityLimits.lean#L32) · [Fixed-δ cost bound](ErdosVolume/Paper/StabilityLimits.lean#L96) |
| Which statements are open? | The five rows marked OPEN in [AUDIT.md](AUDIT.md) are the unconditional statements `Paper.finite_volume`, `Paper.erdos_product`, `Paper.first_order_radius`, `uniform_upper` and `sharp_stability`. |

The comparison checks each finished declaration against its Lean statement in the challenge, including the explicit hypotheses of conditional results. [Comparison instructions](../comparator/README.md)

## Verification of this release

On November 19, 2026, Lean 4.35.0’s native comparator accepted all 157 finished declarations in the v1.22 release candidate against their challenge statements. The comparison permitted only `propext`, `Quot.sound` and `Classical.choice`. The 157 include 117 proofs and 40 proofs under the hypotheses listed in the audit. Five unconditional statements remain open. [Audit](AUDIT.md) · [Comparator configuration](../comparator/comparator.json)

Lean’s paranoid kernel (`leanchecker-paranoid`), `lean4lean`, `nanoda`, `con-leche` and `con-ron` each accepted the same solution export. As a negative control, deleting one line from the export caused the paranoid kernel to reject it with “Expr not found”.

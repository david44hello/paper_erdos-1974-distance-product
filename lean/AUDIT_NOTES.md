# Distance-product proof audit notes
Short paper v1.92 — scope of the proof and the unit-threshold infimum.

In the direct proof, CoareaSlabs applies the coarea formula to the finite-charge potential U. PuncturedGauss applies the divergence theorem to its smooth punctured superlevels. SurfaceFinite says that a smooth compact regular level surface of U has finite area. The integrated differential inequality uses local absolute continuity of W as well as its almost-everywhere derivative estimate.

The capacity proof uses the equality clause of Clark–Laugesen in one direction: equality gives sphere inclusion for every mark. The converse would impose a further capacity-zero restriction outside the ball. Paper.equality_capacity_spheres is the coverage link between the volume equality and the sphere inclusion.

The [short-paper crosswalk](JOURNAL_CROSSWALK.md) identifies the mathematical sources. The [claim map](CLAIM_MAP.tsv) gives their line ranges for each audited declaration.

| Root | Scope of checked deduction |
|---|---|
| volume_capacity and Paper.equality_capacity_spheres | Given open-set isocapacity, variational capacity normalization, the ball capacity law, equilibrium existence with atomlessness and logarithmic integrability, the translated moment bound and its forward sphere implication. The ball-law premise in Paper.ball_log_moment is separate. |
| Flux.direct_bound_eq | Given AnalyticNull, SardScalar, CoareaSlabs, PuncturedGauss, BallGauss, SphereArea, SharpIso and SurfaceFinite. The strict comparison between a noncoincident solid and the potential superlevel has an unconditional proof. |
| Paper.PlanarTwoMarkBound and Paper.planar_scaled_closed | Lean assumes the two-mark case of the open unit sublevel in Erdős–Herzog–Piranian (1958), defined on p. 125 with the area bound and equality case on p. 134. Pólya’s original zweite Mitteilung (1928), Satz II, pp. 280–282, gives the closed sublevel for any positive threshold R. For a monic polynomial of degree n the area is at most π R^(2/n), with equality exactly when all roots coincide. In the two-mark proof, each vertical line meets the boundary in at most four points. Fubini gives zero boundary area, and dilation then gives the closed bound for each positive threshold. [Erdős–Herzog–Piranian, p. 134](https://users.renyi.hu/~p_erdos/1958-05.pdf#page=10) · [DOI 10.1007/BF02790232](https://doi.org/10.1007/BF02790232) · [Pólya, Satz II, p. 280](https://archive.org/download/sitzungsbericht1928preu/page/n311_w900.jpg) |
| Paper.erdos_product_all_dim_given | At threshold one, uniform positive weights convert the ordinary product to the weighted region for every d ≥ 3 and n ≥ 1. The six capacity hypotheses give finiteness, the unit d-ball bound and equality exactly at coincident marks. |
| Paper.erdos_product_given | At threshold one, positive equal weights convert the ordinary distance product in three dimensions to the weighted solid. The six capacity premises yield the bound and its equality case. |
| Paper.general_log_bridge and atomic_g | Gives the formula at every point, including at an atom. An infinite integral of the extended negative logarithm gives potential product zero. |
| sharp_coefficient | A pair of equally weighted points attains ratios arbitrarily close to one at arbitrarily small positive deficits, for each positive threshold. The proof uses ordinary Lebesgue volume, the normalized sphere law, the actual positive radial root and an explicit second-order error bound. |
| Paper.figure_two_components and Paper.figure_volume_loss | At half-separation 5/4 the connected components are precisely the two distinct mark components. Each is contained in its own half-radius ball, so their combined volume is at most one quarter of the unit-ball volume. |
| Paper.figure_ball_cylinder and Paper.coalescent_deficits | At half-separation 3/5 the ball and cylinder have common radius 4/5. At zero separation both deficits vanish. The separate limiting-ratio statement takes a right-hand limit. |

The audit classifies a theorem with a named analytic premise as PROVED GIVEN when its imported proof has only standard Lean axioms. CompactIso and EqExists are intermediate formulations. Paper.compact_iso_for_stability and Paper.equilibrium_exists_for_stability give their precise reductions. Every claim's ordinary geometric, measure-theoretic and positivity hypotheses remain in its linked Lean type. OPEN means the imported proof depends on a placeholder. Public helper theorems in the generated audit count separately from paper claims in the correspondence map.


The final stability module has 35 public theorems. Its local upper-bound root takes CompactIso, EqExists, Frostman, EqUnique and BallLaw. Paper.uniform_upper_given and Paper.sharp_stability_given supply the first two through the open isocapacity, capacity normalization, ball capacity and equilibrium existence premises. Their seven explicit paper-level premises therefore cover the arbitrary-threshold upper bound and both limiting supremum statements. Each permits every compactly supported source probability and imposes no uniform bound on its support radius.

The audit contains 175 public theorems. It classifies 124 as PROVED, 46 as PROVED GIVEN and five as OPEN. The five unconditional targets with placeholders are Paper.finite_volume, Paper.erdos_product, Paper.first_order_radius, uniform_upper and sharp_stability. Source counts include public helpers.

## Bounds for real upper limits

Paper.sequence_cost_limsup, Paper.fixed_delta_cost_limsup and Paper.sequence_inradius_loss_limsup each prove eventual upper boundedness of the same real sequence used in their limsup. The numerical upper bound on a real limsup requires a separate boundedness statement to express the asymptotic estimate. An unbounded real sequence can have a computed real limsup of zero in Lean. The [control](scripts/RealLimsupControl.lean) proves this for the natural numbers embedded in the reals. All three theorems take the seven paper-level stability hypotheses.

For the fixed-width cost estimate the theorem first produces a positive constant C and a positive upper cutoff for δ. At each admissible δ the denominator 1/6 − Cδ is positive. The proof uses the common trial center at that width before taking the upper limit. For the inradius sequence the proof applies the uniform estimate to positive deficits tending to zero. [Exact statements and proofs](ErdosVolume/Paper/StabilityLimits.lean)

The journal proof also includes the exact radial and tangential Hessian actions, the shell direction estimate, and the original-coordinate trial integral. [Final correspondence](JOURNAL_CROSSWALK.md)

## The Discussion in dimension three

At threshold one, attainableRadii takes every admissible source law satisfying the printed volume cutoff. The set has a witness and a real lower bound for each nonnegative ε. The proof at zero deficit takes compact subsets with positive auxiliary tolerances tending to zero. Their capacity deficits force the minimum log cost to vanish, and the source must be a point mass. For the opposite bound, continuity of the equal-pair radial integral gives a pair at each sufficiently small prescribed deficit. Both facts enter the sharp infimum. The theorem uses the same seven hypotheses as the uniform stability result. [Proofs](ErdosVolume/Paper/Discussion.lean)

The real-line length calculation covers arbitrary placements, including the two-interval regime. In arbitrary Euclidean dimension the separate axial and perpendicular results allow every midpoint and the limiting half-separation t=1. These geometric statements have no named analytic input. [Proofs](ErdosVolume/Paper/PairGeometry.lean)

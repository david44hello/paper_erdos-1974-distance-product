# Short-paper claim crosswalk
Version 1.00 — November 19, 2026. Final v1.22 mathematical text and the strengthened real-limit statements.

Theorem 1.1 begins at main line 149. Theorem 2.1 begins at inradius line 34. Both theorem environments match the v1.02 and v1.12 mathematical sources byte for byte. The owner’s scope PDF includes the reviewer link to v1.02. The author updates the shared tag input after checking the v1.22 tag. The expanded companion carries no formalization claim.

The [claim map](CLAIM_MAP.tsv) points each of the 162 public declarations to the final short paper. The [imported audit](AUDIT.md) gives the status and explicit hypotheses of each declaration.

| Source | SHA-256 |
|---|---|
| Scope PDF | fd7d9540f118ee24eb67ddc2bb78b0c07a2071ffdb54001b0d7be9c3d87ba5e8 |
| Main TeX | d89812af0cbbd9df6637d01617fc31f4810757f79130128d8fa89ca5ccba8e5c |
| Inradius TeX | 2dc175e7c17c8959c4cda884190500dabd9dff4da9f143d74c56633393afe5d7 |
| Lean note | 345327ca5f4a6a222e12594aa35857b6d7d77332e266adfb04f083ffb2a8cecc |
| Printed guide tag input | f1831940fe5117162593a220078027088a0b30f1d49e518f889dd584438e653b |
| Companion note | d59e2007aed9dee8ff6ccb49b393975f4e0773888720283d34b995a9268bc819 |
| Author correspondence | c7417d8afaf39dc2c52a6cafd644a8ac2c464e8129603d004538beac91d1faa9 |
| Unified diff from v1.12 | c65f093cce7cf9a9a572a6700b8deef4f39ca2e71c8f4502a94882f8feec0061 |
| Theorem 1.1 environment | 7af608e90789ae6220121b0a49482483c4a9553f83547f761b8f6c7725fd5a69 |
| Theorem 2.1 environment | 1834f60c703ff272b58d6c25fee99f80a3f8c9fe271c2e318a860dff2ab97bb9 |

## Changes from v1.12 to v1.22

The entries follow the author’s numbered correspondence. Each location is in the named TeX source. The first comparison column uses the v1.12 source.

| Entry | Source | v1.12 lines | v1.22 lines | Claim and evidence |
|---|---|---|---|---|
| 01 | erdos_volume.tex | 13 | 14-14 | `Paper.erdos_product_all_dim_given` gives the maximum and equality criterion for fixed d ≥ 3 and n ≥ 1. `Paper.coincident_solid` identifies the translated unit ball. |
| 02 | erdos_volume.tex | 18-23,49-60 | 19-24 | `Paper.erdos_product_all_dim_given` states the ordinary product directly for all the stated dimensions and mark counts. |
| 03 | erdos_volume.tex | - | 23-25 | Pólya, Satz II, is the cited general planar result. `Paper.PlanarTwoMarkBound` supplies its EHP two-mark open specialization. |
| 04 | erdos_volume.tex | 40-44,85-86 | 25-27 | Historical account of the three-dimensional pair. `Paper.distinct_pair_volume_by_slices` and `Paper.distinct_pair_strict_volume_given` prove strict loss. |
| 05 | erdos_volume.tex | 20-23,68-73 | 27-30 | `volume_capacity` uses the six capacity and equilibrium facts. `Flux.direct_bound_eq` proves the weighted conclusion under the eight flux-route facts. |
| 06 | erdos_volume.tex | 24-29 | 30-35 | `Paper.sharp_stability_given` and `Paper.uniform_upper_given` give the uniform three-dimensional law. `pair_ratio_limit` and `sharp_coefficient` supply the sharp examples. |
| 07 | erdos_volume.tex | 37-44 | 43-50 | `Paper.erdos_product_all_dim_given` fixes dimension and count, allowing every placement. The publication date is cited history. |
| 08 | erdos_volume.tex | 37-40,56-59 | 52-57 | `Paper.coincident_solid`, closedBall_volume, `Paper.omega_three` and `Paper.erdos_product_all_dim_given` give attainment and rigidity. |
| 09 | erdos_volume.tex | 68-79,49-60 | 65-69,82-85 | The recorded open status is attributed to the cited authors. `Paper.erdos_product_all_dim_given` gives the mathematical answer. |
| 10 | erdos_volume.tex | 40-44,85-86 | 71-76 | The cited 1976 report concerns two marks in three dimensions. `Paper.distinct_pair_volume_by_slices` gives the opposite strict inequality. |
| 11 | erdos_volume.tex | 99-102,105-115 | 97-108 | `Paper.coincident_solid`, `Paper.figure_two_components` and `Paper.figure_volume_loss` cover the two illustrated placements. The separation 2.5 is the author's example. |
| 12 | erdos_volume.tex | - | 112-118 | `Paper.two_marks_on_line` gives the exact two intervals, their lengths and the strict inequality. |
| 13 | erdos_volume.tex | - | 118-122 | The general all-degree planar bound is cited to Pólya, Satz II, p. 280. EHP p. 134 uses the open unit sublevel. |
| 14 | erdos_volume.tex | 39-42,56-59 | 124-126 | `Paper.coincident_solid` covers a single mark. `Paper.distinct_pair_volume_by_slices` covers separated pairs in space. The expectation is historical. |
| 15 | erdos_volume.tex | 40-47,85-88 | 128-133 | The dated reports and literature-search statement are attributed. `Paper.distinct_pair_strict_volume_given` and `Paper.distinct_pair_volume_by_slices` give the mathematical refutation. |
| 16 | erdos_volume.tex | 45-47 | 135-138 | Ferudun's covering theorem is cited prior work with a connectedness assumption. |
| 17 | erdos_volume.tex | 37-39,49-59 | 45-47,140-147 | The proof of `Paper.erdos_product_all_dim_given` identifies the ordinary product sublevel with the uniform-weight geometric-mean sublevel; `volume_capacity` allows arbitrary weights and positive thresholds. |
| 18 | erdos_volume.tex | 49-60 | 149-160 | `volume_capacity` and `Flux.direct_bound_eq` are the conditional proofs. `Paper.finite_volume` is the open unconditional target. |
| 19 | erdos_volume.tex | 68-73,85-88 | 82-85,165-172 | `Flux.inclusion`, `Flux.integrated` and `Flux.radius_at_threshold` give the enclosing superlevel bound. `volume_capacity` gives the other route. |
| 20 | erdos_volume.tex | 74-79,89-93 | 86-89 | `Paper.uniform_upper_given`, `Paper.sharp_stability_given` and `sharp_coefficient` give the sharp inradius assertion. |
| 21 | erdos_volume.tex | 105-115 | 209-221 | `Paper.pair_axial_polynomial`, `Paper.axial_interval`, `Paper.transverse_segment`, `Paper.missing_midplane`, `Paper.joined_to_mark` and `Paper.figure_two_components` give the component proof. |
| 22 | erdos_volume.tex | - | 174-184 | `Paper.distinct_pair_volume_by_slices` places arbitrary distinct marks in a horizontal plane. `Paper.spatial_pair_section` and `Paper.two_mark_slice_identity` give the section formula. |
| 23 | erdos_volume.tex | - | 185-197,202-207 | `Paper.pair_section_subset`, `Paper.pair_section_empty`, `Paper.planar_scaled_closed` and `Paper.pair_section_area` handle the entire section. |
| 24 | erdos_volume.tex | - | 193-197,202-207 | `Paper.vertical_level_quartic`, `Paper.vertical_level_at_most_four` and `Paper.planar_pair_level_null` justify open/closed equivalence. `Paper.pair_section_area` gives strictness. |
| 25 | erdos_volume.tex | - | 198-200 | `Paper.unit_ball_section_area`, `Paper.spatial_ball_section` and `Paper.distinct_pair_volume_by_slices` give the comparison disk, its membership and strict integration. |
| 26 | erdos_volume.tex | 71-73,118-122,157-165 | 223-233 | `Flux.beyond_last`, `Flux.strict_ball` and `Flux.strict_volume` prove the open-ball and strict volume comparisons. |
| 27 | erdos_volume.tex | 70,152-155 | 271-274 | The order-two weak estimate for densities is credited to Tang and Wang, Theorem 1.1, and the point-charge approximation to the expanded companion after Theorem 4. The short proof uses `Flux.integrated`. |
| 28 | erdos_volume.tex | 169-173 | 290-298 | The predicate equilibrium specifies minimum energy among the supported probability measures. `solid_energy` and `volume_capacity` record its role. |
| 29 | erdos_volume.tex | 222-224 | 349-350 | Bibliographic metadata for the expanded companion. |
| 30 | erdos_volume.tex | - | 359-361 | Bibliography for EHP's restatement of the planar estimate. |
| 31 | inradius.tex | 18-28 | 34-44 | `Paper.sharp_stability_given` proves both right-hand limits under the seven stability hypotheses. `Paper.uniform_upper_given` gives the upper estimate and `sharp_coefficient` supplies the lower witnesses. |
| 32 | inradius.tex | 37-48,53-56 | 58-64 | `pair_ball_cylinder`, `pair_inradius` and `pair_asymptotics` give the three-dimensional equal-weight example. |
| 33 | inradius.tex | 37-56 | 66-88 | `Paper.figure_pair_widths` gives the entire vertical projection and axial section. `Paper.figure_ball_cylinder` and `cylinder_ball_radius` give the inscribed ball and the bound for off-center balls. |
| 34 | inradius.tex | 77-96 | 111-117 | `pair_asymptotics`, `Paper.coalescent_deficits` and `pair_ratio_limit` give the two fourth-order remainder bounds, vanishing deficits and the right-hand ratio limit. The printed 0/0 denotes the undefined ordinary quotient. |
| 35 | inradius.tex | 118-125 | 140-149 | `stability_center` and `stability_center_ball` produce the minimizing center and ball. `Paper.sequence_cost_limsup` gives the bounded cost ratio and upper limit. |
| 36 | inradius.tex | 164-172,273-276 | 199-207,335-341 | `stability_normalize` and `Paper.original_trial_cost_chain` use the same scaling and translation; the trial integral is pulled back to the original measure. |
| 37 | inradius.tex | 126-134,187-190,272-276 | 151-164,222-226 | `stability_center`, `stability_normalize`, `stability_trial_min` and `Paper.original_trial_cost_chain` distinguish the three points. |
| 38 | lean_note.tex | 1-17 | 1-4 | Publication note. Theorem 1.1 uses the capacity or flux hypotheses; Theorem 2.1 uses the seven paper-level stability hypotheses. The linked guide explains each. |
| 39 | erdos_volume.tex | - | 112-115 | `Paper.pair_intercepts` gives axial extension and transverse contraction. `Paper.figure_pair_widths` specializes to the pictured pair. |
| 40 | erdos_volume.tex | 49-60 | 162-164 | `Paper.erdos_product_all_dim_given` states the displayed ordinary-product corollary directly, including finite volume. |
| 41 | erdos_volume.tex | 124-135 | 235-249 | `Flux.geometry` gives equal volumes. `Flux.flux_identity` gives the surface integral at a positive regular level. |
| 42 | erdos_volume.tex | 137-155 | 250-271 | `Flux.null_sets`, `Flux.ae_regular`, `Flux.level_derivative`, `Flux.level_inequalities`, `Flux.scaled_derivative`, `Flux.integrated` and `Flux.radius_at_threshold` implement the slab argument. |
| 43 | erdos_volume.tex | 157-166 | 276-288 | `Flux.strict_volume` proves strict loss; `Flux.coincident` gives the ball and closedBall_volume gives its volume. |
| 44 | erdos_volume.tex | 168-185,187-188 | 290-298,313-315 | `log_moment_sandwich`, `compact_isocapacity`, `capacity_sphere_consequence` and `volume_capacity` give the inequalities and equality step. |
| 45 | inradius.tex | 2-16,18-28 | 5-32 | `Paper.general_log_bridge`, `atomic_g`, `trunc_log_continuous`, measureSolid_regular and `scale_identities` cover the representation, regularity and scaling. |
| 46 | inradius.tex | 18-35 | 46-56 | `Paper.uniform_upper_given` gives the epsilon form. `Paper.sharp_stability_given` gives the sharp limits for all positive thresholds. |
| 47 | inradius.tex | 100-105 | 121-129 | `stability_center` and `stability_center_ball` implement the minimum and its radius estimate. |
| 48 | inradius.tex | 120-125,136-140,155-158,272-276 | 144-149,166-174,185-189,335-341 | `Paper.sequence_cost_limsup`, `stability_piece_bounds`, `stability_normalize` and `Paper.original_trial_cost_chain` apply to admissible compactly supported probabilities. |
| 49 | erdos_volume.tex | 148-155 | 259-271 | `Flux.level_inequalities` and `Flux.scaled_derivative` give the sign, cancellation and almost-everywhere scaled derivative. |
| 50 | inradius.tex | 60-73 | 92-107 | `uniform_radial_error` gives the squared-radius remainder. The private pairRadiusCubeError in the proof of `pair_asymptotics` gives the uniform cubic remainder. `pair_volume_fraction` and `axial_second_moment` give the spherical average. |
| 51 | inradius.tex | 100-105,126-134,272-276 | 121-126,151-164,222-226,335-341 | `stability_center`, `stability_normalize`, `stability_trial_min` and `Paper.original_trial_cost_chain` give the three constructions and the inverse coordinate identity. |
| 52 | inradius.tex | 208-220 | 247-269 | `Paper.discarded_log_chain`, `stability_truncation`, `stability_moving_center` and `stability_compact_gap` give the discarded error and the annular contradiction. |
| 53 | inradius.tex | 231-253 | 279-312 | `Paper.journal_hessian_eigendirections`, `Paper.journal_shell_direction`, `stability_annular_second_moment`, `stability_annular_curvature` and `stability_trial_min` give the quadratic-form estimate and constrained minimum. |
| 54 | inradius.tex | 266-276 | 315-341 | `stability_join_at_center` states the exact minimum, `stability_shift_loss` controls the translation, and `stability_common_center` gives the fixed-width eventual lower bounds. |
| 55 | inradius.tex | 274-281 | 335-346 | `Paper.fixed_delta_cost_limsup` states positive denominator, eventual upper boundedness and the fixed-width upper limit. `Paper.sequence_cost_limsup` states the bounded cost ratio and final upper limit of two. |
| 56 | erdos_volume.tex | - | 185-200,202-207 | `Paper.vertical_level_quartic`, `Paper.vertical_level_at_most_four`, `Paper.planar_pair_level_null`, `Paper.planar_scaled_closed` and `Paper.pair_section_area` cover the planar step for two marks. |
| 57 | inradius.tex | 18-35 | 32-55 | `Paper.sharp_stability_given` uses the right-hand filter and `Paper.uniform_upper_given` restricts to positive deficit. The higher-dimensional stability coefficient is cited to the companion. |
| 58 | inradius.tex | erdos_volume.tex 74-76 | 92-94 | Attribution of the connected pair calculation to Jasion and Magnucki. The three-dimensional radial computation in this repository is given by `pair_radial` and `pair_asymptotics`. |
| 59 | companion_note.tex | 1-5 | 1-5 | Bibliographic and attachment reference to the expanded companion's higher-dimensional result. |
| 60 | erdos_volume.tex | 40-47 | 22-26,47-50 | Historical publication date as given in the cited Canterbury proceedings tables. |
| 61 | erdos_volume.tex | - | 188-200,362-364 | Pólya's general closed area theorem is cited. `Paper.planar_scaled_closed` and `Paper.pair_section_area` give the checked degree-two specialization for the full section. |
| 62 | erdos_volume.tex | - | 202-207,359-364 | The open unit hypothesis is `Paper.PlanarTwoMarkBound`. `Paper.planar_pair_level_null` and `Paper.planar_scaled_closed` connect the two formulations for two marks. |
| 63 | inradius.tex | 118-134,168-171,273-277 | 150-164,200-205,335-342 | `stability_center_ball` and `Paper.original_trial_cost_chain` give the inscribed ball and the cost at the specified trial point. |
| 64 | inradius.tex | 233-247 | 284-303 | `stability_annular_curvature` gives eventual positivity and the uniform Hessian lower bound for every point and direction at each sufficiently small fixed width. |
| 65 | inradius.tex | 272-281 | 343-350 | `Paper.sequence_inradius_loss_limsup` states eventual upper boundedness and the arbitrary-sequence upper limit one. `pair_ratio_limit` and `sharp_coefficient` give the reverse bound for the supremum. |
| 66 | erdos_volume.tex | - | 371-373 | Printed reference to the guide. The mathematical scope PDF uses the previously verified private tag. |
| 67 | proof_guide_release.tex | - | 1-3 | One tag input controls both URLs and the printed citation. The author updates it after verification of the new tag. |

The remaining changed lines are version or layout edits, the inclusion of the tag input, and two changes in wording. Inradius 179 describes the same region used in the Fubini argument. Inradius 216–220 restates the sphere-energy and uniqueness facts supplied by Stability.BallLaw and Stability.EqUnique.

## Publication edits from v0.92 to v1.02

| Source | v0.92 lines | v1.02 lines | Disposition and evidence |
|---|---|---|---|
| Main | 1 | 1 | Version comment. |
| Main | 28 | 28 | The fractional inradius deficit is the numerator in `pair_ratio_limit`. The denominator is the fractional volume deficit. |
| Main | 32 | 32 | Keyword typesetting. |
| Main | 46 | 46–47 | Ferudun’s covering statement is attributed prior work on connected solids. The volume theorem continues to allow any number of components. |
| Main | 60–70 | after 60 | The two-mark strict bound and sharp inradius estimate move to the result bullets below. |
| Main | after 92 | 83–94 | The first bullet applies `Paper.distinct_pair_strict_volume_given` at unit threshold with its six capacity premises. Talenti is a method attribution for `Flux.direct_bound_eq`. The second bullet gives the uniform first-order upper estimate from `Paper.uniform_upper_given` under seven premises. The two-mark lower limit is `pair_ratio_limit`, with `scale_identities` for a positive threshold and `sharp_coefficient` for the general lower witness. |
| Main | 179–180 | 181–185 | `dirichlet_outer` and `Paper.compact_capacity_outer` give the bounded-open-neighborhood infimum. `compact_isocapacity` gives the compact-set volume comparison under three named premises. |
| Main | after 213 | 219–224 | Bibliographic entries for the earlier covering result and expanded companion. |
| Main | 215 | 226 | Bibliographic title correction. |
| Main | 225 | after 235 | Bibliographic index numbers removed. |
| Inradius | 1 | 1 | Version comment. |
| Inradius | 15 | 15–16 | `stability_measure_volume` bounds the unit-threshold volume under compact isocapacity, existence of the equilibrium measure and the potential bound. `scale_identities` preserves the deficit when the source and threshold are rescaled. |
| Inradius | after 56 | 58 | Figure placement. |
| Inradius | 99–101 | 101–102 | The definition of `Stability.J` minimizes the cost over all points of three-dimensional space. `stability_center` proves attainment. When the cost is below log 2, `stability_center_ball` supplies a ball at that point. |
| Inradius | 125–131 | 126–133 | Proof outline. Divide coordinates by the capacity radius (`stability_rescale_dist`), choose the translating point (`stability_normalize`), obtain concentration (`stability_annulus_mass`), and minimize on the small ball (`stability_trial_min`). `Paper.original_trial_cost_chain` gives the cost at the resulting trial point in the original coordinates. |
| Inradius | 143–145 | 145–149 | `stability_fubini` gives integrability, equality of the two means, a nonpositive mean on the solid and the capacity-radius bound. The negative-log estimate is a proof step obtained from the elementary upper bound on log applied at the reciprocal distance. |
| Inradius | 165–166 | 169–171 | `stability_normalize` gives the low-moment point and translates the two measures so this point becomes the origin. |
| Inradius | 205–206 | 210–212 | `stability_moving_center` gives weak convergence to the translated sphere measure and the lower bound for the truncated integrals. |
| Inradius | 226 | 232–234 | `stability_phi_shape`, `stability_phi_integral` and `stability_annular_curvature` give positivity and the restricted integral bound. The explanation of the radial contribution describes the Hessian computation in `Paper.journal_hessian_eigendirections` and `stability_hessian_kernel`. |
| Inradius | 233–234 | 241–245 | `stability_annular_second_moment` gives zero boundary mass and the limiting bilinear form I/3. The symmetry and trace computation is in the proof of `sigma_second`. The Taylor factor of one half explains the passage from the bound on the Hessian in `stability_annular_curvature` to the interior quadratic bound in `stability_trial_min`. |
| Inradius | 254–255 | 265–266 | `stability_join_at_center` gives the exterior bound about the selected center. `stability_shift_loss` gives convergence of the shift error for fixed positive radius. |
| Inradius | 261–263 | 272–274 | For fixed annulus width, `Paper.original_trial_cost_chain` evaluates the cost at the original point c(z+y) and bounds the minimum by its value. This is c(y+z) in the paper. The coefficient and center may depend on the annulus width. |
| Companion note | 1–5 | 1–5 | The companion theorem and bibliographic identifier are publication metadata for the short paper. |

## Main source

| Edit | v0.42 | v0.82 | Disposition and evidence |
|---|---|---|---|
| 1 | 1–2 | 1–2 | Layout. Version comment and document class; no change to a mathematical assertion. |
| 2 | 4–5 | 4 | Layout. Journal package and page geometry. |
| 3 | 9–10 | 8–9 | Layout. Link colors, attachment support and theorem numbering. |
| 4 | 13–15 | after 11 | Moved. Title, author and date reappear below. |
| 5 | 17–18 | 13–17 | Mixed. The new title states maximization. volume_capacity and Flux.direct_bound_eq give the bound and equality characterization under their named inputs. Paper.coincident_solid gives attainment. Author, date and abstract commands are metadata. |
| 6 | 22–23 | 21–22 | Attribution. The authors and year of the equilibrium-moment comparison are spelled out. The deduction is volume_capacity. |
| 7 | 26–31 | 25–35 | Mixed. Uniform D+o(D) is the epsilon bound Paper.uniform_upper_given. sharp_coefficient and pair_ratio_limit give sharpness and the actual two-mark limit. Companion and Lean note includes, keywords, subject classes and section title are publication metadata. |
| 8 | 57–61 | 61–65 | Mathematics. Paper.distinct_pair_strict_volume_given gives finite volume and the strict 4π/3 bound for every pair of distinct points at the ordinary threshold one. Six capacity inputs are explicit. The historical report and rearrangement attribution are bibliography or proof description. |
| 9 | 77–78 | 81–83 | Mathematics. Flux.strict_ball puts an open ball in the Newtonian superlevel outside the product region for any distinct pair of locations. Flux.direct_bound_eq supplies the flux volume comparison. |
| 10 | 81 | 86 | Attribution. “Equally weighted” identifies the historical two-mark example. Its mathematical counterpart is pairLaw. |
| 11 | 131–133 | 136–138 | Mathematics. Paper.analytic_partial_zero_set gives one and the same partial derivative on the connected complement, analytic, nonzero somewhere, with null zero set containing the critical set. It takes AnalyticNull. Flux.null_sets also treats individual levels. |
| 12 | 135 | 140–141 | Mathematics. Flux.level_derivative states the slab consequence, local absolute continuity and the a.e. derivative with the coarea hypothesis and critical/level nullity. |
| 13 | 177–178 | 183–185 | Mathematics. Paper.equality_capacity_spheres applies the forward sphere implication after equality of all moments. Citation and line wrapping changed. |
| 14 | after 190 | 198–200 | Metadata. Acknowledgments and author responsibility. |
| 15 | 203 | 213 | Bibliography. Page range added to the Erdős citation. |
| 16 | 208–210 | after 217 | Moved. The Talenti entry moves to its final position. |
| 17 | after 214 | 222–225 | Bibliography. Relocated entry gains indexing identifiers. |
| 18 | after 215 | 227–228 | Metadata. Author address and contact information. |

## Inradius source

| Edit | v0.42 | v0.82 | Disposition and evidence |
|---|---|---|---|
| 1 | 2 | 2 | Layout. Section numbering changes. |
| 2 | 4–5 | 4–5 | Mathematics. atomic is the explicit weighted sum of Dirac measures. atomic_g identifies the finite product, including at the marks. |
| 3 | 44 | 44–45 | Mathematics. Paper.outside_cylinder_product_bounds gives t²<1/2, b²>t² and 1<(b²+t²)²≤the squared distance product. pair_ball_cylinder gives containment. |
| 4 | 78–80 | 79–81 | Mathematics. The equally weighted pair has a matching ball and cylinder by pair_ball_cylinder and pair_inradius. pair_volume_fraction and pair_ratio_limit give the volume and the limiting quotient. |
| 5 | 104 | 105–107 | Mathematics. stability_center gives the zero gradient and vector integral. stability_center_ball states the Jensen quotient bound and the exact expansion after cancellation as separate conjuncts. |
| 6 | 112 | 115–116 | Mathematics. Paper.sequence_cost_limsup quantifies over every compact-source sequence with positive deficits tending to zero. |
| 7 | 114 | 118 | Mathematics. Paper.sequence_cost_limsup states the limsup of the actual quotient J/γ is at most two, along with the γ/D limit. Its seven analytic premises are explicit. |
| 8 | 116–120 | 120–126 | Mathematics. stability_scalar_limits gives the Taylor error. stability_normalize gives the mean bound after dilation, stability_piece_bounds gives β≤(γ+γ²)/3, and Paper.trial_cost_six gives actual original-source trial centers with cost ≤(6+ε)β eventually for every ε>0 in the normalized setup. |
| 9 | 124–126 | 130–133 | Mathematics. stability_compact_piece and stability_piece_bounds give compact subsets of the same solid at the printed exp(−γ−γ²) volume threshold. Positive deficits tending to zero are eventually below one, the regime where γ is defined by the real logarithm. |
| 10 | 132 | 139 | Mathematics. stability_fubini identifies the two mean logarithms and bounds the mean by zero. The superscript denotes the original source law. |
| 11 | 140–141 | 147–150 | Mathematics. Paper.compact_piece_unit_bound gives c≤1, \|K\|≤ω₃ and finite volume with \|E₁\|≤ω₃ for the whole compact source; stability_compact_comparison and stability_measure_volume give the two constituent comparisons. |
| 12 | 143 | 152 | Notation. Original source and original equilibrium measures are now explicitly named before rescaling. stability_rescale_dist and stability_normalize express the change of variables. |
| 13 | 154 | after 162 | Removed. The translation-isometry sentence was deleted. The distance identity in stability_normalize remains a supporting step. |
| 14 | 195–197 | 203–206 | Mathematics. Paper.discarded_log_chain states all pointwise inequalities from the removed log through C√η/s, for 0<s<η<1. stability_truncation gives the uniform integrated O(√η) bound. |
| 15 | 215–216 | 224–228 | Mathematics. Paper.journal_hessian_eigendirections gives the exact radial and tangential actions in the center variable on every test vector. Paper.journal_shell_direction gives \|s−1\|≤2δ and an explicit 4δ direction bound. stability_hessian_kernel gives the resulting operator estimate. |
| 16 | 222–223 | 234–236 | Mathematics. stability_trial_min gives the constrained minimizer and nonnegative first variation toward every point of the closed ball. |
| 17 | 228–229 | 241–243 | Mathematics. Paper.trial_inner_chain gives the same minimizing centers and both inequalities g≥b times squared distance≥b times log(1+squared distance). |
| 18 | 243–248 | 257–268 | Mathematics. Paper.original_trial_cost_chain identifies the original-center cost with the printed integral and proves all three comparisons through β/k. Paper.sequence_cost_limsup gives the limit after division; stability_common_center gives the fixed-δ and arbitrary-tolerance bounds. pair_ratio_limit and sharp_coefficient supply the lower examples. |

## Figure revisions from v0.82 to v0.92

| Short-paper location in v0.92 | Claim and corresponding Lean statement |
|---|---|
| Main 1, 28–29 | The version comment records the figure edit. The abstract specifies which deficit is the numerator. The definition of `ratio` and `pair_ratio_limit` give that quotient and its one-sided limit. |
| Inradius 51–55, Figure 2 | At half-separation 3/5, `Paper.figure_ball_cylinder` gives a ball of radius 4/5 inside the solid, containment of the solid in a cylinder of that same radius, and inradius 4/5. The supremum in the inradius ranges over every center. |
| Inradius 77–84, Figure 3 table | At unit threshold, `pair_ratio_limit` and `sharp_coefficient` exclude smaller first-order coefficients. The two-mark example alone gives no uniform upper bound. `Paper.uniform_upper_given` gives the upper estimate with factor 1 + ε for every ε > 0 and all sufficiently small positive deficits, under seven named analytic premises. |
| Inradius 87–91, Figure 3 caption | `pair_asymptotics` gives leading term t²/2 for both deficits and error at most a constant times t⁴. `pair_ratio_limit` gives the one-sided ratio limit. `Paper.coalescent_deficits` gives both zero losses at coincidence. The red, grey and green key on line 87 explains the table. The open marker denotes the limit. |
| Inradius 92–93, Figure 3 caption | `sharp_coefficient` at unit threshold gives, for each C < 1 and every positive upper bound on the deficit, an equal-weight configuration with positive deficit below or equal to that bound and inradius loss greater than C times that deficit. |

The plotting code changes the Figure 2 legend size and spacing. The figure widths and the Figure 3 table layout are presentation changes. Source lines after the Figure 3 caption move by four in the inradius file.


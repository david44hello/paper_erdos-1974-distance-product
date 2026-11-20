# Short-paper claim crosswalk
Version 1.10 — Mathematical text v1.42, including the name-only reader addendum.

The weighted volume theorem at Main 159–170 matches the v1.22 theorem environment byte for byte. Inradius 41–51 changes “their support radii” to “the radii of their supports”. Each law has compact support, with no radius bound shared across laws. The quantifiers and mathematical conclusion agree.

The main source, inradius source, mathematical PDF and source archive are pinned below. The name-only reader removes two lines after the bibliography and preserves every mathematical location. The formalization covers the short paper; separate extensions and research questions are identified in the table. [Claim map](CLAIM_MAP.tsv) · [Theorem audit](AUDIT.md)

| Input | SHA-256 |
|---|---|
| Mathematical short PDF | e5b7c13b0a0c0ddc5fe0750b32740e2487252842844e4c33c5a3c41df9bc2948 |
| Mathematical sources | 8b863901c2069d87b40d47a80f50aab5aac1ce8b94fac3bb1c20871a64aa529e |
| Name-only reader PDF | ad12e3b878c6caac63913fa15297cafbbd2c4612601bcea99629dee7f91f53f3 |
| Reader source archive | 61aecdcdb81200ad37c894331a8a2c35939e1774b3a942ab0c5c9ecdb2aaea3b |
| Reader main TeX | bd49e2b46d2ea0228887060bfe76441e2df319b20cc5ed921f07f7736585dd45 |
| Mathematical main TeX | 7b93eb17b6b6c8b810aeeb9610af8315fb27bb0988fdabea6abfd3e070f672bd |
| Inradius TeX | 99d8e071359dde3b23f1524aa0025a97fb9683d8dfe34971c3244a73ceed2877 |
| Lean note | 1d32ef8fb31087b2069892f030f9c3a98905bfa6f219013f6c351804504fb1b7 |
| Guide tag input | 39ba79a6e9e718bd4c385fef865d94be0f1264b0f88eddaa034cb0eed9b00549 |
| Owner correspondence | 842f0f0541247e7041d20d93dc028e80c9049b6f118a931c6e50df150c8c8416 |

## Changes from mathematical text v1.22

| Source | v1.22 lines | v1.42 lines | Claim and scope | Lean evidence or attribution |
|---|---|---|---|---|
| companion_note.tex | 1–5 | 1–3 | Companion reference only. | Attachment and DOI |
| erdos_volume.tex | 1–17 | 1–17 | Title includes d=2 from cited Pólya; the tagged arbitrary-n Lean result begins at d=3. | `Paper.erdos_product_all_dim_given` |
| erdos_volume.tex | 18–40 | 18–40 | Main 26 states the weighted extension; 27–29 rejects the reported pair. Main 30–35 and the footnote qualify the Lean claim. | `Paper.erdos_product_all_dim_given` · `volume_capacity` · `Flux.direct_bound_eq` · `Paper.distinct_pair_strict_volume_given` · `Paper.distinct_pair_volume_by_slices` · `Paper.uniform_upper_given` · `sharp_coefficient` |
| erdos_volume.tex | 41–58 | 41–57 | Unit ball at one location; strict loss at multiple locations under six premises. Historical question is separate. | `Paper.coincident_solid` · `Paper.omega_three` · `Paper.erdos_product_all_dim_given` |
| erdos_volume.tex | 59–91 | 58–77 | Pólya gives the cited planar maximum. The capacity and flux proofs establish the weighted bound for d ≥ 3 under their respective analytic hypotheses. The strict two-mark comparison refutes the historical report in dimension three. | `Paper.erdos_product_all_dim_given` · `volume_capacity` · `Flux.direct_bound_eq` · `Paper.distinct_pair_strict_volume_given` · `Paper.distinct_pair_volume_by_slices` |
| erdos_volume.tex | 92–111 | 78–97 | General maximum and strictness in the table are conditional; the pictured separation 2.5 is a proved instance. | `Paper.erdos_product_given` · `Paper.distinct_pair_strict_volume_given` · `Paper.distinct_pair_volume_by_slices` · `Paper.figure_two_components` · `Paper.figure_lobe_balls` · `Paper.figure_volume_loss` |
| erdos_volume.tex | 112–123 | 98–133 | Axial and perpendicular rays use arbitrary midpoints and unit directions, including t=1. The full real-line calculation covers coincidence, the strictly increasing single-interval length up to t=1, the disjoint intervals at t>1, and the sharp bound with equality exactly at separation two. Pólya supplies the cited general planar result. | `Paper.pair_intercepts` · `Paper.two_marks_on_line` · `Paper.erdos_product_all_dim_given` · `Paper.pair_axis_reach` · `Paper.pair_transverse_reach` · `Paper.line_pair_interval` · `Paper.line_pair_two_intervals` · `Paper.line_pair_optimum` |
| erdos_volume.tex | 124–139 | 134–149 | The historical report concerns two marks in three dimensions. Strict volume loss refutes it. Ferudun addresses the separate covering question. | `Paper.coincident_solid` · `Paper.distinct_pair_strict_volume_given` · `Paper.distinct_pair_volume_by_slices` |
| erdos_volume.tex | 140–148 | 150–158 | Positive weights, total one, positive R. Ordinary-product set equals the threshold-one equal-weight region. | `Paper.erdos_product_all_dim_given` · `volume_capacity` · `Flux.direct_bound_eq` |
| erdos_volume.tex | 149–161 | 159–171 | Both weighted routes prove the bound and exact equality condition. Theorem environment SHA 7af608e9 is unchanged. | `volume_capacity` · `Flux.direct_bound_eq` · `Paper.erdos_product_given` |
| erdos_volume.tex | 162–173 | 172–181 | The ordinary-product corollary uses equal weights. The slice argument covers a pair in space. Both weighted proof routes apply for d ≥ 3. | `Paper.erdos_product_all_dim_given` · `volume_capacity` · `Flux.direct_bound_eq` · `Paper.distinct_pair_volume_by_slices` |
| erdos_volume.tex | 174–208 | 182–222 | Arbitrary-n closed Pólya result cited; two-mark argument takes the open unit premise and derives the closed every-positive-threshold bound, strict for distinct marks. Height endpoints have zero 3-D volume; quartic degree, fiber cardinality and area zero are independently proved. | `Paper.two_mark_slice_identity` · `Paper.pair_section_subset` · `Paper.pair_section_empty` · `Paper.pair_section_area` · `Paper.planar_scaled_closed` · `Paper.vertical_level_quartic` · `Paper.vertical_level_at_most_four` · `Paper.planar_pair_level_null` · `Paper.unit_ball_section_area` · `Paper.distinct_pair_volume_by_slices` |
| erdos_volume.tex | 209–222 | 223–237 | At t=5/4, fixed-s radial increase, axial intervals, joining paths and the excluded plane distinguish the two components. | `Paper.pair_axial_polynomial` · `Paper.transverse_strict` · `Paper.axial_interval` · `Paper.transverse_segment` · `Paper.joined_to_mark` · `Paper.missing_midplane` · `Paper.figure_two_components` |
| erdos_volume.tex | 223–234 | 238–251 | Infinite potential at the marks. The negative exponent reverses the comparison away from them. | `Flux.at_mark` · `Flux.off_formula` · `Flux.amgm` · `Flux.inclusion` · `Flux.strict_ball` · `Flux.strict_volume` |
| erdos_volume.tex | 235–249 | 252–269 | Level outward derivative is negative. Stored sphere shellFlux uses the outward-from-center normal, opposite the inward-pointing normal on an excised ball. Self term changes sign and other terms vanish. | `Flux.geometry` · `Flux.regular_frontier` · `Flux.smooth_harmonic` · `Flux.combine_marks` · `Flux.outer_derivative` · `Flux.shell_self` · `Flux.shell_other` · `Flux.flux_identity` |
| erdos_volume.tex | 250–275 | 270–304 | The Cauchy–Schwarz statement has both surface integrals in its type. The equal-volume radius to the power 2−d is absolutely continuous on every compact interval of strictly positive levels. Exhaustion controls the endpoint at zero. The order-two density estimate is due to Tang and Wang; the companion describes the point-charge approximation. | `Flux.critical_witness` · `Paper.analytic_partial_zero_set` · `Flux.null_sets` · `Flux.ae_regular` · `Flux.level_derivative` · `Flux.level_inequalities` · `Flux.scaled_derivative` · `Flux.exhaustion` · `Flux.integrated` · `Flux.radius_at_threshold` · `Flux.level_surface_cauchy_schwarz` · `Flux.scaled_radius_absolute_continuity` |
| erdos_volume.tex | 276–289 | 305–320 | Strict AM–GM along supporting ray, positive-volume missing ball, and exact coincident case. | `Flux.ray_dist` · `Flux.last_point` · `Flux.strict_amgm` · `Flux.beyond_last` · `Flux.strict_ball` · `Flux.strict_volume` · `Flux.coincident` · `Flux.direct_bound_eq` |
| erdos_volume.tex | 290–312 | 321–348 | Charge at unit potential explains capacity. The equilibrium moment bound, ball law and capacity normalization have different hypotheses. Outer infimum over bounded open neighborhoods yields the compact inequality. | `solid_compact_interior` · `solid_energy` · `Paper.ball_log_moment` · `Paper.integral_log_product` · `log_moment_sandwich` · `compact_isocapacity` · `Paper.compact_capacity_outer` |
| erdos_volume.tex | 313–327 | 349–365 | Positive weights force equality in every individual moment. Forward sphere inclusion and supporting-direction distance identity give coincidence; the reverse follows for a ball. | `Paper.each_moment_eq` · `capacity_sphere_consequence` · `Paper.equality_capacity_spheres` · `Paper.extreme_distance` · `sphere_rigidity` · `volume_capacity` |
| erdos_volume.tex | 328–377 | 366–442 (reader) | In d=3 the inradius infimum includes all compactly supported probabilities meeting the actual volume cutoff. Zero deficit forces a point mass. The radial integral is continuous and the intermediate value theorem supplies an equal pair at each sufficiently small prescribed deficit. The normalized loss of the nonempty, lower-bounded infimum tends to one. The higher-dimensional and planar statements are cited companion results. The three questions are open. The reader addendum removes only two trailing contact lines. | `Paper.erdos_product_all_dim_given` · `volume_capacity` · `Paper.distinct_pair_strict_volume_given` · `Paper.sharp_stability_given` · `pair_asymptotics` · `pair_ratio_limit` · `Paper.zero_deficit_rigidity` · `Paper.pair_hits_volume_deficit` · `Paper.discussion_sharp_infimum` |
| inradius.tex | 1–33 | 1–40 | General compact support, possible negative-infinite logarithm, finite atomic bridge, measurable bounded set, nonnegative deficit. The short paper proves the sharp inradius coefficient in dimension three and cites the expanded paper for the higher-dimensional estimate. | `Paper.general_log_bridge` · `trunc_log_continuous` · `atomic_g` · `measureSolid_regular` · `Paper.omega_three` · `stability_measure_volume` · `scale_identities` |
| inradius.tex | 34–45 | 41–52 | Theorem 2.1 asserts both right-hand limits at all R>0 with no uniform support-radius restriction. Nonempty and bounded sets of ratios matter in real sSup. Only one support-radius phrase changes from v1.22. | `Paper.sharp_stability_given` · `Paper.sup_nonempty` · `Paper.sup_bdd_given` · `sharp_coefficient` |
| inradius.tex | 46–57 | 53–64 | Positive cutoff h, common upper estimate and scaling of the threshold; higher dimensions cited. | `Paper.uniform_upper_given` · `sharp_coefficient` · `scale_identities` |
| inradius.tex | 58–91 | 65–104 | 3-D subfamily t<1/sqrt(2), both centered lower ball and center-independent cylinder obstruction; figure t=3/5. | `pair_squared_mean` · `pair_mem_iff` · `pair_squared_product` · `Paper.outside_cylinder_product_bounds` · `pair_ball_cylinder` · `cylinder_ball_radius` · `pair_inradius` · `Paper.figure_ball_cylinder` · `Paper.figure_pair_widths` |
| inradius.tex | 92–120 | 105–137 | The positive radial root, the uniform squared- and cubed-radius remainders and both angular means give the deficit expansions. The existing pair calculation is attributed in the manuscript; Figure 3 shows a positive-side limit. | `pair_radial` · `uniform_radial_error` · `pair_volume_fraction` · `axial_second_moment` · `pair_asymptotics` · `pair_ratio_limit` · `Paper.coalescent_deficits` · `pair_cubic_radial_mean` |
| inradius.tex | 121–142 | 138–169 | Attained minimum, coercivity and vanishing gradient; Jensen and the quotient identity give the ball at the true minimizer when J<log 2. | `stability_center` · `stability_center_ball` |
| inradius.tex | 143–165 | 170–203 | Both real upper-limit bounds carry eventual upper boundedness and the minimum cost tends to zero. The cost-minimizing center, the translating origin and the trial point perform different roles. | `Paper.sequence_cost_limsup` · `Paper.sequence_inradius_loss_limsup` · `stability_scalar_limits` · `stability_center_ball` · `Paper.original_trial_cost_chain` · `Paper.trial_cost_six` · `Paper.minimum_cost_tends_zero` |
| inradius.tex | 166–190 | 204–230 | Positive-deficit compact approximation has a strict exponential slack. General volume bound follows from arbitrary positive-volume compact pieces. At zero deficit, zero_deficit_rigidity uses compact subsets with an independent positive approximation tolerance. | `stability_compact_piece` · `stability_log_moment` · `stability_fubini` · `stability_piece_bounds` · `stability_compact_comparison` · `Paper.compact_piece_unit_bound` · `stability_measure_volume` |
| inradius.tex | 191–205 | 231–246 | Scaling law for Newton kernel includes poles; real-log distance identity is off the pole. Potential bound provides zero pole-mass for integrating. Translation direction and its inverse agree. | `stability_rescale_dist` · `stability_normalize` · `Paper.original_trial_cost_chain` |
| inradius.tex | 206–221 | 247–265 | Positivity and both coercive ends of phi, annular concentration, weak limits and identification of the uniform sphere law using its energy and uniqueness. | `stability_phi_shape` · `stability_phi_integral` · `stability_annulus_mass` · `stability_weak_limit` · `stability_sphere_limit` |
| inradius.tex | 222–246 | 266–296 | Jensen lower bound on the Laplacian, gap strict increase inside, sphere continuity including the integrable logarithm, and inversion outside. | `stability_spherical_radial` · `stability_radial_lap` · `stability_radial_gap` · `stability_sphere_H` |
| inradius.tex | 247–261 | 297–313 | Truncation and reciprocal-distance bounds are uniform under moving centers; liminf direction is lower, with the eventual bound interpretation. | `stability_truncation` · `Paper.discarded_log_chain` · `stability_moving_center` |
| inradius.tex | 262–279 | 314–335 | Fixed positive inner radius, compact annulus contradiction, far-field ratio 1/2 and simultaneous eventual exterior lower bound. | `stability_compact_gap` · `stability_exterior` |
| inradius.tex | 280–304 | 336–363 | Radial and tangential Hessian actions, shell boundary mass zero, limiting quadratic form I/3, then 1/2 from Taylor. The operator error is uniform on the ball at fixed δ before the limit in the index. | `Paper.journal_hessian_eigendirections` · `Paper.journal_shell_direction` · `stability_hessian_kernel` · `stability_annular_second_moment` · `stability_annular_curvature` |
| inradius.tex | 305–334 | 364–395 | One-sided segment derivative at the boundary minimizer, interior Taylor inequality, one-Lipschitz radial log, and matching center for the exterior away from zero. | `stability_trial_min` · `Paper.trial_inner_chain` · `stability_shift_loss` · `stability_join_at_center` · `stability_common_center` |
| inradius.tex | 335–350 | 396–412 | The original-coordinate trial integral gives the fixed-width quotient with positive denominator, the upper limit 2 for cost, and the inradius loss upper limit 1. For every positive cutoff the ratio set is nonempty and bounded above and its supremum is at least one. | `stability_unscale_cost` · `Paper.original_trial_cost_chain` · `Paper.fixed_delta_cost_limsup` · `Paper.sequence_cost_limsup` · `Paper.sequence_inradius_loss_limsup` · `Paper.sharp_stability_given` · `pair_ratio_limit` · `Paper.cutoff_sup_at_least_one` |
| lean_note.tex | 1–4 | 1–7 | Footnote 1.50 states conditional verification of the two numbered theorems and refers to the guide for the hypotheses. | Owner footnote 1.50 · 1d32ef8f |
| proof_guide_release.tex | 1–3 | 1–3 | The mathematical scope PDF and the name-only reader still cite the verified v1.22 guide. The author changes the tag input after the new private tag is verified. | Owner macro 39ba79a6 |

## References in Lean source comments

All 53 source comments now refer to the v1.42 mathematics. The removed summary bullets are mapped to the surviving abstract and inradius statements.

| Source | Following declaration | v1.22 text | v1.42 text |
|---|---|---|---|
| [ErdosVolume/Capacity.lean, line 55](ErdosVolume/Capacity.lean#L55) | `solid_compact_interior` | Main 294–297 | Main 328–332 |
| [ErdosVolume/Capacity.lean, line 255](ErdosVolume/Capacity.lean#L255) | `log_moment_sandwich` | Main 299–305 | Main 333–340 |
| [ErdosVolume/Capacity.lean, line 288](ErdosVolume/Capacity.lean#L288) | `sphere_rigidity` | Main 313–325 | Main 349–363 |
| [ErdosVolume/Sharpness.lean, line 89](ErdosVolume/Sharpness.lean#L89) | `measureSolid_regular` | Inradius 12–25 | Inradius 17–31 |
| [ErdosVolume/Sharpness.lean, line 266](ErdosVolume/Sharpness.lean#L266) | `pair_ball_cylinder` | Inradius 66–88 | Inradius 73–102 |
| [ErdosVolume/Sharpness.lean, line 327](ErdosVolume/Sharpness.lean#L327) | `pair_radial` | Inradius 94–102 | Inradius 105–124 |
| [ErdosVolume/Sharpness.lean, line 660](ErdosVolume/Sharpness.lean#L660) | `uniform_upper` | Main 86–89; Inradius 46–50 | Main 30–35; Inradius 53–57 |
| [ErdosVolume/Paper/Equality.lean, line 8](ErdosVolume/Paper/Equality.lean#L8) | `equality_capacity_spheres` | Main 313–318 | Main 349–355 |
| [ErdosVolume/Paper/VolumeDetails.lean, line 12](ErdosVolume/Paper/VolumeDetails.lean#L12) | `distinct_pair_strict_volume_given` | Main 75–76 | Main 72–73 |
| [ErdosVolume/Paper/VolumeDetails.lean, line 24](ErdosVolume/Paper/VolumeDetails.lean#L24) | `analytic_partial_zero_set` | Main 250–255 | Main 271–278 |
| [ErdosVolume/Paper/VolumeDetails.lean, line 46](ErdosVolume/Paper/VolumeDetails.lean#L46) | `outside_cylinder_product_bounds` | Inradius 70–78 | Inradius 79–91 |
| [ErdosVolume/Paper/Representation.lean, line 15](ErdosVolume/Paper/Representation.lean#L15) | `general_log_bridge` | Inradius 12–25 | Inradius 17–31 |
| [ErdosVolume/Paper/Statements.lean, line 19](ErdosVolume/Paper/Statements.lean#L19) | `coincident_solid` | Main 52–57, 285–287 | Main 49–55, 316–318 |
| [ErdosVolume/Paper/Statements.lean, line 37](ErdosVolume/Paper/Statements.lean#L37) | `ball_log_moment` | Main 296–301 | Main 328–335 |
| [ErdosVolume/Paper/Statements.lean, line 55](ErdosVolume/Paper/Statements.lean#L55) | `integral_log_product` | Main 299–305 | Main 333–340 |
| [ErdosVolume/Paper/Statements.lean, line 62](ErdosVolume/Paper/Statements.lean#L62) | `each_moment_eq` | Main 313–318 | Main 349–354 |
| [ErdosVolume/Paper/Statements.lean, line 67](ErdosVolume/Paper/Statements.lean#L67) | `extreme_distance` | Main 318–325 | Main 354–363 |
| [ErdosVolume/Paper/Statements.lean, line 86](ErdosVolume/Paper/Statements.lean#L86) | `omega_three` | Inradius 26–32 | Inradius 32–39 |
| [ErdosVolume/Paper/Statements.lean, line 123](ErdosVolume/Paper/Statements.lean#L123) | `first_order_radius` | Main 86–89 | Main 30–35 |
| [ErdosVolume/Stability.lean, line 243](ErdosVolume/Stability.lean#L243) | `stability_center` | Inradius 121–132 | Inradius 138–150 |
| [ErdosVolume/Stability.lean, line 321](ErdosVolume/Stability.lean#L321) | `stability_center_ball` | Inradius 129–142 | Inradius 146–166 |
| [ErdosVolume/Stability.lean, line 392](ErdosVolume/Stability.lean#L392) | `stability_scalar_limits` | Inradius 144–149 | Inradius 170–180 |
| [ErdosVolume/Stability.lean, line 428](ErdosVolume/Stability.lean#L428) | `stability_compact_piece` | Inradius 167–172 | Inradius 205–211 |
| [ErdosVolume/Stability.lean, line 456](ErdosVolume/Stability.lean#L456) | `stability_log_moment` | Inradius 171–177 | Inradius 210–214 |
| [ErdosVolume/Stability.lean, line 588](ErdosVolume/Stability.lean#L588) | `stability_fubini` | Inradius 174–180 | Inradius 212–219 |
| [ErdosVolume/Stability.lean, line 624](ErdosVolume/Stability.lean#L624) | `stability_piece_bounds` | Inradius 167–185 | Inradius 205–224 |
| [ErdosVolume/Stability.lean, line 658](ErdosVolume/Stability.lean#L658) | `stability_compact_comparison` | Inradius 181–189 | Inradius 219–229 |
| [ErdosVolume/Stability.lean, line 676](ErdosVolume/Stability.lean#L676) | `stability_measure_volume` | Inradius 186–189 | Inradius 225–229 |
| [ErdosVolume/Stability.lean, line 691](ErdosVolume/Stability.lean#L691) | `stability_rescale_dist` | Inradius 191–197 | Inradius 231–237 |
| [ErdosVolume/Stability.lean, line 712](ErdosVolume/Stability.lean#L712) | `stability_normalize` | Inradius 198–205 | Inradius 238–246 |
| [ErdosVolume/Stability.lean, line 780](ErdosVolume/Stability.lean#L780) | `stability_phi_shape` | Inradius 206–207 | Inradius 247–248 |
| [ErdosVolume/Stability.lean, line 814](ErdosVolume/Stability.lean#L814) | `stability_phi_integral` | Inradius 208–213 | Inradius 249–257 |
| [ErdosVolume/Stability.lean, line 829](ErdosVolume/Stability.lean#L829) | `stability_annulus_mass` | Inradius 212–214 | Inradius 254–258 |
| [ErdosVolume/Stability.lean, line 893](ErdosVolume/Stability.lean#L893) | `stability_weak_limit` | Inradius 214–217 | Inradius 258–261 |
| [ErdosVolume/Stability.lean, line 968](ErdosVolume/Stability.lean#L968) | `stability_sphere_limit` | Inradius 216–220 | Inradius 260–264 |
| [ErdosVolume/Stability.lean, line 1004](ErdosVolume/Stability.lean#L1004) | `stability_spherical_radial` | Inradius 227–231, 247–249 | Inradius 273–277, 297–299 |
| [ErdosVolume/Stability.lean, line 1184](ErdosVolume/Stability.lean#L1184) | `stability_radial_lap` | Inradius 229–238 | Inradius 273–288 |
| [ErdosVolume/Stability.lean, line 1347](ErdosVolume/Stability.lean#L1347) | `stability_radial_gap` | Inradius 229–240 | Inradius 273–290 |
| [ErdosVolume/Stability.lean, line 1433](ErdosVolume/Stability.lean#L1433) | `stability_sphere_H` | Inradius 227–231, 238–245 | Inradius 273–277, 287–295 |
| [ErdosVolume/Stability.lean, line 1481](ErdosVolume/Stability.lean#L1481) | `stability_truncation` | Inradius 247–260 | Inradius 297–312 |
| [ErdosVolume/Stability.lean, line 1526](ErdosVolume/Stability.lean#L1526) | `stability_moving_center` | Inradius 247–260 | Inradius 297–312 |
| [ErdosVolume/Stability.lean, line 1611](ErdosVolume/Stability.lean#L1611) | `stability_compact_gap` | Inradius 262–269 | Inradius 314–320 |
| [ErdosVolume/Stability.lean, line 1640](ErdosVolume/Stability.lean#L1640) | `stability_exterior` | Inradius 268–278 | Inradius 320–334 |
| [ErdosVolume/Stability.lean, line 1764](ErdosVolume/Stability.lean#L1764) | `stability_hessian_kernel` | Inradius 283–292 | Inradius 340–350 |
| [ErdosVolume/Stability.lean, line 1918](ErdosVolume/Stability.lean#L1918) | `stability_annular_second_moment` | Inradius 292–297 | Inradius 350–356 |
| [ErdosVolume/Stability.lean, line 2057](ErdosVolume/Stability.lean#L2057) | `stability_annular_curvature` | Inradius 280–303 | Inradius 336–362 |
| [ErdosVolume/Stability.lean, line 2123](ErdosVolume/Stability.lean#L2123) | `stability_trial_min` | Inradius 305–314 | Inradius 364–374 |
| [ErdosVolume/Stability.lean, line 2200](ErdosVolume/Stability.lean#L2200) | `stability_shift_loss` | Inradius 313–323 | Inradius 373–384 |
| [ErdosVolume/Stability.lean, line 2248](ErdosVolume/Stability.lean#L2248) | `stability_join_at_center` | Inradius 313–332 | Inradius 373–394 |
| [ErdosVolume/Stability.lean, line 2275](ErdosVolume/Stability.lean#L2275) | `stability_common_center` | Inradius 322–333 | Inradius 382–394 |
| [ErdosVolume/Stability.lean, line 2321](ErdosVolume/Stability.lean#L2321) | `stability_unscale_cost` | Inradius 335–343 | Inradius 396–403 |
| [ErdosVolume/Stability.lean, line 2372](ErdosVolume/Stability.lean#L2372) | `stability_cost_upper` | Inradius 144–149, 343–346 | Inradius 170–180, 404–410 |
| [ErdosVolume/Stability.lean, line 2445](ErdosVolume/Stability.lean#L2445) | `stability_uniform_upper` | Inradius 46–50, 346–350 | Inradius 53–57, 406–412 |

## Earlier mathematical text v1.22

Tag v1.22 preserves its own manuscript pins and previous comparisons in lean/JOURNAL_CROSSWALK.md.

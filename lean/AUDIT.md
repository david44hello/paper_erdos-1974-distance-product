# Lean theorem audit

5 OPEN, 117 PROVED, 40 PROVED GIVEN

Counts include public helper theorems. Each status applies to the full linked statement.
The source inventory and paper line map distinguish the printed claims from their supporting lemmas.

| Theorem | Status | Explicit analytic inputs |
|---|---|---|
| [ErdosVolume.solid_compact_interior](ErdosVolume/Capacity.lean#L56) | PROVED |  |
| [ErdosVolume.energy_bounds_of_radius_pos](ErdosVolume/Capacity.lean#L90) | PROVED |  |
| [ErdosVolume.solid_energy](ErdosVolume/Capacity.lean#L105) | PROVED GIVEN | ErdosVolume.BallCapacityFact |
| [ErdosVolume.dirichlet_outer](ErdosVolume/Capacity.lean#L125) | PROVED |  |
| [ErdosVolume.omega_positive](ErdosVolume/Capacity.lean#L178) | PROVED |  |
| [ErdosVolume.closedBall_volume](ErdosVolume/Capacity.lean#L181) | PROVED |  |
| [ErdosVolume.compact_isocapacity](ErdosVolume/Capacity.lean#L188) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.OpenIsoFact |
| [ErdosVolume.integral_log_G](ErdosVolume/Capacity.lean#L247) | PROVED |  |
| [ErdosVolume.log_moment_sandwich](ErdosVolume/Capacity.lean#L256) | PROVED GIVEN | ErdosVolume.EquilibriumMomentFact |
| [ErdosVolume.sphere_rigidity](ErdosVolume/Capacity.lean#L289) | PROVED |  |
| [ErdosVolume.weighted_equality](ErdosVolume/Capacity.lean#L320) | PROVED |  |
| [ErdosVolume.capacity_sphere_consequence](ErdosVolume/Capacity.lean#L333) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.volume_capacity](ErdosVolume/Capacity.lean#L359) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Flux.combine_marks](ErdosVolume/Flux.lean#L106) | PROVED |  |
| [ErdosVolume.Flux.at_mark](ErdosVolume/Flux.lean#L120) | PROVED |  |
| [ErdosVolume.Flux.off_formula](ErdosVolume/Flux.lean#L127) | PROVED |  |
| [ErdosVolume.Flux.amgm](ErdosVolume/Flux.lean#L135) | PROVED |  |
| [ErdosVolume.Flux.inclusion](ErdosVolume/Flux.lean#L141) | PROVED |  |
| [ErdosVolume.Flux.geometry](ErdosVolume/Flux.lean#L181) | PROVED |  |
| [ErdosVolume.Flux.regular_frontier](ErdosVolume/Flux.lean#L224) | PROVED |  |
| [ErdosVolume.Flux.smooth_harmonic](ErdosVolume/Flux.lean#L343) | PROVED |  |
| [ErdosVolume.Flux.critical_witness](ErdosVolume/Flux.lean#L357) | PROVED |  |
| [ErdosVolume.Flux.outer_derivative](ErdosVolume/Flux.lean#L373) | PROVED |  |
| [ErdosVolume.Flux.null_sets](ErdosVolume/Flux.lean#L383) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull |
| [ErdosVolume.Flux.ae_regular](ErdosVolume/Flux.lean#L403) | PROVED GIVEN | ErdosVolume.Flux.SardScalar |
| [ErdosVolume.Flux.shell_self](ErdosVolume/Flux.lean#L422) | PROVED GIVEN | ErdosVolume.Flux.SphereArea |
| [ErdosVolume.Flux.shell_other](ErdosVolume/Flux.lean#L451) | PROVED GIVEN | ErdosVolume.Flux.BallGauss |
| [ErdosVolume.Flux.flux_identity](ErdosVolume/Flux.lean#L506) | PROVED GIVEN | ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SphereArea |
| [ErdosVolume.Flux.level_derivative](ErdosVolume/Flux.lean#L549) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.CoareaSlabs |
| [ErdosVolume.Flux.level_inequalities](ErdosVolume/Flux.lean#L597) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.scaled_derivative](ErdosVolume/Flux.lean#L664) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.exhaustion](ErdosVolume/Flux.lean#L718) | PROVED |  |
| [ErdosVolume.Flux.integrated](ErdosVolume/Flux.lean#L745) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.radius_at_threshold](ErdosVolume/Flux.lean#L780) | PROVED |  |
| [ErdosVolume.Flux.ray_dist](ErdosVolume/Flux.lean#L787) | PROVED |  |
| [ErdosVolume.Flux.last_point](ErdosVolume/Flux.lean#L802) | PROVED |  |
| [ErdosVolume.Flux.strict_amgm](ErdosVolume/Flux.lean#L839) | PROVED |  |
| [ErdosVolume.Flux.beyond_last](ErdosVolume/Flux.lean#L852) | PROVED |  |
| [ErdosVolume.Flux.strict_ball](ErdosVolume/Flux.lean#L873) | PROVED |  |
| [ErdosVolume.Flux.strict_volume](ErdosVolume/Flux.lean#L889) | PROVED |  |
| [ErdosVolume.Flux.coincident](ErdosVolume/Flux.lean#L907) | PROVED |  |
| [ErdosVolume.Flux.direct_bound_eq](ErdosVolume/Flux.lean#L919) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Paper.equilibrium_exists_for_stability](ErdosVolume/Paper/Conditional.lean#L13) | PROVED GIVEN | ErdosVolume.EquilibriumExistence |
| [ErdosVolume.Paper.compact_iso_for_stability](ErdosVolume/Paper/Conditional.lean#L24) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.uniform_upper_given](ErdosVolume/Paper/Conditional.lean#L28) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.sharp_stability_given](ErdosVolume/Paper/Conditional.lean#L36) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.equality_capacity_spheres](ErdosVolume/Paper/Equality.lean#L10) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.pair_axial_polynomial](ErdosVolume/Paper/Illustrations.lean#L13) | PROVED |  |
| [ErdosVolume.Paper.transverse_strict](ErdosVolume/Paper/Illustrations.lean#L24) | PROVED |  |
| [ErdosVolume.Paper.axial_interval](ErdosVolume/Paper/Illustrations.lean#L36) | PROVED |  |
| [ErdosVolume.Paper.transverse_segment](ErdosVolume/Paper/Illustrations.lean#L57) | PROVED |  |
| [ErdosVolume.Paper.missing_midplane](ErdosVolume/Paper/Illustrations.lean#L73) | PROVED |  |
| [ErdosVolume.Paper.joined_to_mark](ErdosVolume/Paper/Illustrations.lean#L104) | PROVED |  |
| [ErdosVolume.Paper.figure_two_components](ErdosVolume/Paper/Illustrations.lean#L119) | PROVED |  |
| [ErdosVolume.Paper.figure_lobe_balls](ErdosVolume/Paper/Illustrations.lean#L153) | PROVED |  |
| [ErdosVolume.Paper.figure_volume_loss](ErdosVolume/Paper/Illustrations.lean#L179) | PROVED |  |
| [ErdosVolume.Paper.figure_ball_cylinder](ErdosVolume/Paper/Illustrations.lean#L193) | PROVED |  |
| [ErdosVolume.Paper.coalescent_deficits](ErdosVolume/Paper/Illustrations.lean#L205) | PROVED |  |
| [ErdosVolume.Paper.journal_hessian_eigendirections](ErdosVolume/Paper/JournalHessian.lean#L64) | PROVED |  |
| [ErdosVolume.Paper.journal_shell_direction](ErdosVolume/Paper/JournalHessian.lean#L112) | PROVED |  |
| [ErdosVolume.Paper.general_log_bridge](ErdosVolume/Paper/Representation.lean#L16) | PROVED |  |
| [ErdosVolume.Paper.pair_squared_mean](ErdosVolume/Paper/Representation.lean#L94) | PROVED |  |
| [ErdosVolume.Paper.pair_outside_cylinder](ErdosVolume/Paper/Representation.lean#L98) | PROVED |  |
| [ErdosVolume.Paper.sup_nonempty](ErdosVolume/Paper/Representation.lean#L103) | PROVED |  |
| [ErdosVolume.Paper.sup_bdd_given](ErdosVolume/Paper/Representation.lean#L109) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.sequence_inradius_loss_limsup](ErdosVolume/Paper/StabilityLimits.lean#L32) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.fixed_delta_cost_limsup](ErdosVolume/Paper/StabilityLimits.lean#L96) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.finite_volume](ErdosVolume/Paper/Statements.lean#L14) | OPEN |  |
| [ErdosVolume.Paper.coincident_solid](ErdosVolume/Paper/Statements.lean#L20) | PROVED |  |
| [ErdosVolume.Paper.ball_log_moment](ErdosVolume/Paper/Statements.lean#L38) | PROVED GIVEN | ErdosVolume.Paper.EquilibriumBallLaw |
| [ErdosVolume.Paper.integral_log_product](ErdosVolume/Paper/Statements.lean#L56) | PROVED |  |
| [ErdosVolume.Paper.each_moment_eq](ErdosVolume/Paper/Statements.lean#L63) | PROVED |  |
| [ErdosVolume.Paper.extreme_distance](ErdosVolume/Paper/Statements.lean#L68) | PROVED |  |
| [ErdosVolume.Paper.compact_capacity_outer](ErdosVolume/Paper/Statements.lean#L82) | PROVED |  |
| [ErdosVolume.Paper.omega_three](ErdosVolume/Paper/Statements.lean#L87) | PROVED |  |
| [ErdosVolume.Paper.erdos_product](ErdosVolume/Paper/Statements.lean#L104) | OPEN |  |
| [ErdosVolume.Paper.erdos_product_given](ErdosVolume/Paper/Statements.lean#L112) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.first_order_radius](ErdosVolume/Paper/Statements.lean#L125) | OPEN |  |
| [ErdosVolume.Paper.sequence_cost_limsup](ErdosVolume/Paper/TrialCost.lean#L11) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.discarded_log_chain](ErdosVolume/Paper/TrialCost.lean#L39) | PROVED |  |
| [ErdosVolume.Paper.compact_piece_unit_bound](ErdosVolume/Paper/TrialCost.lean#L56) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.trial_inner_chain](ErdosVolume/Paper/TrialCost.lean#L67) | PROVED |  |
| [ErdosVolume.Paper.original_trial_cost_chain](ErdosVolume/Paper/TrialCost.lean#L87) | PROVED |  |
| [ErdosVolume.Paper.trial_cost_six](ErdosVolume/Paper/TrialCost.lean#L129) | PROVED |  |
| [ErdosVolume.Paper.two_marks_on_line](ErdosVolume/Paper/TwoMarkSlices.lean#L12) | PROVED |  |
| [ErdosVolume.Paper.pair_intercepts](ErdosVolume/Paper/TwoMarkSlices.lean#L42) | PROVED |  |
| [ErdosVolume.Paper.figure_pair_widths](ErdosVolume/Paper/TwoMarkSlices.lean#L81) | PROVED |  |
| [ErdosVolume.Paper.planar_coincident_disk](ErdosVolume/Paper/TwoMarkSlices.lean#L114) | PROVED |  |
| [ErdosVolume.Paper.vertical_level_quartic](ErdosVolume/Paper/TwoMarkSlices.lean#L131) | PROVED |  |
| [ErdosVolume.Paper.vertical_level_at_most_four](ErdosVolume/Paper/TwoMarkSlices.lean#L146) | PROVED |  |
| [ErdosVolume.Paper.planar_pair_level_null](ErdosVolume/Paper/TwoMarkSlices.lean#L166) | PROVED |  |
| [ErdosVolume.Paper.planar_scaled_closed](ErdosVolume/Paper/TwoMarkSlices.lean#L182) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.two_mark_slice_identity](ErdosVolume/Paper/TwoMarkSlices.lean#L227) | PROVED |  |
| [ErdosVolume.Paper.pair_section_subset](ErdosVolume/Paper/TwoMarkSlices.lean#L234) | PROVED |  |
| [ErdosVolume.Paper.pair_section_empty](ErdosVolume/Paper/TwoMarkSlices.lean#L244) | PROVED |  |
| [ErdosVolume.Paper.pair_section_area](ErdosVolume/Paper/TwoMarkSlices.lean#L253) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.unit_ball_section_area](ErdosVolume/Paper/TwoMarkSlices.lean#L280) | PROVED |  |
| [ErdosVolume.Paper.spatial_pair_section](ErdosVolume/Paper/TwoMarkSlices.lean#L301) | PROVED |  |
| [ErdosVolume.Paper.spatial_ball_section](ErdosVolume/Paper/TwoMarkSlices.lean#L307) | PROVED |  |
| [ErdosVolume.Paper.distinct_pair_volume_by_slices](ErdosVolume/Paper/TwoMarkSlices.lean#L356) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.erdos_product_all_dim_given](ErdosVolume/Paper/TwoMarkSlices.lean#L401) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.distinct_pair_strict_volume_given](ErdosVolume/Paper/VolumeDetails.lean#L13) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.analytic_partial_zero_set](ErdosVolume/Paper/VolumeDetails.lean#L26) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull |
| [ErdosVolume.Paper.outside_cylinder_product_bounds](ErdosVolume/Paper/VolumeDetails.lean#L48) | PROVED |  |
| [ErdosVolume.atomic_g](ErdosVolume/Sharpness.lean#L29) | PROVED |  |
| [ErdosVolume.trunc_log_continuous](ErdosVolume/Sharpness.lean#L62) | PROVED |  |
| [ErdosVolume.measureSolid_regular](ErdosVolume/Sharpness.lean#L90) | PROVED |  |
| [ErdosVolume.dilated_g](ErdosVolume/Sharpness.lean#L146) | PROVED |  |
| [ErdosVolume.scale_identities](ErdosVolume/Sharpness.lean#L196) | PROVED |  |
| [ErdosVolume.axis_dist_sq](ErdosVolume/Sharpness.lean#L225) | PROVED |  |
| [ErdosVolume.pair_squared_product](ErdosVolume/Sharpness.lean#L231) | PROVED |  |
| [ErdosVolume.pair_mem_iff](ErdosVolume/Sharpness.lean#L237) | PROVED |  |
| [ErdosVolume.pair_squared_mean](ErdosVolume/Sharpness.lean#L247) | PROVED |  |
| [ErdosVolume.pair_outside_cylinder](ErdosVolume/Sharpness.lean#L253) | PROVED |  |
| [ErdosVolume.pair_ball_cylinder](ErdosVolume/Sharpness.lean#L267) | PROVED |  |
| [ErdosVolume.cylinder_ball_radius](ErdosVolume/Sharpness.lean#L291) | PROVED |  |
| [ErdosVolume.pair_inradius](ErdosVolume/Sharpness.lean#L311) | PROVED |  |
| [ErdosVolume.pair_radial](ErdosVolume/Sharpness.lean#L328) | PROVED |  |
| [ErdosVolume.uniform_radial_error](ErdosVolume/Sharpness.lean#L375) | PROVED |  |
| [ErdosVolume.axial_second_moment](ErdosVolume/Sharpness.lean#L445) | PROVED |  |
| [ErdosVolume.pair_volume_fraction](ErdosVolume/Sharpness.lean#L485) | PROVED |  |
| [ErdosVolume.pair_asymptotics](ErdosVolume/Sharpness.lean#L576) | PROVED |  |
| [ErdosVolume.pair_ratio_limit](ErdosVolume/Sharpness.lean#L632) | PROVED |  |
| [ErdosVolume.uniform_upper](ErdosVolume/Sharpness.lean#L661) | OPEN |  |
| [ErdosVolume.sharp_coefficient](ErdosVolume/Sharpness.lean#L686) | PROVED |  |
| [ErdosVolume.worst_ratio_limit](ErdosVolume/Sharpness.lean#L716) | PROVED |  |
| [ErdosVolume.sharp_stability](ErdosVolume/Sharpness.lean#L744) | OPEN |  |
| [ErdosVolume.stability_center](ErdosVolume/Stability.lean#L244) | PROVED |  |
| [ErdosVolume.stability_center_ball](ErdosVolume/Stability.lean#L322) | PROVED |  |
| [ErdosVolume.stability_scalar_limits](ErdosVolume/Stability.lean#L393) | PROVED |  |
| [ErdosVolume.stability_compact_piece](ErdosVolume/Stability.lean#L429) | PROVED |  |
| [ErdosVolume.stability_log_moment](ErdosVolume/Stability.lean#L457) | PROVED |  |
| [ErdosVolume.stability_fubini](ErdosVolume/Stability.lean#L589) | PROVED |  |
| [ErdosVolume.stability_piece_bounds](ErdosVolume/Stability.lean#L625) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_compact_comparison](ErdosVolume/Stability.lean#L659) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_measure_volume](ErdosVolume/Stability.lean#L677) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_rescale_dist](ErdosVolume/Stability.lean#L692) | PROVED |  |
| [ErdosVolume.stability_normalize](ErdosVolume/Stability.lean#L713) | PROVED |  |
| [ErdosVolume.stability_phi_shape](ErdosVolume/Stability.lean#L781) | PROVED |  |
| [ErdosVolume.stability_phi_integral](ErdosVolume/Stability.lean#L815) | PROVED |  |
| [ErdosVolume.stability_annulus_mass](ErdosVolume/Stability.lean#L830) | PROVED |  |
| [ErdosVolume.stability_weak_limit](ErdosVolume/Stability.lean#L894) | PROVED |  |
| [ErdosVolume.stability_sphere_limit](ErdosVolume/Stability.lean#L969) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique |
| [ErdosVolume.stability_spherical_radial](ErdosVolume/Stability.lean#L1005) | PROVED |  |
| [ErdosVolume.stability_radial_lap](ErdosVolume/Stability.lean#L1185) | PROVED |  |
| [ErdosVolume.stability_radial_gap](ErdosVolume/Stability.lean#L1348) | PROVED |  |
| [ErdosVolume.stability_sphere_H](ErdosVolume/Stability.lean#L1434) | PROVED |  |
| [ErdosVolume.stability_truncation](ErdosVolume/Stability.lean#L1482) | PROVED |  |
| [ErdosVolume.stability_moving_center](ErdosVolume/Stability.lean#L1527) | PROVED |  |
| [ErdosVolume.stability_compact_gap](ErdosVolume/Stability.lean#L1612) | PROVED |  |
| [ErdosVolume.stability_exterior](ErdosVolume/Stability.lean#L1641) | PROVED |  |
| [ErdosVolume.stability_hessian_kernel](ErdosVolume/Stability.lean#L1765) | PROVED |  |
| [ErdosVolume.stability_annular_second_moment](ErdosVolume/Stability.lean#L1919) | PROVED |  |
| [ErdosVolume.stability_annular_curvature](ErdosVolume/Stability.lean#L2058) | PROVED |  |
| [ErdosVolume.stability_trial_min](ErdosVolume/Stability.lean#L2124) | PROVED |  |
| [ErdosVolume.stability_shift_loss](ErdosVolume/Stability.lean#L2201) | PROVED |  |
| [ErdosVolume.stability_join_at_center](ErdosVolume/Stability.lean#L2249) | PROVED |  |
| [ErdosVolume.stability_common_center](ErdosVolume/Stability.lean#L2276) | PROVED |  |
| [ErdosVolume.stability_unscale_cost](ErdosVolume/Stability.lean#L2322) | PROVED |  |
| [ErdosVolume.stability_cost_upper](ErdosVolume/Stability.lean#L2373) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_uniform_upper](ErdosVolume/Stability.lean#L2446) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_normalized_example](ErdosVolume/Stability.lean#L2504) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.Frostman |

# Lean theorem audit

5 OPEN, 130 PROVED, 46 PROVED GIVEN

Counts include public helper theorems. Each status applies to the full linked statement.
The source inventory and paper line map distinguish the printed claims from their supporting lemmas.

| Theorem | Status | Explicit analytic inputs |
|---|---|---|
| [ErdosVolume.solid_compact_interior](ErdosVolume/Capacity.lean#L67) | PROVED |  |
| [ErdosVolume.energy_bounds_of_radius_pos](ErdosVolume/Capacity.lean#L101) | PROVED |  |
| [ErdosVolume.solid_energy](ErdosVolume/Capacity.lean#L116) | PROVED GIVEN | ErdosVolume.BallCapacityFact |
| [ErdosVolume.dirichlet_outer](ErdosVolume/Capacity.lean#L136) | PROVED |  |
| [ErdosVolume.omega_positive](ErdosVolume/Capacity.lean#L189) | PROVED |  |
| [ErdosVolume.closedBall_volume](ErdosVolume/Capacity.lean#L192) | PROVED |  |
| [ErdosVolume.compact_isocapacity](ErdosVolume/Capacity.lean#L199) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.OpenIsoFact |
| [ErdosVolume.integral_log_G](ErdosVolume/Capacity.lean#L258) | PROVED |  |
| [ErdosVolume.log_moment_sandwich](ErdosVolume/Capacity.lean#L267) | PROVED GIVEN | ErdosVolume.EquilibriumMomentFact |
| [ErdosVolume.sphere_rigidity](ErdosVolume/Capacity.lean#L300) | PROVED |  |
| [ErdosVolume.weighted_equality](ErdosVolume/Capacity.lean#L331) | PROVED |  |
| [ErdosVolume.capacity_sphere_consequence](ErdosVolume/Capacity.lean#L344) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.volume_capacity](ErdosVolume/Capacity.lean#L370) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.CoordinateFacts.finiteCoordinates](ErdosVolume/Defs.lean#L13) | PROVED |  |
| [ErdosVolume.CoordinateFacts.borelCoordinates](ErdosVolume/Defs.lean#L16) | PROVED |  |
| [ErdosVolume.CoordinateFacts.ennrealScalarTower](ErdosVolume/Defs.lean#L19) | PROVED |  |
| [ErdosVolume.CoordinateFacts.twoAtLeastTwo](ErdosVolume/Defs.lean#L27) | PROVED |  |
| [ErdosVolume.CoordinateFacts.finiteThree](ErdosVolume/Defs.lean#L30) | PROVED |  |
| [ErdosVolume.CoordinateFacts.borelThree](ErdosVolume/Defs.lean#L33) | PROVED |  |
| [ErdosVolume.Flux.combine_marks](ErdosVolume/Flux.lean#L119) | PROVED |  |
| [ErdosVolume.Flux.at_mark](ErdosVolume/Flux.lean#L133) | PROVED |  |
| [ErdosVolume.Flux.off_formula](ErdosVolume/Flux.lean#L140) | PROVED |  |
| [ErdosVolume.Flux.amgm](ErdosVolume/Flux.lean#L148) | PROVED |  |
| [ErdosVolume.Flux.inclusion](ErdosVolume/Flux.lean#L154) | PROVED |  |
| [ErdosVolume.Flux.geometry](ErdosVolume/Flux.lean#L194) | PROVED |  |
| [ErdosVolume.Flux.regular_frontier](ErdosVolume/Flux.lean#L237) | PROVED |  |
| [ErdosVolume.Flux.smooth_harmonic](ErdosVolume/Flux.lean#L356) | PROVED |  |
| [ErdosVolume.Flux.critical_witness](ErdosVolume/Flux.lean#L370) | PROVED |  |
| [ErdosVolume.Flux.outer_derivative](ErdosVolume/Flux.lean#L386) | PROVED |  |
| [ErdosVolume.Flux.null_sets](ErdosVolume/Flux.lean#L396) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull |
| [ErdosVolume.Flux.ae_regular](ErdosVolume/Flux.lean#L416) | PROVED GIVEN | ErdosVolume.Flux.SardScalar |
| [ErdosVolume.Flux.shell_self](ErdosVolume/Flux.lean#L435) | PROVED GIVEN | ErdosVolume.Flux.SphereArea |
| [ErdosVolume.Flux.shell_other](ErdosVolume/Flux.lean#L464) | PROVED GIVEN | ErdosVolume.Flux.BallGauss |
| [ErdosVolume.Flux.flux_identity](ErdosVolume/Flux.lean#L519) | PROVED GIVEN | ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SphereArea |
| [ErdosVolume.Flux.level_derivative](ErdosVolume/Flux.lean#L562) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.CoareaSlabs |
| [ErdosVolume.Flux.level_inequalities](ErdosVolume/Flux.lean#L610) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.scaled_derivative](ErdosVolume/Flux.lean#L677) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.exhaustion](ErdosVolume/Flux.lean#L731) | PROVED |  |
| [ErdosVolume.Flux.integrated](ErdosVolume/Flux.lean#L758) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.radius_at_threshold](ErdosVolume/Flux.lean#L793) | PROVED |  |
| [ErdosVolume.Flux.ray_dist](ErdosVolume/Flux.lean#L800) | PROVED |  |
| [ErdosVolume.Flux.last_point](ErdosVolume/Flux.lean#L815) | PROVED |  |
| [ErdosVolume.Flux.strict_amgm](ErdosVolume/Flux.lean#L852) | PROVED |  |
| [ErdosVolume.Flux.beyond_last](ErdosVolume/Flux.lean#L865) | PROVED |  |
| [ErdosVolume.Flux.strict_ball](ErdosVolume/Flux.lean#L886) | PROVED |  |
| [ErdosVolume.Flux.strict_volume](ErdosVolume/Flux.lean#L902) | PROVED |  |
| [ErdosVolume.Flux.coincident](ErdosVolume/Flux.lean#L920) | PROVED |  |
| [ErdosVolume.Flux.direct_bound_eq](ErdosVolume/Flux.lean#L932) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Flux.scaled_radius_absolute_continuity](ErdosVolume/Flux.lean#L961) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.CoareaSlabs |
| [ErdosVolume.Flux.level_surface_cauchy_schwarz](ErdosVolume/Flux.lean#L977) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull, ErdosVolume.Flux.BallGauss, ErdosVolume.Flux.CoareaSlabs, ErdosVolume.Flux.PuncturedGauss, ErdosVolume.Flux.SardScalar, ErdosVolume.Flux.SharpIso, ErdosVolume.Flux.SphereArea, ErdosVolume.Flux.SurfaceFinite |
| [ErdosVolume.Paper.equilibrium_exists_for_stability](ErdosVolume/Paper/Conditional.lean#L17) | PROVED GIVEN | ErdosVolume.EquilibriumExistence |
| [ErdosVolume.Paper.compact_iso_for_stability](ErdosVolume/Paper/Conditional.lean#L28) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.uniform_upper_given](ErdosVolume/Paper/Conditional.lean#L32) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.sharp_stability_given](ErdosVolume/Paper/Conditional.lean#L40) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.zero_deficit_rigidity](ErdosVolume/Paper/Discussion.lean#L82) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.pair_hits_volume_deficit](ErdosVolume/Paper/Discussion.lean#L161) | PROVED |  |
| [ErdosVolume.Paper.discussion_sharp_infimum](ErdosVolume/Paper/Discussion.lean#L212) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.minimum_cost_tends_zero](ErdosVolume/Paper/Discussion.lean#L261) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.cutoff_sup_at_least_one](ErdosVolume/Paper/Discussion.lean#L279) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.equality_capacity_spheres](ErdosVolume/Paper/Equality.lean#L14) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.pair_axial_polynomial](ErdosVolume/Paper/Illustrations.lean#L17) | PROVED |  |
| [ErdosVolume.Paper.transverse_strict](ErdosVolume/Paper/Illustrations.lean#L28) | PROVED |  |
| [ErdosVolume.Paper.axial_interval](ErdosVolume/Paper/Illustrations.lean#L40) | PROVED |  |
| [ErdosVolume.Paper.transverse_segment](ErdosVolume/Paper/Illustrations.lean#L61) | PROVED |  |
| [ErdosVolume.Paper.missing_midplane](ErdosVolume/Paper/Illustrations.lean#L77) | PROVED |  |
| [ErdosVolume.Paper.joined_to_mark](ErdosVolume/Paper/Illustrations.lean#L108) | PROVED |  |
| [ErdosVolume.Paper.figure_two_components](ErdosVolume/Paper/Illustrations.lean#L123) | PROVED |  |
| [ErdosVolume.Paper.figure_lobe_balls](ErdosVolume/Paper/Illustrations.lean#L157) | PROVED |  |
| [ErdosVolume.Paper.figure_volume_loss](ErdosVolume/Paper/Illustrations.lean#L183) | PROVED |  |
| [ErdosVolume.Paper.figure_ball_cylinder](ErdosVolume/Paper/Illustrations.lean#L197) | PROVED |  |
| [ErdosVolume.Paper.coalescent_deficits](ErdosVolume/Paper/Illustrations.lean#L209) | PROVED |  |
| [ErdosVolume.Paper.journal_hessian_eigendirections](ErdosVolume/Paper/JournalHessian.lean#L68) | PROVED |  |
| [ErdosVolume.Paper.journal_shell_direction](ErdosVolume/Paper/JournalHessian.lean#L116) | PROVED |  |
| [ErdosVolume.Paper.pair_axis_reach](ErdosVolume/Paper/PairGeometry.lean#L27) | PROVED |  |
| [ErdosVolume.Paper.pair_transverse_reach](ErdosVolume/Paper/PairGeometry.lean#L49) | PROVED |  |
| [ErdosVolume.Paper.line_pair_interval](ErdosVolume/Paper/PairGeometry.lean#L85) | PROVED |  |
| [ErdosVolume.Paper.line_pair_two_intervals](ErdosVolume/Paper/PairGeometry.lean#L105) | PROVED |  |
| [ErdosVolume.Paper.line_pair_optimum](ErdosVolume/Paper/PairGeometry.lean#L148) | PROVED |  |
| [ErdosVolume.Paper.general_log_bridge](ErdosVolume/Paper/Representation.lean#L20) | PROVED |  |
| [ErdosVolume.Paper.pair_squared_mean](ErdosVolume/Paper/Representation.lean#L98) | PROVED |  |
| [ErdosVolume.Paper.pair_outside_cylinder](ErdosVolume/Paper/Representation.lean#L102) | PROVED |  |
| [ErdosVolume.Paper.sup_nonempty](ErdosVolume/Paper/Representation.lean#L107) | PROVED |  |
| [ErdosVolume.Paper.sup_bdd_given](ErdosVolume/Paper/Representation.lean#L113) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.sequence_inradius_loss_limsup](ErdosVolume/Paper/StabilityLimits.lean#L36) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.fixed_delta_cost_limsup](ErdosVolume/Paper/StabilityLimits.lean#L100) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.finite_volume](ErdosVolume/Paper/Statements.lean#L18) | OPEN |  |
| [ErdosVolume.Paper.coincident_solid](ErdosVolume/Paper/Statements.lean#L24) | PROVED |  |
| [ErdosVolume.Paper.ball_log_moment](ErdosVolume/Paper/Statements.lean#L42) | PROVED GIVEN | ErdosVolume.Paper.EquilibriumBallLaw |
| [ErdosVolume.Paper.integral_log_product](ErdosVolume/Paper/Statements.lean#L60) | PROVED |  |
| [ErdosVolume.Paper.each_moment_eq](ErdosVolume/Paper/Statements.lean#L67) | PROVED |  |
| [ErdosVolume.Paper.extreme_distance](ErdosVolume/Paper/Statements.lean#L72) | PROVED |  |
| [ErdosVolume.Paper.compact_capacity_outer](ErdosVolume/Paper/Statements.lean#L86) | PROVED |  |
| [ErdosVolume.Paper.omega_three](ErdosVolume/Paper/Statements.lean#L91) | PROVED |  |
| [ErdosVolume.Paper.erdos_product](ErdosVolume/Paper/Statements.lean#L108) | OPEN |  |
| [ErdosVolume.Paper.erdos_product_given](ErdosVolume/Paper/Statements.lean#L116) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.first_order_radius](ErdosVolume/Paper/Statements.lean#L129) | OPEN |  |
| [ErdosVolume.Paper.sequence_cost_limsup](ErdosVolume/Paper/TrialCost.lean#L15) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.OpenIsoFact, ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.discarded_log_chain](ErdosVolume/Paper/TrialCost.lean#L43) | PROVED |  |
| [ErdosVolume.Paper.compact_piece_unit_bound](ErdosVolume/Paper/TrialCost.lean#L60) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.Paper.trial_inner_chain](ErdosVolume/Paper/TrialCost.lean#L71) | PROVED |  |
| [ErdosVolume.Paper.original_trial_cost_chain](ErdosVolume/Paper/TrialCost.lean#L91) | PROVED |  |
| [ErdosVolume.Paper.trial_cost_six](ErdosVolume/Paper/TrialCost.lean#L133) | PROVED |  |
| [ErdosVolume.Paper.two_marks_on_line](ErdosVolume/Paper/TwoMarkSlices.lean#L16) | PROVED |  |
| [ErdosVolume.Paper.pair_intercepts](ErdosVolume/Paper/TwoMarkSlices.lean#L46) | PROVED |  |
| [ErdosVolume.Paper.figure_pair_widths](ErdosVolume/Paper/TwoMarkSlices.lean#L85) | PROVED |  |
| [ErdosVolume.Paper.planar_coincident_disk](ErdosVolume/Paper/TwoMarkSlices.lean#L118) | PROVED |  |
| [ErdosVolume.Paper.vertical_level_quartic](ErdosVolume/Paper/TwoMarkSlices.lean#L135) | PROVED |  |
| [ErdosVolume.Paper.vertical_level_at_most_four](ErdosVolume/Paper/TwoMarkSlices.lean#L150) | PROVED |  |
| [ErdosVolume.Paper.planar_pair_level_null](ErdosVolume/Paper/TwoMarkSlices.lean#L170) | PROVED |  |
| [ErdosVolume.Paper.planar_scaled_closed](ErdosVolume/Paper/TwoMarkSlices.lean#L186) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.two_mark_slice_identity](ErdosVolume/Paper/TwoMarkSlices.lean#L231) | PROVED |  |
| [ErdosVolume.Paper.pair_section_subset](ErdosVolume/Paper/TwoMarkSlices.lean#L238) | PROVED |  |
| [ErdosVolume.Paper.pair_section_empty](ErdosVolume/Paper/TwoMarkSlices.lean#L248) | PROVED |  |
| [ErdosVolume.Paper.pair_section_area](ErdosVolume/Paper/TwoMarkSlices.lean#L257) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.unit_ball_section_area](ErdosVolume/Paper/TwoMarkSlices.lean#L284) | PROVED |  |
| [ErdosVolume.Paper.spatial_pair_section](ErdosVolume/Paper/TwoMarkSlices.lean#L305) | PROVED |  |
| [ErdosVolume.Paper.spatial_ball_section](ErdosVolume/Paper/TwoMarkSlices.lean#L311) | PROVED |  |
| [ErdosVolume.Paper.distinct_pair_volume_by_slices](ErdosVolume/Paper/TwoMarkSlices.lean#L360) | PROVED GIVEN | ErdosVolume.Paper.PlanarTwoMarkBound |
| [ErdosVolume.Paper.erdos_product_all_dim_given](ErdosVolume/Paper/TwoMarkSlices.lean#L405) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.distinct_pair_strict_volume_given](ErdosVolume/Paper/VolumeDetails.lean#L17) | PROVED GIVEN | ErdosVolume.BallCapacityFact, ErdosVolume.CapacityNormalization, ErdosVolume.EquilibriumExistence, ErdosVolume.EquilibriumMomentFact, ErdosVolume.EquilibriumSphereFact, ErdosVolume.OpenIsoFact |
| [ErdosVolume.Paper.analytic_partial_zero_set](ErdosVolume/Paper/VolumeDetails.lean#L30) | PROVED GIVEN | ErdosVolume.Flux.AnalyticNull |
| [ErdosVolume.Paper.outside_cylinder_product_bounds](ErdosVolume/Paper/VolumeDetails.lean#L52) | PROVED |  |
| [ErdosVolume.atomic_g](ErdosVolume/Sharpness.lean#L40) | PROVED |  |
| [ErdosVolume.trunc_log_continuous](ErdosVolume/Sharpness.lean#L73) | PROVED |  |
| [ErdosVolume.measureSolid_regular](ErdosVolume/Sharpness.lean#L101) | PROVED |  |
| [ErdosVolume.dilated_g](ErdosVolume/Sharpness.lean#L157) | PROVED |  |
| [ErdosVolume.scale_identities](ErdosVolume/Sharpness.lean#L207) | PROVED |  |
| [ErdosVolume.axis_dist_sq](ErdosVolume/Sharpness.lean#L236) | PROVED |  |
| [ErdosVolume.pair_squared_product](ErdosVolume/Sharpness.lean#L242) | PROVED |  |
| [ErdosVolume.pair_mem_iff](ErdosVolume/Sharpness.lean#L248) | PROVED |  |
| [ErdosVolume.pair_squared_mean](ErdosVolume/Sharpness.lean#L258) | PROVED |  |
| [ErdosVolume.pair_outside_cylinder](ErdosVolume/Sharpness.lean#L264) | PROVED |  |
| [ErdosVolume.pair_ball_cylinder](ErdosVolume/Sharpness.lean#L278) | PROVED |  |
| [ErdosVolume.cylinder_ball_radius](ErdosVolume/Sharpness.lean#L302) | PROVED |  |
| [ErdosVolume.pair_inradius](ErdosVolume/Sharpness.lean#L322) | PROVED |  |
| [ErdosVolume.pair_radial](ErdosVolume/Sharpness.lean#L339) | PROVED |  |
| [ErdosVolume.uniform_radial_error](ErdosVolume/Sharpness.lean#L386) | PROVED |  |
| [ErdosVolume.axial_second_moment](ErdosVolume/Sharpness.lean#L456) | PROVED |  |
| [ErdosVolume.pair_volume_fraction](ErdosVolume/Sharpness.lean#L496) | PROVED |  |
| [ErdosVolume.pair_asymptotics](ErdosVolume/Sharpness.lean#L587) | PROVED |  |
| [ErdosVolume.pair_ratio_limit](ErdosVolume/Sharpness.lean#L643) | PROVED |  |
| [ErdosVolume.uniform_upper](ErdosVolume/Sharpness.lean#L672) | OPEN |  |
| [ErdosVolume.sharp_coefficient](ErdosVolume/Sharpness.lean#L697) | PROVED |  |
| [ErdosVolume.worst_ratio_limit](ErdosVolume/Sharpness.lean#L727) | PROVED |  |
| [ErdosVolume.sharp_stability](ErdosVolume/Sharpness.lean#L755) | OPEN |  |
| [ErdosVolume.pair_cubic_radial_mean](ErdosVolume/Sharpness.lean#L765) | PROVED |  |
| [ErdosVolume.stability_center](ErdosVolume/Stability.lean#L257) | PROVED |  |
| [ErdosVolume.stability_center_ball](ErdosVolume/Stability.lean#L335) | PROVED |  |
| [ErdosVolume.stability_scalar_limits](ErdosVolume/Stability.lean#L406) | PROVED |  |
| [ErdosVolume.stability_compact_piece](ErdosVolume/Stability.lean#L442) | PROVED |  |
| [ErdosVolume.stability_log_moment](ErdosVolume/Stability.lean#L470) | PROVED |  |
| [ErdosVolume.stability_fubini](ErdosVolume/Stability.lean#L602) | PROVED |  |
| [ErdosVolume.stability_piece_bounds](ErdosVolume/Stability.lean#L638) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_compact_comparison](ErdosVolume/Stability.lean#L672) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_measure_volume](ErdosVolume/Stability.lean#L690) | PROVED GIVEN | ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_rescale_dist](ErdosVolume/Stability.lean#L705) | PROVED |  |
| [ErdosVolume.stability_normalize](ErdosVolume/Stability.lean#L726) | PROVED |  |
| [ErdosVolume.stability_phi_shape](ErdosVolume/Stability.lean#L794) | PROVED |  |
| [ErdosVolume.stability_phi_integral](ErdosVolume/Stability.lean#L828) | PROVED |  |
| [ErdosVolume.stability_annulus_mass](ErdosVolume/Stability.lean#L843) | PROVED |  |
| [ErdosVolume.stability_weak_limit](ErdosVolume/Stability.lean#L907) | PROVED |  |
| [ErdosVolume.stability_sphere_limit](ErdosVolume/Stability.lean#L982) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.EqUnique |
| [ErdosVolume.stability_spherical_radial](ErdosVolume/Stability.lean#L1018) | PROVED |  |
| [ErdosVolume.stability_radial_lap](ErdosVolume/Stability.lean#L1198) | PROVED |  |
| [ErdosVolume.stability_radial_gap](ErdosVolume/Stability.lean#L1361) | PROVED |  |
| [ErdosVolume.stability_sphere_H](ErdosVolume/Stability.lean#L1447) | PROVED |  |
| [ErdosVolume.stability_truncation](ErdosVolume/Stability.lean#L1495) | PROVED |  |
| [ErdosVolume.stability_moving_center](ErdosVolume/Stability.lean#L1540) | PROVED |  |
| [ErdosVolume.stability_compact_gap](ErdosVolume/Stability.lean#L1625) | PROVED |  |
| [ErdosVolume.stability_exterior](ErdosVolume/Stability.lean#L1654) | PROVED |  |
| [ErdosVolume.stability_hessian_kernel](ErdosVolume/Stability.lean#L1778) | PROVED |  |
| [ErdosVolume.stability_annular_second_moment](ErdosVolume/Stability.lean#L1932) | PROVED |  |
| [ErdosVolume.stability_annular_curvature](ErdosVolume/Stability.lean#L2071) | PROVED |  |
| [ErdosVolume.stability_trial_min](ErdosVolume/Stability.lean#L2137) | PROVED |  |
| [ErdosVolume.stability_shift_loss](ErdosVolume/Stability.lean#L2214) | PROVED |  |
| [ErdosVolume.stability_join_at_center](ErdosVolume/Stability.lean#L2262) | PROVED |  |
| [ErdosVolume.stability_common_center](ErdosVolume/Stability.lean#L2289) | PROVED |  |
| [ErdosVolume.stability_unscale_cost](ErdosVolume/Stability.lean#L2335) | PROVED |  |
| [ErdosVolume.stability_cost_upper](ErdosVolume/Stability.lean#L2386) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_uniform_upper](ErdosVolume/Stability.lean#L2459) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.CompactIso, ErdosVolume.Stability.EqExists, ErdosVolume.Stability.EqUnique, ErdosVolume.Stability.Frostman |
| [ErdosVolume.stability_normalized_example](ErdosVolume/Stability.lean#L2517) | PROVED GIVEN | ErdosVolume.Stability.BallLaw, ErdosVolume.Stability.Frostman |

import ErdosVolume
import Lean
/- Inspect binders in the elaborated theorem type. The named propositions are the
potential theory, flux and stability inputs identified in AUDIT_NOTES.md. -/
namespace ErdosVolumeAudit
open Lean Elab Command

def analyticInputs : List Name := [
  `ErdosVolume.OpenIsoFact, `ErdosVolume.CapacityNormalization,
  `ErdosVolume.BallCapacityFact, `ErdosVolume.EquilibriumExistence,
  `ErdosVolume.EquilibriumMomentFact, `ErdosVolume.EquilibriumSphereFact,
  `ErdosVolume.Paper.EquilibriumBallLaw,
  `ErdosVolume.Flux.AnalyticNull, `ErdosVolume.Flux.SardScalar,
  `ErdosVolume.Flux.CoareaSlabs, `ErdosVolume.Flux.PuncturedGauss,
  `ErdosVolume.Flux.BallGauss, `ErdosVolume.Flux.SphereArea,
  `ErdosVolume.Flux.SharpIso, `ErdosVolume.Flux.SurfaceFinite,
  `ErdosVolume.Stability.CompactIso, `ErdosVolume.Stability.EqExists,
  `ErdosVolume.Stability.Frostman, `ErdosVolume.Stability.EqUnique,
  `ErdosVolume.Stability.BallLaw,
  `ErdosVolume.Paper.PlanarTwoMarkBound]

partial def binderInputs : Expr → NameSet
  | .forallE _ domain body _ => Id.run do
    let mut found := binderInputs body
    for name in domain.getUsedConstants do
      if analyticInputs.contains name then found := found.insert name
    return found
  | .letE _ _ _ body _ | .mdata _ body => binderInputs body
  | _ => {}

def report (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  let inputs := ((binderInputs info.type).toList.map Name.toString).mergeSort (· ≤ ·)
  logInfo m!"INPUTS|{name}|{String.intercalate "," inputs}|END"
end ErdosVolumeAudit

#print axioms ErdosVolume.solid_compact_interior
run_cmd ErdosVolumeAudit.report ``ErdosVolume.solid_compact_interior
#print axioms ErdosVolume.energy_bounds_of_radius_pos
run_cmd ErdosVolumeAudit.report ``ErdosVolume.energy_bounds_of_radius_pos
#print axioms ErdosVolume.solid_energy
run_cmd ErdosVolumeAudit.report ``ErdosVolume.solid_energy
#print axioms ErdosVolume.dirichlet_outer
run_cmd ErdosVolumeAudit.report ``ErdosVolume.dirichlet_outer
#print axioms ErdosVolume.omega_positive
run_cmd ErdosVolumeAudit.report ``ErdosVolume.omega_positive
#print axioms ErdosVolume.closedBall_volume
run_cmd ErdosVolumeAudit.report ``ErdosVolume.closedBall_volume
#print axioms ErdosVolume.compact_isocapacity
run_cmd ErdosVolumeAudit.report ``ErdosVolume.compact_isocapacity
#print axioms ErdosVolume.integral_log_G
run_cmd ErdosVolumeAudit.report ``ErdosVolume.integral_log_G
#print axioms ErdosVolume.log_moment_sandwich
run_cmd ErdosVolumeAudit.report ``ErdosVolume.log_moment_sandwich
#print axioms ErdosVolume.sphere_rigidity
run_cmd ErdosVolumeAudit.report ``ErdosVolume.sphere_rigidity
#print axioms ErdosVolume.weighted_equality
run_cmd ErdosVolumeAudit.report ``ErdosVolume.weighted_equality
#print axioms ErdosVolume.capacity_sphere_consequence
run_cmd ErdosVolumeAudit.report ``ErdosVolume.capacity_sphere_consequence
#print axioms ErdosVolume.volume_capacity
run_cmd ErdosVolumeAudit.report ``ErdosVolume.volume_capacity
#print axioms ErdosVolume.Flux.combine_marks
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.combine_marks
#print axioms ErdosVolume.Flux.at_mark
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.at_mark
#print axioms ErdosVolume.Flux.off_formula
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.off_formula
#print axioms ErdosVolume.Flux.amgm
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.amgm
#print axioms ErdosVolume.Flux.inclusion
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.inclusion
#print axioms ErdosVolume.Flux.geometry
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.geometry
#print axioms ErdosVolume.Flux.regular_frontier
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.regular_frontier
#print axioms ErdosVolume.Flux.smooth_harmonic
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.smooth_harmonic
#print axioms ErdosVolume.Flux.critical_witness
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.critical_witness
#print axioms ErdosVolume.Flux.outer_derivative
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.outer_derivative
#print axioms ErdosVolume.Flux.null_sets
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.null_sets
#print axioms ErdosVolume.Flux.ae_regular
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.ae_regular
#print axioms ErdosVolume.Flux.shell_self
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.shell_self
#print axioms ErdosVolume.Flux.shell_other
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.shell_other
#print axioms ErdosVolume.Flux.flux_identity
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.flux_identity
#print axioms ErdosVolume.Flux.level_derivative
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.level_derivative
#print axioms ErdosVolume.Flux.level_inequalities
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.level_inequalities
#print axioms ErdosVolume.Flux.scaled_derivative
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.scaled_derivative
#print axioms ErdosVolume.Flux.exhaustion
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.exhaustion
#print axioms ErdosVolume.Flux.integrated
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.integrated
#print axioms ErdosVolume.Flux.radius_at_threshold
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.radius_at_threshold
#print axioms ErdosVolume.Flux.ray_dist
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.ray_dist
#print axioms ErdosVolume.Flux.last_point
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.last_point
#print axioms ErdosVolume.Flux.strict_amgm
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.strict_amgm
#print axioms ErdosVolume.Flux.beyond_last
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.beyond_last
#print axioms ErdosVolume.Flux.strict_ball
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.strict_ball
#print axioms ErdosVolume.Flux.strict_volume
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.strict_volume
#print axioms ErdosVolume.Flux.coincident
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.coincident
#print axioms ErdosVolume.Flux.direct_bound_eq
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Flux.direct_bound_eq
#print axioms ErdosVolume.Paper.equilibrium_exists_for_stability
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.equilibrium_exists_for_stability
#print axioms ErdosVolume.Paper.compact_iso_for_stability
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.compact_iso_for_stability
#print axioms ErdosVolume.Paper.uniform_upper_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.uniform_upper_given
#print axioms ErdosVolume.Paper.sharp_stability_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.sharp_stability_given
#print axioms ErdosVolume.Paper.equality_capacity_spheres
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.equality_capacity_spheres
#print axioms ErdosVolume.Paper.pair_axial_polynomial
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_axial_polynomial
#print axioms ErdosVolume.Paper.transverse_strict
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.transverse_strict
#print axioms ErdosVolume.Paper.axial_interval
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.axial_interval
#print axioms ErdosVolume.Paper.transverse_segment
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.transverse_segment
#print axioms ErdosVolume.Paper.missing_midplane
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.missing_midplane
#print axioms ErdosVolume.Paper.joined_to_mark
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.joined_to_mark
#print axioms ErdosVolume.Paper.figure_two_components
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.figure_two_components
#print axioms ErdosVolume.Paper.figure_lobe_balls
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.figure_lobe_balls
#print axioms ErdosVolume.Paper.figure_volume_loss
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.figure_volume_loss
#print axioms ErdosVolume.Paper.figure_ball_cylinder
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.figure_ball_cylinder
#print axioms ErdosVolume.Paper.coalescent_deficits
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.coalescent_deficits
#print axioms ErdosVolume.Paper.journal_hessian_eigendirections
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.journal_hessian_eigendirections
#print axioms ErdosVolume.Paper.journal_shell_direction
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.journal_shell_direction
#print axioms ErdosVolume.Paper.general_log_bridge
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.general_log_bridge
#print axioms ErdosVolume.Paper.pair_squared_mean
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_squared_mean
#print axioms ErdosVolume.Paper.pair_outside_cylinder
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_outside_cylinder
#print axioms ErdosVolume.Paper.sup_nonempty
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.sup_nonempty
#print axioms ErdosVolume.Paper.sup_bdd_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.sup_bdd_given
#print axioms ErdosVolume.Paper.sequence_inradius_loss_limsup
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.sequence_inradius_loss_limsup
#print axioms ErdosVolume.Paper.fixed_delta_cost_limsup
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.fixed_delta_cost_limsup
#print axioms ErdosVolume.Paper.finite_volume
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.finite_volume
#print axioms ErdosVolume.Paper.coincident_solid
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.coincident_solid
#print axioms ErdosVolume.Paper.ball_log_moment
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.ball_log_moment
#print axioms ErdosVolume.Paper.integral_log_product
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.integral_log_product
#print axioms ErdosVolume.Paper.each_moment_eq
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.each_moment_eq
#print axioms ErdosVolume.Paper.extreme_distance
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.extreme_distance
#print axioms ErdosVolume.Paper.compact_capacity_outer
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.compact_capacity_outer
#print axioms ErdosVolume.Paper.omega_three
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.omega_three
#print axioms ErdosVolume.Paper.erdos_product
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.erdos_product
#print axioms ErdosVolume.Paper.erdos_product_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.erdos_product_given
#print axioms ErdosVolume.Paper.first_order_radius
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.first_order_radius
#print axioms ErdosVolume.Paper.sequence_cost_limsup
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.sequence_cost_limsup
#print axioms ErdosVolume.Paper.discarded_log_chain
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.discarded_log_chain
#print axioms ErdosVolume.Paper.compact_piece_unit_bound
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.compact_piece_unit_bound
#print axioms ErdosVolume.Paper.trial_inner_chain
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.trial_inner_chain
#print axioms ErdosVolume.Paper.original_trial_cost_chain
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.original_trial_cost_chain
#print axioms ErdosVolume.Paper.trial_cost_six
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.trial_cost_six
#print axioms ErdosVolume.Paper.two_marks_on_line
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.two_marks_on_line
#print axioms ErdosVolume.Paper.pair_intercepts
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_intercepts
#print axioms ErdosVolume.Paper.figure_pair_widths
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.figure_pair_widths
#print axioms ErdosVolume.Paper.planar_coincident_disk
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.planar_coincident_disk
#print axioms ErdosVolume.Paper.vertical_level_quartic
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.vertical_level_quartic
#print axioms ErdosVolume.Paper.vertical_level_at_most_four
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.vertical_level_at_most_four
#print axioms ErdosVolume.Paper.planar_pair_level_null
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.planar_pair_level_null
#print axioms ErdosVolume.Paper.planar_scaled_closed
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.planar_scaled_closed
#print axioms ErdosVolume.Paper.two_mark_slice_identity
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.two_mark_slice_identity
#print axioms ErdosVolume.Paper.pair_section_subset
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_section_subset
#print axioms ErdosVolume.Paper.pair_section_empty
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_section_empty
#print axioms ErdosVolume.Paper.pair_section_area
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.pair_section_area
#print axioms ErdosVolume.Paper.unit_ball_section_area
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.unit_ball_section_area
#print axioms ErdosVolume.Paper.spatial_pair_section
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.spatial_pair_section
#print axioms ErdosVolume.Paper.spatial_ball_section
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.spatial_ball_section
#print axioms ErdosVolume.Paper.distinct_pair_volume_by_slices
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.distinct_pair_volume_by_slices
#print axioms ErdosVolume.Paper.erdos_product_all_dim_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.erdos_product_all_dim_given
#print axioms ErdosVolume.Paper.distinct_pair_strict_volume_given
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.distinct_pair_strict_volume_given
#print axioms ErdosVolume.Paper.analytic_partial_zero_set
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.analytic_partial_zero_set
#print axioms ErdosVolume.Paper.outside_cylinder_product_bounds
run_cmd ErdosVolumeAudit.report ``ErdosVolume.Paper.outside_cylinder_product_bounds
#print axioms ErdosVolume.atomic_g
run_cmd ErdosVolumeAudit.report ``ErdosVolume.atomic_g
#print axioms ErdosVolume.trunc_log_continuous
run_cmd ErdosVolumeAudit.report ``ErdosVolume.trunc_log_continuous
#print axioms ErdosVolume.measureSolid_regular
run_cmd ErdosVolumeAudit.report ``ErdosVolume.measureSolid_regular
#print axioms ErdosVolume.dilated_g
run_cmd ErdosVolumeAudit.report ``ErdosVolume.dilated_g
#print axioms ErdosVolume.scale_identities
run_cmd ErdosVolumeAudit.report ``ErdosVolume.scale_identities
#print axioms ErdosVolume.axis_dist_sq
run_cmd ErdosVolumeAudit.report ``ErdosVolume.axis_dist_sq
#print axioms ErdosVolume.pair_squared_product
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_squared_product
#print axioms ErdosVolume.pair_mem_iff
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_mem_iff
#print axioms ErdosVolume.pair_squared_mean
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_squared_mean
#print axioms ErdosVolume.pair_outside_cylinder
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_outside_cylinder
#print axioms ErdosVolume.pair_ball_cylinder
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_ball_cylinder
#print axioms ErdosVolume.cylinder_ball_radius
run_cmd ErdosVolumeAudit.report ``ErdosVolume.cylinder_ball_radius
#print axioms ErdosVolume.pair_inradius
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_inradius
#print axioms ErdosVolume.pair_radial
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_radial
#print axioms ErdosVolume.uniform_radial_error
run_cmd ErdosVolumeAudit.report ``ErdosVolume.uniform_radial_error
#print axioms ErdosVolume.axial_second_moment
run_cmd ErdosVolumeAudit.report ``ErdosVolume.axial_second_moment
#print axioms ErdosVolume.pair_volume_fraction
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_volume_fraction
#print axioms ErdosVolume.pair_asymptotics
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_asymptotics
#print axioms ErdosVolume.pair_ratio_limit
run_cmd ErdosVolumeAudit.report ``ErdosVolume.pair_ratio_limit
#print axioms ErdosVolume.uniform_upper
run_cmd ErdosVolumeAudit.report ``ErdosVolume.uniform_upper
#print axioms ErdosVolume.sharp_coefficient
run_cmd ErdosVolumeAudit.report ``ErdosVolume.sharp_coefficient
#print axioms ErdosVolume.worst_ratio_limit
run_cmd ErdosVolumeAudit.report ``ErdosVolume.worst_ratio_limit
#print axioms ErdosVolume.sharp_stability
run_cmd ErdosVolumeAudit.report ``ErdosVolume.sharp_stability
#print axioms ErdosVolume.stability_center
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_center
#print axioms ErdosVolume.stability_center_ball
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_center_ball
#print axioms ErdosVolume.stability_scalar_limits
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_scalar_limits
#print axioms ErdosVolume.stability_compact_piece
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_compact_piece
#print axioms ErdosVolume.stability_log_moment
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_log_moment
#print axioms ErdosVolume.stability_fubini
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_fubini
#print axioms ErdosVolume.stability_piece_bounds
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_piece_bounds
#print axioms ErdosVolume.stability_compact_comparison
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_compact_comparison
#print axioms ErdosVolume.stability_measure_volume
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_measure_volume
#print axioms ErdosVolume.stability_rescale_dist
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_rescale_dist
#print axioms ErdosVolume.stability_normalize
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_normalize
#print axioms ErdosVolume.stability_phi_shape
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_phi_shape
#print axioms ErdosVolume.stability_phi_integral
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_phi_integral
#print axioms ErdosVolume.stability_annulus_mass
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_annulus_mass
#print axioms ErdosVolume.stability_weak_limit
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_weak_limit
#print axioms ErdosVolume.stability_sphere_limit
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_sphere_limit
#print axioms ErdosVolume.stability_spherical_radial
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_spherical_radial
#print axioms ErdosVolume.stability_radial_lap
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_radial_lap
#print axioms ErdosVolume.stability_radial_gap
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_radial_gap
#print axioms ErdosVolume.stability_sphere_H
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_sphere_H
#print axioms ErdosVolume.stability_truncation
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_truncation
#print axioms ErdosVolume.stability_moving_center
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_moving_center
#print axioms ErdosVolume.stability_compact_gap
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_compact_gap
#print axioms ErdosVolume.stability_exterior
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_exterior
#print axioms ErdosVolume.stability_hessian_kernel
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_hessian_kernel
#print axioms ErdosVolume.stability_annular_second_moment
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_annular_second_moment
#print axioms ErdosVolume.stability_annular_curvature
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_annular_curvature
#print axioms ErdosVolume.stability_trial_min
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_trial_min
#print axioms ErdosVolume.stability_shift_loss
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_shift_loss
#print axioms ErdosVolume.stability_join_at_center
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_join_at_center
#print axioms ErdosVolume.stability_common_center
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_common_center
#print axioms ErdosVolume.stability_unscale_cost
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_unscale_cost
#print axioms ErdosVolume.stability_cost_upper
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_cost_upper
#print axioms ErdosVolume.stability_uniform_upper
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_uniform_upper
#print axioms ErdosVolume.stability_normalized_example
run_cmd ErdosVolumeAudit.report ``ErdosVolume.stability_normalized_example

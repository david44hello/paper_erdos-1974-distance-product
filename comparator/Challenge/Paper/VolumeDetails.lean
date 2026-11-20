import Challenge.Paper.Illustrations

noncomputable section

open MeasureTheory Set InnerProductSpace

open scoped ENNReal BigOperators

namespace ErdosVolume.Paper

theorem distinct_pair_strict_volume_given
    (hO : OpenIsoFact 3) (hN : CapacityNormalization 3) (hB : BallCapacityFact 3)
    (hE : EquilibriumExistence 3) (hM : EquilibriumMomentFact 3) (hS : EquilibriumSphereFact 3)
    (p q : Space 3) (hpq : p ≠ q) :
    let E := {x : Space 3 | dist x p * dist x q ≤ 1}
    volume E < ⊤ ∧ vol E < 4 * Real.pi / 3 := by sorry

theorem analytic_partial_zero_set {d n : ℕ} (hd : 3 ≤ d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (hZ : Flux.AnalyticNull d) :
    IsConnected (Flux.off a) ∧ ∃ k : Fin d,
      let D := fun x => fderiv ℝ (Flux.u a w) x (EuclideanSpace.single k 1)
      AnalyticOnNhd ℝ D (Flux.off a) ∧ (∃ x ∈ Flux.off a, D x ≠ 0) ∧
      volume {x | x ∈ Flux.off a ∧ D x = 0} = 0 ∧
      {x | x ∈ Flux.off a ∧ gradient (Flux.u a w) x = 0} ⊆ {x | x ∈ Flux.off a ∧ D x = 0} := by sorry

theorem outside_cylinder_product_bounds (x : Space 3) (t : ℝ)
    (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) (hout : 1 - t^2 < (transverse x)^2) :
    t^2 < 1/2 ∧ t^2 < (transverse x)^2 ∧
    1 < ((transverse x)^2 + t^2)^2 ∧
    ((transverse x)^2 + t^2)^2 ≤ (dist x (t • axis) * dist x ((-t) • axis))^2 := by sorry

end ErdosVolume.Paper

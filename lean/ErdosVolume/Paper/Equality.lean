module

public import ErdosVolume.Paper.Representation

@[expose] public section

/-! Equality in the capacity comparison. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
noncomputable section
open MeasureTheory Set Metric
namespace ErdosVolume.Paper

/-- Equality realizes the capacity radius and puts
each complete sphere centered at a mark into the distance-product solid. -/
theorem equality_capacity_spheres {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hO : OpenIsoFact d) (hN : CapacityNormalization d) (hB : BallCapacityFact d)
    (hE : EquilibriumExistence d) (hM : EquilibriumMomentFact d) (hS : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hvol : vol (solid a w R) = omega d * R ^ d) :
    capRadius (solid a w R) = R ∧ ∀ i, sphere (a i) R ⊆ solid a w R :=
  capacity_sphere_consequence hd hn hO hN hB hE hM hS a w hw R hR hvol

end ErdosVolume.Paper

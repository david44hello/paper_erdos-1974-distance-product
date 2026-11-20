import Challenge.Paper.Statements

import Challenge.Stability

import Challenge.Flux

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

namespace ErdosVolume.Paper

theorem equilibrium_exists_for_stability (hE : EquilibriumExistence 3) : Stability.EqExists := by sorry

theorem compact_iso_for_stability (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) : Stability.CompactIso := by sorry

theorem uniform_upper_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    ∀ ε > (0 : ℝ), ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R := by sorry

theorem sharp_stability_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    Tendsto (worstRatio (fun _ => True) R) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (worstRatio equalAtomic R) (𝓝[>] 0) (𝓝 1) := by sorry

end ErdosVolume.Paper

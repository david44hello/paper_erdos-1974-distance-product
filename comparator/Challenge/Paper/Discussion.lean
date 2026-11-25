import Challenge.Paper.TrialCost
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace ErdosVolume.Paper
open Stability

theorem zero_deficit_rigidity (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : Law) (hm : admissible μ) (hz : deficit μ 1 = 0) :
    J μ = 0 ∧ ∃ z : X, μ = Measure.dirac z ∧ measureSolid μ 1 = closedBall z 1 := by sorry

theorem pair_hits_volume_deficit (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∃ t ∈ Ioo (0:ℝ) δ, deficit (pairLaw t) 1 = ε := by sorry

def attainableRadii (ε : ℝ) : Set ℝ :=
  {r | ∃ μ : Law, admissible μ ∧ (1-ε)*omega 3 ≤ vol (measureSolid μ 1) ∧ r = inradius (measureSolid μ 1)}

theorem discussion_sharp_infimum (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) :
    (∀ ε : ℝ, 0 ≤ ε → (attainableRadii ε).Nonempty ∧ BddBelow (attainableRadii ε)) ∧
    Tendsto (fun ε => (1 - sInf (attainableRadii ε))/ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by sorry

theorem minimum_cost_tends_zero (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hp : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    Tendsto (fun j => J (μ j)) atTop (𝓝 0) := by sorry

theorem cutoff_sup_at_least_one (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (h : ℝ) (hh : 0 < h) (P : Law → Prop)
    (hP : ∀ μ : Law, equalAtomic μ → P μ) :
    let ratios := {v : ℝ | ∃ μ : Law, admissible μ ∧ P μ ∧
      0 < deficit μ 1 ∧ deficit μ 1 ≤ h ∧ v = ratio μ 1}
    ratios.Nonempty ∧ BddAbove ratios ∧ 1 ≤ worstRatio P 1 h := by sorry

end ErdosVolume.Paper

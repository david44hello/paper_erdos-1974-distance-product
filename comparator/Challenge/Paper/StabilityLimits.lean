import Challenge.Paper.TrialCost

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace ErdosVolume.Paper
open Stability

theorem sequence_inradius_loss_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    atTop.IsBoundedUnder (· ≤ ·) (fun j => (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1) ∧
    Filter.limsup (fun j => (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1) atTop ≤ 1 := by sorry

theorem fixed_delta_cost_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      0 < 1/6 - C*δ ∧
      atTop.IsBoundedUnder (· ≤ ·) (fun j => J (μ j) / gamma (μ j)) ∧
      Filter.limsup (fun j => J (μ j) / gamma (μ j)) atTop ≤ (1/3) / (1/6 - C*δ) := by sorry

end ErdosVolume.Paper

import Challenge.Paper.Illustrations

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology ENNReal

namespace ErdosVolume.Paper

open Stability

theorem sequence_cost_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    Tendsto (fun j => gamma (μ j) / deficit (μ j) 1) atTop (𝓝 1) ∧
    atTop.IsBoundedUnder (· ≤ ·) (fun j => J (μ j) / gamma (μ j)) ∧
    Filter.limsup (fun j => J (μ j) / gamma (μ j)) atTop ≤ 2 := by sorry

theorem discarded_log_chain : ∃ C > (0:ℝ), ∀ {s η : ℝ}, 0 < s → s < η → η < 1 →
    0 ≤ Real.log η - Real.log s ∧ Real.log η - Real.log s ≤ |Real.log s| ∧
    |Real.log s| ≤ C / Real.sqrt s ∧ C / Real.sqrt s ≤ C * Real.sqrt η / s := by sorry

theorem compact_piece_unit_bound (iso : CompactIso) (ex : EqExists) (frost : Frostman)
    (μ : Law) (hm : admissible μ) (K : Set X) (hK : IsCompact K) (hv : 0 < vol K)
    (hs : K ⊆ measureSolid μ 1) :
    capRadius K ≤ 1 ∧ vol K ≤ omega 3 ∧ volume (measureSolid μ 1) < ⊤ ∧
      vol (measureSolid μ 1) ≤ omega 3 := by sorry

theorem trial_inner_chain (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ : ℝ) (hδ : δ ∈ Ioo (0:ℝ) (1/8)) (b : ℕ → ℝ)
    (hb : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ b j)
    (hh : ∀ᶠ j in atTop, ∀ a ∈ closedBall (0:X) δ, ContDiffAt ℝ 2 (F (ν j) δ) a ∧
      ∀ v : X, 2*b j*‖v‖^2 ≤ hess (F (ν j) δ) a v v) :
    ∃ z : ℕ → X, (∀ j, z j ∈ closedBall (0:X) δ ∧
      ∀ a ∈ closedBall (0:X) δ, F (ν j) δ (z j) ≤ F (ν j) δ a) ∧
      Tendsto z atTop (𝓝 0) ∧ ∀ᶠ j in atTop, ∀ a : X, ‖a‖ ≤ δ →
        b j * Real.log (1+‖a-z j‖^2) ≤ b j * ‖a-z j‖^2 ∧ b j * ‖a-z j‖^2 ≤ g (ν j) a := by sorry

theorem original_trial_cost_chain (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (hp : ∀ a, potential ν a ≤ 1) (c k β : ℝ) (p z : X) (hc : 0 < c) (hc1 : c ≤ 1)
    (hk : 0 < k) (hz : ∀ a : X, k*L (a-z) ≤ g ν a)
    (havg : (∫ a, g ν a ∂(shifted p (scaled c μ))) ≤ β) :
    let ρ := shifted p (scaled c μ)
    let I := ∫ a, Real.log (1+c^2*‖a-z‖^2) ∂ρ
    cost μ (c • (z+p)) = I ∧ J μ ≤ I ∧ I ≤ k⁻¹*(∫ a, g ν a ∂ρ) ∧ k⁻¹*(∫ a, g ν a ∂ρ) ≤ β/k := by sorry

theorem trial_cost_six (μ ν : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hn : Normalized ν) (hw : weak ν sigma) (c β : ℕ → ℝ) (p : ℕ → X)
    (hc : ∀ j, 0 < c j ∧ c j ≤ 1)
    (havg : ∀ j, (∫ a, g (ν j) a ∂(shifted (p j) (scaled (c j) (μ j)))) ≤ β j) :
    ∀ ε > (0:ℝ), ∀ᶠ j in atTop, ∃ z : X,
      J (μ j) ≤ cost (μ j) z ∧ cost (μ j) z ≤ (6+ε)*β j := by sorry

end ErdosVolume.Paper

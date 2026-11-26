module

public import ErdosVolume.Paper.Statements
public import ErdosVolume.Stability
public import ErdosVolume.Flux

@[expose] public section

/-! Versions with named analytic hypotheses for the two public stability statements.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ErdosVolume.Paper

theorem equilibrium_exists_for_stability (hE : EquilibriumExistence 3) : Stability.EqExists := by
  intro K hK hc
  have hzero : leastEnergy K ≠ 0 := by
    intro h
    norm_num [capRadius, h] at hc
  have htop : leastEnergy K ≠ ⊤ := by
    intro h
    norm_num [capRadius, h] at hc
  obtain ⟨ν, hν, _⟩ := hE K hK (pos_iff_ne_zero.mpr hzero) (lt_top_iff_ne_top.mpr htop)
  exact ⟨ν, hν⟩

theorem compact_iso_for_stability (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) : Stability.CompactIso := by
  exact fun K hK => (compact_isocapacity (by decide) hO hN hB K hK).2

theorem uniform_upper_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    ∀ ε > (0 : ℝ), ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R :=
  stability_uniform_upper (compact_iso_for_stability hO hN hB)
    (equilibrium_exists_for_stability hE) hF hU hL R hR

theorem sharp_stability_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    Tendsto (worstRatio (fun _ => True) R) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (worstRatio equalAtomic R) (𝓝[>] 0) (𝓝 1) := by
  have upper := uniform_upper_given hO hN hB hE hF hU hL R hR
  refine ⟨worst_ratio_limit R _ upper ?_,worst_ratio_limit R _ upper (sharp_coefficient R hR)⟩
  intro c hc h hh
  obtain ⟨μ,hm,_,rest⟩ := sharp_coefficient R hR c hc h hh
  exact ⟨μ,hm,trivial,rest⟩

end ErdosVolume.Paper

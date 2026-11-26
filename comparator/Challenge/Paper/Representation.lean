module

public import Challenge.Paper.Conditional

@[expose] public section
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology

namespace ErdosVolume.Paper

def logPos {d : ℕ} (x a : Space d) : ℝ≥0∞ := ENNReal.ofReal (Real.log (dist x a))

def logNeg {d : ℕ} (x a : Space d) : ℝ≥0∞ :=
  if x = a then ⊤ else ENNReal.ofReal (-Real.log (dist x a))

theorem general_log_bridge (μ : Measure (Space 3)) (hμ : admissible μ) (x : Space 3) :
    let p := ∫⁻ a, logPos x a ∂μ
    let n := ∫⁻ a, logNeg x a ∂μ
    p < ⊤ ∧ gMeasure μ x = if n = ⊤ then 0 else Real.exp (p.toReal - n.toReal) := by sorry

theorem pair_squared_mean (x : Space 3) (t : ℝ) :
    (dist x (t • axis)^2 + dist x ((-t) • axis)^2)/2 = ‖x‖^2+t^2 := by sorry

theorem pair_outside_cylinder (x : Space 3) (t : ℝ) (ht : 0 < t) (ht' : t < 1/Real.sqrt 2)
    (hx : 1-t^2 < (transverse x)^2) : 1 < (dist x (t • axis)*dist x ((-t) • axis))^2 := by sorry

theorem sup_nonempty (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    ∃ μ, admissible μ ∧ equalAtomic μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h := by sorry

theorem sup_bdd_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    ∃ h > 0, BddAbove {v | ∃ μ, admissible μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧ v = ratio μ R} := by sorry

end ErdosVolume.Paper

import Challenge.Defs
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open MeasureTheory Set Filter Metric

open scoped ENNReal BigOperators Topology ContDiff

namespace ErdosVolume

def dirichletCap {d : ℕ} (K : Set (Space d)) : ℝ≥0∞ :=
  sInf {q | ∃ f : Space d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ x ∈ K, 1 ≤ f x) ∧
    q = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)}

def OpenIsoFact (d : ℕ) : Prop :=
  ∀ (U : Set (Space d)) (r : ℝ), IsOpen U → Bornology.IsBounded U → 0 < r →
    volume U = volume (Metric.ball (0 : Space d) r) →
    dirichletCap (Metric.ball (0 : Space d) r) ≤ dirichletCap U

def CapacityNormalization (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K →
    dirichletCap K = ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 2) * omega d *
      capRadius K ^ (d - 2))

def EquilibriumExistence (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → 0 < leastEnergy K → leastEnergy K < ⊤ →
    ∃ ν : Measure (Space d), equilibrium K ν ∧
      (∀ a, ν ({a} : Set (Space d)) = 0) ∧
      ∀ a, Integrable (fun x => Real.log (dist x a)) ν

def BallCapacityFact (d : ℕ) : Prop :=
  ∀ (z : Space d) (r : ℝ), 0 < r → capRadius (Metric.closedBall z r) = r

def EquilibriumMomentFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    Real.log (capRadius K) ≤ ∫ x, Real.log (dist x a) ∂ν

def EquilibriumSphereFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    (∫ x, Real.log (dist x a) ∂ν) = Real.log (capRadius K) →
    Metric.sphere a (capRadius K) ⊆ K

theorem solid_compact_interior {d n : ℕ} (hn : 0 < n) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    IsCompact (solid a w R) ∧ ∃ z r, 0 < r ∧ Metric.closedBall z r ⊆ solid a w R := by sorry

theorem energy_bounds_of_radius_pos {d : ℕ} (hd : 3 ≤ d) {K : Set (Space d)}
    (hc : 0 < capRadius K) : 0 < leastEnergy K ∧ leastEnergy K < ⊤ := by sorry

theorem solid_energy {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n) (hball : BallCapacityFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    0 < leastEnergy (solid a w R) ∧ leastEnergy (solid a w R) < ⊤ := by sorry

theorem dirichlet_outer {d : ℕ} (K : Set (Space d)) :
    dirichletCap K = sInf {v | ∃ U : Set (Space d), IsOpen U ∧ Bornology.IsBounded U ∧
      K ⊆ U ∧ dirichletCap U = v} := by sorry

theorem omega_positive (d : ℕ) : 0 < omega d := by sorry

theorem closedBall_volume {d : ℕ} (z : Space d) {r : ℝ} (hr : 0 ≤ r) :
    vol (Metric.closedBall z r) = omega d * r ^ d := by sorry

theorem compact_isocapacity {d : ℕ} (hd : 3 ≤ d) (hopen : OpenIsoFact d)
    (hnorm : CapacityNormalization d) (hball : BallCapacityFact d)
    (K : Set (Space d)) (hK : IsCompact K) :
    volume K < ⊤ ∧ vol K ≤ omega d * capRadius K ^ d := by sorry

theorem integral_log_G {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (ν : Measure (Space d)) (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    ∫ x, Real.log (G a w x) ∂ν = ∑ i, w i * ∫ x, Real.log (dist x (a i)) ∂ν := by sorry

theorem log_moment_sandwich {d n : ℕ} (hd : 3 ≤ d) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hM : EquilibriumMomentFact d) (ν : Measure (Space d))
    (heq : equilibrium (solid a w R) ν) (hc : 0 < capRadius (solid a w R))
    (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    Real.log (capRadius (solid a w R)) ≤ ∫ x, Real.log (G a w x) ∂ν ∧
    (∫ x, Real.log (G a w x) ∂ν) ≤ Real.log R := by sorry

theorem sphere_rigidity {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hs : ∀ i, Metric.sphere (a i) R ⊆ solid a w R) : ∀ i j, a i = a j := by sorry

theorem weighted_equality {n : ℕ} (w v : Fin n → ℝ) (m : ℝ) (hw : ValidWeights w)
    (hl : ∀ i, m ≤ v i) (hu : ∑ i, w i * v i ≤ m) : ∀ i, v i = m := by sorry

theorem capacity_sphere_consequence {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hO : OpenIsoFact d) (hN : CapacityNormalization d) (hB : BallCapacityFact d)
    (hE : EquilibriumExistence d) (hM : EquilibriumMomentFact d) (hS : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hvol : vol (solid a w R) = omega d * R ^ d) :
    capRadius (solid a w R) = R ∧ ∀ i, sphere (a i) R ⊆ solid a w R := by sorry

theorem volume_capacity {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hopen : OpenIsoFact d) (hnorm : CapacityNormalization d) (hball : BallCapacityFact d)
    (hex : EquilibriumExistence d) (hm : EquilibriumMomentFact d) (hs : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∀ i j, a i = a j) := by sorry

end ErdosVolume

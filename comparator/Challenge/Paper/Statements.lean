module

public import Challenge.Capacity

public import Challenge.Flux

public import Challenge.Sharpness

@[expose] public section
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace ErdosVolume.Paper

theorem coincident_solid {d n : ℕ} (w : Fin n → ℝ) (hw : ValidWeights w)
    (z : Space d) (R : ℝ) :
    (∀ x : Space d, G (fun _ => z) w x = dist x z) ∧
    solid (fun _ => z) w R = closedBall z R := by sorry

def sphereProbability {d : ℕ} (a : Space d) (r : ℝ) : Measure (Space d) :=
  let S := (volume : Measure (Space d)).toSphere
  Measure.map (fun θ : sphere (0 : Space d) 1 => a + r • (θ : Space d)) ((S univ)⁻¹ • S)

def EquilibriumBallLaw (d : ℕ) : Prop :=
  ∀ (z : Space d) (r : ℝ), 0 < r →
    equilibrium (closedBall z r) (sphereProbability z r) ∧
    ∀ ν, equilibrium (closedBall z r) ν → ν = sphereProbability z r

theorem ball_log_moment {d : ℕ} (hd : 3 ≤ d) (hb : EquilibriumBallLaw d)
    (a : Space d) (r : ℝ) (hr : 0 < r) (ν : Measure (Space d))
    (hν : equilibrium (closedBall a r) ν) :
    ∫ x, Real.log (dist x a) ∂ν = Real.log r := by sorry

theorem integral_log_product {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (ν : Measure (Space d)) (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    ∫ x, Real.log (G a w x) ∂ν = ∑ i, w i * ∫ x, Real.log (dist x (a i)) ∂ν := by sorry

theorem each_moment_eq {n : ℕ} (w v : Fin n → ℝ) (m : ℝ) (hw : ValidWeights w)
    (hl : ∀ i, m ≤ v i) (hu : ∑ i, w i * v i ≤ m) : ∀ i, v i = m := by sorry

theorem extreme_distance {d : ℕ} (a b u : Space d) (hu : ‖u‖ = 1)
    (hab : b ≠ a) (hproj : 0 ≤ inner ℝ u (a-b)) (R : ℝ) (hR : 0 < R) :
    dist (a + R • u) b ^ 2 = R^2 + 2*R*(inner ℝ u (a-b)) + ‖a-b‖^2 ∧
    R < dist (a + R • u) b := by sorry

theorem compact_capacity_outer {d : ℕ} (K : Set (Space d)) (hK : IsCompact K) :
    dirichletCap K = sInf {v | ∃ U : Set (Space d), IsOpen U ∧ Bornology.IsBounded U ∧
      K ⊆ U ∧ dirichletCap U = v} := by sorry

theorem omega_three : omega 3 = 4 * Real.pi / 3 := by sorry

theorem erdos_product_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3)
    (hM : EquilibriumMomentFact 3) (hS : EquilibriumSphereFact 3)
    {n : ℕ} (hn : 0 < n) (a : Fin n → Space 3) :
    let E := {x : Space 3 | ∏ i, dist x (a i) ≤ 1}
    volume E < ⊤ ∧ vol E ≤ 4 * Real.pi / 3 ∧ (vol E = 4*Real.pi/3 ↔ ∀ i j, a i = a j) := by sorry

end ErdosVolume.Paper

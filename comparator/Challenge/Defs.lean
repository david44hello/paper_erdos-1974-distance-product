import Mathlib

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal BigOperators Topology

namespace ErdosVolume

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def ValidWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ∑ i, w i = 1

def G {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ :=
  ∏ i, dist x (a i) ^ w i

def solid {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) (R : ℝ) : Set (Space d) :=
  {x | G a w x ≤ R}

def vol {d : ℕ} (K : Set (Space d)) : ℝ := (volume K).toReal

def omega (d : ℕ) : ℝ := vol (Metric.ball (0 : Space d) 1)

def gMeasure {d : ℕ} (μ : Measure (Space d)) (x : Space d) : ℝ :=
  ⨅ k : ℕ, Real.exp (∫ a, Real.log (max (dist x a) (Real.exp (-(k : ℝ)))) ∂μ)

def measureSolid {d : ℕ} (μ : Measure (Space d)) (R : ℝ) : Set (Space d) :=
  {x | gMeasure μ x ≤ R}

def inradius {d : ℕ} (K : Set (Space d)) : ℝ :=
  sSup (insert 0 {r : ℝ | 0 < r ∧ ∃ z, Metric.ball z r ⊆ K})

def deficit (μ : Measure (Space 3)) (R : ℝ) : ℝ :=
  1 - vol (measureSolid μ R) / (omega 3 * R ^ 3)

def admissible (μ : Measure (Space 3)) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support

def atomic {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) : Measure (Space d) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i)

def newtonKernel {d : ℕ} (x y : Space d) : ℝ≥0∞ :=
  (ENNReal.ofReal (dist x y)) ^ (2 - (d : ℝ))

def energy {d : ℕ} (ν : Measure (Space d)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, newtonKernel x y ∂ν ∂ν

def leastEnergy {d : ℕ} (K : Set (Space d)) : ℝ≥0∞ :=
  sInf {v | ∃ ν : Measure (Space d), IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧ energy ν = v}

def capRadius {d : ℕ} (K : Set (Space d)) : ℝ :=
  ((leastEnergy K) ^ (1 / (2 - (d : ℝ)))).toReal

def equilibrium {d : ℕ} (K : Set (Space d)) (ν : Measure (Space d)) : Prop :=
  IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧ energy ν = leastEnergy K

end ErdosVolume

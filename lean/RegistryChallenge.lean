-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

module

public import Mathlib

@[expose] public section

/-!
# Volume and inradius of distance-product solids
Two proofs bound the volume in dimensions at least three, with six capacity or
eight flux hypotheses. The three-dimensional first-order inradius bound takes
seven analytic inputs. Its lower sharpness witness is unconditional.
-/

namespace ErdosVolume.CoordinateFacts

/-- Finite real coordinate spaces are finite real modules. -/
theorem finiteCoordinates (d : ℕ) : Module.Finite ℝ (WithLp 2 (Fin d → ℝ)) := inferInstance

/-- The coordinate Euclidean space carries its Borel measurable structure. -/
theorem borelCoordinates (d : ℕ) : BorelSpace (PiLp 2 (fun _ : Fin d => ℝ)) := inferInstance

/-- Multiplication gives the scalar-tower law for extended nonnegative scalars. -/
theorem ennrealScalarTower :
    @IsScalarTower ENNReal ENNReal ENNReal
      (@Algebra.toSMul ENNReal ENNReal _ _ (Algebra.id ENNReal))
      (inferInstance : SMul ENNReal ENNReal)
      (@Algebra.toSMul ENNReal ENNReal _ _ (Algebra.id ENNReal)) :=
  IsScalarTower.right

/-- The coordinate norm exponent is at least two. -/
theorem twoAtLeastTwo : (1 + 1 : ℕ).AtLeastTwo := inferInstance

/-- The finite-module fact specialized to three dimensions. -/
theorem finiteThree : Module.Finite ℝ (WithLp 2 (Fin 3 → ℝ)) := finiteCoordinates 3

/-- The Borel-space fact specialized to three dimensions. -/
theorem borelThree : BorelSpace (PiLp 2 (fun _ : Fin 3 => ℝ)) := borelCoordinates 3

end ErdosVolume.CoordinateFacts

attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.ennrealScalarTower
attribute [local instance 2000] ErdosVolume.CoordinateFacts.twoAtLeastTwo
attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteThree
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelThree

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal BigOperators Topology ContDiff Classical Pointwise
namespace ErdosVolume

/-- Euclidean d-space, with coordinates indexed by Fin d. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The weights are strictly positive and sum to one. -/
def ValidWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ∑ i, w i = 1

/-- Weighted geometric mean of the distances from x to the marked points. -/
def G {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ :=
  ∏ i, dist x (a i) ^ w i

/-- Closed sublevel set of the weighted geometric mean at threshold R. -/
def solid {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) (R : ℝ) : Set (Space d) :=
  {x | G a w x ≤ R}

/-- Lebesgue volume expressed as a real number; finiteness is proved separately where needed. -/
def vol {d : ℕ} (K : Set (Space d)) : ℝ := (volume K).toReal

/-- Volume of the open unit ball in Euclidean d-space. -/
def omega (d : ℕ) : ℝ := vol (Metric.ball (0 : Space d) 1)

/-- Geometric potential of a measure obtained by truncating the logarithm from below. -/
def gMeasure {d : ℕ} (μ : Measure (Space d)) (x : Space d) : ℝ :=
  ⨅ k : ℕ, Real.exp (∫ a, Real.log (max (dist x a) (Real.exp (-(k : ℝ)))) ∂μ)

/-- Closed sublevel set of the measure potential at threshold R. -/
def measureSolid {d : ℕ} (μ : Measure (Space d)) (R : ℝ) : Set (Space d) :=
  {x | gMeasure μ x ≤ R}

/-- Supremum of zero and the radii of open balls contained in the set. -/
def inradius {d : ℕ} (K : Set (Space d)) : ℝ :=
  sSup (insert 0 {r : ℝ | 0 < r ∧ ∃ z, Metric.ball z r ⊆ K})

/-- One minus the sublevel volume divided by the volume of the radius-R ball in dimension three. -/
def deficit (μ : Measure (Space 3)) (R : ℝ) : ℝ :=
  1 - vol (measureSolid μ R) / (omega 3 * R ^ 3)

/-- A compactly supported probability measure. -/
def admissible (μ : Measure (Space 3)) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support

/-- Weighted sum of Dirac masses at the marked points. -/
def atomic {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ) : Measure (Space d) :=
  letI : SMul ENNReal (Measure (Space d)) :=
    @MeasureTheory.Measure.instSMul (Space d) ENNReal _ _ ErdosVolume.CoordinateFacts.ennrealScalarTower
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i)

/-- Newtonian kernel with exponent 2−d and values in the extended nonnegative reals. -/
def newtonKernel {d : ℕ} (x y : Space d) : ℝ≥0∞ :=
  (ENNReal.ofReal (dist x y)) ^ (2 - (d : ℝ))

/-- Double integral of the Newtonian kernel against the given measure. -/
def energy {d : ℕ} (ν : Measure (Space d)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, newtonKernel x y ∂ν ∂ν

/-- Infimum of the energies of probability measures concentrated on K. -/
def leastEnergy {d : ℕ} (K : Set (Space d)) : ℝ≥0∞ :=
  sInf {v | ∃ ν : Measure (Space d), IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧ energy ν = v}

/-- Capacity radius derived from the least energy with exponent 1/(2−d). -/
def capRadius {d : ℕ} (K : Set (Space d)) : ℝ :=
  ((leastEnergy K) ^ (1 / (2 - (d : ℝ)))).toReal

/-- A probability measure concentrated on K that realizes its least energy. -/
def equilibrium {d : ℕ} (K : Set (Space d)) (ν : Measure (Space d)) : Prop :=
  IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧ energy ν = leastEnergy K

/-- Infimum of Dirichlet energy among smooth compactly supported functions at least one on K. -/
def dirichletCap {d : ℕ} (K : Set (Space d)) : ℝ≥0∞ :=
  sInf {q | ∃ f : Space d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ x ∈ K, 1 ≤ f x) ∧
    q = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)}

/-- Among bounded open sets of a fixed volume, the ball minimizes Dirichlet capacity. -/
def OpenIsoFact (d : ℕ) : Prop :=
  ∀ (U : Set (Space d)) (r : ℝ), IsOpen U → Bornology.IsBounded U → 0 < r →
    volume U = volume (Metric.ball (0 : Space d) r) →
    dirichletCap (Metric.ball (0 : Space d) r) ≤ dirichletCap U

/-- The stated conversion between Dirichlet capacity and capacity radius of a compact set. -/
def CapacityNormalization (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K →
    dirichletCap K = ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 2) * omega d *
      capRadius K ^ (d - 2))

/-- A compact set of positive finite least energy admits an atomless equilibrium law with integrable log distances. -/
def EquilibriumExistence (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → 0 < leastEnergy K → leastEnergy K < ⊤ →
    ∃ ν : Measure (Space d), equilibrium K ν ∧
      (∀ a, ν ({a} : Set (Space d)) = 0) ∧
      ∀ a, Integrable (fun x => Real.log (dist x a)) ν

/-- The capacity radius of every closed ball of positive radius equals its radius. -/
def BallCapacityFact (d : ℕ) : Prop :=
  ∀ (z : Space d) (r : ℝ), 0 < r → capRadius (Metric.closedBall z r) = r

/-- Each equilibrium log-distance moment is bounded below by the log of the capacity radius. -/
def EquilibriumMomentFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    Real.log (capRadius K) ≤ ∫ x, Real.log (dist x a) ∂ν

/-- Equality in that moment bound forces the specified sphere to lie in the compact set. -/
def EquilibriumSphereFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    (∫ x, Real.log (dist x a) ∂ν) = Real.log (capRadius K) →
    Metric.sphere a (capRadius K) ⊆ K

/-- Capacity proof of finite volume, the sharp ball bound, and equality exactly at coincident marks. -/
theorem volume_capacity {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hopen : OpenIsoFact d) (hnorm : CapacityNormalization d) (hball : BallCapacityFact d)
    (hex : EquilibriumExistence d) (hm : EquilibriumMomentFact d) (hs : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∀ i j, a i = a j) := by sorry

namespace Flux

variable {d n : ℕ}

/-- Weighted Newtonian potential of the finite configuration, in extended nonnegative reals. -/
def potential (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (w i) * newtonKernel x (a i)

/-- Complement of the set of marked points. -/
def off (a : Fin n → Space d) : Set (Space d) := (Set.range a)ᶜ

/-- Real-valued Newtonian potential away from its sources. -/
def u (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ :=
  ∑ i, w i * dist x (a i) ^ (2 - (d : ℝ))

/-- Superlevel set of the extended Newtonian potential. -/
def super (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | ENNReal.ofReal t ≤ potential a w x}

/-- Level set of the real potential off the marked points. -/
def level (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | x ∈ off a ∧ u a w x = t}

/-- Volume of the superlevel set. -/
def W (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) := vol (super a w t)

/-- Radius of a Euclidean ball with the given superlevel volume. -/
def rad (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  (W a w t / omega d) ^ (1 / (d : ℝ))

/-- Normalized codimension-one Hausdorff measure restricted to the set. -/
def surface (S : Set (Space d)) : Measure (Space d) :=
  letI : SMul ENNReal (Measure (Space d)) :=
    @MeasureTheory.Measure.instSMul (Space d) ENNReal _ _ ErdosVolume.CoordinateFacts.ennrealScalarTower
  ENNReal.ofReal (omega (d-1) / (2 : ℝ) ^ (d-1)) •
    ((Measure.hausdorffMeasure ((d : ℝ) - 1)).restrict S)

/-- The gradient of the real potential is nonzero throughout the indicated level set. -/
def regular (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ x ∈ level a w t, gradient (u a w) x ≠ 0

/-- Vector normalized by its norm, with Lean's value at the zero vector. -/
def normal (v : Space d) := ‖v‖⁻¹ • v

/-- Integral of the outward normal derivative over a sphere of given center and radius. -/
def shellFlux (f : Space d → ℝ) (b : Space d) (e : ℝ) :=
  ∫ x, inner ℝ (gradient f x) (normal (x-b)) ∂(surface (sphere b e))

/-- Level-set integral of the reciprocal gradient norm. -/
def density (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ∫ x, ‖gradient (u a w) x‖⁻¹ ∂(surface (level a w t))

/-- Total normalized surface measure of a level set. -/
def area (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ((surface (level a w t)) Set.univ).toReal

/-- A nontrivial real-analytic function on a connected open set has a null zero set. -/
def AnalyticNull (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → IsConnected O →
    AnalyticOnNhd ℝ f O → (∃ x ∈ O, f x ≠ 0) → volume {x | x ∈ O ∧ f x = 0} = 0

/-- The critical values of every smooth real-valued function on an open set form a null set. -/
def SardScalar (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → ContDiffOn ℝ ∞ f O →
    volume (f '' {x | x ∈ O ∧ gradient f x = 0}) = 0

/-- Under the displayed null-set assumptions, integrating level density gives the volume between two levels. -/
def CoareaSlabs (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  volume {x | x ∈ off a ∧ gradient (u a w) x = 0} = 0 →
  (∀ t > 0, volume (level a w t) = 0) →
  ∀ s t : ℝ, 0 < s → s < t →
    IntervalIntegrable (density a w) volume s t ∧
    W a w s - W a w t = ∫ z in s..t, density a w z

/-- Flux identity for harmonic functions on a potential superlevel set with source balls excised. -/
def PuncturedGauss (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → ∀ᶠ e in 𝓝[>] (0 : ℝ),
    ∀ f : Space d → ℝ, HarmonicOnNhd f (super a w t \ ⋃ b ∈ Set.range a, ball b e) →
    (∫ x, inner ℝ (gradient f x) (-normal (gradient (u a w) x)) ∂(surface (level a w t))) =
      ∑ b ∈ Finset.univ.image a, shellFlux f b e

/-- The outward flux of a function harmonic near a closed ball is zero. -/
def BallGauss (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ) (f : Space d → ℝ), 0 < e →
    HarmonicOnNhd f (closedBall b e) → shellFlux f b e = 0

/-- The surface area of a positive-radius sphere has the displayed Euclidean normalization. -/
def SphereArea (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ), 0 < e →
    (surface (sphere b e)) Set.univ = ENNReal.ofReal ((d : ℝ) * omega d * e ^ (d-1))

/-- Sharp isoperimetric inequality between volume and boundary measure of a compact measurable set. -/
def SharpIso (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → MeasurableSet K →
    ENNReal.ofReal ((d : ℝ) * omega d * (vol K / omega d) ^ (((d : ℝ)-1)/d)) ≤
      (surface (frontier K)) Set.univ

/-- Regular positive level sets have finite surface measure. -/
def SurfaceFinite (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → (surface (level a w t)) Set.univ < ⊤

variable (a : Fin n → Space d) (w : Fin n → ℝ)

/-- Flux proof of the sharp volume bound with equality exactly for coincident marks. -/
theorem direct_bound_eq (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) {R : ℝ} (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∃ p : Space d, ∀ i, a i = p) := by sorry

end Flux

/-- An empirical probability measure placing equal mass at each listed mark, allowing repetitions. -/
def equalAtomic (μ : Measure (Space 3)) : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (a : Fin n → Space 3), μ = atomic a (fun _ => ((n : ℝ)⁻¹))

/-- Normalized loss of inradius divided by the volume deficit. -/
def ratio (μ : Measure (Space 3)) (R : ℝ) : ℝ :=
  (1 - inradius (measureSolid μ R) / R) / deficit μ R

/-- Supremum of ratios for admissible measures with positive deficit bounded by h and satisfying P. -/
def worstRatio (P : Measure (Space 3) → Prop) (R h : ℝ) : ℝ :=
  sSup {v | ∃ μ, admissible μ ∧ P μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧ v = ratio μ R}

namespace Stability

/-- Three-dimensional Euclidean space. -/
abbrev X := Space 3

/-- A measure on three-dimensional Euclidean space. -/
abbrev Law := Measure X

/-- Newtonian potential of a measure at the point a. -/
def potential (ν : Law) (a : X) : ℝ≥0∞ := ∫⁻ x, newtonKernel x a ∂ν

/-- Normalized surface probability on the unit sphere regarded as a measure in Euclidean space. -/
def sigma : Law :=
  letI : SMul ENNReal (Measure (X)) :=
    @MeasureTheory.Measure.instSMul (X) ENNReal _ _ ErdosVolume.CoordinateFacts.ennrealScalarTower
  let S := (volume : Law).toSphere
  (S Set.univ)⁻¹ • S.map (fun x : Metric.sphere (0 : X) 1 => (x : X))

/-- The equilibrium potential is bounded above pointwise by the reciprocal capacity radius. -/
def Frostman : Prop := ∀ (K : Set X) (ν : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → ∀ a, potential ν a ≤ ENNReal.ofReal ((capRadius K)⁻¹)

/-- An equilibrium law on a compact set of positive capacity radius is unique. -/
def EqUnique : Prop := ∀ (K : Set X) (ν ν' : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → equilibrium K ν' → ν = ν'

/-- The closed unit ball has capacity radius and least energy one, with equilibrium law given by surface probability. -/
def BallLaw : Prop := capRadius (Metric.closedBall (0 : X) 1) = 1 ∧
  leastEnergy (Metric.closedBall (0 : X) 1) = 1 ∧ equilibrium (Metric.closedBall (0 : X) 1) sigma

end Stability

namespace Paper

/-- Under seven analytic hypotheses, the worst inradius-to-volume deficit ratio tends to one for both classes of measures. -/
theorem sharp_stability_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    Tendsto (worstRatio (fun _ => True) R) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (worstRatio equalAtomic R) (𝓝[>] 0) (𝓝 1) := by sorry

end Paper

/-- Every coefficient less than one fails for equal atomic measures of arbitrarily small positive deficit. -/
theorem sharp_coefficient (R : ℝ) (hR : 0 < R) (c : ℝ) (hc : c < 1) (h : ℝ) (hh : 0 < h) :
    ∃ μ, admissible μ ∧ equalAtomic μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧
       c * deficit μ R < 1 - inradius (measureSolid μ R) / R := by sorry

end ErdosVolume

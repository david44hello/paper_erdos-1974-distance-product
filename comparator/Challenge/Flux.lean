import Challenge.Defs
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open MeasureTheory Set Filter Metric InnerProductSpace

open scoped ENNReal BigOperators Topology ContDiff Classical

namespace ErdosVolume

namespace Flux

variable {d n : ℕ}

def potential (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (w i) * newtonKernel x (a i)

def off (a : Fin n → Space d) : Set (Space d) := (Set.range a)ᶜ

def u (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ :=
  ∑ i, w i * dist x (a i) ^ (2 - (d : ℝ))

def super (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | ENNReal.ofReal t ≤ potential a w x}

def level (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | x ∈ off a ∧ u a w x = t}

def W (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) := vol (super a w t)

def rad (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  (W a w t / omega d) ^ (1 / (d : ℝ))

def surface (S : Set (Space d)) : Measure (Space d) :=
  ENNReal.ofReal (omega (d-1) / (2 : ℝ) ^ (d-1)) •
    ((Measure.hausdorffMeasure ((d : ℝ) - 1)).restrict S)

def regular (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ x ∈ level a w t, gradient (u a w) x ≠ 0

def normal (v : Space d) := ‖v‖⁻¹ • v

def shellFlux (f : Space d → ℝ) (b : Space d) (e : ℝ) :=
  ∫ x, inner ℝ (gradient f x) (normal (x-b)) ∂(surface (sphere b e))

def density (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ∫ x, ‖gradient (u a w) x‖⁻¹ ∂(surface (level a w t))

def area (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ((surface (level a w t)) Set.univ).toReal

def AnalyticNull (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → IsConnected O →
    AnalyticOnNhd ℝ f O → (∃ x ∈ O, f x ≠ 0) → volume {x | x ∈ O ∧ f x = 0} = 0

def SardScalar (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → ContDiffOn ℝ ∞ f O →
    volume (f '' {x | x ∈ O ∧ gradient f x = 0}) = 0

def CoareaSlabs (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  volume {x | x ∈ off a ∧ gradient (u a w) x = 0} = 0 →
  (∀ t > 0, volume (level a w t) = 0) →
  ∀ s t : ℝ, 0 < s → s < t →
    IntervalIntegrable (density a w) volume s t ∧
    W a w s - W a w t = ∫ z in s..t, density a w z

def PuncturedGauss (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → ∀ᶠ e in 𝓝[>] (0 : ℝ),
    ∀ f : Space d → ℝ, HarmonicOnNhd f (super a w t \ ⋃ b ∈ Set.range a, ball b e) →
    (∫ x, inner ℝ (gradient f x) (-normal (gradient (u a w) x)) ∂(surface (level a w t))) =
      ∑ b ∈ Finset.univ.image a, shellFlux f b e

def BallGauss (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ) (f : Space d → ℝ), 0 < e →
    HarmonicOnNhd f (closedBall b e) → shellFlux f b e = 0

def SphereArea (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ), 0 < e →
    (surface (sphere b e)) Set.univ = ENNReal.ofReal ((d : ℝ) * omega d * e ^ (d-1))

def SharpIso (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → MeasurableSet K →
    ENNReal.ofReal ((d : ℝ) * omega d * (vol K / omega d) ^ (((d : ℝ)-1)/d)) ≤
      (surface (frontier K)) Set.univ

def SurfaceFinite (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → (surface (level a w t)) Set.univ < ⊤

variable (a : Fin n → Space d) (w : Fin n → ℝ)

theorem combine_marks (x : Space d) :
    u a w x = ∑ b ∈ Finset.univ.image a,
      (∑ i ∈ Finset.univ.filter (fun i => a i = b), w i) * dist x b ^ (2 - (d : ℝ)) := by sorry

theorem at_mark (hd : 3 ≤ d) (hw : ValidWeights w) (i : Fin n) :
    potential a w (a i) = ⊤ := by sorry

theorem off_formula (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a) :
    potential a w x = ENNReal.ofReal (u a w x) := by sorry

theorem amgm (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a) :
    G a w x ^ (2 - (d : ℝ)) ≤ u a w x := by sorry

theorem inclusion (hd : 3 ≤ d) (hw : ValidWeights w) {R : ℝ} (hR : 0 < R) :
    solid a w R ⊆ super a w (R ^ (2 - (d : ℝ))) := by sorry

theorem geometry (hd : 3 ≤ d) (hw : ValidWeights w) {t : ℝ} (ht : 0 < t) :
    IsCompact (super a w t) ∧ (∀ i : Fin n, super a w t ∈ 𝓝 (a i)) ∧
    0 < rad a w t ∧ W a w t = omega d * rad a w t ^ d := by sorry

theorem regular_frontier (hd : 3 ≤ d) (hw : ValidWeights w) {t : ℝ} (ht : 0 < t)
    (hr : regular a w t) : frontier (super a w t) = level a w t := by sorry

theorem smooth_harmonic (hd : 3 ≤ d) (hw : ValidWeights w) :
    AnalyticOnNhd ℝ (u a w) (off a) ∧ ContDiffOn ℝ ∞ (u a w) (off a) ∧
    HarmonicOnNhd (u a w) (off a) := by sorry

theorem critical_witness (hd : 3 ≤ d) (hw : ValidWeights w) :
    IsConnected (off a) ∧ ∃ k : Fin d, ∃ x ∈ off a,
      fderiv ℝ (u a w) x (EuclideanSpace.single k 1) ≠ 0 := by sorry

theorem outer_derivative (t : ℝ) {x : Space d} (hx : x ∈ level a w t) :
    inner ℝ (gradient (u a w) x) (-normal (gradient (u a w) x)) =
      -‖gradient (u a w) x‖ := by sorry

theorem null_sets (hd : 3 ≤ d) (hw : ValidWeights w) (hZ : AnalyticNull d) :
    volume {x | x ∈ off a ∧ gradient (u a w) x = 0} = 0 ∧
    ∀ t : ℝ, volume (level a w t) = 0 := by sorry

theorem ae_regular (hd : 3 ≤ d) (hw : ValidWeights w) (hS : SardScalar d) :
    ∀ᵐ t : ℝ, 0 < t → regular a w t := by sorry

theorem shell_self (hd : 3 ≤ d) (hA : SphereArea d) (b : Space d) {e : ℝ} (he : 0 < e) :
    shellFlux (fun x => dist x b ^ (2 - (d : ℝ))) b e = -((d : ℝ) * (d-2 : ℝ) * omega d) := by sorry

theorem shell_other (hd : 3 ≤ d) (hB : BallGauss d) (b c : Space d) {e : ℝ}
    (he : 0 < e) (hc : e < dist b c) :
    shellFlux (fun x => dist x c ^ (2 - (d : ℝ))) b e = 0 := by sorry

theorem flux_identity (hd : 3 ≤ d) (hw : ValidWeights w)
    (hG : PuncturedGauss a w) (hB : BallGauss d) (hA : SphereArea d) {t : ℝ}
    (ht : 0 < t) (hr : regular a w t) :
    (∫ x, ‖gradient (u a w) x‖ ∂(surface (level a w t))) =
      (d : ℝ) * (d-2 : ℝ) * omega d := by sorry

theorem level_derivative (hd : 3 ≤ d) (hw : ValidWeights w)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    (∀ s t : ℝ, 0 < s → s < t → AbsolutelyContinuousOnInterval (W a w) s t) ∧
    ∀ᵐ t : ℝ, 0 < t → HasDerivAt (W a w) (-density a w t) t := by sorry

theorem level_inequalities (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → ((d : ℝ) * omega d * rad a w t ^ (d-1)) ^ 2 ≤ area a w t ^ 2 ∧
      area a w t ^ 2 ≤ (d : ℝ) * (d-2 : ℝ) * omega d * (-deriv (W a w) t) := by sorry

theorem scaled_derivative (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → 1 ≤ deriv (fun z => rad a w z ^ (2 - (d : ℝ))) t := by sorry

theorem exhaustion (hd : 3 ≤ d) (hw : ValidWeights w) :
    (⋃ t ∈ Set.Ioi (0 : ℝ), super a w t) = Set.univ ∧
    Tendsto (fun t => rad a w t ^ (2 - (d : ℝ))) (𝓝[>] 0) (𝓝 0) := by sorry

theorem integrated (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) {t : ℝ} (ht : 0 < t) :
    t ≤ rad a w t ^ (2 - (d : ℝ)) := by sorry

theorem radius_at_threshold (hd : 3 ≤ d) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (h : R ^ (2 - (d : ℝ)) ≤ r ^ (2 - (d : ℝ))) : r ≤ R := by sorry

def ray (a b : Space d) (s : ℝ) := a + s • (a-b)

theorem ray_dist (p q : Space d) (hpq : p ≠ q) {s : ℝ} (hs : 0 ≤ s) :
    dist (ray p q s) p < dist (ray p q s) q := by sorry

theorem last_point (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) : ∃ s ≥ (0 : ℝ), G a w (ray (a i) (a j) s) = R ∧
      ∀ v > s, R < G a w (ray (a i) (a j) v) := by sorry

theorem strict_amgm (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a)
    {i j : Fin n} (hij : dist x (a i) ≠ dist x (a j)) :
    G a w x ^ (2 - (d : ℝ)) < u a w x := by sorry

theorem beyond_last (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hy : G a w (ray (a i) (a j) s) = R)
    (hlast : ∀ v > s, R < G a w (ray (a i) (a j) v)) :
    ∀ᶠ v in 𝓝[>] s, R < G a w (ray (a i) (a j) v) ∧
      R ^ (2 - (d : ℝ)) < u a w (ray (a i) (a j) v) := by sorry

theorem strict_ball (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) : ∃ z : Space d, ∃ ε > (0 : ℝ),
      ball z ε ⊆ super a w (R ^ (2 - (d : ℝ))) \ solid a w R := by sorry

theorem strict_volume (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ volume (super a w (R ^ (2 - (d : ℝ)))) < ⊤ ∧
    vol (solid a w R) < W a w (R ^ (2 - (d : ℝ))) := by sorry

theorem coincident {p : Space d} (hw : ValidWeights w) (hp : ∀ i, a i = p) {R : ℝ} :
    G a w = (fun x => dist x p) ∧ solid a w R = closedBall p R := by sorry

theorem direct_bound_eq (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) {R : ℝ} (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∃ p : Space d, ∀ i, a i = p) := by sorry

theorem scaled_radius_absolute_continuity (hd : 3 ≤ d) (hw : ValidWeights w)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    AbsolutelyContinuousOnInterval (fun z => rad a w z ^ (2-(d:ℝ))) s t := by sorry

theorem level_surface_cauchy_schwarz (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → area a w t ^ 2 ≤
      (∫ x, ‖gradient (u a w) x‖ ∂(surface (level a w t))) *
      (∫ x, ‖gradient (u a w) x‖⁻¹ ∂(surface (level a w t))) := by sorry

end Flux

end ErdosVolume

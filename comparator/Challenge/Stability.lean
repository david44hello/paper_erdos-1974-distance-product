import Challenge.Defs

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal Topology BigOperators BoundedContinuousFunction

namespace ErdosVolume

namespace Stability

abbrev X := Space 3

abbrev Law := Measure X

def L (x : X) : ℝ := Real.log (1 + ‖x‖^2)

def cost (μ : Law) (z : X) : ℝ := ∫ a, L (z-a) ∂μ

def J (μ : Law) : ℝ := sInf (Set.range (cost μ))

def M (μ : Law) (z : X) : ℝ := ∫ a, (1 + ‖z-a‖^2)⁻¹ ∂μ

def gamma (μ : Law) : ℝ := -Real.log (1 - deficit μ 1)

def beta (K : Set X) : ℝ := -Real.log (capRadius K)

def potential (ν : Law) (a : X) : ℝ≥0∞ := ∫⁻ x, newtonKernel x a ∂ν

def g (ν : Law) (a : X) : ℝ := ∫ x, Real.log (dist x a) ∂ν

def phi (s : ℝ) : ℝ := Real.log s + s⁻¹ - 1

def ann (δ : ℝ) : Set X := {x | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ}

def F (ν : Law) (δ : ℝ) (a : X) : ℝ := ∫ x in ann δ, phi (dist x a) ∂ν

def e₁ : X := EuclideanSpace.single (0 : Fin 3) 1

def sigma : Law :=
  let S := (volume : Law).toSphere
  (S Set.univ)⁻¹ • S.map (fun x : Metric.sphere (0 : X) 1 => (x : X))

def H (s : ℝ) : ℝ := g sigma (s • e₁)

def comparison (s : ℝ) : ℝ := Real.log (1+s^2) / 6

def radialLap (f : ℝ → ℝ) (s : ℝ) : ℝ := deriv (fun t => t^2 * deriv f t) s / s^2

def weak (ν : ℕ → Law) (limLaw : Law) : Prop :=
  ∀ f : X →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂ν j) atTop (𝓝 (∫ x, f x ∂limLaw))

def scaled (c : ℝ) (ν : Law) : Law := ν.map (fun x => c⁻¹ • x)

def shifted (p : X) (ν : Law) : Law := ν.map (fun x => x - p)

def hess (f : X → ℝ) (a u v : X) : ℝ := (fderiv ℝ (fderiv ℝ f) a u) v

def direction (x : X) : X := ‖x‖⁻¹ • x

def CompactIso : Prop := ∀ K : Set X, IsCompact K → vol K ≤ omega 3 * capRadius K ^ 3

def EqExists : Prop := ∀ K : Set X, IsCompact K → 0 < capRadius K → ∃ ν, equilibrium K ν

def Frostman : Prop := ∀ (K : Set X) (ν : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → ∀ a, potential ν a ≤ ENNReal.ofReal ((capRadius K)⁻¹)

def EqUnique : Prop := ∀ (K : Set X) (ν ν' : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → equilibrium K ν' → ν = ν'

def BallLaw : Prop := capRadius (Metric.closedBall (0 : X) 1) = 1 ∧
  leastEnergy (Metric.closedBall (0 : X) 1) = 1 ∧ equilibrium (Metric.closedBall (0 : X) 1) sigma

def Normalized (ν : ℕ → Law) : Prop :=
  (∀ j, admissible (ν j) ∧ ∀ a, potential (ν j) a ≤ 1) ∧
    Tendsto (fun j => g (ν j) 0) atTop (𝓝 0)

end Stability

open Stability

theorem stability_center (μ : Law) (hμ : admissible μ) :
    Continuous (cost μ) ∧ Tendsto (cost μ) (cocompact X) atTop ∧
    (∃ z, cost μ z = J μ) ∧ ∀ z, cost μ z = J μ →
      fderiv ℝ (cost μ) z = 0 ∧ (∫ a, (1 + ‖z-a‖^2)⁻¹ • (z-a) ∂μ) = 0 := by sorry

theorem stability_center_ball (μ : Law) (hμ : admissible μ) (z : X) (hz : cost μ z = J μ) :
    0 ≤ J μ ∧ Real.exp (-J μ) ≤ M μ z ∧
    (∀ v : X, ‖v‖ ≤ 1 →
      Real.exp (-J μ) * gMeasure μ (z+v)^2 ≤ (∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ) ∧
      (∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ) = 1 - (1-‖v‖^2) * M μ z ∧
      gMeasure μ (z+v)^2 ≤ Real.exp (J μ) - 1 + ‖v‖^2) ∧
    (J μ < Real.log 2 →
      Metric.closedBall z (Real.sqrt (2-Real.exp (J μ))) ⊆ measureSolid μ 1) := by sorry

theorem stability_scalar_limits :
    (∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t ∈ Set.Icc 0 δ,
      |(1 - Real.sqrt (2 - Real.exp t)) - t/2| ≤ C*t^2) ∧
    Tendsto (fun d : ℝ => -Real.log (1-d)/d) (𝓝[>] 0) (𝓝 1) := by sorry

theorem stability_compact_piece (μ : Law) (hμ : admissible μ)
    (hD : 0 < deficit μ 1) (hD' : deficit μ 1 < 1) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ measureSolid μ 1 ∧
      omega 3 * Real.exp (-gamma μ - (gamma μ)^2) ≤ vol K := by sorry

theorem stability_log_moment (ν : Law) (hν : admissible ν) (c : ℝ) (hc : 0 < c)
    (hpot : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) (a : X) :
    ν {a} = 0 ∧ Integrable (fun x => Real.log (dist x a)) ν ∧ Real.log c ≤ g ν a := by sorry

theorem stability_fubini (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (K : Set X) (hK : IsCompact K) (hsub : K ⊆ measureSolid μ 1) (hνK : ν Kᶜ = 0)
    (c : ℝ) (hc : 0 < c) (hpot : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) :
    Integrable (fun p : X × X => Real.log (dist p.1 p.2)) (ν.prod μ) ∧
    (∀ᵐ x ∂ν, 0 < gMeasure μ x ∧ Real.log (gMeasure μ x) = ∫ a, Real.log (dist x a) ∂μ) ∧
    (∫ a, g ν a ∂μ) = (∫ x, Real.log (gMeasure μ x) ∂ν) ∧
    (∫ a, g ν a ∂μ) ≤ 0 ∧ c ≤ 1 := by sorry

theorem stability_piece_bounds (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) (hD : 0 < deficit μ 1) (hD' : deficit μ 1 < 1) :
    ∃ (K : Set X) (ν : Law), IsCompact K ∧ K ⊆ measureSolid μ 1 ∧
      omega 3 * Real.exp (-gamma μ - (gamma μ)^2) ≤ vol K ∧ equilibrium K ν ∧
      0 < capRadius K ∧ capRadius K ≤ 1 ∧ (vol K / omega 3) ^ (1/3:ℝ) ≤ capRadius K ∧
      0 ≤ beta K ∧ beta K ≤ (gamma μ + (gamma μ)^2)/3 := by sorry

theorem stability_compact_comparison (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) (K : Set X) (hK : IsCompact K) (hvol : 0 < vol K)
    (hsub : K ⊆ measureSolid μ 1) :
    volume K < ⊤ ∧ 0 < capRadius K ∧ capRadius K ≤ 1 ∧ vol K ≤ omega 3 * capRadius K ^ 3 := by sorry

theorem stability_measure_volume (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) :
    volume (measureSolid μ 1) < ⊤ ∧ vol (measureSolid μ 1) ≤ omega 3 := by sorry

theorem stability_rescale_dist (c : ℝ) (hc : 0 < c) (x a : X) :
    newtonKernel (c⁻¹ • x) (c⁻¹ • a) = ENNReal.ofReal c * newtonKernel x a ∧
    (x ≠ a → Real.log (dist (c⁻¹ • x) (c⁻¹ • a)) = Real.log (dist x a) - Real.log c) := by sorry

theorem stability_normalize (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hp : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) (havg : (∫ a, g ν a ∂μ) ≤ 0) :
    (∀ a, potential (scaled c ν) a ≤ 1 ∧ 0 ≤ g (scaled c ν) a) ∧
    (∫ a, g (scaled c ν) a ∂(scaled c μ)) ≤ -Real.log c ∧
    ∃ p : X, g (scaled c ν) p ≤ -Real.log c + ε ∧
      g (shifted p (scaled c ν)) 0 = g (scaled c ν) p ∧
      (∀ a, potential (shifted p (scaled c ν)) a ≤ 1) ∧
      (∫ a, g (shifted p (scaled c ν)) a ∂(shifted p (scaled c μ))) ≤ -Real.log c ∧
      ∀ x a : X, dist (x-p) (a-p) = dist x a := by sorry

theorem stability_phi_shape :
    (∀ s : ℝ, 0 < s → 0 ≤ phi s ∧ (phi s = 0 ↔ s = 1)) ∧
    Tendsto phi (𝓝[>] 0) atTop ∧ Tendsto phi atTop atTop := by sorry

theorem stability_phi_integral (ν : Law) (hν : admissible ν) (h : ∀ a, potential ν a ≤ 1) (a : X) :
    Integrable (fun x => phi (dist x a)) ν ∧ 0 ≤ (∫ x, phi (dist x a) ∂ν) ∧
      (∫ x, phi (dist x a) ∂ν) ≤ g ν a := by sorry

theorem stability_annulus_mass (ν : ℕ → Law) (hn : Normalized ν) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun j => ν j (ann δ)) atTop (𝓝 1) := by sorry

theorem stability_weak_limit (ν : ℕ → Law) (hn : Normalized ν) :
    IsTightMeasureSet (Set.range ν) ∧
    ∀ (k : ℕ → ℕ) (limLaw : Law), StrictMono k → IsProbabilityMeasure limLaw →
      weak (ν ∘ k) limLaw → limLaw (Metric.sphere 0 1)ᶜ = 0 ∧
      (∀ a, potential limLaw a ≤ 1) ∧ energy limLaw ≤ 1 := by sorry

theorem stability_sphere_limit (uniqueEq : EqUnique) (ballLaw : BallLaw) (ν : ℕ → Law) (hn : Normalized ν) :
    (IsProbabilityMeasure sigma ∧ energy sigma = 1) ∧
    (∀ limLaw : Law, IsProbabilityMeasure limLaw → limLaw (Metric.sphere 0 1)ᶜ = 0 →
      1 ≤ energy limLaw ∧ (energy limLaw = 1 → limLaw = sigma)) ∧ weak ν sigma := by sorry

theorem stability_spherical_radial (a : X) : g sigma a = H ‖a‖ := by sorry

theorem stability_radial_lap (s : ℝ) (hs : s ∈ Set.Ioo 0 1) :
    radialLap H s = (∫ θ, (dist θ (s • e₁))⁻¹ ^ 2 ∂sigma) ∧
    (1+s^2)⁻¹ ≤ radialLap H s ∧
    radialLap comparison s = (1+s^2)⁻¹ - (2/3 : ℝ)*s^2/(1+s^2)^2 := by sorry

theorem stability_radial_gap :
    H 0 = 0 ∧ deriv H 0 = 0 ∧ comparison 0 = 0 ∧ deriv comparison 0 = 0 ∧
    StrictMonoOn (fun s => H s - comparison s) (Set.Icc 0 1) ∧ ContinuousAt H 1 ∧
    Integrable (fun θ => Real.log (dist θ e₁)) sigma ∧
    ∀ θ : X, ‖θ‖ = 1 → ∀ s : ℝ, dist θ (s • e₁)^2 = (1-s)^2 + s * dist θ e₁ ^ 2 := by sorry

theorem stability_sphere_H :
    (∀ s : ℝ, 1 < s → H s = Real.log s + H (1/s) ∧
      H s - comparison s = H (1/s) - comparison (1/s) + (2/3 : ℝ)*Real.log s) ∧
    ∀ s : ℝ, 0 < s → comparison s < H s := by sorry

theorem stability_truncation :
    (∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Ioo (0:ℝ) 1, |Real.log s| ≤ C / Real.sqrt s) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Law), admissible ν → (∀ a, potential ν a ≤ 1) →
      ∀ a : X, ∀ η ∈ Set.Ioo (0:ℝ) 1,
      0 ≤ (∫ x, Real.log (max η (dist x a)) ∂ν) - g ν a ∧
      (∫ x, Real.log (max η (dist x a)) ∂ν) - g ν a ≤ C * Real.sqrt η := by sorry

theorem stability_moving_center (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (a : X) (ha : a ≠ 0) (p : ℕ → X) (hp : Tendsto p atTop (𝓝 a)) :
    weak (fun j => shifted (p j) (ν j)) (shifted a sigma) ∧
    (∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      (∫ x, Real.log (max η (dist x a)) ∂sigma) - ε ≤
        ∫ x, Real.log (max η (dist x (p j))) ∂(ν j)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, H ‖a‖ - ε ≤ g (ν j) (p j) := by sorry

theorem stability_compact_gap (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ A : ℝ) (hδ : 0 < δ) (hA : δ < A) :
    ∀ᶠ j in atTop, ∀ a : X, δ ≤ ‖a‖ → ‖a‖ ≤ A → L a / 6 ≤ g (ν j) a := by sorry

theorem stability_exterior (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    Tendsto (fun j => ν j (Metric.ball 0 2)) atTop (𝓝 1) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → (max 0 (-Real.log s))^2 ≤ C/s) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ j (a : X), 3 < ‖a‖ →
      ((ν j (Metric.ball 0 2)).toReal * Real.log (‖a‖-2)
        - C * Real.sqrt ((ν j (Metric.ball 0 2)ᶜ).toReal)) ≤ g (ν j) a) ∧
    Tendsto (fun r : ℝ => Real.log (r-2)/Real.log (1+r^2)) atTop (𝓝 (1/2)) ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, ∀ a : X, δ ≤ ‖a‖ → L a / 6 ≤ g (ν j) a := by sorry

theorem stability_hessian_kernel :
    deriv phi 1 = 0 ∧ deriv (deriv phi) 1 = 1 ∧
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioo (0:ℝ) (1/8), ∀ x ∈ ann δ, ∀ a : X, ‖a‖ ≤ δ →
      |dist x a - 1| ≤ 2*δ ∧ ContDiffAt ℝ 2 (fun y : X => phi (dist x y)) a ∧
      ∀ u v : X, |hess (fun y => phi (dist x y)) a u v -
        inner ℝ (direction x) u * inner ℝ (direction x) v| ≤ C*δ*‖u‖*‖v‖ := by sorry

theorem stability_annular_second_moment (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) (1/8)) :
    sigma (frontier (ann δ)) = 0 ∧ ∀ u v : X,
      Tendsto (fun j => ∫ x in ann δ, inner ℝ (direction x) u * inner ℝ (direction x) v ∂(ν j))
        atTop (𝓝 (inner ℝ u v / 3)) := by sorry

theorem stability_annular_curvature (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    (∀ (j : ℕ) (δ : ℝ) (a : X), 0 ≤ F (ν j) δ a ∧ F (ν j) δ a ≤ g (ν j) a) ∧
    ∃ (C δ₀ : ℝ), 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1/8 ∧
      ∀ δ ∈ Set.Ioo (0:ℝ) δ₀, ∃ b : ℕ → ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, 1/6 - C*δ - ε ≤ b j) ∧
      (∀ᶠ j in atTop, 0 < b j ∧ ∀ a ∈ Metric.closedBall (0:X) δ,
        ContDiffAt ℝ 2 (F (ν j) δ) a ∧
        ∀ v : X, 2*b j * ‖v‖^2 ≤ hess (F (ν j) δ) a v v) := by sorry

theorem stability_trial_min (ν : ℕ → Law) (hn : Normalized ν)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) (1/8)) (b : ℕ → ℝ)
    (hb : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ b j)
    (hh : ∀ᶠ j in atTop, ∀ a ∈ Metric.closedBall (0:X) δ,
      ContDiffAt ℝ 2 (F (ν j) δ) a ∧ ∀ v : X, 2*b j * ‖v‖^2 ≤ hess (F (ν j) δ) a v v) :
    ∃ z : ℕ → X, (∀ j, z j ∈ Metric.closedBall 0 δ ∧
      ∀ a ∈ Metric.closedBall (0:X) δ, F (ν j) δ (z j) ≤ F (ν j) δ a ∧
        0 ≤ (fderiv ℝ (F (ν j) δ) (z j)) (a-z j)) ∧
    (∀ᶠ j in atTop, b j * ‖z j‖^2 ≤ g (ν j) 0 ∧
      ∀ a ∈ Metric.closedBall (0:X) δ, F (ν j) δ (z j) + b j * ‖a-z j‖^2 ≤ g (ν j) a) ∧ Tendsto z atTop (𝓝 0) := by sorry

theorem stability_shift_loss :
    (∀ a : X, L a ≤ ‖a‖^2) ∧ LipschitzWith 1 L ∧
    (∀ (δ : ℝ) (z a : X), 0 < δ → δ ≤ ‖a‖ →
      L (a-z) ≤ L a + ‖z‖ ∧ L a + ‖z‖ ≤ (1 + ‖z‖ / Real.log (1+δ^2))*L a) ∧
    ∀ (δ : ℝ) (z : ℕ → X), 0 < δ → Tendsto z atTop (𝓝 0) →
      Tendsto (fun j => ‖z j‖ / Real.log (1+δ^2)) atTop (𝓝 0) := by sorry

theorem stability_join_at_center (ν : Law) (δ b : ℝ) (z : X) (hδ : 0 < δ) (hb : 0 ≤ b)
    (hi : ∀ a : X, ‖a‖ ≤ δ → b*‖a-z‖^2 ≤ g ν a)
    (ho : ∀ a : X, δ ≤ ‖a‖ → L a/6 ≤ g ν a) :
    let q := ‖z‖ / Real.log (1+δ^2)
    (∀ a : X, ‖a‖ ≤ δ → b*L (a-z) ≤ g ν a) ∧
      (∀ a : X, δ ≤ ‖a‖ → L (a-z) / (6*(1+q)) ≤ g ν a) ∧
      ∀ a : X, min b (1/(6*(1+q))) * L (a-z) ≤ g ν a := by sorry

theorem stability_common_center (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    (∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ δ ∈ Set.Ioo (0:ℝ) δ₀,
      ∃ z : ℕ → X, (∀ j, ‖z j‖ ≤ δ) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a : X, (1/6-C*δ-ε)*L (a-z j) ≤ g (ν j) a) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∃ z : X, ∀ a : X, (1/6-ε)*L (a-z) ≤ g (ν j) a := by sorry

theorem stability_unscale_cost (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (hp : ∀ a, potential ν a ≤ 1) (c b β : ℝ) (p z : X) (hc : 0 < c) (hc' : c ≤ 1)
    (hb : 0 < b) (hz : ∀ a, b*L (a-z) ≤ g ν a)
    (havg : (∫ a, g ν a ∂(shifted p (scaled c μ))) ≤ β) :
    b * cost (shifted p (scaled c μ)) z ≤ β ∧
    cost μ (c • (z+p)) ≤ cost (shifted p (scaled c μ)) z ∧ b * J μ ≤ β := by sorry

theorem stability_cost_upper (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (uniqueEq : EqUnique) (ballLaw : BallLaw) :
    (∀ μ : ℕ → Law, (∀ j, admissible (μ j) ∧ 0 < deficit (μ j) 1 ∧ deficit (μ j) 1 < 1) →
      Tendsto (fun j => gamma (μ j)) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, J (μ j) ≤ (2+ε)*gamma (μ j)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ ∀ μ : Law, admissible μ →
      0 < deficit μ 1 → deficit μ 1 ≤ h → J μ ≤ (2+ε)*gamma μ := by sorry

theorem stability_uniform_upper (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (uniqueEq : EqUnique) (ballLaw : BallLaw) (R : ℝ) (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ ∀ μ : Law, admissible μ →
      0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε) * deficit μ R := by sorry

theorem stability_normalized_example (frost : Frostman) (ballLaw : BallLaw) :
    Normalized (fun _ => sigma) := by sorry

end ErdosVolume

module

public import Challenge.Defs

@[expose] public section
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open MeasureTheory Filter Set Metric

open scoped Topology ENNReal BigOperators Pointwise

namespace ErdosVolume

def axis : Space 3 := EuclideanSpace.single 0 (1 : ℝ)

def pairMarks (t : ℝ) : Fin 2 → Space 3 := ![t • axis, (-t) • axis]

def pairLaw (t : ℝ) := atomic (pairMarks t) (fun _ => (1/2 : ℝ))

def equalAtomic (μ : Measure (Space 3)) : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (a : Fin n → Space 3), μ = atomic a (fun _ => ((n : ℝ)⁻¹))

def ratio (μ : Measure (Space 3)) (R : ℝ) : ℝ :=
  (1 - inradius (measureSolid μ R) / R) / deficit μ R

def worstRatio (P : Measure (Space 3) → Prop) (R h : ℝ) : ℝ :=
  sSup {v | ∃ μ, admissible μ ∧ P μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧ v = ratio μ R}

def transverse (x : Space 3) : ℝ := Real.sqrt (x 1 ^ 2 + x 2 ^ 2)

def boundarySq (t u : ℝ) : ℝ :=
  t^2*(2*u^2-1) + Real.sqrt (1-4*t^4*u^2*(1-u^2))

def sphereLaw : Measure (sphere (0 : Space 3) 1) :=
  let S := (volume : Measure (Space 3)).toSphere
  (S univ)⁻¹ • S

theorem atomic_g {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (hw : ValidWeights w) (x : Space d) : gMeasure (atomic a w) x = G a w x := by sorry

theorem trunc_log_continuous (μ : Measure (Space 3)) (hμ : admissible μ) (k : ℕ) :
    Continuous (fun x => ∫ a, Real.log (max (dist x a) (Real.exp (-(k : ℝ)))) ∂μ) := by sorry

theorem measureSolid_regular (μ : Measure (Space 3)) (hμ : admissible μ)
    (R : ℝ) (hR : 0 < R) :
    MeasurableSet (measureSolid μ R) ∧ Bornology.IsBounded (measureSolid μ R) := by sorry

theorem dilated_g (μ : Measure (Space 3)) (hμ : admissible μ) (x : Space 3)
    (c : ℝ) (hc : 0 < c) :
    gMeasure (μ.map (fun a => c • a)) (c • x) = c * gMeasure μ x := by sorry

theorem scale_identities (μ : Measure (Space 3)) (hμ : admissible μ) (R : ℝ) (hR : 0 < R) :
    let μ' := μ.map (fun a => R⁻¹ • a)
    (∀ x, gMeasure μ' (R⁻¹ • x) = gMeasure μ x / R) ∧
    inradius (measureSolid μ' 1) = inradius (measureSolid μ R) / R ∧
    deficit μ' 1 = deficit μ R := by sorry

theorem axis_dist_sq (x : Space 3) (s : ℝ) :
    dist x (s • axis)^2 = (x 0 - s)^2 + (transverse x)^2 := by sorry

theorem pair_squared_product (t : ℝ) (x : Space 3) :
    (dist x (t • axis) * dist x ((-t) • axis))^2 =
      ((transverse x)^2 + t^2)^2 + 2*(x 0)^2*((transverse x)^2-t^2) + (x 0)^4 := by sorry

theorem pair_mem_iff (t : ℝ) (x : Space 3) :
    x ∈ measureSolid (pairLaw t) 1 ↔ dist x (t • axis) * dist x ((-t) • axis) ≤ 1 := by sorry

theorem pair_squared_mean (x : Space 3) (t : ℝ) :
    (dist x (t • axis)^2 + dist x ((-t) • axis)^2)/2 = ‖x‖^2+t^2 := by sorry

theorem pair_outside_cylinder (x : Space 3) (t : ℝ) (ht : 0 < t) (ht' : t < 1/Real.sqrt 2)
    (hx : 1-t^2 < (transverse x)^2) : 1 < (dist x (t • axis)*dist x ((-t) • axis))^2 := by sorry

theorem pair_ball_cylinder (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    closedBall 0 (Real.sqrt (1-t^2)) ⊆ measureSolid (pairLaw t) 1 ∧
    measureSolid (pairLaw t) 1 ⊆ {x | transverse x ≤ Real.sqrt (1-t^2)} := by sorry

theorem cylinder_ball_radius (B r : ℝ) (z : Space 3) (hr : 0 < r)
    (hsub : ball z r ⊆ {x | transverse x ≤ B}) : r ≤ B := by sorry

theorem pair_inradius (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    inradius (measureSolid (pairLaw t) 1) = Real.sqrt (1-t^2) := by sorry

theorem pair_radial (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2)
    (θ : Space 3) (hθ : ‖θ‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    (r • θ ∈ measureSolid (pairLaw t) 1 ↔ r^2 ≤ boundarySq t (θ 0)) ∧
    (0 < boundarySq t (θ 0)) ∧
    (∀ q : ℝ, 0 < q → ((q+t^2)^2 - 4*q*t^2*(θ 0)^2 = 1 ↔ q = boundarySq t (θ 0))) := by sorry

theorem uniform_radial_error :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t u : ℝ, 0 < t → t < δ → |u| ≤ 1 →
    |boundarySq t u - (1 + t^2*(2*u^2-1))| ≤ C*t^4 := by sorry

section PairVolume

open scoped Pointwise

theorem axial_second_moment :
    (∫ θ, ((θ : Space 3) 0)^2 ∂sphereLaw) = 1/3 := by sorry

theorem pair_volume_fraction (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    volume (measureSolid (pairLaw t) 1) < ⊤ ∧ vol (measureSolid (pairLaw t) 1) / omega 3 =
      ∫ θ, (Real.sqrt (boundarySq t ((θ : Space 3) 0)))^3 ∂sphereLaw := by sorry

theorem pair_asymptotics :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    |deficit (pairLaw t) 1 - t^2/2| ≤ C*t^4 ∧
    |(1-inradius (measureSolid (pairLaw t) 1)) - t^2/2| ≤ C*t^4 := by sorry

theorem pair_ratio_limit : Tendsto (fun t : ℝ => ratio (pairLaw t) 1) (𝓝[>] 0) (𝓝 1) := by sorry

end PairVolume

theorem sharp_coefficient (R : ℝ) (hR : 0 < R) (c : ℝ) (hc : c < 1) (h : ℝ) (hh : 0 < h) :
    ∃ μ, admissible μ ∧ equalAtomic μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧
       c * deficit μ R < 1 - inradius (measureSolid μ R) / R := by sorry

theorem worst_ratio_limit (R : ℝ) (P : Measure (Space 3) → Prop)
    (hupper : ∀ ε > (0:ℝ), ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R)
    (hlower : ∀ c : ℝ, c < 1 → ∀ h > 0, ∃ μ, admissible μ ∧ P μ ∧
      0 < deficit μ R ∧ deficit μ R ≤ h ∧ c*deficit μ R < 1-inradius (measureSolid μ R)/R) :
    Tendsto (worstRatio P R) (𝓝[>] 0) (𝓝 1) := by sorry

theorem pair_cubic_radial_mean :
    (∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ θ : sphere (0 : Space 3) 1,
        |(Real.sqrt (boundarySq t ((θ : Space 3) 0)))^3 -
          (1+(3/2:ℝ)*t^2*(2*((θ : Space 3) 0)^2-1))| ≤ C*t^4) ∧
    (∫ θ : sphere (0 : Space 3) 1, 2*((θ : Space 3) 0)^2-1 ∂sphereLaw) = -(1/3:ℝ) := by sorry

end ErdosVolume

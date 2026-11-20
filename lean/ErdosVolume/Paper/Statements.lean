import ErdosVolume.Capacity
import ErdosVolume.Flux
import ErdosVolume.Sharpness

/-! Principal statements and additional printed claims, with proof obligations exposed.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BigOperators RealInnerProductSpace
namespace ErdosVolume.Paper

/-- Theorem 1: the full printed target, including equality for repeated marks. -/
theorem finite_volume {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
      (vol (solid a w R) = omega d * R ^ d ↔ ∀ i j, a i = a j) := by sorry

/-- Main text lines 49–55, 316–318: co-located marks give the closed ball itself. -/
theorem coincident_solid {d n : ℕ} (w : Fin n → ℝ) (hw : ValidWeights w)
    (z : Space d) (R : ℝ) :
    (∀ x : Space d, G (fun _ => z) w x = dist x z) ∧
    solid (fun _ => z) w R = closedBall z R := by
  obtain ⟨hG, hK⟩ := Flux.coincident (fun _ : Fin n => z) w hw (fun _ => rfl) (R := R)
  exact ⟨fun x => congrFun hG x, hK⟩

def sphereProbability {d : ℕ} (a : Space d) (r : ℝ) : Measure (Space d) :=
  let S := (volume : Measure (Space d)).toSphere
  Measure.map (fun θ : sphere (0 : Space d) 1 => a + r • (θ : Space d)) ((S univ)⁻¹ • S)

/-- Clark–Laugesen, Appendix A, ball equilibrium law, translated to the chosen center. -/
def EquilibriumBallLaw (d : ℕ) : Prop :=
  ∀ (z : Space d) (r : ℝ), 0 < r →
    equilibrium (closedBall z r) (sphereProbability z r) ∧
    ∀ ν, equilibrium (closedBall z r) ν → ν = sphereProbability z r

/-- Main text lines 328–335. The ball's logarithmic moment at its center. -/
theorem ball_log_moment {d : ℕ} (hd : 3 ≤ d) (hb : EquilibriumBallLaw d)
    (a : Space d) (r : ℝ) (hr : 0 < r) (ν : Measure (Space d))
    (hν : equilibrium (closedBall a r) ν) :
    ∫ x, Real.log (dist x a) ∂ν = Real.log r := by
  letI : IsProbabilityMeasure ν := hν.1
  have hrad : ∀ᵐ x ∂ν, dist x a = r := by
    rw [(hb a r hr).2 ν hν]
    unfold sphereProbability
    apply (ae_map_iff (by fun_prop) (isClosed_eq (continuous_id.dist continuous_const) continuous_const).measurableSet).2
    apply Filter.Eventually.of_forall
    intro θ
    have hnorm : ‖(θ : Space d)‖ = 1 := by simpa using θ.property
    simp [dist_eq_norm, norm_smul, hnorm, abs_of_pos hr]
  calc
    _ = ∫ _ : Space d, Real.log r ∂ν := integral_congr_ae (hrad.mono fun _ hx => congrArg Real.log hx)
    _ = _ := by simp

/-- Main text lines 333–340: logarithm of the finite weighted product a.e. -/
theorem integral_log_product {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (ν : Measure (Space d)) (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    ∫ x, Real.log (G a w x) ∂ν = ∑ i, w i * ∫ x, Real.log (dist x (a i)) ∂ν :=
  integral_log_G a w ν ha hi

/-- Main text lines 349–354: equality in a positive weighted sum propagates to each mark. -/
theorem each_moment_eq {n : ℕ} (w v : Fin n → ℝ) (m : ℝ) (hw : ValidWeights w)
    (hl : ∀ i, m ≤ v i) (hu : ∑ i, w i * v i ≤ m) : ∀ i, v i = m :=
  weighted_equality w v m hw hl hu

/-- Main text lines 354–363: squared distance at a supporting direction. -/
theorem extreme_distance {d : ℕ} (a b u : Space d) (hu : ‖u‖ = 1)
    (hab : b ≠ a) (hproj : 0 ≤ inner ℝ u (a-b)) (R : ℝ) (hR : 0 < R) :
    dist (a + R • u) b ^ 2 = R^2 + 2*R*(inner ℝ u (a-b)) + ‖a-b‖^2 ∧
    R < dist (a + R • u) b := by
  have hsq : dist (a + R • u) b ^ 2 = R^2 + 2*R*(inner ℝ u (a-b)) + ‖a-b‖^2 := by
    rw [dist_eq_norm, show a + R • u - b = R • u + (a-b) by abel,
      norm_add_sq_real, real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hu]
    ring
  refine ⟨hsq, ?_⟩
  have hn := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm))
  nlinarith [mul_nonneg hR.le hproj, dist_nonneg (x := a + R • u) (y := b)]

/-- The variational compact-to-open approximation can be proved by enlarging a smooth test
function slightly and using its open superlevel as a neighborhood of K. -/
theorem compact_capacity_outer {d : ℕ} (K : Set (Space d)) (hK : IsCompact K) :
    dirichletCap K = sInf {v | ∃ U : Set (Space d), IsOpen U ∧ Bornology.IsBounded U ∧
      K ⊆ U ∧ dirichletCap U = v} := dirichlet_outer K

/-- Inradius lines 32–39: Euclidean unit ball normalization. -/
theorem omega_three : omega 3 = 4 * Real.pi / 3 := by
  rw [omega, vol, EuclideanSpace.volume_ball_fin_three]
  simp [ENNReal.toReal_ofReal (show 0 ≤ Real.pi * 4 / 3 by positivity), mul_comm]

private theorem ordinary_product_solid {n : ℕ} (hn : 0 < n) (a : Fin n → Space 3) :
    {x | ∏ i, dist x (a i) ≤ 1} = solid a (fun _ => ((n:ℝ)⁻¹)) 1 := by
  ext x
  change (∏ i, dist x (a i)) ≤ 1 ↔ (∏ i, dist x (a i) ^ ((n:ℝ)⁻¹)) ≤ 1
  rw [Real.finsetProd_rpow _ _ (fun _ _ => dist_nonneg)]
  simpa only [Real.one_rpow] using (Real.rpow_le_rpow_iff (x := ∏ i, dist x (a i)) (Finset.prod_nonneg (fun _ _ => dist_nonneg))
    zero_le_one (inv_pos.2 (by exact_mod_cast hn : 0 < (n:ℝ)))).symm

private theorem uniform_weights {n : ℕ} (hn : 0 < n) : ValidWeights (fun _ : Fin n => (n:ℝ)⁻¹) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  exact ⟨fun _ => inv_pos.2 hn',by simp [hn'.ne']⟩

/-- The motivating three-dimensional product uses ordinary (unweighted) distances. -/
theorem erdos_product {n : ℕ} (hn : 0 < n) (a : Fin n → Space 3) :
    let E := {x : Space 3 | ∏ i, dist x (a i) ≤ 1}
    volume E < ⊤ ∧ vol E ≤ 4 * Real.pi / 3 ∧ (vol E = 4*Real.pi/3 ↔ ∀ i j, a i = a j) := by
  dsimp only
  rw [ordinary_product_solid hn a]
  simpa [omega_three] using finite_volume (by decide) hn a _ (uniform_weights hn) 1 one_pos

/-- The motivating three-dimensional consequence with the capacity route's inputs visible. -/
theorem erdos_product_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3)
    (hM : EquilibriumMomentFact 3) (hS : EquilibriumSphereFact 3)
    {n : ℕ} (hn : 0 < n) (a : Fin n → Space 3) :
    let E := {x : Space 3 | ∏ i, dist x (a i) ≤ 1}
    volume E < ⊤ ∧ vol E ≤ 4 * Real.pi / 3 ∧ (vol E = 4*Real.pi/3 ↔ ∀ i j, a i = a j) := by
  dsimp only
  rw [ordinary_product_solid hn a]
  simpa [omega_three] using volume_capacity (by decide) hn hO hN hB hE hM hS
    a _ (uniform_weights hn) 1 one_pos

/-- Main text lines 30–35: sharp uniform bound and sharpness in the same normalization.
The explicit epsilon statement and sharpness rows remain individually auditable. -/
theorem first_order_radius (R : ℝ) (hR : 0 < R) :
    (∀ ε > (0 : ℝ), ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R) ∧
    (∀ c : ℝ, c < 1 → ∀ h > 0, ∃ μ, admissible μ ∧ equalAtomic μ ∧
      0 < deficit μ R ∧ deficit μ R ≤ h ∧
      c*deficit μ R < 1 - inradius (measureSolid μ R) / R) := by
  exact ⟨uniform_upper R hR, sharp_coefficient R hR⟩

end ErdosVolume.Paper

import ErdosVolume.Paper.Illustrations

/-! Volume comparisons and the critical set in the distance-product paper.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ENNReal BigOperators

namespace ErdosVolume.Paper

/-- At unit threshold two distinct marks give strict volume loss. -/
theorem distinct_pair_strict_volume_given
    (hO : OpenIsoFact 3) (hN : CapacityNormalization 3) (hB : BallCapacityFact 3)
    (hE : EquilibriumExistence 3) (hM : EquilibriumMomentFact 3) (hS : EquilibriumSphereFact 3)
    (p q : Space 3) (hpq : p ≠ q) :
    let E := {x : Space 3 | dist x p * dist x q ≤ 1}
    volume E < ⊤ ∧ vol E < 4 * Real.pi / 3 := by
  let a : Fin 2 → Space 3 := ![p, q]
  have ⟨hfin, hle, heq⟩ := erdos_product_given hO hN hB hE hM hS (n := 2) (by decide) a
  have hne : ¬ ∀ i j, a i = a j := fun h => hpq (h 0 1)
  simpa [Fin.prod_univ_two, a] using And.intro hfin (lt_of_le_of_ne hle (fun h => hne (heq.mp h)))

/-- One coordinate partial witnesses the null-set argument
on the complement of the charges. -/
theorem analytic_partial_zero_set {d n : ℕ} (hd : 3 ≤ d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (hZ : Flux.AnalyticNull d) :
    IsConnected (Flux.off a) ∧ ∃ k : Fin d,
      let D := fun x => fderiv ℝ (Flux.u a w) x (EuclideanSpace.single k 1)
      AnalyticOnNhd ℝ D (Flux.off a) ∧ (∃ x ∈ Flux.off a, D x ≠ 0) ∧
      volume {x | x ∈ Flux.off a ∧ D x = 0} = 0 ∧
      {x | x ∈ Flux.off a ∧ gradient (Flux.u a w) x = 0} ⊆ {x | x ∈ Flux.off a ∧ D x = 0} := by
  obtain ⟨hc, k, x, hx, hDx⟩ := Flux.critical_witness a w hd hw
  let v : Space d := EuclideanSpace.single k 1
  let D := fun y => fderiv ℝ (Flux.u a w) y v
  have hU := (Flux.smooth_harmonic a w hd hw).1
  have hD : AnalyticOnNhd ℝ D (Flux.off a) := fun y hy =>
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp (hU y hy).fderiv
  have hopen : IsOpen (Flux.off a) := (Set.finite_range a).isClosed.isOpen_compl
  refine ⟨hc, k, hD, ⟨x, hx, hDx⟩, hZ _ D hopen hc hD ⟨x, hx, hDx⟩, ?_⟩
  rintro y ⟨hy, hg⟩
  refine ⟨hy, ?_⟩
  change fderiv ℝ (Flux.u a w) y v = 0
  rw [← inner_gradient_left, hg, inner_zero_left]

/-- Outside the cylinder the transverse term
alone makes the squared distance product strictly greater than one. -/
theorem outside_cylinder_product_bounds (x : Space 3) (t : ℝ)
    (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) (hout : 1 - t^2 < (transverse x)^2) :
    t^2 < 1/2 ∧ t^2 < (transverse x)^2 ∧
    1 < ((transverse x)^2 + t^2)^2 ∧
    ((transverse x)^2 + t^2)^2 ≤ (dist x (t • axis) * dist x ((-t) • axis))^2 := by
  have ht' := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mp hsmall
  have hs := (sq_lt_sq₀ (mul_nonneg ht.le (Real.sqrt_nonneg 2)) zero_le_one).mpr ht'
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), one_pow] at hs
  have hhalf : t^2 < 1/2 := by linarith
  have hb : t^2 < (transverse x)^2 := by linarith
  have hsum : 1 < (transverse x)^2 + t^2 := by linarith
  refine ⟨hhalf, hb, ?_, ?_⟩
  · simpa only [one_pow] using (sq_lt_sq₀ zero_le_one (by positivity)).mpr hsum
  · rw [pair_squared_product]
    have hcross : 0 ≤ 2*(x 0)^2*((transverse x)^2-t^2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hb.le)
    linarith [show 0 ≤ (x 0)^4 by positivity]

end ErdosVolume.Paper

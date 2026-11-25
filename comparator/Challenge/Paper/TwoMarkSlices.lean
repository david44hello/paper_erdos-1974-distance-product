import Challenge.Paper.Illustrations
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise
namespace ErdosVolume.Paper

theorem two_marks_on_line :
    {x : ℝ | dist x (-1) * dist x 1 ≤ 1} = {x | |x^2-1| ≤ 1} ∧
    {x : ℝ | |x^2-1| ≤ 1} = Icc (-Real.sqrt 2) (Real.sqrt 2) ∧
    volume.real {x : ℝ | dist x (-1) * dist x 1 ≤ 1} = 2 * Real.sqrt 2 ∧
    volume.real {x : ℝ | dist x 0 * dist x 0 ≤ 1} = 2 ∧ 2 < 2 * Real.sqrt 2 := by sorry

theorem pair_intercepts (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∀ s : ℝ, s • axis ∈ measureSolid (pairLaw t) 1 ↔ |s| ≤ Real.sqrt (1+t^2)) ∧
    (∀ x : Space 3, x 0 = 0 →
      (x ∈ measureSolid (pairLaw t) 1 ↔ transverse x ≤ Real.sqrt (1-t^2))) ∧
    1 < Real.sqrt (1+t^2) ∧ Real.sqrt (1-t^2) < 1 := by sorry

theorem figure_pair_widths :
    let K := measureSolid (pairLaw (3/5)) 1
    (∀ s : ℝ, s • axis ∈ K ↔ |s| ≤ Real.sqrt (34/25)) ∧
    (fun x : Space 3 => x 1) '' K = Icc (-(4/5:ℝ)) (4/5) ∧
    2 < 2 * Real.sqrt (34/25) ∧ (4/5:ℝ) - (-(4/5)) = 8/5 := by sorry

def PlanarTwoMarkBound : Prop :=
  ∀ a b : Space 2,
    volume {z : Space 2 | dist z a * dist z b < 1} ≤ ENNReal.ofReal Real.pi ∧
    (a ≠ b → volume {z : Space 2 | dist z a * dist z b < 1} < ENNReal.ofReal Real.pi)

theorem planar_coincident_disk (a : Space 2) (c : ℝ) (hc : 0 < c) :
    {z : Space 2 | dist z a * dist z a ≤ c} = closedBall a (Real.sqrt c) ∧
    volume {z : Space 2 | dist z a * dist z a ≤ c} = ENNReal.ofReal (Real.pi*c) := by sorry

def planePoint (v : ℝ × ℝ) : Space 2 := WithLp.toLp 2 ![v.1,v.2]

theorem vertical_level_quartic (a b : Space 2) (c x : ℝ) :
    ∃ P : Polynomial ℝ, P.Monic ∧ P.natDegree = 4 ∧
      ∀ y : ℝ, P.eval y = (dist (planePoint (x,y)) a * dist (planePoint (x,y)) b)^2 - c^2 := by sorry

theorem vertical_level_at_most_four (a b : Space 2) (c x : ℝ) :
    let F := {y : ℝ | dist (planePoint (x,y)) a * dist (planePoint (x,y)) b = c}
    F.Finite ∧ F.ncard ≤ 4 := by sorry

theorem planar_pair_level_null (a b : Space 2) (c : ℝ) :
    volume {z : Space 2 | dist z a * dist z b = c} = 0 := by sorry

theorem planar_scaled_closed (hp : PlanarTwoMarkBound) (a b : Space 2) (c : ℝ) (hc : 0 < c) :
    volume {z : Space 2 | dist z a * dist z b ≤ c} ≤ ENNReal.ofReal (Real.pi*c) ∧
    (a ≠ b → volume {z : Space 2 | dist z a * dist z b ≤ c} < ENNReal.ofReal (Real.pi*c)) := by sorry

theorem two_mark_slice_identity (u v h : ℝ) :
    (u^2+h^2)*(v^2+h^2) = (u*v+h^2)^2 + h^2*(u-v)^2 := by sorry

def pairSection (a b : Space 2) (h : ℝ) : Set (Space 2) :=
  {z | ((dist z a)^2+h^2)*((dist z b)^2+h^2) ≤ 1}

theorem pair_section_subset (a b : Space 2) (h : ℝ) :
    pairSection a b h ⊆ {z | dist z a * dist z b ≤ 1-h^2} := by sorry

theorem pair_section_empty (a b : Space 2) (h : ℝ) (hh : 1 < |h|) :
    pairSection a b h = ∅ := by sorry

theorem pair_section_area (hp : PlanarTwoMarkBound) (a b : Space 2) (hab : a ≠ b)
    (h : ℝ) (hh : |h| < 1) :
    volume (pairSection a b h) ≤ volume {z : Space 2 | dist z a * dist z b ≤ 1-h^2} ∧
    volume {z : Space 2 | dist z a * dist z b ≤ 1-h^2} < ENNReal.ofReal (Real.pi*(1-h^2)) := by sorry

def slicePoint (v : ℝ × Space 2) : Space 3 :=
  WithLp.toLp 2 (Fin.cons v.1 (WithLp.ofLp v.2))

def ballSection (h : ℝ) : Set (Space 2) :=
  {z | dist z 0 ^ 2+h^2 ≤ 1}

theorem unit_ball_section_area (h : ℝ) (hh : |h| ≤ 1) :
    ballSection h = closedBall 0 (Real.sqrt (1-h^2)) ∧
    volume (ballSection h) = ENNReal.ofReal (Real.pi*(1-h^2)) := by sorry

theorem spatial_pair_section (a b z : Space 2) (h : ℝ) :
    dist (slicePoint (h,z)) (slicePoint (0,a)) * dist (slicePoint (h,z)) (slicePoint (0,b)) ≤ 1 ↔
      z ∈ pairSection a b h := by sorry

theorem spatial_ball_section (z : Space 2) (h : ℝ) :
    slicePoint (h,z) ∈ closedBall (slicePoint (0,0)) 1 ↔ z ∈ ballSection h := by sorry

theorem distinct_pair_volume_by_slices (hp : PlanarTwoMarkBound) (p q : Space 3) (hpq : p ≠ q) :
    let S := {x : Space 3 | dist x p * dist x q ≤ 1}
    volume S < ⊤ ∧ vol S < 4*Real.pi/3 := by sorry

theorem erdos_product_all_dim_given {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hO : OpenIsoFact d) (hN : CapacityNormalization d) (hB : BallCapacityFact d)
    (hE : EquilibriumExistence d) (hM : EquilibriumMomentFact d) (hS : EquilibriumSphereFact d)
    (a : Fin n → Space d) :
    let E := {x : Space d | ∏ i, dist x (a i) ≤ 1}
    volume E < ⊤ ∧ vol E ≤ omega d ∧ (vol E = omega d ↔ ∀ i j, a i = a j) := by sorry

end ErdosVolume.Paper

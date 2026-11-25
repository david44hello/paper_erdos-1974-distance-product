import Challenge.Paper.Equality
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section

open Set Metric MeasureTheory

namespace ErdosVolume.Paper

def axialPolynomial (s t ρ : ℝ) := (s^2-t^2)^2 + 2*(s^2+t^2)*ρ^2 + ρ^4

theorem pair_axial_polynomial (x : Space 3) (t : ℝ) :
    (dist x (t • axis) * dist x ((-t) • axis))^2 = axialPolynomial (x 0) t (transverse x) := by sorry

theorem transverse_strict (s t : ℝ) : StrictMonoOn (axialPolynomial s t) (Ici 0) := by sorry

abbrev figureSet := measureSolid (pairLaw (5/4)) 1

theorem axial_interval (s : ℝ) :
    s • axis ∈ figureSet ↔ 3/4 ≤ |s| ∧ |s| ≤ Real.sqrt 41 / 4 := by sorry

theorem transverse_segment (x : Space 3) (hx : x ∈ figureSet) :
    segment ℝ x ((x 0) • axis) ⊆ figureSet := by sorry

theorem missing_midplane (x : Space 3) (hx : x ∈ figureSet) : x 0 ≠ 0 := by sorry

def sideMark (s : ℝ) : ℝ := if 0 ≤ s then 5/4 else -(5/4)

theorem joined_to_mark (x : Space 3) (hx : x ∈ figureSet) :
    JoinedIn figureSet x ((sideMark (x 0)) • axis) := by sorry

theorem figure_two_components :
    let pos := (5/4 : ℝ) • axis
    let neg := (-(5/4) : ℝ) • axis
    connectedComponentIn figureSet '' figureSet =
      {connectedComponentIn figureSet pos, connectedComponentIn figureSet neg} ∧
    connectedComponentIn figureSet pos ≠ connectedComponentIn figureSet neg := by sorry

theorem figure_lobe_balls :
    figureSet ⊆ closedBall ((5/4 : ℝ) • axis) (1/2) ∪ closedBall ((-(5/4) : ℝ) • axis) (1/2) := by sorry

theorem figure_volume_loss : volume figureSet < ⊤ ∧ vol figureSet ≤ omega 3 / 4 ∧ vol figureSet < omega 3 := by sorry

theorem figure_ball_cylinder :
    let K := measureSolid (pairLaw (3/5)) 1
    closedBall 0 (4/5) ⊆ K ∧ K ⊆ {x | transverse x ≤ 4/5} ∧ inradius K = 4/5 := by sorry

theorem coalescent_deficits :
    deficit (pairLaw 0) 1 = 0 ∧ 1 - inradius (measureSolid (pairLaw 0) 1) = 0 := by sorry

end ErdosVolume.Paper

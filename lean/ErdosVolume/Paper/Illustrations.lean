import ErdosVolume.Paper.Equality

/-! Geometry of the two-mark figures in the illustrated paper.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open Set Metric MeasureTheory
namespace ErdosVolume.Paper

/-- Figure 1. The squared product in axial coordinate s and transverse radius ρ. -/
def axialPolynomial (s t ρ : ℝ) := (s^2-t^2)^2 + 2*(s^2+t^2)*ρ^2 + ρ^4

theorem pair_axial_polynomial (x : Space 3) (t : ℝ) :
    (dist x (t • axis) * dist x ((-t) • axis))^2 = axialPolynomial (x 0) t (transverse x) := by
  rw [pair_squared_product, axialPolynomial]
  ring

private theorem pair_mem_poly (x : Space 3) (t : ℝ) :
    x ∈ measureSolid (pairLaw t) 1 ↔ axialPolynomial (x 0) t (transverse x) ≤ 1 := by
  rw [pair_mem_iff, ← pair_axial_polynomial]
  simpa using (sq_le_sq₀ (show 0 ≤ dist x (t • axis) * dist x ((-t) • axis) by positivity)
    zero_le_one).symm

theorem transverse_strict (s t : ℝ) : StrictMonoOn (axialPolynomial s t) (Ici 0) := by
  intro u hu v hv huv
  have huv₂ := (sq_lt_sq₀ hu hv).2 huv
  have huv₄ := (sq_lt_sq₀ (sq_nonneg u) (sq_nonneg v)).2 huv₂
  unfold axialPolynomial
  nlinarith [mul_nonneg (add_nonneg (sq_nonneg s) (sq_nonneg t)) (sub_nonneg.mpr huv₂.le)]

private theorem on_axis (s : ℝ) : (s • axis) 0 = s ∧ transverse (s • axis) = 0 := by
  norm_num [axis, transverse, EuclideanSpace.single, PiLp.single_apply, PiLp.smul_apply]

abbrev figureSet := measureSolid (pairLaw (5/4)) 1

theorem axial_interval (s : ℝ) :
    s • axis ∈ figureSet ↔ 3/4 ≤ |s| ∧ |s| ≤ Real.sqrt 41 / 4 := by
  rw [pair_mem_poly, (on_axis s).1, (on_axis s).2, axialPolynomial]
  have hroot := Real.sq_sqrt (show (0:ℝ) ≤ 41 by norm_num)
  have hroot' := Real.sqrt_nonneg (41:ℝ)
  have hcond : (s^2 - (5/4:ℝ)^2)^2 ≤ 1 ↔
      -(1:ℝ) ≤ s^2 - (5/4:ℝ)^2 ∧ s^2 - (5/4:ℝ)^2 ≤ 1 := by
    rw [← abs_le]
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (s^2-(5/4:ℝ)^2)) zero_le_one)
  have hlo := sq_le_sq₀ (show 0 ≤ (3/4:ℝ) by norm_num) (abs_nonneg s)
  have hup := sq_le_sq₀ (abs_nonneg s) (div_nonneg hroot' (by norm_num : (0:ℝ) ≤ 4))
  simp only [sq_abs] at hlo hup
  constructor
  · intro h
    have hh := hcond.1 (by simpa using h)
    exact ⟨hlo.1 (by nlinarith [hh.1]), hup.1 (by nlinarith [hh.2])⟩
  · rintro ⟨hl,hu⟩
    have hh := hcond.2 ⟨by nlinarith [hlo.2 hl], by nlinarith [hup.2 hu]⟩
    simpa using hh

/-- The whole straight transverse segment stays in the solid. -/
theorem transverse_segment (x : Space 3) (hx : x ∈ figureSet) :
    segment ℝ x ((x 0) • axis) ⊆ figureSet := by
  rintro y ⟨a,b,ha,hb,hab,rfl⟩
  have hcoord : (a • x + b • (x 0 • axis)) 0 = x 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, (on_axis (x 0)).1]
    nlinarith [congrArg (fun c : ℝ => c*x 0) hab]
  have hρ : transverse (a • x + b • (x 0 • axis)) = a * transverse x := by
    unfold transverse
    norm_num [axis, EuclideanSpace.single, PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply]
    rw [show (a*x 1)^2 + (a*x 2)^2 = a^2*(x 1^2+x 2^2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha]
  rw [pair_mem_poly, hcoord, hρ]
  exact ((transverse_strict _ _).monotoneOn (mul_nonneg ha (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _) (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith))).trans
      ((pair_mem_poly _ _).1 hx)

theorem missing_midplane (x : Space 3) (hx : x ∈ figureSet) : x 0 ≠ 0 := by
  have h := (axial_interval _).1 (transverse_segment x hx (right_mem_segment ℝ _ _))
  intro hz
  rw [hz, abs_zero] at h
  norm_num at h

private theorem axial_path {s t : ℝ} (hs : s • axis ∈ figureSet) (ht : t • axis ∈ figureSet)
    (hsame : (0 ≤ s ∧ 0 ≤ t) ∨ (s ≤ 0 ∧ t ≤ 0)) :
    JoinedIn figureSet (s • axis) (t • axis) := by
  apply JoinedIn.of_segment_subset
  rintro _ ⟨a,b,ha,hb,hab,rfl⟩
  rw [smul_smul, smul_smul, ← add_smul, axial_interval]
  have hs' := (axial_interval s).1 hs
  have ht' := (axial_interval t).1 ht
  have havg : |a*s+b*t| = a*|s| + b*|t| := by
    rcases hsame with ⟨hs0,ht0⟩ | ⟨hs0,ht0⟩
    · rw [abs_of_nonneg hs0, abs_of_nonneg ht0, abs_of_nonneg (by positivity)]
    · rw [abs_of_nonpos hs0, abs_of_nonpos ht0,
        abs_of_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hs0) (mul_nonpos_of_nonneg_of_nonpos hb ht0))]
      ring
  rw [havg]
  exact (convex_Icc (3/4:ℝ) (Real.sqrt 41/4)) hs' ht' ha hb hab

def sideMark (s : ℝ) : ℝ := if 0 ≤ s then 5/4 else -(5/4)

private theorem mark_mem (t : ℝ) : (sideMark t) • axis ∈ figureSet := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 41 by norm_num)
  have hp := Real.sqrt_nonneg (41:ℝ)
  rw [axial_interval, sideMark]
  split <;> norm_num <;> nlinarith

theorem joined_to_mark (x : Space 3) (hx : x ∈ figureSet) :
    JoinedIn figureSet x ((sideMark (x 0)) • axis) := by
  have hp := JoinedIn.of_segment_subset (transverse_segment x hx)
  apply hp.trans (axial_path hp.target_mem (mark_mem _) ?_)
  unfold sideMark
  split <;> grind

private theorem component_eq_of_joined {s : Set (Space 3)} {x y} (h : JoinedIn s x y) :
    connectedComponentIn s x = connectedComponentIn s y := by
  obtain ⟨p,hp⟩ := h
  apply connectedComponentIn_eq
  exact (isConnected_range p.continuous).2.subset_connectedComponentIn
    ⟨0,p.source⟩ (range_subset_iff.mpr hp) ⟨1,p.target⟩

/-- Exactly two components: the component image consists precisely of the two distinct mark components. -/
theorem figure_two_components :
    let pos := (5/4 : ℝ) • axis
    let neg := (-(5/4) : ℝ) • axis
    connectedComponentIn figureSet '' figureSet =
      {connectedComponentIn figureSet pos, connectedComponentIn figureSet neg} ∧
    connectedComponentIn figureSet pos ≠ connectedComponentIn figureSet neg := by
  dsimp only
  have hp : (5/4 : ℝ) • axis ∈ figureSet := by simpa [sideMark] using mark_mem 0
  have hn : (-(5/4) : ℝ) • axis ∈ figureSet := by convert mark_mem (-1) using 1 <;> norm_num [sideMark]
  constructor
  · ext c
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [component_eq_of_joined (joined_to_mark x hx)]
      unfold sideMark
      split <;> simp
    · intro hc
      rcases hc with rfl | hc
      · exact mem_image_of_mem _ hp
      · have hneg : c = connectedComponentIn figureSet ((-(5/4) : ℝ) • axis) := hc
        rw [hneg]
        exact mem_image_of_mem _ hn
  · intro heq
    have hneg := mem_connectedComponentIn hn
    rw [← heq] at hneg
    have hIV := isPreconnected_connectedComponentIn.intermediate_value hneg (mem_connectedComponentIn hp)
      (f := fun x : Space 3 => x 0) (by fun_prop)
    have h0 : (0:ℝ) ∈ Icc (((-(5/4) : ℝ) • axis) 0) (((5/4 : ℝ) • axis) 0) := by
      rw [(on_axis _).1, (on_axis _).1]
      norm_num
    obtain ⟨x,hx,hz⟩ := hIV h0
    exact missing_midplane x (connectedComponentIn_subset _ _ hx) hz

/-- Figure 1. Each lobe fits in a ball of radius 1/2 about its own mark. -/
theorem figure_lobe_balls :
    figureSet ⊆ closedBall ((5/4 : ℝ) • axis) (1/2) ∪ closedBall ((-(5/4) : ℝ) • axis) (1/2) := by
  intro x hx
  have habs := ((axial_interval _).1 (transverse_segment x hx (right_mem_segment ℝ _ _))).1
  have hmul := (pair_mem_iff _ x).1 hx
  have hcoord (s : ℝ) : |x 0 - s| ≤ dist x (s • axis) := by
    apply (sq_le_sq₀ (abs_nonneg _) dist_nonneg).1
    rw [sq_abs, axis_dist_sq]
    linarith [sq_nonneg (transverse x)]
  rcases le_total 0 (x 0) with hs | hs
  · left
    rw [abs_of_nonneg hs] at habs
    have hh := hcoord (-(5/4))
    rw [abs_of_nonneg (by linarith)] at hh
    change dist x ((5/4:ℝ) • axis) ≤ 1/2
    nlinarith [mul_nonneg (dist_nonneg (x := x) (y := (5/4:ℝ) • axis))
      (show 0 ≤ dist x ((-(5/4):ℝ) • axis)-2 by linarith)]
  · right
    rw [abs_of_nonpos hs] at habs
    have hh := hcoord (5/4)
    rw [abs_of_nonpos (by linarith)] at hh
    change dist x ((-(5/4):ℝ) • axis) ≤ 1/2
    nlinarith [mul_nonneg (dist_nonneg (x := x) (y := (-(5/4):ℝ) • axis))
      (show 0 ≤ dist x ((5/4:ℝ) • axis)-2 by linarith)]

/-- The two lobes together have at most one quarter of the unit ball's volume. -/
theorem figure_volume_loss : volume figureSet < ⊤ ∧ vol figureSet ≤ omega 3 / 4 ∧ vol figureSet < omega 3 := by
  let B (t : ℝ) := closedBall (t • axis) (1/2:ℝ)
  have hf (t : ℝ) : volume (B t) < ⊤ := measure_closedBall_lt_top
  have hv (t : ℝ) : vol (B t) = omega 3 * (1/2)^3 := closedBall_volume _ (by norm_num)
  have hμ : volume figureSet ≤ volume (B (5/4)) + volume (B (-(5/4))) :=
    (measure_mono figure_lobe_balls).trans (measure_union_le _ _)
  have hfin := ENNReal.add_lt_top.mpr ⟨hf (5/4),hf (-(5/4))⟩
  have hreal := ENNReal.toReal_mono hfin.ne hμ
  rw [ENNReal.toReal_add (hf _).ne (hf _).ne] at hreal
  change vol figureSet ≤ vol (B (5/4)) + vol (B (-(5/4))) at hreal
  rw [hv,hv] at hreal
  exact ⟨hμ.trans_lt hfin,by linarith,by linarith [omega_positive 3]⟩

/-- Figure 2. At separation parameter 3/5 the exact common radius is 4/5. -/
theorem figure_ball_cylinder :
    let K := measureSolid (pairLaw (3/5)) 1
    closedBall 0 (4/5) ⊆ K ∧ K ⊆ {x | transverse x ≤ 4/5} ∧ inradius K = 4/5 := by
  have hsmall : (3/5:ℝ) < 1 / Real.sqrt 2 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).2
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hrad : Real.sqrt (1-(3/5:ℝ)^2) = 4/5 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1-(3/5:ℝ)^2 by norm_num), Real.sqrt_nonneg (1-(3/5:ℝ)^2)]
  obtain ⟨ha,hb⟩ := pair_ball_cylinder _ (by norm_num) hsmall
  simpa only [hrad] using And.intro ha (And.intro hb (pair_inradius _ (by norm_num) hsmall))

/-- Figure 3 at coalescence. Both the volume deficit and the relative radius loss vanish. -/
theorem coalescent_deficits :
    deficit (pairLaw 0) 1 = 0 ∧ 1 - inradius (measureSolid (pairLaw 0) 1) = 0 := by
  have hK : measureSolid (pairLaw 0) 1 = closedBall (0 : Space 3) 1 := by
    ext x
    rw [pair_mem_iff]
    simp only [zero_smul, neg_zero, mem_closedBall, ← sq]
    simpa using sq_le_sq₀ (dist_nonneg (x := x) (y := (0:Space 3))) zero_le_one
  have hvol : vol (closedBall (0 : Space 3) 1) = omega 3 := by
    rw [vol, volume.addHaar_closedBall_eq_addHaar_ball]
    rfl
  have hω : 0 < omega 3 := by rw [omega_three]; positivity
  constructor
  · simp [deficit, hK, hvol, hω.ne']
  · rw [hK, sub_eq_zero]
    symm
    let K := closedBall (0 : Space 3) 1
    let A := insert 0 {r : ℝ | 0 < r ∧ ∃ z, ball z r ⊆ K}
    have hcyl : K ⊆ {x | transverse x ≤ 1} := by
      intro x hx
      have hn : ‖x‖ ≤ 1 := by simpa [K] using hx
      have hh := (sq_le_sq₀ (norm_nonneg x) zero_le_one).2 hn
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hh
      apply (Real.sqrt_le_iff).2
      exact ⟨zero_le_one, by nlinarith [sq_nonneg (x 0)]⟩
    have hup (r : ℝ) (hr : r ∈ A) : r ≤ 1 := by
      rcases hr with hz | ⟨hr,z,hz⟩
      · rw [hz]; norm_num
      · exact cylinder_ball_radius _ r z hr (hz.trans hcyl)
    exact le_antisymm (csSup_le ⟨0,Or.inl rfl⟩ (fun r hr => hup r hr))
      (le_csSup ⟨_, fun r hr => hup r hr⟩ (show (1:ℝ) ∈ A from
        Or.inr ⟨one_pos, 0, ball_subset_closedBall⟩))

end ErdosVolume.Paper

module

public import ErdosVolume.Paper.Illustrations

@[expose] public section

/-! One-dimensional example and the horizontal-slice proof for two distinct marks.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise
namespace ErdosVolume.Paper

/-- The real-line example at −1 and 1, including the exact interval and its length. -/
theorem two_marks_on_line :
    {x : ℝ | dist x (-1) * dist x 1 ≤ 1} = {x | |x^2-1| ≤ 1} ∧
    {x : ℝ | |x^2-1| ≤ 1} = Icc (-Real.sqrt 2) (Real.sqrt 2) ∧
    volume.real {x : ℝ | dist x (-1) * dist x 1 ≤ 1} = 2 * Real.sqrt 2 ∧
    volume.real {x : ℝ | dist x 0 * dist x 0 ≤ 1} = 2 ∧ 2 < 2 * Real.sqrt 2 := by
  have first : {x : ℝ | dist x (-1) * dist x 1 ≤ 1} = {x | |x^2-1| ≤ 1} := by
    ext x
    simp only [mem_ofPred_eq, Real.dist_eq, ← abs_mul]
    ring_nf
  have second : {x : ℝ | |x^2-1| ≤ 1} = Icc (-Real.sqrt 2) (Real.sqrt 2) := by
    ext x
    simp only [mem_ofPred_eq, abs_le, mem_Icc]
    have hr := Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
    have hp := Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))
    constructor
    · rintro ⟨_,hi⟩
      constructor <;> nlinarith
    · rintro ⟨lo,hi⟩
      constructor <;> nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 2 + x by linarith) (sub_nonneg.mpr hi)]
  have unit : {x : ℝ | dist x 0 * dist x 0 ≤ 1} = Icc (-1) 1 := by
    ext x
    simp only [mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs, ← sq, sq_le_one_iff₀ (abs_nonneg x), abs_le, mem_Icc]
  refine ⟨first, second, ?_, ?_, ?_⟩
  · rw [first, second, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.sqrt_nonneg (2:ℝ)])]
    ring
  · rw [unit, Measure.real, Real.volume_Icc]
    norm_num
  · nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ)), Real.sqrt_nonneg (2:ℝ)]

/-- Axial and transverse intercepts for the equal pair at ±t, compared with the unit ball. -/
theorem pair_intercepts (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∀ s : ℝ, s • axis ∈ measureSolid (pairLaw t) 1 ↔ |s| ≤ Real.sqrt (1+t^2)) ∧
    (∀ x : Space 3, x 0 = 0 →
      (x ∈ measureSolid (pairLaw t) 1 ↔ transverse x ≤ Real.sqrt (1-t^2))) ∧
    1 < Real.sqrt (1+t^2) ∧ Real.sqrt (1-t^2) < 1 := by
  have ts : t^2 < 1 := by nlinarith [mul_pos ht (sub_pos.mpr ht1), sq_nonneg (1-t)]
  have tpos : 0 < t^2 := sq_pos_of_pos ht
  have hi : 0 ≤ 1+t^2 := by positivity
  have lo : 0 ≤ 1-t^2 := by linarith
  have hmem (x : Space 3) : x ∈ measureSolid (pairLaw t) 1 ↔ axialPolynomial (x 0) t (transverse x) ≤ 1 := by
    rw [pair_mem_iff, ← pair_axial_polynomial]
    exact (sq_le_one_iff₀ (mul_nonneg dist_nonneg dist_nonneg)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    rw [hmem]
    have ha : (s • axis) 0 = s ∧ transverse (s • axis) = 0 := by
      norm_num [axis, transverse, EuclideanSpace.single, PiLp.single_apply, PiLp.smul_apply]
    rw [ha.1,ha.2]
    simp only [axialPolynomial, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
      mul_zero,add_zero]
    rw [← sq_le_sq₀ (abs_nonneg s) (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt hi]
    constructor
    · intro h
      nlinarith [sq_nonneg (s^2-t^2-1)]
    · intro h
      have hlow : -(1:ℝ) ≤ s^2-t^2 := by nlinarith [sq_nonneg s]
      nlinarith [mul_nonneg (show 0 ≤ 1-(s^2-t^2) by linarith) (show 0 ≤ 1+(s^2-t^2) by linarith)]
  · intro x hx
    rw [hmem,hx]
    have hρ : 0 ≤ transverse x := Real.sqrt_nonneg _
    rw [← sq_le_sq₀ hρ (Real.sqrt_nonneg _), Real.sq_sqrt lo]
    change axialPolynomial 0 t (transverse x) ≤ 1 ↔ _
    have eq : axialPolynomial 0 t (transverse x) = ((transverse x)^2+t^2)^2 := by unfold axialPolynomial; ring
    rw [eq,sq_le_one_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  · nlinarith [Real.sq_sqrt hi, Real.sqrt_nonneg (1+t^2)]
  · nlinarith [Real.sq_sqrt lo, Real.sqrt_nonneg (1-t^2)]

/-- The horizontal axial section and full vertical projection in the pictured pair example. -/
theorem figure_pair_widths :
    let K := measureSolid (pairLaw (3/5)) 1
    (∀ s : ℝ, s • axis ∈ K ↔ |s| ≤ Real.sqrt (34/25)) ∧
    (fun x : Space 3 => x 1) '' K = Icc (-(4/5:ℝ)) (4/5) ∧
    2 < 2 * Real.sqrt (34/25) ∧ (4/5:ℝ) - (-(4/5)) = 8/5 := by
  dsimp only
  have ha := pair_intercepts (3/5) (by norm_num) (by norm_num)
  have hr : 1 + (3/5:ℝ)^2 = 34/25 := by norm_num
  rw [hr] at ha
  refine ⟨ha.1, Set.Subset.antisymm ?_ ?_, by linarith [ha.2.2.1], by norm_num⟩
  · rintro y ⟨x,hx,rfl⟩
    have upper := figure_ball_cylinder.2.1 hx
    change transverse x ≤ 4/5 at upper
    have sqtr : transverse x ^ 2 = (x 1)^2 + (x 2)^2 := Real.sq_sqrt (by positivity)
    have tr := Real.sqrt_nonneg ((x 1)^2+(x 2)^2)
    change 0 ≤ transverse x at tr
    have bound : |x 1| ≤ transverse x := (sq_le_sq₀ (abs_nonneg _) tr).mp (by rw [sq_abs,sqtr]; nlinarith [sq_nonneg (x 2)])
    exact abs_le.mp (bound.trans upper)
  · intro y hy
    refine ⟨EuclideanSpace.single 1 y, figure_ball_cylinder.1 ?_, ?_⟩
    · simpa [mem_closedBall, dist_zero_right, EuclideanSpace.single, PiLp.norm_single,
        Real.norm_eq_abs] using abs_le.mpr hy
    · simp [EuclideanSpace.single]

/-- This assumes the open unit sublevel for two marks from Erdős–Herzog–Piranian (1958),
pp. 125, 134. Pólya (1928), zweite Mitteilung, Satz II, pp. 280–282, gives the closed
sublevel bound for every positive threshold, with equality exactly for coincident roots. -/
def PlanarTwoMarkBound : Prop :=
  ∀ a b : Space 2,
    volume {z : Space 2 | dist z a * dist z b < 1} ≤ ENNReal.ofReal Real.pi ∧
    (a ≠ b → volume {z : Space 2 | dist z a * dist z b < 1} < ENNReal.ofReal Real.pi)

/-- In the coincident case the full disk attains the planar bound at every positive threshold. -/
theorem planar_coincident_disk (a : Space 2) (c : ℝ) (hc : 0 < c) :
    {z : Space 2 | dist z a * dist z a ≤ c} = closedBall a (Real.sqrt c) ∧
    volume {z : Space 2 | dist z a * dist z a ≤ c} = ENNReal.ofReal (Real.pi*c) := by
  have disk : {z : Space 2 | dist z a * dist z a ≤ c} = closedBall a (Real.sqrt c) := by
    ext z
    simp only [mem_ofPred_eq, mem_closedBall, ← sq, ← Real.le_sqrt dist_nonneg hc.le]
  refine ⟨disk,?_⟩
  rw [disk,EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt hc.le, ← ENNReal.ofReal_mul hc.le, mul_comm]

def planePoint (v : ℝ × ℝ) : Space 2 := WithLp.toLp 2 ![v.1,v.2]

private theorem planePoint_preserving : MeasurePreserving planePoint := by
  have hf := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp hf

/-- The positive level in each vertical line is contained in the zero set of a monic quartic. -/
theorem vertical_level_quartic (a b : Space 2) (c x : ℝ) :
    ∃ P : Polynomial ℝ, P.Monic ∧ P.natDegree = 4 ∧
      ∀ y : ℝ, P.eval y = (dist (planePoint (x,y)) a * dist (planePoint (x,y)) b)^2 - c^2 := by
  let A (p : Space 2) : Polynomial ℝ :=
    (Polynomial.X - Polynomial.C (p 1))^2 + Polynomial.C ((x-p 0)^2)
  let P := A a * A b - Polynomial.C (c^2)
  have hm : P.Monic := by dsimp [P,A]; monicity!
  have hd : P.natDegree = 4 := by dsimp [P,A]; compute_degree!
  refine ⟨P,hm,hd,?_⟩
  intro y
  have dist_sq (p : Space 2) : dist (planePoint (x,y)) p ^ 2 = (y-p 1)^2 + (x-p 0)^2 := by
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two,planePoint,Real.dist_eq,sq_abs,add_comm]
  simp [P, A, mul_pow, dist_sq]

/-- Each vertical line meets a given product level in at most four distinct points. -/
theorem vertical_level_at_most_four (a b : Space 2) (c x : ℝ) :
    let F := {y : ℝ | dist (planePoint (x,y)) a * dist (planePoint (x,y)) b = c}
    F.Finite ∧ F.ncard ≤ 4 := by
  classical
  obtain ⟨P,hm,hd,hev⟩ := vertical_level_quartic a b c x
  let F := {y : ℝ | dist (planePoint (x,y)) a * dist (planePoint (x,y)) b = c}
  have sub : F ⊆ (P.roots.toFinset : Set ℝ) := by
    intro y hy
    change y ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hm.ne_zero]
    change P.eval y = 0
    rw [hev, show dist (planePoint (x,y)) a * dist (planePoint (x,y)) b = c from hy, sub_self]
  refine ⟨P.roots.toFinset.finite_toSet.subset sub, ?_⟩
  calc F.ncard ≤ (P.roots.toFinset : Set ℝ).ncard := Set.ncard_le_ncard sub P.roots.toFinset.finite_toSet
       _ = P.roots.toFinset.card := Set.ncard_coe_finset _
       _ ≤ P.roots.card := Multiset.toFinset_card_le _
       _ ≤ P.natDegree := P.card_roots'
       _ = 4 := hd

/-- The boundary level has area zero, so Fubini transfers the published open inequality. -/
theorem planar_pair_level_null (a b : Space 2) (c : ℝ) :
    volume {z : Space 2 | dist z a * dist z b = c} = 0 := by
  let S := {z : Space 2 | dist z a * dist z b = c}
  have hs : MeasurableSet S :=
    (isClosed_eq ((continuous_id.dist continuous_const).mul (continuous_id.dist continuous_const))
      continuous_const).measurableSet
  rw [← planePoint_preserving.measure_preimage hs.nullMeasurableSet]
  change ((volume : Measure ℝ).prod volume) (planePoint ⁻¹' S) = 0
  rw [Measure.prod_apply (planePoint_preserving.measurable hs)]
  calc _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := by
         apply lintegral_congr
         intro x
         exact (vertical_level_at_most_four a b c x).1.measure_zero volume
       _ = 0 := by simp

/-- Close the sublevel at no area cost and dilate the unit-threshold inequality by √c. -/
theorem planar_scaled_closed (hp : PlanarTwoMarkBound) (a b : Space 2) (c : ℝ) (hc : 0 < c) :
    volume {z : Space 2 | dist z a * dist z b ≤ c} ≤ ENNReal.ofReal (Real.pi*c) ∧
    (a ≠ b → volume {z : Space 2 | dist z a * dist z b ≤ c} < ENNReal.ofReal (Real.pi*c)) := by
  let r := Real.sqrt c
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  have hsq : r^2 = c := Real.sq_sqrt hc.le
  let A : Space 2 := r⁻¹ • a
  let B : Space 2 := r⁻¹ • b
  let E := {z : Space 2 | dist z A * dist z B ≤ 1}
  have close_eq : volume E = volume {z : Space 2 | dist z A * dist z B < 1} := by
    apply measure_congr
    have away : ∀ᵐ z : Space 2 ∂volume, dist z A * dist z B ≠ 1 := by
      simpa [ae_iff] using planar_pair_level_null A B 1
    filter_upwards [away] with z hz
    exact propext ((lt_iff_le_and_ne).trans (and_iff_left hz)).symm
  have da : r • A = a := by simp [A,smul_smul,hr.ne']
  have db : r • B = b := by simp [B,smul_smul,hr.ne']
  have factor (z : Space 2) :
      dist (r • z) a * dist (r • z) b = c * (dist z A * dist z B) := by
    calc _ = dist (r • z) (r • A) * dist (r • z) (r • B) := by rw [da,db]
         _ = c * (dist z A * dist z B) := by rw [dist_smul₀, dist_smul₀,Real.norm_eq_abs,abs_of_pos hr,←hsq]; ring
  have scale : {x : Space 2 | dist x a * dist x b ≤ c} = r • E := by
    ext x
    constructor
    · intro hx
      have hundo : r • (r⁻¹ • x) = x := by simp [smul_smul,hr.ne']
      refine ⟨r⁻¹ • x,?_,hundo⟩
      change dist (r⁻¹ • x) A * dist (r⁻¹ • x) B ≤ 1
      apply (mul_le_mul_iff_right₀ hc).mp
      rw [← factor,hundo,mul_one]
      exact hx
    · rintro ⟨z,hz,rfl⟩
      change dist (r • z) a * dist (r • z) b ≤ c
      rw [factor]
      simpa using mul_le_mul_of_nonneg_left hz hc.le
  have size : volume {x : Space 2 | dist x a * dist x b ≤ c} =
      ENNReal.ofReal c * volume {z : Space 2 | dist z A * dist z B < 1} := by
    rw [scale,volume.addHaar_smul_of_nonneg hr.le,close_eq]
    simp [Space, hsq]
  rw [size,mul_comm Real.pi c,ENNReal.ofReal_mul hc.le]
  refine ⟨mul_le_mul_right (hp A B).1 _,?_⟩
  intro hab
  have hAB : A ≠ B := fun h => hab (da.symm.trans ((congrArg (r • ·) h).trans db))
  exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top ((hp A B).2 hAB)

theorem two_mark_slice_identity (u v h : ℝ) :
    (u^2+h^2)*(v^2+h^2) = (u*v+h^2)^2 + h^2*(u-v)^2 := by ring

/-- Horizontal section of the unit-threshold solid, with both marks at height zero. -/
def pairSection (a b : Space 2) (h : ℝ) : Set (Space 2) :=
  {z | ((dist z a)^2+h^2)*((dist z b)^2+h^2) ≤ 1}

theorem pair_section_subset (a b : Space 2) (h : ℝ) :
    pairSection a b h ⊆ {z | dist z a * dist z b ≤ 1-h^2} := by
  intro z hz
  change ((dist z a)^2+h^2)*((dist z b)^2+h^2) ≤ 1 at hz
  rw [two_mark_slice_identity] at hz
  have hprod : (dist z a * dist z b+h^2)^2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg (dist z a-dist z b))]
  have hle := (sq_le_one_iff₀ (show 0 ≤ dist z a * dist z b+h^2 by positivity)).mp hprod
  exact show dist z a * dist z b ≤ 1-h^2 by linarith

theorem pair_section_empty (a b : Space 2) (h : ℝ) (hh : 1 < |h|) :
    pairSection a b h = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hu := pair_section_subset a b h hz
  change dist z a * dist z b ≤ 1-h^2 at hu
  have hh2 : 1 < h^2 := by simpa using (sq_lt_sq₀ zero_le_one (abs_nonneg h)).2 hh
  linarith [mul_nonneg (dist_nonneg (x:=z) (y:=a)) (dist_nonneg (x:=z) (y:=b))]

theorem pair_section_area (hp : PlanarTwoMarkBound) (a b : Space 2) (hab : a ≠ b)
    (h : ℝ) (hh : |h| < 1) :
    volume (pairSection a b h) ≤ volume {z : Space 2 | dist z a * dist z b ≤ 1-h^2} ∧
    volume {z : Space 2 | dist z a * dist z b ≤ 1-h^2} < ENNReal.ofReal (Real.pi*(1-h^2)) := by
  have hsq : h^2 < 1 := by simpa using (sq_lt_sq₀ (abs_nonneg h) zero_le_one).2 hh
  exact ⟨measure_mono (pair_section_subset a b h), (planar_scaled_closed hp a b (1-h^2) (by linarith)).2 hab⟩

def slicePoint (v : ℝ × Space 2) : Space 3 :=
  WithLp.toLp 2 (Fin.cons v.1 (WithLp.ofLp v.2))

private theorem stack_preserving : MeasurePreserving slicePoint := by
  have h1 := (MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
    (PiLp.volume_preserving_ofLp (Fin 2))
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have h3 := PiLp.volume_preserving_toLp (Fin 3)
  convert h3.comp (h2.comp h1) using 1
  funext v
  simp [slicePoint, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

private theorem stack_dist_sq (h : ℝ) (z a : Space 2) :
    dist (slicePoint (h,z)) (slicePoint (0,a)) ^ 2 = dist z a ^ 2 + h^2 := by
  simp [EuclideanSpace.dist_sq_eq, slicePoint, Fin.sum_univ_succ, Real.dist_eq, sq_abs]; ring

def ballSection (h : ℝ) : Set (Space 2) :=
  {z | dist z 0 ^ 2+h^2 ≤ 1}

theorem unit_ball_section_area (h : ℝ) (hh : |h| ≤ 1) :
    ballSection h = closedBall 0 (Real.sqrt (1-h^2)) ∧
    volume (ballSection h) = ENNReal.ofReal (Real.pi*(1-h^2)) := by
  have hsq : h^2 ≤ 1 := by simpa using (sq_le_sq₀ (abs_nonneg h) zero_le_one).2 hh
  have hc : 0 ≤ 1-h^2 := by linarith
  have heq : ballSection h = closedBall 0 (Real.sqrt (1-h^2)) := by
    ext z
    change dist z 0 ^ 2 + h^2 ≤ 1 ↔ dist z 0 ≤ Real.sqrt (1-h^2)
    rw [Real.le_sqrt dist_nonneg hc]
    constructor <;> intro hz <;> linarith
  refine ⟨heq,?_⟩
  rw [heq, EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt hc, ← ENNReal.ofReal_mul hc, mul_comm]


private def productSolid (p q : Space 3) : Set (Space 3) := {x | dist x p * dist x q ≤ 1}

private theorem solid_measurable (p q : Space 3) : MeasurableSet (productSolid p q) :=
  (isClosed_le ((continuous_id.dist continuous_const).mul (continuous_id.dist continuous_const))
    continuous_const).measurableSet

theorem spatial_pair_section (a b z : Space 2) (h : ℝ) :
    dist (slicePoint (h,z)) (slicePoint (0,a)) * dist (slicePoint (h,z)) (slicePoint (0,b)) ≤ 1 ↔
      z ∈ pairSection a b h := by
  rw [← sq_le_one_iff₀ (mul_nonneg dist_nonneg dist_nonneg), mul_pow, stack_dist_sq,stack_dist_sq]
  rfl

theorem spatial_ball_section (z : Space 2) (h : ℝ) :
    slicePoint (h,z) ∈ closedBall (slicePoint (0,0)) 1 ↔ z ∈ ballSection h := by
  rw [mem_closedBall, ← sq_le_one_iff₀ dist_nonneg, stack_dist_sq]
  rfl

private theorem integrated_slice_bound (hp : PlanarTwoMarkBound) (a b : Space 2) (hab : a ≠ b) :
    volume (productSolid (slicePoint (0,a)) (slicePoint (0,b))) <
      volume (closedBall (slicePoint (0,(0:Space 2))) 1) := by
  let S := slicePoint ⁻¹' productSolid (slicePoint (0,a)) (slicePoint (0,b))
  let B := slicePoint ⁻¹' closedBall (slicePoint (0,(0:Space 2))) 1
  have sm : MeasurableSet S := stack_preserving.measurable (solid_measurable _ _)
  have bm : MeasurableSet B := stack_preserving.measurable isClosed_closedBall.measurableSet
  have s_slice (h : ℝ) : Prod.mk h ⁻¹' S = pairSection a b h :=
    Set.ext fun z => spatial_pair_section a b z h
  have b_slice (h : ℝ) : Prod.mk h ⁻¹' B = ballSection h :=
    Set.ext fun z => spatial_ball_section z h
  have si : (∫⁻ h, volume (pairSection a b h)) =
      volume (productSolid (slicePoint (0,a)) (slicePoint (0,b))) := by
    simp_rw [← s_slice, ← Measure.prod_apply sm]
    exact stack_preserving.measure_preimage (solid_measurable _ _).nullMeasurableSet
  have bi : (∫⁻ h, volume (ballSection h)) =
      volume (closedBall (slicePoint (0,(0:Space 2))) 1) := by
    simp_rw [← b_slice, ← Measure.prod_apply bm]
    exact stack_preserving.measure_preimage isClosed_closedBall.measurableSet.nullMeasurableSet
  have slope (h : ℝ) (hh : |h| < 1) : volume (pairSection a b h) < volume (ballSection h) := by
    rw [(unit_ball_section_area h hh.le).2]
    exact (pair_section_area hp a b hab h hh).1.trans_lt (pair_section_area hp a b hab h hh).2
  have ae_le : ∀ᵐ h : ℝ ∂volume, volume (pairSection a b h) ≤ volume (ballSection h) := by
    have away (x : ℝ) : ∀ᵐ y : ℝ ∂volume, y ≠ x := by simp [ae_iff]
    filter_upwards [away 1, away (-1)] with h h1 h2
    rcases lt_trichotomy |h| 1 with hl | he | hg
    · exact (slope h hl).le
    · exfalso
      rcases abs_choice h with eq | eq
      · exact h1 (eq ▸ he)
      · exact h2 (by linarith)
    · simp [pair_section_empty a b h hg]
  have bmeas : Measurable (fun h : ℝ => volume (ballSection h)) := by
    simpa only [b_slice] using (measurable_measure_prodMk_left (ν := (volume : Measure (Space 2))) bm)
  have finite : (∫⁻ h, volume (pairSection a b h)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [bi]; exact measure_closedBall_lt_top.ne) (lintegral_mono_ae ae_le)
  rw [← si,← bi]
  exact lintegral_strict_mono_of_ae_le_of_ae_lt_on bmeas.aemeasurable finite ae_le
    (s := Ioo (-1:ℝ) 1) (by simp [Real.volume_Ioo])
    (ae_of_all _ fun h hh => slope h (abs_lt.mpr hh))


/-- Rotate and translate an arbitrary pair into a horizontal plane, then integrate
the strict planar section inequalities. The only external hypothesis is the planar bound. -/
theorem distinct_pair_volume_by_slices (hp : PlanarTwoMarkBound) (p q : Space 3) (hpq : p ≠ q) :
    let S := {x : Space 3 | dist x p * dist x q ≤ 1}
    volume S < ⊤ ∧ vol S < 4*Real.pi/3 := by
  let b : Space 2 := EuclideanSpace.single 0 ‖q-p‖
  let w := slicePoint (0,b)
  have hzero : slicePoint (0,(0:Space 2)) = 0 := by
    ext i; fin_cases i <;> rfl
  have hb : ‖b‖ = ‖q-p‖ := by
    simp [b, EuclideanSpace.single, PiLp.norm_single]
  have hnorm : ‖q-p‖ = ‖w‖ := by
    have eq := stack_dist_sq 0 b 0
    rw [hzero,dist_zero_right,dist_zero_right,hb] at eq
    nlinarith [norm_nonneg (q-p),norm_nonneg w,show w = slicePoint (0,b) from rfl]
  let U := (ℝ ∙ ((q-p)-w))ᗮ.reflection
  have hUw : U (q-p) = w := Submodule.reflection_sub hnorm
  have hab : (0:Space 2) ≠ b := by
    intro h
    have hnorm0 : ‖q-p‖ = 0 := by rw [← hb,← h,norm_zero]
    exact hpq (sub_eq_zero.mp (norm_eq_zero.mp hnorm0)).symm
  let T : Space 3 → Space 3 := fun x => p + U.symm x
  have hT : MeasurePreserving T :=
    (measurePreserving_add_left (volume : Measure (Space 3)) p).comp U.symm.measurePreserving
  have tp : T 0 = p := by simp [T]
  have tq : T w = q := by rw [show T w = p + U.symm w from rfl, ← hUw,U.symm_apply_apply]; abel
  have dT (x y : Space 3) : dist (T x) (T y) = dist x y := by
    simpa only [T,dist_add_left] using U.symm.dist_map x y
  have pre : T ⁻¹' productSolid p q = productSolid (slicePoint (0,0)) (slicePoint (0,b)) := by
    ext x
    change dist (T x) p * dist (T x) q ≤ 1 ↔ _
    rw [← tp,← tq,dT,dT,hzero]
    rfl
  have eq := hT.measure_preimage (solid_measurable p q).nullMeasurableSet
  rw [pre] at eq
  have lt := integrated_slice_bound hp 0 b hab
  rw [eq,EuclideanSpace.volume_closedBall_fin_three] at lt
  have value : 0 ≤ 4*Real.pi/3 := by positivity
  have strict : volume (productSolid p q) < ENNReal.ofReal (4*Real.pi/3) := by
    simpa [mul_comm Real.pi (4:ℝ)] using lt
  have fin := strict.trans_le le_top
  refine ⟨fin,?_⟩
  change (volume (productSolid p q)).toReal < _
  rwa [← ENNReal.toReal_ofReal value, ENNReal.toReal_lt_toReal fin.ne ENNReal.ofReal_ne_top]

/-- The unit ordinary distance product in every dimension at least three.
Uniform positive weights reduce the ordinary product to the capacity theorem. -/
theorem erdos_product_all_dim_given {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hO : OpenIsoFact d) (hN : CapacityNormalization d) (hB : BallCapacityFact d)
    (hE : EquilibriumExistence d) (hM : EquilibriumMomentFact d) (hS : EquilibriumSphereFact d)
    (a : Fin n → Space d) :
    let E := {x : Space d | ∏ i, dist x (a i) ≤ 1}
    volume E < ⊤ ∧ vol E ≤ omega d ∧ (vol E = omega d ↔ ∀ i j, a i = a j) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : ValidWeights (fun _ : Fin n => (n : ℝ)⁻¹) :=
    ⟨fun _ => inv_pos.mpr hn', by simp [hn'.ne']⟩
  have hsolid : {x : Space d | ∏ i, dist x (a i) ≤ 1} = solid a (fun _ => (n : ℝ)⁻¹) 1 := by
    ext x
    change (∏ i, dist x (a i)) ≤ 1 ↔ (∏ i, dist x (a i) ^ (n : ℝ)⁻¹) ≤ 1
    rw [Real.finsetProd_rpow _ _ (fun _ _ => dist_nonneg)]
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow_iff (x := ∏ i, dist x (a i)) (Finset.prod_nonneg fun _ _ => dist_nonneg)
        zero_le_one (inv_pos.mpr hn')).symm
  dsimp only
  rw [hsolid]
  simpa only [one_pow, mul_one] using volume_capacity hd hn hO hN hB hE hM hS a _ hw 1 one_pos

end ErdosVolume.Paper

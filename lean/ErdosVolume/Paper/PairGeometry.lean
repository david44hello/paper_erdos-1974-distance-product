import ErdosVolume.Paper.Illustrations

/-! Two equal marks in arbitrary dimension and the sharp length on the real line. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
noncomputable section
open Metric Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace ErdosVolume.Paper

def pairRegion {X : Type*} [PseudoMetricSpace X] (p q : X) : Set X :=
  {x | dist x p * dist x q ≤ 1}

private theorem scalar_band (s t : ℝ) :
    |s^2-t^2| ≤ 1 ↔ t^2-1 ≤ s^2 ∧ s^2 ≤ t^2+1 := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem outer_cut (s t : ℝ) :
    s^2 ≤ t^2+1 ↔ |s| ≤ Real.sqrt (1+t^2) := by
  rw [← sq_le_sq₀ (abs_nonneg s) (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt (by positivity)]
  rw [add_comm]

/-- Exact product and reach on the line through the marks, including t = 1. -/
theorem pair_axis_reach {d : ℕ} (m e : Space d) (he : ‖e‖ = 1)
    (t : ℝ) (hp : 0 < t) (ht : t ≤ 1) (s : ℝ) :
    let x := m + s • e
    let p := m + t • e
    let q := m + (-t) • e
    dist x p = |s-t| ∧ dist x q = |s+t| ∧ dist x p * dist x q = |s^2-t^2| ∧
    (x ∈ pairRegion p q ↔ t^2-1 ≤ s^2 ∧ s^2 ≤ t^2+1) ∧
    (x ∈ pairRegion p q ↔ |s| ≤ Real.sqrt (1+t^2)) ∧ 1 < Real.sqrt (1+t^2) := by
  dsimp only
  have distance (r : ℝ) : dist (m+s • e) (m+r • e) = |s-r| := by
    rw [dist_add_left,dist_eq_norm,← sub_smul,norm_smul,he, mul_one, Real.norm_eq_abs]
  have prod : |s-t| * |s+t| = |s^2-t^2| := by rw [← abs_mul]; congr 1; ring
  have hs := (sq_le_sq₀ hp.le zero_le_one).mpr ht
  have band := scalar_band s t
  have hd := distance (-t)
  simp only [sub_neg_eq_add] at hd
  simp only [pairRegion, mem_ofPred_eq, distance t, hd, prod, true_and]
  refine ⟨band, ?_, ?_⟩
  · rw [band, and_iff_right (show t^2-1 ≤ s^2 by nlinarith [sq_nonneg s]), outer_cut]
  · simpa using Real.sqrt_lt_sqrt (x := 1) zero_le_one (show 1 < 1+t^2 by nlinarith [sq_pos_of_pos hp])

/-- Exact product and reach in any perpendicular unit direction through the midpoint. -/
theorem pair_transverse_reach {d : ℕ} (m e u : Space d) (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (horth : inner ℝ u e = 0) (t : ℝ) (hp : 0 < t) (ht : t ≤ 1) (b : ℝ) :
    let x := m+b • u
    let p := m+t • e
    let q := m+(-t) • e
    dist x p = Real.sqrt (b^2+t^2) ∧ dist x q = Real.sqrt (b^2+t^2) ∧
    dist x p * dist x q = b^2+t^2 ∧
    (x ∈ pairRegion p q ↔ |b| ≤ Real.sqrt (1-t^2)) ∧
    Real.sqrt (1-t^2) < 1 ∧ (t = 1 → (x ∈ pairRegion p q ↔ b = 0)) := by
  dsimp only
  have distance (r : ℝ) : dist (m+b • u) (m+r • e) = Real.sqrt (b^2+r^2) := by
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity),dist_add_left,dist_eq_norm,norm_sub_sq_real]
    simp [norm_smul,he,hu,real_inner_smul_left,real_inner_smul_right,horth,Real.norm_eq_abs,sq_abs]
  have hd := distance (-t)
  simp only [neg_sq] at hd
  have hsq : 0 ≤ 1-t^2 := by nlinarith [(sq_le_sq₀ hp.le zero_le_one).mpr ht]
  simp only [pairRegion,mem_ofPred_eq,distance t,hd,← sq,Real.sq_sqrt (by positivity : 0 ≤ b^2+t^2),true_and]
  refine ⟨?_, ?_, ?_⟩
  · rw [← sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _),sq_abs,Real.sq_sqrt hsq]
    constructor <;> intro h <;> linarith
  · simpa using Real.sqrt_lt_sqrt hsq (show 1-t^2 < 1 by nlinarith [sq_pos_of_pos hp])
  · rintro rfl
    simp

private theorem line_product (x m t : ℝ) :
    dist x (m-t) * dist x (m+t) = |(x-m)^2-t^2| := by
  simp only [Real.dist_eq, ← abs_mul]
  congr 1
  ring

private theorem interval_length (a b : ℝ) (h : a ≤ b) :
    volume.real (Icc a b) = b-a := by
  rw [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

/-- The whole interval, its length, and strict growth in the overlapping regime. -/
theorem line_pair_interval (m t : ℝ) (ht : 0 ≤ t) (h₁ : t ≤ 1) :
    let B := Real.sqrt (1+t^2)
    pairRegion (m-t) (m+t) = Icc (m-B) (m+B) ∧
    volume.real (pairRegion (m-t) (m+t)) = 2*B ∧
    StrictMonoOn (fun s : ℝ => 2*Real.sqrt (1+s^2)) (Icc 0 1) := by
  dsimp only
  have eq : pairRegion (m-t) (m+t) = Icc (m-Real.sqrt (1+t^2)) (m+Real.sqrt (1+t^2)) := by
    ext x
    simp only [pairRegion,mem_ofPred_eq,line_product,scalar_band,mem_Icc]
    rw [and_iff_right (show t^2-1 ≤ (x-m)^2 by nlinarith [(sq_le_sq₀ ht zero_le_one).mpr h₁,sq_nonneg (x-m)]),
      outer_cut,abs_le]
    constructor <;> rintro ⟨h,k⟩ <;> constructor <;> linarith
  refine ⟨eq, ?_, ?_⟩
  · rw [eq,interval_length _ _ (by linarith [Real.sqrt_nonneg (1+t^2)])]; ring
  · intro x hx y hy hxy
    have h := Real.sqrt_lt_sqrt (by positivity : 0 ≤ 1+x^2)
      (show 1+x^2 < 1+y^2 by linarith [(sq_lt_sq₀ hx.1 hy.1).mpr hxy])
    linarith

/-- Separated marks produce two disjoint intervals with the stated sharp length formula. -/
theorem line_pair_two_intervals (m t : ℝ) (ht : 1 < t) :
    let A := Real.sqrt (t^2-1)
    let B := Real.sqrt (t^2+1)
    Disjoint (Icc (m-B) (m-A)) (Icc (m+A) (m+B)) ∧
    pairRegion (m-t) (m+t) = Icc (m-B) (m-A) ∪ Icc (m+A) (m+B) ∧
    volume.real (pairRegion (m-t) (m+t)) = 2*(B-A) ∧ 2*(B-A) = 4/(B+A) ∧
    4/(B+A) < 2*Real.sqrt 2 := by
  let A := Real.sqrt (t^2-1)
  let B := Real.sqrt (t^2+1)
  have ht2 : 1 < t^2 := by nlinarith [sq_nonneg (t-1)]
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hB : 0 < B := Real.sqrt_pos.mpr (by positivity)
  have hA2 : A^2 = t^2-1 := Real.sq_sqrt (by linarith)
  have hB2 : B^2 = t^2+1 := Real.sq_sqrt (by positivity)
  have hAB : A < B := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have dis : Disjoint (Icc (m-B) (m-A)) (Icc (m+A) (m+B)) := Set.disjoint_left.mpr fun x hx hy => by
    linarith [hx.2,hy.1]
  have eq : pairRegion (m-t) (m+t) = Icc (m-B) (m-A) ∪ Icc (m+A) (m+B) := by
    ext x
    simp only [pairRegion,mem_ofPred_eq,line_product,scalar_band,mem_union,mem_Icc]
    rw [← hA2,← hB2,← sq_abs (x-m)]
    rw [sq_le_sq₀ hA.le (abs_nonneg _),sq_le_sq₀ (abs_nonneg _) hB.le,le_abs,abs_le]
    constructor
    · rintro ⟨h,lo,hi⟩
      rcases h with h|h
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    · rintro (⟨lo,hi⟩ | ⟨lo,hi⟩)
      · exact ⟨Or.inr (by linarith),by linarith,by linarith⟩
      · exact ⟨Or.inl (by linarith),by linarith,by linarith⟩
  refine ⟨dis,eq,?_,?_,?_⟩
  · rw [eq,measureReal_union dis measurableSet_Icc isCompact_Icc.measure_ne_top isCompact_Icc.measure_ne_top,interval_length _ _ (by linarith : m-B ≤ m-A),
      interval_length _ _ (by linarith : m+A ≤ m+B)]
    dsimp [A,B]; ring
  · change 2*(B-A) = 4/(B+A)
    apply (eq_div_iff (by linarith : B+A ≠ 0)).mpr
    nlinarith
  · change 4/(B+A) < _
    apply (div_lt_iff₀ (by linarith : 0 < B+A)).mpr
    have hs : Real.sqrt 2 < B := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    nlinarith [mul_lt_mul_of_pos_left (show Real.sqrt 2 < B+A by linarith) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Any pair of real marks maximizes length exactly at separation two. -/
theorem line_pair_optimum (p q : ℝ) :
    volume.real (pairRegion p q) ≤ 2*Real.sqrt 2 ∧
    (volume.real (pairRegion p q) = 2*Real.sqrt 2 ↔ dist p q = 2) := by
  wlog hpq : p ≤ q generalizing p q
  · have eq : pairRegion p q = pairRegion q p := by ext x; simp [pairRegion,mul_comm]
    rw [eq,dist_comm p q]
    exact this q p (by linarith)
  let m := (p+q)/2
  let t := (q-p)/2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have pe : m-t=p := by dsimp [m,t]; ring
  have qe : m+t=q := by dsimp [m,t]; ring
  have distEq : dist p q = 2*t := by rw [Real.dist_eq,abs_of_nonpos (by linarith)]; dsimp [t]; ring
  rw [distEq,← pe,← qe]
  by_cases h : t ≤ 1
  · have f := (line_pair_interval m t ht h).2.1
    rw [f]
    have h2 := (sq_le_sq₀ ht zero_le_one).mpr h
    have hs : Real.sqrt (1+t^2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by nlinarith)
    refine ⟨by linarith, ?_⟩
    constructor
    · intro he
      have hroot : Real.sqrt (1+t^2) = Real.sqrt 2 := by linarith
      have hsq := congrArg (fun w : ℝ => w^2) hroot
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)] at hsq
      nlinarith [mul_eq_zero.mp (show (t-1)*(t+1)=0 by nlinarith) |>.resolve_right (by linarith)]
    · intro he
      have : t=1 := by linarith
      rw [this]; norm_num
  · obtain ⟨_,_,hvol,hrat,hlt⟩ := line_pair_two_intervals m t (lt_of_not_ge h)
    rw [hvol,hrat]
    exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) (by intro he; apply h; linarith)⟩

end ErdosVolume.Paper

import ErdosVolume.Defs

/-! Two equally weighted marks and the sharp inradius statement.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

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

/-- The truncated potential agrees with the finite distance product, also at atoms. -/
theorem atomic_g {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (hw : ValidWeights w) (x : Space d) : gMeasure (atomic a w) x = G a w x := by
  let D (k : ℕ) (i : Fin n) := max (dist x (a i)) (Real.exp (-(k : ℝ)))
  have hD (k : ℕ) (i : Fin n) : 0 < D k i := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have heq (k : ℕ) : Real.exp (∫ b, Real.log (max (dist x b) (Real.exp (-(k : ℝ)))) ∂atomic a w) =
      ∏ i, D k i ^ w i := by
    rw [atomic, integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top), Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw.1 i).le]
    change Real.exp (w i * Real.log (D k i)) = D k i ^ w i
    rw [mul_comm, Real.exp_mul, Real.exp_log (hD k i)]
  unfold gMeasure
  simp_rw [heq]
  apply iInf_eq_of_forall_le_of_tendsto (F := atTop)
  · intro k
    exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg dist_nonneg _)
      (fun i _ => Real.rpow_le_rpow dist_nonneg (le_max_left _ _) (hw.1 i).le)
  · apply tendsto_finsetProd
    intro i _
    have hz : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hmax := (tendsto_const_nhds (x := dist x (a i)) (f := (atTop : Filter ℕ))).max hz
    rw [max_eq_left dist_nonneg] at hmax
    exact hmax.rpow_const (Or.inr (hw.1 i).le)

private theorem integrable_on_source (μ : Measure (Space 3)) (hμ : admissible μ)
    {f : Space 3 → ℝ} (hf : Continuous f) : Integrable f μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hμ.2
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := μ.support) Measure.support_mem_ae] at h

theorem trunc_log_continuous (μ : Measure (Space 3)) (hμ : admissible μ) (k : ℕ) :
    Continuous (fun x => ∫ a, Real.log (max (dist x a) (Real.exp (-(k : ℝ)))) ∂μ) := by
  let e := Real.exp (-(k:ℝ))
  have he : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have cont (x : Space 3) : Continuous (fun a => Real.log (max (dist x a) e)) :=
    ((continuous_const.dist continuous_id).max continuous_const).log
      (fun a => (he.trans_le (le_max_right _ _)).ne')
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun a => dist x a + 1 + (k:ℝ))
    (.of_forall fun z => (cont z).aestronglyMeasurable)
  · filter_upwards [ball_mem_nhds x zero_lt_one] with z hz
    apply Filter.Eventually.of_forall
    intro a
    have hupper : max (dist z a) e ≤ dist x a + 1 := max_le
      (by linarith [dist_triangle z x a, show dist z x < 1 from hz])
      (by linarith [dist_nonneg (x := x) (y := a)])
    have hlog := Real.log_le_log he (le_max_right (dist z a) e)
    rw [show Real.log e = -(k:ℝ) by exact Real.log_exp _] at hlog
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [dist_nonneg (x := x) (y := a),
      Real.log_le_sub_one_of_pos (he.trans_le (le_max_right (dist z a) e))]
  · exact integrable_on_source μ hμ (by fun_prop)
  · exact .of_forall fun a => (((continuous_id.dist (continuous_const (y := a))).max continuous_const).log
      (fun z => (he.trans_le (le_max_right (dist z a) e)).ne')).continuousAt

/-- The solid for a compact source is bounded and measurable (inradius lines 12–25). -/
theorem measureSolid_regular (μ : Measure (Space 3)) (hμ : admissible μ)
    (R : ℝ) (hR : 0 < R) :
    MeasurableSet (measureSolid μ R) ∧ Bornology.IsBounded (measureSolid μ R) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hm : Measurable (gMeasure μ) := Measurable.iInf (fun k => (trunc_log_continuous μ hμ k).rexp.measurable)
  refine ⟨measurableSet_le hm measurable_const,?_⟩
  obtain ⟨B,hB⟩ := hμ.2.isBounded.exists_norm_le
  apply (Metric.isBounded_iff_subset_closedBall (0 : Space 3)).mpr
  refine ⟨B+R+1,?_⟩
  intro x hx
  by_contra! ho
  have hnorm : B+R+1 < ‖x‖ := by simpa [mem_closedBall] using ho
  have hR1 : 0 < R+1 := by linarith
  have hg : R+1 ≤ gMeasure μ x := by
    apply le_ciInf
    intro k
    let f (a : Space 3) := Real.log (max (dist x a) (Real.exp (-(k:ℝ))))
    have cf : Continuous f := ((continuous_const.dist continuous_id).max continuous_const).log
      (fun a => ((Real.exp_pos _).trans_le (le_max_right (dist x a) _)).ne')
    apply (Real.log_le_iff_le_exp hR1).mp
    have h := integral_mono_ae (integrable_const (Real.log (R+1))) (integrable_on_source μ hμ cf) (by
      filter_upwards [Measure.support_mem_ae (μ := μ)] with a ha
      apply Real.log_le_log hR1
      apply le_trans _ (le_max_left _ _)
      rw [dist_eq_norm]
      linarith [norm_sub_norm_le x a, hB a ha])
    simpa [f] using h
  change gMeasure μ x ≤ R at hx
  linarith

private def cutExp (μ : Measure (Space 3)) (x : Space 3) (e : ℝ) :=
  Real.exp (∫ a, Real.log (max (dist x a) e) ∂μ)

private theorem cut_cont (x : Space 3) {e : ℝ} (he : 0 < e) :
    Continuous (fun a => Real.log (max (dist x a) e)) :=
  ((continuous_const.dist continuous_id).max continuous_const).log
    (fun a => (he.trans_le (le_max_right (dist x a) e)).ne')

private theorem cutoff_inf (μ : Measure (Space 3)) (hμ : admissible μ) (x : Space 3)
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (hlim : Tendsto e atTop (𝓝 0)) :
    (⨅ k, cutExp μ x (e k)) = ⨅ y : Ioi (0 : ℝ), cutExp μ x y := by
  have hbd (f : ℕ → ℝ) : BddBelow (range (fun k => cutExp μ x (f k))) :=
    ⟨0,by rintro _ ⟨k,rfl⟩; exact (Real.exp_pos _).le⟩
  have hbd' : BddBelow (range (fun y : Ioi (0 : ℝ) => cutExp μ x y)) :=
    ⟨0,by rintro _ ⟨y,rfl⟩; exact (Real.exp_pos _).le⟩
  apply le_antisymm
  · apply le_ciInf
    intro y
    obtain ⟨k,hk⟩ := (hlim.eventually_lt_const y.property).exists
    apply (ciInf_le (hbd e) k).trans
    apply Real.exp_le_exp.mpr
    exact integral_mono (integrable_on_source μ hμ (cut_cont x (he k)))
      (integrable_on_source μ hμ (cut_cont x y.property)) (fun a => Real.log_le_log
        ((he k).trans_le (le_max_right _ _)) (max_le_max_left _ hk.le))
  · exact le_ciInf fun k => ciInf_le hbd' ⟨e k,he k⟩

theorem dilated_g (μ : Measure (Space 3)) (hμ : admissible μ) (x : Space 3)
    (c : ℝ) (hc : 0 < c) :
    gMeasure (μ.map (fun a => c • a)) (c • x) = c * gMeasure μ x := by
  letI : IsProbabilityMeasure μ := hμ.1
  let e (k : ℕ) := Real.exp (-(k:ℝ))
  have hlim : Tendsto e atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc' (k : ℕ) : 0 < e k/c := div_pos (Real.exp_pos _) hc
  have htr (k : ℕ) : cutExp (μ.map (fun a => c • a)) (c • x) (e k) = c * cutExp μ x (e k/c) := by
    unfold cutExp
    rw [integral_map_of_stronglyMeasurable (by fun_prop) (cut_cont (c • x) (Real.exp_pos _)).stronglyMeasurable]
    have heq (a : Space 3) : Real.log (max (dist (c • x) (c • a)) (e k)) =
        Real.log c + Real.log (max (dist x a) (e k/c)) := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc, ← Real.log_mul hc.ne'
        ((hc' k).trans_le (le_max_right _ _)).ne', mul_max_of_nonneg _ _ hc.le]
      field_simp
    change Real.exp (∫ a, Real.log (max (dist (c • x) (c • a)) (e k)) ∂μ) = _
    simp_rw [heq]
    rw [integral_add (integrable_const _) (integrable_on_source μ hμ (cut_cont x (hc' k))),
      integral_const, probReal_univ, one_smul, Real.exp_add, Real.exp_log hc]
  change (⨅ k, cutExp _ _ (e k)) = c * ⨅ k, cutExp μ x (e k)
  simp_rw [htr]
  rw [← show (c • ⨅ k, cutExp μ x (e k/c)) = ⨅ k, c * cutExp μ x (e k/c) from
    Real.smul_iInf_of_nonneg hc.le _]
  change c * _ = c * _
  congr 1
  exact (cutoff_inf μ hμ x _ hc' (by simpa using hlim.div_const c)).trans
    (cutoff_inf μ hμ x e (fun _ => Real.exp_pos _) hlim).symm

private theorem inradius_dilate (K : Set (Space 3)) (c : ℝ) (hc : 0 < c) :
    inradius (c • K) = c * inradius K := by
  let A (S : Set (Space 3)) := insert 0 {r : ℝ | 0 < r ∧ ∃ z, ball z r ⊆ S}
  have heq : A (c • K) = c • A K := by
    ext r
    constructor
    · rintro (rfl | ⟨hr,z,hinc⟩)
      · exact ⟨0,Or.inl rfl,smul_zero _⟩
      · refine ⟨c⁻¹ * r,Or.inr ⟨mul_pos (inv_pos.2 hc) hr,c⁻¹ • z,?_⟩,?_⟩
        · have hh := Set.smul_set_mono (a := c⁻¹) hinc
          simpa [smul_ball (inv_ne_zero hc.ne'),abs_of_pos hc,smul_smul,hc.ne'] using hh
        · change c*(c⁻¹*r) = r
          field_simp
    · rintro ⟨r,(rfl | ⟨hr,z,hinc⟩),rfl⟩
      · exact Or.inl (smul_zero _)
      · refine Or.inr ⟨mul_pos hc hr,c • z,?_⟩
        have hh := Set.smul_set_mono (a := c) hinc
        simpa [smul_ball hc.ne',abs_of_pos hc] using hh
  change sSup (A (c • K)) = c * sSup (A K)
  rw [heq,Real.sSup_smul_of_nonneg hc.le]
  rfl

theorem scale_identities (μ : Measure (Space 3)) (hμ : admissible μ) (R : ℝ) (hR : 0 < R) :
    let μ' := μ.map (fun a => R⁻¹ • a)
    (∀ x, gMeasure μ' (R⁻¹ • x) = gMeasure μ x / R) ∧
    inradius (measureSolid μ' 1) = inradius (measureSolid μ R) / R ∧
    deficit μ' 1 = deficit μ R := by
  dsimp only
  have hg (x : Space 3) := dilated_g μ hμ x R⁻¹ (inv_pos.2 hR)
  have hset : measureSolid (μ.map (fun a => R⁻¹ • a)) 1 = R⁻¹ • measureSolid μ R := by
    ext y
    constructor
    · intro hy
      refine ⟨R • y,?_, by simp [smul_smul,hR.ne']⟩
      have he := hg (R • y)
      simp only [smul_smul,inv_mul_cancel₀ hR.ne',one_smul] at he
      change gMeasure _ y ≤ 1 at hy
      rw [he] at hy
      change gMeasure μ (R • y) ≤ R
      rwa [← div_eq_inv_mul, div_le_one hR] at hy
    · rintro ⟨x,hx,rfl⟩
      change gMeasure _ _ ≤ 1
      rwa [hg, ← div_eq_inv_mul, div_le_one hR]
  refine ⟨fun x => by simpa [div_eq_inv_mul] using hg x,?_,?_⟩
  · rw [hset, inradius_dilate _ _ (inv_pos.2 hR), div_eq_inv_mul]
  · unfold deficit vol
    rw [hset,volume.addHaar_smul_of_nonneg (inv_pos.2 hR).le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [Space,finrank_euclideanSpace_fin,one_pow,mul_one,inv_pow]
    ring

theorem axis_dist_sq (x : Space 3) (s : ℝ) :
    dist x (s • axis)^2 = (x 0 - s)^2 + (transverse x)^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three, transverse, Real.sq_sqrt (by positivity)]
  norm_num [axis, EuclideanSpace.single, PiLp.single_apply, PiLp.smul_apply, Real.dist_eq,
    sq_abs, add_assoc]

theorem pair_squared_product (t : ℝ) (x : Space 3) :
    (dist x (t • axis) * dist x ((-t) • axis))^2 =
      ((transverse x)^2 + t^2)^2 + 2*(x 0)^2*((transverse x)^2-t^2) + (x 0)^4 := by
  rw [mul_pow, axis_dist_sq, axis_dist_sq]
  ring

theorem pair_mem_iff (t : ℝ) (x : Space 3) :
    x ∈ measureSolid (pairLaw t) 1 ↔ dist x (t • axis) * dist x ((-t) • axis) ≤ 1 := by
  have hw : ValidWeights (fun _ : Fin 2 => (1/2 : ℝ)) := by
    constructor <;> norm_num [Fin.sum_univ_two]
  change gMeasure (atomic (pairMarks t) _) x ≤ 1 ↔ _
  rw [atomic_g _ _ hw, G, Fin.prod_univ_two]
  change dist x (t • axis) ^ (1/2:ℝ) * dist x ((-t) • axis) ^ (1/2:ℝ) ≤ 1 ↔ _
  rw [← Real.mul_rpow dist_nonneg dist_nonneg, ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  norm_num

theorem pair_squared_mean (x : Space 3) (t : ℝ) :
    (dist x (t • axis)^2 + dist x ((-t) • axis)^2)/2 = ‖x‖^2+t^2 := by
  rw [axis_dist_sq, axis_dist_sq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    transverse, Real.sq_sqrt (by positivity)]
  ring

theorem pair_outside_cylinder (x : Space 3) (t : ℝ) (ht : 0 < t) (ht' : t < 1/Real.sqrt 2)
    (hx : 1-t^2 < (transverse x)^2) : 1 < (dist x (t • axis)*dist x ((-t) • axis))^2 := by
  have hrt := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h := (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).1 ht'
  have hpos : 0 ≤ t * Real.sqrt 2 := by positivity
  have hs := (sq_lt_sq₀ hpos zero_le_one).2 h
  rw [mul_pow, hrt] at hs
  rw [pair_squared_product]
  have hgt : 1 < (transverse x)^2 + t^2 := by linarith
  have hsq := (sq_lt_sq₀ zero_le_one (by positivity : 0 ≤ (transverse x)^2 + t^2)).2 hgt
  nlinarith [mul_nonneg (sq_nonneg (x 0)) (show 0 ≤ (transverse x)^2-t^2 by linarith),
    sq_nonneg ((x 0)^2)]

/-- Inradius lines 66–88. Both the inscribed ball and the enclosing cylinder. -/
theorem pair_ball_cylinder (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    closedBall 0 (Real.sqrt (1-t^2)) ⊆ measureSolid (pairLaw t) 1 ∧
    measureSolid (pairLaw t) 1 ⊆ {x | transverse x ≤ Real.sqrt (1-t^2)} := by
  have hrt := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h := (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).1 hsmall
  have hs := (sq_lt_sq₀ (mul_nonneg ht.le (Real.sqrt_nonneg _)) zero_le_one).2 h
  rw [mul_pow, hrt] at hs
  have hrad : 0 < 1-t^2 := by nlinarith
  constructor
  · intro x hx
    have hn : ‖x‖ ≤ Real.sqrt (1-t^2) := by simpa using hx
    have hsq := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).2 hn
    rw [Real.sq_sqrt hrad.le] at hsq
    rw [pair_mem_iff]
    nlinarith [sq_nonneg (dist x (t • axis) - dist x ((-t) • axis)), pair_squared_mean x t]
  · intro x hx
    change transverse x ≤ _
    by_contra! hbad
    have hsep := (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hbad
    rw [Real.sq_sqrt hrad.le] at hsep
    have hmem := (pair_mem_iff t x).1 hx
    exact (not_lt_of_ge ((sq_le_sq₀ (by positivity) zero_le_one).2 hmem))
      (by simpa using pair_outside_cylinder x t ht hsmall hsep)

theorem cylinder_ball_radius (B r : ℝ) (z : Space 3) (hr : 0 < r)
    (hsub : ball z r ⊆ {x | transverse x ≤ B}) : r ≤ B := by
  by_contra! hbad
  obtain ⟨s,hs,hsr⟩ := exists_between (max_lt hbad hr : max B 0 < r)
  have hs0 := (le_max_right B 0).trans_lt hs
  let e : Space 3 := EuclideanSpace.single 1 1
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single, PiLp.norm_single]
  have he1 : e 1 = 1 := by simp [e, EuclideanSpace.single, PiLp.single_apply]
  have hcoord (x : Space 3) : |x 1| ≤ transverse x := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    linarith [sq_nonneg (x 2)]
  have hshift (c : ℝ) (hc : |c| = s) : |z 1 + c| ≤ B := by
    have hmem : z + c • e ∈ ball z r := by
      simpa [mem_ball, dist_eq_norm, norm_smul, he, hc] using hsr
    simpa [PiLp.add_apply, PiLp.smul_apply, he1] using (hcoord _).trans (hsub hmem)
  have hp := (abs_le.mp (hshift s (abs_of_pos hs0))).2
  have hn := (abs_le.mp (hshift (-s) (by simp [abs_of_pos hs0]))).1
  linarith [le_max_left B 0]

theorem pair_inradius (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    inradius (measureSolid (pairLaw t) 1) = Real.sqrt (1-t^2) := by
  obtain ⟨hball,hcyl⟩ := pair_ball_cylinder t ht hsmall
  have hlt : t < 1 := lt_of_lt_of_le hsmall (by
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).2
    nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num), Real.sqrt_nonneg (2:ℝ)])
  have hpos : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 (by nlinarith [(sq_lt_sq₀ ht.le zero_le_one).2 hlt])
  let A := insert 0 {r : ℝ | 0 < r ∧ ∃ z, ball z r ⊆ measureSolid (pairLaw t) 1}
  have hup (r : ℝ) (hr : r ∈ A) : r ≤ Real.sqrt (1-t^2) := by
    rcases hr with hz | ⟨hr,z,hz⟩
    · simpa [hz] using hpos.le
    · exact cylinder_ball_radius _ r z hr (hz.trans hcyl)
  exact le_antisymm (csSup_le ⟨0, Or.inl rfl⟩ (fun r hr => hup r hr))
    (le_csSup ⟨_, fun r hr => hup r hr⟩ (show Real.sqrt (1-t^2) ∈ A from
      Or.inr ⟨hpos, 0, ball_subset_closedBall.trans hball⟩))

/-- Inradius lines 94–102. A ray meets the boundary at the unique positive root. -/
theorem pair_radial (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2)
    (θ : Space 3) (hθ : ‖θ‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    (r • θ ∈ measureSolid (pairLaw t) 1 ↔ r^2 ≤ boundarySq t (θ 0)) ∧
    (0 < boundarySq t (θ 0)) ∧
    (∀ q : ℝ, 0 < q → ((q+t^2)^2 - 4*q*t^2*(θ 0)^2 = 1 ↔ q = boundarySq t (θ 0))) := by
  let u := θ 0
  let B := t^2*(2*u^2-1)
  let Δ := 1-4*t^4*u^2*(1-u^2)
  have ht1 : t < 1 := lt_of_lt_of_le hsmall (by
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).2
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)])
  have ht2 := (sq_lt_sq₀ ht.le zero_le_one).2 ht1
  have ht4 : t^4 < 1 := by nlinarith [(sq_lt_sq₀ (sq_nonneg t) zero_le_one).2 (show t^2 < 1 by simpa using ht2)]
  have hdis : Δ - B^2 = 1-t^4 := by dsimp [Δ,B]; ring
  have hΔ : 0 ≤ Δ := by nlinarith [sq_nonneg B]
  have hroot := Real.sq_sqrt hΔ
  have hroot' := Real.sqrt_nonneg Δ
  have habs : |B| < Real.sqrt Δ := (sq_lt_sq₀ (abs_nonneg _) hroot').1 (by rw [sq_abs]; nlinarith)
  have hsign := abs_lt.mp habs
  have hf (q : ℝ) : (q+t^2)^2 - 4*q*t^2*u^2 - 1 =
      (q - (B+Real.sqrt Δ)) * (q - B + Real.sqrt Δ) := by
    dsimp [B,Δ] at hroot ⊢
    linear_combination hroot
  have hprod : (dist (r • θ) (t • axis)*dist (r • θ) ((-t) • axis))^2 =
      (r^2+t^2)^2 - 4*r^2*t^2*u^2 := by
    have hn := EuclideanSpace.real_norm_sq_eq θ
    rw [hθ,Fin.sum_univ_three] at hn
    have hρ : (transverse (r • θ))^2 = r^2*(1-u^2) := by
      rw [transverse, Real.sq_sqrt (by positivity)]
      simp only [PiLp.smul_apply, smul_eq_mul]
      dsimp [u]
      linear_combination -(r^2)*hn
    rw [mul_pow, axis_dist_sq, axis_dist_sq, hρ]
    simp only [PiLp.smul_apply,smul_eq_mul,u]
    ring
  change (_ ↔ r^2 ≤ B + Real.sqrt Δ) ∧ 0 < B + Real.sqrt Δ ∧ _
  refine ⟨?_,by linarith [hsign.1],?_⟩
  · rw [pair_mem_iff, ← sq_le_sq₀ (by positivity : 0 ≤ dist (r • θ) (t • axis) * dist (r • θ) ((-t) • axis)) zero_le_one, hprod, one_pow,
        ← sub_nonpos, hf]
    have hp : 0 < r^2 - B + Real.sqrt Δ := by linarith [sq_nonneg r, hsign.2]
    rw [show (0:ℝ) = 0 * (r^2 - B + Real.sqrt Δ) by simp, mul_le_mul_iff_left₀ hp,sub_nonpos]
  · intro q hq
    change _ = 1 ↔ q = B+Real.sqrt Δ
    rw [← sub_eq_zero, hf, mul_eq_zero]
    have hn : q - B + Real.sqrt Δ ≠ 0 := ne_of_gt (by linarith [hsign.2])
    rw [or_iff_left hn,sub_eq_zero]

theorem uniform_radial_error :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t u : ℝ, 0 < t → t < δ → |u| ≤ 1 →
    |boundarySq t u - (1 + t^2*(2*u^2-1))| ≤ C*t^4 := by
  refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
  intro t u ht ht1 hu
  have hu2 : u^2 ≤ 1 := by simpa using (sq_le_sq₀ (abs_nonneg u) zero_le_one).2 hu
  let k := 4*t^4*u^2*(1-u^2)
  have hk0 : 0 ≤ k := by dsimp [k]; exact mul_nonneg (by positivity) (sub_nonneg.mpr hu2)
  have hk1 : k ≤ t^4 := by
    dsimp [k]
    nlinarith [mul_nonneg (by positivity : 0 ≤ t^4) (sq_nonneg (2*u^2-1))]
  have ht2 : t^2 < 1 := by simpa using (sq_lt_sq₀ ht.le zero_le_one).2 ht1
  have ht4 : t^4 < 1 := by nlinarith [(sq_lt_sq₀ (sq_nonneg t) zero_le_one).2 ht2]
  have hk := Real.sq_sqrt (show 0 ≤ 1-k by linarith)
  have hpos := Real.sqrt_nonneg (1-k)
  have hle : Real.sqrt (1-k) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  change |t^2*(2*u^2-1) + Real.sqrt (1-k) - (1+t^2*(2*u^2-1))| ≤ 1*t^4
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hpos (sub_nonneg.mpr hle)]

section PairVolume
open scoped Pointwise

private abbrev PairDirection := sphere (0 : Space 3) 1

local instance probSphereLaw : IsProbabilityMeasure sphereLaw where
  measure_univ := by
    unfold sphereLaw
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) (measure_ne_top _ _)

private theorem directionNorm (θ : PairDirection) : ‖(θ : Space 3)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp θ.property

private theorem pairDirectionCoord (i : Fin 3) : Continuous (fun θ : PairDirection => (θ : Space 3) i) :=
  (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val

private theorem sphereIntegrable {μ : Measure PairDirection} [IsFiniteMeasure μ]
    {f : PairDirection → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private def onPairSphere (e : Space 3 ≃ₗᵢ[ℝ] Space 3) (θ : PairDirection) : PairDirection :=
  ⟨e θ, mem_sphere_zero_iff_norm.mpr (by rw [e.norm_map, directionNorm])⟩

/-- An orthogonal map carries each spherical sector to the sector of its image. -/
private theorem mapPairSphere (e : Space 3 ≃ₗᵢ[ℝ] Space 3) :
    Measure.map (onPairSphere e) sphereLaw = sphereLaw := by
  have hm : Continuous (onPairSphere e) :=
    (e.continuous.comp continuous_subtype_val).subtype_mk _
  unfold sphereLaw
  rw [Measure.map_smul _ hm.measurable.aemeasurable]
  congr 1
  ext s hs
  rw [Measure.map_apply hm.measurable hs, Measure.toSphere_apply' _ (hm.measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  rw [← e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding
    (Ioo (0:ℝ) 1 • (Subtype.val '' s))]
  congr 1
  ext x
  constructor
  · rintro ⟨r,hr,_,⟨θ,hθ,rfl⟩,rfl⟩
    exact ⟨r,hr,_,⟨onPairSphere e θ,hθ,rfl⟩,(e.map_smul r θ).symm⟩
  · rintro ⟨r,hr,_,⟨θ,hθ,rfl⟩,h⟩
    refine ⟨r,hr,_,⟨onPairSphere e.symm θ,?_,rfl⟩,?_⟩
    · change onPairSphere e (onPairSphere e.symm θ) ∈ s
      rwa [show onPairSphere e (onPairSphere e.symm θ) = θ from Subtype.ext (e.apply_symm_apply _)]
    · apply e.injective
      simpa only [e.map_smul, onPairSphere, e.apply_symm_apply] using h

theorem axial_second_moment :
    (∫ θ, ((θ : Space 3) 0)^2 ∂sphereLaw) = 1/3 := by
  let f (i : Fin 3) (θ : PairDirection) := (θ : Space 3) i ^ 2
  have hI (i : Fin 3) : (∫ θ, f i θ ∂sphereLaw) = ∫ θ, f 0 θ ∂sphereLaw := by
    let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) i)
    have hm : Continuous (onPairSphere e) := (e.continuous.comp continuous_subtype_val).subtype_mk _
    calc
      _ = ∫ θ, f 0 (onPairSphere e θ) ∂sphereLaw := by
        congr 1
      _ = ∫ θ, f 0 θ ∂(Measure.map (onPairSphere e) sphereLaw) :=
        (integral_map hm.measurable.aemeasurable ((pairDirectionCoord _).pow 2).aestronglyMeasurable).symm
      _ = _ := by rw [mapPairSphere]
  have hs (θ : PairDirection) : ∑ i, f i θ = 1 := by
    change ∑ i, (θ : Space 3) i ^ 2 = 1
    rw [← EuclideanSpace.real_norm_sq_eq, directionNorm, one_pow]
  have hsum := integral_finsetSum (μ := sphereLaw) Finset.univ
    (fun (i : Fin 3) _ => sphereIntegrable ((pairDirectionCoord i).pow 2))
  change (∫ θ, ∑ i, f i θ ∂sphereLaw) = ∑ i, ∫ θ, f i θ ∂sphereLaw at hsum
  simp only [hs, hI, Finset.sum_const, Finset.card_univ, Fintype.card_fin, integral_const,
    probReal_univ, one_smul, nsmul_eq_mul] at hsum
  change (∫ θ, f 0 θ ∂sphereLaw) = 1/3
  norm_num at hsum
  linarith


private theorem boundaryContinuous (t : ℝ) :
    Continuous (fun θ : PairDirection => Real.sqrt (boundarySq t ((θ : Space 3) 0))) := by
  have h := pairDirectionCoord 0
  unfold boundarySq
  fun_prop

private theorem radialMass (r : Ioi (0:ℝ)) :
    Measure.volumeIoiPow 2 (Iic r) = ENNReal.ofReal ((r:ℝ)^3/3) := by
  have hnull : Measure.volumeIoiPow 2 {r} = 0 := by
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    simp
  rw [← measure_congr (Iio_ae_eq_Iic' hnull), Measure.volumeIoiPow_apply_Iio]
  norm_num

theorem pair_volume_fraction (t : ℝ) (ht : 0 < t) (hsmall : t < 1 / Real.sqrt 2) :
    volume (measureSolid (pairLaw t) 1) < ⊤ ∧ vol (measureSolid (pairLaw t) 1) / omega 3 =
      ∫ θ, (Real.sqrt (boundarySq t ((θ : Space 3) 0)))^3 ∂sphereLaw := by
  let S := (volume : Measure (Space 3)).toSphere
  let E := measureSolid (pairLaw t) 1
  let R (θ : PairDirection) := Real.sqrt (boundarySq t ((θ : Space 3) 0))
  have hR (θ : PairDirection) : 0 < R θ := Real.sqrt_pos.mpr
    (pair_radial t ht hsmall θ (directionNorm θ) 0 le_rfl).2.1
  have hi : Integrable (fun θ => (R θ)^3/3) S :=
    sphereIntegrable (((boundaryContinuous t).pow 3).div_const 3)
  have hE : MeasurableSet E := by
    rw [show E = {x | dist x (t • axis) * dist x ((-t) • axis) ≤ 1} from Set.ext (pair_mem_iff t)]
    exact measurableSet_le (by fun_prop) measurable_const
  let H := homeomorphUnitSphereProd (Space 3)
  let D : Set (PairDirection × Ioi (0:ℝ)) := (fun p => (H.symm p : Space 3)) ⁻¹' E
  have hD : MeasurableSet D := hE.preimage (continuous_subtype_val.comp H.symm.continuous).measurable
  have hslice (θ : PairDirection) : (Prod.mk θ ⁻¹' D) = Iic (⟨R θ,hR θ⟩ : Ioi (0:ℝ)) := by
    ext r
    change ((H.symm (θ,r) : _) : Space 3) ∈ E ↔ (r:ℝ) ≤ R θ
    rw [show ((H.symm (θ,r) : _) : Space 3) = (r:ℝ) • (θ:Space 3) by
      simp [H,homeomorphUnitSphereProd_symm_apply_coe]]
    rw [(pair_radial t ht hsmall θ (directionNorm θ) r r.2.le).1]
    exact (Real.le_sqrt r.2.le ((pair_radial t ht hsmall θ (directionNorm θ) 0 le_rfl).2.1.le)).symm
  have hvol : volume E = ENNReal.ofReal (∫ θ, (R θ)^3/3 ∂S) := by
    -- Polar coordinates omit the null singleton at the origin. Each radial slice is (0,R].
    have hp := (volume : Measure (Space 3)).measurePreserving_homeomorphUnitSphereProd
    have hprod := hp.measure_preimage hD.nullMeasurableSet
    have hpre : H ⁻¹' D = (Subtype.val : ({0}ᶜ : Set (Space 3)) → Space 3) ⁻¹' E := by
      ext x
      change ((H.symm (H x) : _) : Space 3) ∈ E ↔ (x : Space 3) ∈ E
      rw [H.symm_apply_apply]
    change volume.comap Subtype.val (H ⁻¹' D) = S.prod (Measure.volumeIoiPow _) D at hprod
    rw [hpre, comap_subtype_coe_apply (measurableSet_singleton _).compl, Set.image_preimage_eq_inter_range,
      Subtype.range_coe, measure_inter_conull (by simp), Measure.prod_apply hD] at hprod
    rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun θ => by positivity), hprod]
    apply lintegral_congr
    intro θ
    rw [hslice]
    simpa [Space,finrank_euclideanSpace_fin] using (radialMass ⟨R θ,hR θ⟩)
  refine ⟨hvol.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  have hnorm : (S univ).toReal = 3 * omega 3 := by
    simp [S, omega,vol,Measure.toSphere_apply_univ,Space,ENNReal.toReal_mul]
  have hω : 0 < omega 3 := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  change (volume E).toReal / omega 3 = ∫ θ, (R θ)^3 ∂sphereLaw
  rw [hvol, ENNReal.toReal_ofReal (integral_nonneg fun θ => by positivity), integral_div,
    sphereLaw, integral_smul_measure, ENNReal.toReal_inv]
  change _ = (S univ).toReal⁻¹ * ∫ θ, (R θ)^3 ∂S
  rw [hnorm]
  field_simp

private theorem pairRadiusCubeError (C t u : ℝ) (hC : 0 < C) (ht : 0 < t) (ht1 : t < 1)
    (hu : |u| ≤ 1) (hB : 0 ≤ boundarySq t u)
    (herr : |boundarySq t u - (1+t^2*(2*u^2-1))| ≤ C*t^4) :
    |(Real.sqrt (boundarySq t u))^3 - (1+(3/2:ℝ)*t^2*(2*u^2-1))| ≤
      ((C+1)^2*(C+3)+3*C/2)*t^4 := by
  let r := Real.sqrt (boundarySq t u)
  let a := t^2*(2*u^2-1)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = boundarySq t u := Real.sq_sqrt hB
  have hu2 : u^2 ≤ 1 := by simpa using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hu
  have ha : |a| ≤ t^2 := by
    dsimp [a]
    rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
    exact mul_le_of_le_one_right (sq_nonneg _) (abs_le.mpr ⟨by nlinarith [sq_nonneg u],by linarith⟩)
  have ht2 : t^2 ≤ 1 := by simpa using (sq_le_sq₀ ht.le zero_le_one).2 ht1.le
  have ht4 : t^4 ≤ t^2 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)]
  have hda : |r^2-(1+a)| ≤ C*t^4 := hr2 ▸ herr
  have hd : |r^2-1| ≤ (C+1)*t^2 := calc
    _ = |(r^2-(1+a))+a| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left ht4 hC.le]
  have hsmall : |r-1| ≤ (C+1)*t^2 := calc
    _ ≤ |r-1| * (r+1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |r^2-1| := by rw [← abs_of_nonneg (by linarith : 0 ≤ r+1), ← abs_mul]; ring_nf
    _ ≤ _ := hd
  have hbound : r+1/2 ≤ C+3 := by
    linarith [(abs_le.mp hsmall).2, mul_le_of_le_one_right (by linarith : 0 ≤ C+1) ht2]
  -- The cubic Taylor remainder in r is exactly (r-1)^2*(r+1/2).
  have hsq : (r-1)^2 ≤ (C+1)^2*t^4 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hsmall
    rw [sq_abs] at h
    linarith only [h]
  change |r^3 - (1 + (3/2:ℝ)*t^2*(2*u^2-1))| ≤ _
  calc
    _ = |(r-1)^2*(r+1/2) + (3/2:ℝ)*(r^2-(1+a))| := by dsimp [a]; ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (by linarith)),
        abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/2)]
      linarith only [mul_le_mul hsq hbound (by linarith) (by positivity),hda]

theorem pair_asymptotics :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    |deficit (pairLaw t) 1 - t^2/2| ≤ C*t^4 ∧
    |(1-inradius (measureSolid (pairLaw t) 1)) - t^2/2| ≤ C*t^4 := by
  obtain ⟨C,δ,hC,hδ,herr⟩ := uniform_radial_error
  let K := (C+1)^2*(C+3)+3*C/2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨max 1 K, min δ (min 1 (1 / Real.sqrt 2)), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_min hδ (lt_min zero_lt_one (by positivity)), ?_⟩
  intro t ht hts
  obtain ⟨htδ,ht1,htr⟩ := (lt_min_iff.mp hts).imp_right lt_min_iff.mp
  let r (θ : PairDirection) := Real.sqrt (boundarySq t ((θ : Space 3) 0))
  let p (θ : PairDirection) := 1+(3/2:ℝ)*t^2*(2*((θ:Space 3) 0)^2-1)
  have hp (θ : PairDirection) : |(r θ)^3 - p θ| ≤ K*t^4 := by
    have hθ : |(θ : Space 3) 0| ≤ 1 := by
      simpa [Real.norm_eq_abs, directionNorm θ] using (PiLp.norm_apply_le (p := 2) (θ:Space 3) 0)
    exact pairRadiusCubeError C t _ hC ht ht1 hθ
      (pair_radial t ht htr θ (directionNorm θ) 0 le_rfl).2.1.le (herr t _ ht htδ hθ)
  have hf : Integrable (fun θ => r θ ^3) sphereLaw := sphereIntegrable ((boundaryContinuous _).pow 3)
  have hu := sphereIntegrable (μ := sphereLaw) ((pairDirectionCoord 0).pow 2)
  have hpoly : Integrable p sphereLaw := (integrable_const 1).add (((hu.const_mul 2).sub (integrable_const 1)).const_mul _)
  have hmean : (∫ θ, p θ ∂sphereLaw) = 1-t^2/2 := by
    have hg : Integrable (fun θ : PairDirection => 2*((θ : Space 3) 0)^2 - 1) sphereLaw :=
      (hu.const_mul 2).sub (integrable_const 1)
    have hlin : Integrable (fun θ : PairDirection => (3/2:ℝ)*t^2*(2*((θ:Space 3) 0)^2-1)) sphereLaw :=
      hg.const_mul _
    dsimp [p]
    rw [integral_add (f := fun _ : PairDirection => (1:ℝ)) (integrable_const _) hlin,
      integral_const_mul, integral_sub (f := fun θ : PairDirection => 2*((θ : Space 3) 0)^2) (g := fun _ => 1) (hu.const_mul 2) (integrable_const _), integral_const_mul,axial_second_moment]
    norm_num
    ring
  have havg : |(∫ θ, r θ ^3 ∂sphereLaw) - (1-t^2/2)| ≤ K*t^4 := by
    rw [← hmean,← integral_sub hf hpoly]
    have hn : ∀ᵐ θ ∂sphereLaw, ‖r θ^3 - p θ‖ ≤ K*t^4 := .of_forall hp
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hn
  constructor
  · have hfrac := (pair_volume_fraction t ht htr).2
    unfold deficit
    rw [one_pow,mul_one,hfrac]
    have he : 1 - (∫ θ, r θ ^3 ∂sphereLaw) - t^2/2 = -((∫ θ, r θ ^3 ∂sphereLaw) - (1-t^2/2)) := by ring
    change |1 - (∫ θ, r θ ^3 ∂sphereLaw) - t^2/2| ≤ _
    rw [he,abs_neg]
    exact havg.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · rw [pair_inradius t ht htr]
    let b := Real.sqrt (1-t^2)
    have ht2 : t^2 ≤ 1 := by simpa using (sq_le_sq₀ ht.le zero_le_one).2 ht1.le
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    have hb2 : b^2 = 1-t^2 := Real.sq_sqrt (by linarith)
    have hb1 : b ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg t])
    have hgap : 1-b ≤ t^2 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hb1)]
    have hgap2 := (sq_le_sq₀ (sub_nonneg.mpr hb1) (sq_nonneg t)).2 hgap
    change |1-b-t^2/2| ≤ _
    rw [show 1-b-t^2/2 = (1-b)^2/2 by linarith only [hb2], abs_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 K) (by positivity : 0 ≤ t^4)
    nlinarith [sq_nonneg (1-b)]

theorem pair_ratio_limit : Tendsto (fun t : ℝ => ratio (pairLaw t) 1) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨C,δ,hC,hδ,h⟩ := pair_asymptotics
  have hs (f : ℝ → ℝ) (hf : ∀ t, 0<t → t<δ → |f t - t^2/2| ≤ C*t^4) :
      Tendsto (fun t => f t / t^2) (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
    have ht : Tendsto (fun t : ℝ => C*t^2) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := C)).mul (hid.pow 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using (tendsto_const_nhds (x := (1/2:ℝ))).sub ht)
      (by simpa using (tendsto_const_nhds (x := (1/2:ℝ))).add ht)
    · filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      apply (le_div_iff₀ (sq_pos_of_pos ht.1)).2
      linarith only [(abs_le.mp (hf t ht.1 ht.2)).1]
    · filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      apply (div_le_iff₀ (sq_pos_of_pos ht.1)).2
      linarith only [(abs_le.mp (hf t ht.1 ht.2)).2]
  have hn := hs _ (fun t ht hδt => (h t ht hδt).2)
  have hd := hs _ (fun t ht hδt => (h t ht hδt).1)
  have hr := hn.div hd (by norm_num)
  rw [div_self (by norm_num : (1/2:ℝ) ≠ 0)] at hr
  apply hr.congr'
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with t ht
    simpa only [Pi.div_apply,ratio,div_one] using
      div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt (show 0<t from ht)))
        (1-inradius (measureSolid (pairLaw t) 1)) (deficit (pairLaw t) 1)

end PairVolume

/-- Main text lines 86–89 and inradius lines 46–50. -/
theorem uniform_upper (R : ℝ) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) :
    ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
       1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R := by sorry

private theorem pair_admissible (t : ℝ) : admissible (pairLaw t) := by
  let K : Set (Space 3) := {t • axis,(-t) • axis}
  have hk : IsCompact K := ((Set.finite_singleton _).insert _).isCompact
  constructor
  · constructor
    norm_num [pairLaw,atomic,Fin.sum_univ_two,Measure.add_apply,Measure.smul_apply,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)]
  · apply hk.of_isClosed_subset Measure.isClosed_support
    apply Measure.support_subset_of_isClosed hk.isClosed
    change pairLaw t Kᶜ = 0
    simp [pairLaw,atomic,Fin.sum_univ_two,pairMarks,Measure.add_apply,Measure.smul_apply,
      Measure.dirac_apply',K]

private theorem pair_scale (R t : ℝ) (hR : 0 < R) :
    (pairLaw (R*t)).map (fun a => R⁻¹ • a) = pairLaw t := by
  have hm : Measurable (fun a : Space 3 => R⁻¹ • a) := by fun_prop
  simp only [pairLaw,atomic,Fin.sum_univ_two,Measure.map_add _ _ hm,
    Measure.map_smul _ hm.aemeasurable,Measure.map_dirac' hm]
  simp [pairMarks,smul_smul,hR.ne',← mul_assoc]

/-- Sharp coefficient for every threshold, already among equally weighted finite sources. -/
theorem sharp_coefficient (R : ℝ) (hR : 0 < R) (c : ℝ) (hc : c < 1) (h : ℝ) (hh : 0 < h) :
    ∃ μ, admissible μ ∧ equalAtomic μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧
       c * deficit μ R < 1 - inradius (measureSolid μ R) / R := by
  obtain ⟨C,δ,hC,hδ,herr⟩ := pair_asymptotics
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, C*t^2 < 1/2 :=
    ((show Tendsto (fun t : ℝ => C*t^2) (𝓝[>] 0) (𝓝 0) by simpa using (ht0.pow 2).const_mul C)).eventually_lt_const (by norm_num)
  have hsize : ∀ᶠ t : ℝ in 𝓝[>] 0, t^2/2+C*t^4 < h :=
    (show Tendsto (fun t : ℝ => t^2/2+C*t^4) (𝓝[>] 0) (𝓝 0) by
      simpa using ((ht0.pow 2).div_const 2).add ((ht0.pow 4).const_mul C)).eventually_lt_const hh
  have hright : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hall := hright.and ((ht0.eventually_lt_const hδ).and
    (hsmall.and (hsize.and ((tendsto_order.mp pair_ratio_limit).1 c hc))))
  obtain ⟨t,ht,htδ,htsmall,htsize,hrat⟩ := hall.exists
  have hpos : 0 < t := ht
  have he := abs_le.mp (herr t hpos htδ).1
  have hd : 0 < deficit (pairLaw t) 1 := by
    nlinarith [mul_pos (sq_pos_of_pos hpos) (sub_pos.mpr htsmall),he.1]
  have hd' : deficit (pairLaw t) 1 ≤ h := by linarith [he.2]
  let μ := pairLaw (R*t)
  have hadm := pair_admissible (R*t)
  obtain ⟨_,hi,hD⟩ := scale_identities μ hadm R hR
  dsimp only [μ] at hi hD
  rw [pair_scale R t hR] at hi hD
  refine ⟨μ,hadm,⟨2,by decide,pairMarks (R*t),?_⟩,hD ▸ hd,hD ▸ hd',?_⟩
  · norm_num [μ,pairLaw]
  · change c * deficit (pairLaw (R*t)) R < 1 - inradius (measureSolid (pairLaw (R*t)) R) / R
    rw [← hi, ← hD]
    simpa [ratio] using (lt_div_iff₀ hd).1 hrat

theorem worst_ratio_limit (R : ℝ) (P : Measure (Space 3) → Prop)
    (hupper : ∀ ε > (0:ℝ), ∃ h > 0, ∀ μ, admissible μ → 0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε)*deficit μ R)
    (hlower : ∀ c : ℝ, c < 1 → ∀ h > 0, ∃ μ, admissible μ ∧ P μ ∧
      0 < deficit μ R ∧ deficit μ R ≤ h ∧ c*deficit μ R < 1-inradius (measureSolid μ R)/R) :
    Tendsto (worstRatio P R) (𝓝[>] 0) (𝓝 1) := by
  let A (h : ℝ) := {v | ∃ μ, admissible μ ∧ P μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧ v = ratio μ R}
  have upper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ v ∈ A h, v ≤ 1+ε := by
    obtain ⟨δ,hδ,hu⟩ := hupper ε hε
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    rintro _ ⟨μ,hm,_,hd,hv,rfl⟩
    exact (div_le_iff₀ hd).2 (hu μ hm hd (hv.trans hh.2.le))
  apply tendsto_order.mpr
  constructor
  · intro c hc
    filter_upwards [upper 1 one_pos,self_mem_nhdsWithin] with h hu hh
    obtain ⟨μ,hm,hP,hd,hδ,hx⟩ := hlower c hc h hh
    apply ((lt_div_iff₀ hd).2 hx).trans_le
    exact le_csSup (s := A h) ⟨_,hu⟩ ⟨μ,hm,hP,hd,hδ,rfl⟩
  · intro c hc
    let ε := (c-1)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [upper ε hε,self_mem_nhdsWithin] with h hu hh
    obtain ⟨μ,hm,hP,hd,hδ,_⟩ := hlower 0 zero_lt_one h hh
    have hne : (A h).Nonempty := ⟨_,μ,hm,hP,hd,hδ,rfl⟩
    exact (csSup_le hne hu).trans_lt (by dsimp [ε]; linarith)

/-- The two versions of Theorem 2. No bound shared by the supports is imposed. -/
theorem sharp_stability (R : ℝ) (hR : 0 < R) :
    Tendsto (worstRatio (fun _ => True) R) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (worstRatio equalAtomic R) (𝓝[>] 0) (𝓝 1) := by
  refine ⟨worst_ratio_limit R _ (uniform_upper R hR) ?_,
    worst_ratio_limit R _ (uniform_upper R hR) (sharp_coefficient R hR)⟩
  intro c hc h hh
  obtain ⟨μ,hm,_,rest⟩ := sharp_coefficient R hR c hc h hh
  exact ⟨μ,hm,trivial,rest⟩

end ErdosVolume

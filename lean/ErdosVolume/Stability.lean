import ErdosVolume.Sharpness

/-! Logarithmic moments and the upper estimate for the inradius.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

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

/-- The extended kernel takes value infinity at its pole. -/
def potential (ν : Law) (a : X) : ℝ≥0∞ := ∫⁻ x, newtonKernel x a ∂ν

/-- Used when the integrability and pole-null statements below apply. -/
def g (ν : Law) (a : X) : ℝ := ∫ x, Real.log (dist x a) ∂ν
def phi (s : ℝ) : ℝ := Real.log s + s⁻¹ - 1
def ann (δ : ℝ) : Set X := {x | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + δ}
def F (ν : Law) (δ : ℝ) (a : X) : ℝ := ∫ x in ann δ, phi (dist x a) ∂ν
def e₁ : X := EuclideanSpace.single (0 : Fin 3) 1

/-- Push normalized Euclidean surface measure forward by the sphere inclusion. -/
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

/-- Compact isocapacity, obtained in the other proof from open-set isocapacity.
The capacity radius uses exactly the energy normalization in the shared definitions. -/
def CompactIso : Prop := ∀ K : Set X, IsCompact K → vol K ≤ omega 3 * capRadius K ^ 3

/-- Positive-capacity equilibrium existence for a compact set. -/
def EqExists : Prop := ∀ K : Set X, IsCompact K → 0 < capRadius K → ∃ ν, equilibrium K ν

/-- Clark and Laugesen, Appendix A, Lemma A.1, the Newtonian upper bound. -/
def Frostman : Prop := ∀ (K : Set X) (ν : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → ∀ a, potential ν a ≤ ENNReal.ofReal ((capRadius K)⁻¹)

/-- Clark and Laugesen, Appendix A, uniqueness at positive capacity. -/
def EqUnique : Prop := ∀ (K : Set X) (ν ν' : Law), IsCompact K → 0 < capRadius K →
  equilibrium K ν → equilibrium K ν' → ν = ν'

/-- Clark and Laugesen, Appendix A, radius and equilibrium law of the closed unit ball. -/
def BallLaw : Prop := capRadius (Metric.closedBall (0 : X) 1) = 1 ∧
  leastEnergy (Metric.closedBall (0 : X) 1) = 1 ∧ equilibrium (Metric.closedBall (0 : X) 1) sigma

/-- Bounds on the translated, capacity-scaled equilibrium sequence, before taking a weak limit. -/
def Normalized (ν : ℕ → Law) : Prop :=
  (∀ j, admissible (ν j) ∧ ∀ a, potential (ν j) a ≤ 1) ∧
    Tendsto (fun j => g (ν j) 0) atTop (𝓝 0)

end Stability
open Stability

private theorem integrable_of_compact_law {E : Type*} [NormedAddCommGroup E]
    (μ : Law) (hμ : admissible μ) {f : X → E} (hf : Continuous f) : Integrable f μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hμ.2
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := μ.support) (μ := μ) Measure.support_mem_ae] at h

private theorem continuous_L : Continuous L := by
  unfold L
  exact (continuous_const.add (continuous_norm.pow 2)).log (fun x => by change (1+‖x‖^2:ℝ) ≠ 0; positivity)

private theorem exp_mean_le (μ : Law) (hμ : admissible μ) (f : X → ℝ) (hf : Continuous f) :
    Real.exp (∫ a, f a ∂μ) ≤ ∫ a, Real.exp (f a) ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  exact strictConvexOn_exp.convexOn.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) (integrable_of_compact_law μ hμ hf)
    (integrable_of_compact_law μ hμ (Real.continuous_exp.comp hf))

private theorem adjusted_jensen (μ : Law) (hμ : admissible μ) (z v : X) :
    Real.exp (-cost μ z) * gMeasure μ (z+v)^2 ≤
      ∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  let den (a : X) := 1 + ‖z-a‖^2
  let num (a : X) := dist (z+v) a
  have den_pos (a : X) : 0 < den a := by dsimp [den]; positivity
  have num_cts : Continuous num := continuous_const.dist continuous_id
  have den_cts : Continuous den := continuous_const.add ((continuous_const.sub continuous_id).norm.pow 2)
  let I := ∫ a, num a ^ 2 / den a ∂μ
  have hs : ∀ k : ℕ, Real.exp (-cost μ z) * gMeasure μ (z+v)^2 ≤ I + (Real.exp (-(k:ℝ)))^2 := by
    intro k
    let e := Real.exp (-(k:ℝ))
    have ep : 0 < e := Real.exp_pos _
    let f (a : X) := Real.log (max (num a) e)
    let l (a : X) := Real.log (den a)
    have cf : Continuous f := (num_cts.max continuous_const).log fun a =>
      (ep.trans_le (le_max_right (num a) e)).ne'
    have cl : Continuous l := den_cts.log (fun a => (den_pos a).ne')
    have htr : gMeasure μ (z+v) ≤ Real.exp (∫ a, f a ∂μ) :=
      ciInf_le (f := fun i : ℕ => Real.exp (∫ a, Real.log (max (dist (z+v) a) (Real.exp (-(i:ℝ)))) ∂μ))
        ⟨0, fun _ ⟨i, hi⟩ => hi ▸ (Real.exp_pos _).le⟩ k
    have hnon : 0 ≤ gMeasure μ (z+v) := le_ciInf (fun i => (Real.exp_pos _).le)
    have hsq : gMeasure μ (z+v)^2 ≤ Real.exp (2*(∫ a, f a ∂μ)) := by
      rw [two_mul,Real.exp_add]
      nlinarith [mul_self_le_mul_self hnon htr]
    have hj := exp_mean_le μ hμ (fun a => 2*f a - l a) ((continuous_const.mul cf).sub cl)
    rw [integral_sub ((integrable_of_compact_law μ hμ cf).const_mul 2)
      (integrable_of_compact_law μ hμ cl),integral_const_mul] at hj
    have hcost : (∫ a, l a ∂μ) = cost μ z := rfl
    rw [hcost] at hj
    calc Real.exp (-cost μ z) * gMeasure μ (z+v)^2
        ≤ Real.exp (-cost μ z) * Real.exp (2 * ∫ a, f a ∂μ) := mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = Real.exp (2 * (∫ a, f a ∂μ) - cost μ z) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := hj
      _ ≤ ∫ a, (num a ^ 2 / den a + e^2) ∂μ := by
        apply integral_mono (integrable_of_compact_law μ hμ (Real.continuous_exp.comp ((continuous_const.mul cf).sub cl)))
          (integrable_of_compact_law μ hμ (((num_cts.pow 2).div den_cts (fun a => (den_pos a).ne')).add continuous_const))
        intro a
        change Real.exp (2*f a - l a) ≤ num a ^ 2 / den a + e^2
        simp only [f,l,two_mul,Real.exp_sub,Real.exp_add, Real.exp_log (ep.trans_le (le_max_right _ _)),
          Real.exp_log (den_pos a)]
        rw [div_le_iff₀ (den_pos a), add_mul, div_mul_cancel₀ _ (den_pos a).ne']
        have h1 : 1 ≤ den a := by dsimp [den]; nlinarith [sq_nonneg ‖z-a‖]
        have he : e^2 ≤ e^2 * den a := le_mul_of_one_le_right (sq_nonneg e) h1
        rcases le_total (num a) e with ht | ht
        · rw [max_eq_right ht]; nlinarith [sq_nonneg (num a)]
        · rw [max_eq_left ht]; nlinarith [sq_nonneg (num a)]
      _ = I + e^2 := by
        have hi : Integrable (fun a => num a^2/den a) μ := integrable_of_compact_law μ hμ ((num_cts.pow 2).div den_cts (fun a => (den_pos a).ne'))
        rw [integral_add hi (integrable_const (e^2))]
        simp [I]
  have he : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hI : Real.exp (-cost μ z) * gMeasure μ (z+v)^2 ≤ I :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using (he.pow 2).const_add I) hs
  convert hI using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by simp [num,den,dist_eq_norm,sub_add_eq_add_sub]
private theorem kernel3 (x a : X) : newtonKernel x a = (ENNReal.ofReal (dist x a))⁻¹ := by
  unfold newtonKernel
  norm_num [ENNReal.rpow_neg_one]

private theorem inv_data (ν : Law) (a : X) (B : ℝ) (hB : 0 ≤ B)
    (hpot : potential ν a ≤ ENNReal.ofReal B) :
    ν {a} = 0 ∧ Integrable (fun x => (dist x a)⁻¹) ν ∧ (∫ x, (dist x a)⁻¹ ∂ν) ≤ B := by
  have hf : Measurable (fun x => newtonKernel x a) := by simp only [kernel3]; fun_prop
  have he : (∫⁻ x, newtonKernel x a ∂ν) ≠ ⊤ := (hpot.trans_lt ENNReal.ofReal_lt_top).ne
  have hfinite := ae_lt_top hf he
  have hne : ∀ᵐ x ∂ν, x ≠ a := by
    filter_upwards [hfinite] with x hx
    rintro rfl
    simpa [kernel3] using hx
  have realKer : (fun x => (newtonKernel x a).toReal) = (fun x => (dist x a)⁻¹) := by
    funext x
    simp [kernel3, ENNReal.toReal_ofReal dist_nonneg]
  refine ⟨?_, realKer ▸ integrable_toReal_of_lintegral_ne_top hf.aemeasurable he, ?_⟩
  · simpa [ae_iff] using hne
  · rw [←realKer,integral_toReal hf.aemeasurable hfinite]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpot).trans_eq (ENNReal.toReal_ofReal hB)
private theorem geometric_log_ae (μ : Law) (hμ : admissible μ) (x : X)
    (hne : ∀ᵐ a ∂μ, x ≠ a) (hi : Integrable (fun a => Real.log (dist x a)) μ) :
    gMeasure μ x = Real.exp (∫ a, Real.log (dist x a) ∂μ) := by
  let t (k : ℕ) := Real.exp (-(k:ℝ))
  let f (k : ℕ) (a : X) := Real.log (max (dist x a) (t k))
  have tp (k : ℕ) : 0 < t k := Real.exp_pos _
  have meas (k : ℕ) : Continuous (f k) := ((continuous_const.dist continuous_id).max continuous_const).log
    (fun a => ((tp k).trans_le (le_max_right (dist x a) (t k))).ne')
  have ht : Tendsto t atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := f)
    (f := fun a => Real.log (dist x a)) (fun a => ‖Real.log (dist x a)‖)
    (fun k => (meas k).aestronglyMeasurable) hi.norm
    (fun k => hne.mono fun a ha => by
      by_cases h : t k ≤ dist x a
      · simp [f,max_eq_left h]
      · have he : t k ≤ 1 := by simp [t]
        have hlog := Real.log_le_log (dist_pos.mpr ha) (le_of_not_ge h)
        have hlog' : Real.log (t k) ≤ 0 := Real.log_nonpos (tp k).le he
        simp only [f,max_eq_right (le_of_not_ge h),Real.norm_eq_abs,abs_of_nonpos hlog',
          abs_of_nonpos (hlog.trans hlog')]
        linarith)
    (hne.mono fun a ha => by
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [ht.eventually_lt_const (dist_pos.mpr ha)] with k hk
      simp [f,max_eq_left hk.le])
  have hB : BddBelow (Set.range (fun k => Real.exp (∫ a, f k a ∂μ))) :=
    ⟨0,fun _ ⟨k, hk⟩ => hk ▸ (Real.exp_pos _).le⟩
  refine le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds (Real.continuous_exp.continuousAt.tendsto.comp hlim)
    (fun k => ciInf_le hB k)) ?_
  apply le_ciInf
  intro k
  apply Real.exp_le_exp.mpr
  exact integral_mono_ae hi (integrable_of_compact_law μ hμ (meas k))
    (hne.mono fun a ha => Real.log_le_log (dist_pos.mpr ha) (le_max_left _ _))
private theorem omega3_pos : 0 < omega 3 :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume (0:X) zero_lt_one).ne' measure_ball_lt_top.ne

private theorem solid3_regular (μ : Law) (hμ : admissible μ) :
    MeasurableSet (measureSolid μ 1) ∧ volume (measureSolid μ 1) < ⊤ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hm : Measurable (gMeasure μ) := by
    apply Measurable.iInf
    intro k
    apply Real.measurable_exp.comp
    have hp : Continuous (fun p : X × X => Real.log (max (dist p.1 p.2) (Real.exp (-(k:ℝ))))) :=
      ((continuous_fst.dist continuous_snd).max continuous_const).log
        (fun p => ((Real.exp_pos _).trans_le (le_max_right (dist p.1 p.2) _)).ne')
    exact hp.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨B,hB⟩ := hμ.2.isBounded.exists_norm_le
  have hsub : measureSolid μ 1 ⊆ Metric.closedBall 0 (B+2) := by
    intro x hx
    change gMeasure μ x ≤ 1 at hx
    by_contra! ho
    have hnorm : B + 2 < ‖x‖ := by simpa [Metric.mem_closedBall] using ho
    have hg : 2 ≤ gMeasure μ x := by
      apply le_ciInf
      intro k
      let f (a : X) := Real.log (max (dist x a) (Real.exp (-(k:ℝ))))
      have cf : Continuous f := ((continuous_const.dist continuous_id).max continuous_const).log
        (fun a => ((Real.exp_pos _).trans_le (le_max_right (dist x a) _)).ne')
      apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mp
      have hh := integral_mono_ae (integrable_const (Real.log 2)) (integrable_of_compact_law μ hμ cf) (by
        filter_upwards [Measure.support_mem_ae (μ := μ)] with a ha
        apply Real.log_le_log (by norm_num)
        apply le_trans _ (le_max_left _ _)
        rw [dist_eq_norm]
        linarith [norm_sub_norm_le x a,hB a ha])
      simpa [f] using hh
    linarith
  exact ⟨measurableSet_le hm measurable_const,(measure_mono hsub).trans_lt measure_closedBall_lt_top⟩

/-- Coercivity and continuity give a minimizer; the vector integral there vanishes. -/
theorem stability_center (μ : Law) (hμ : admissible μ) :
    Continuous (cost μ) ∧ Tendsto (cost μ) (cocompact X) atTop ∧
    (∃ z, cost μ z = J μ) ∧ ∀ z, cost μ z = J μ →
      fderiv ℝ (cost μ) z = 0 ∧ (∫ a, (1 + ‖z-a‖^2)⁻¹ • (z-a) ∂μ) = 0 := by
  letI : IsProbabilityMeasure μ := hμ.1
  let D (z a : X) : X →L[ℝ] ℝ := (2/(1+‖z-a‖^2)) • innerSL ℝ (z-a)
  have hD (z a : X) : HasFDerivAt (fun x : X => L (x-a)) (D z a) z := by
    have h := ((((hasFDerivAt_id (𝕜 := ℝ) z).sub_const a).norm_sq).const_add 1).log
      (show 1+‖z-a‖^2 ≠ 0 by positivity)
    convert h using 1
    · rfl
    · ext v
      simp [D, two_smul, div_eq_mul_inv] <;> ring
  have Dcont (z : X) : Continuous (D z) := by
    unfold D
    exact (continuous_const.div (continuous_const.add ((continuous_const.sub continuous_id).norm.pow 2))
      (fun a => by change (1+‖z-a‖^2:ℝ) ≠ 0; positivity)).smul ((innerSL ℝ).continuous.comp (continuous_const.sub continuous_id))
  have iD (z : X) := integrable_of_compact_law μ hμ (Dcont z)
  have hi (z : X) := integrable_of_compact_law μ hμ (continuous_L.comp (continuous_const.sub continuous_id) :
    Continuous (fun a : X => L (z-a)))
  have derivCost (z : X) : HasFDerivAt (cost μ) (∫ a, D z a ∂μ) z := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
      (bound := fun _ : X => (1:ℝ)) Filter.univ_mem
    · exact Eventually.of_forall fun x => (continuous_L.comp (continuous_const.sub continuous_id) :
        Continuous (fun a : X => L (x-a))).aestronglyMeasurable
    · exact hi z
    · exact (Dcont z).aestronglyMeasurable
    · apply Eventually.of_forall
      intro a x _
      simp only [D, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (2:ℝ)/(1+‖x-a‖^2) by positivity),
        innerSL_apply_norm]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖x-a‖-1)]
    · exact integrable_const _
    · exact Eventually.of_forall fun a x _ => hD x a
  have cont : Continuous (cost μ) := continuous_iff_continuousAt.mpr fun z =>
    (derivCost z).continuousAt
  obtain ⟨R,hR⟩ := hμ.2.isBounded.exists_norm_le
  have coerc : Tendsto (cost μ) (cocompact X) atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_norm_cocompact_atTop (E := X)).eventually_ge_atTop (max (Real.exp b) 1 + R)] with z hz
    have hpoint : ∀ᵐ a ∂μ, b ≤ L (z-a) := by
      filter_upwards [Measure.support_mem_ae (μ := μ)] with a ha
      have hdist := norm_sub_norm_le z a
      have hr := hR a ha
      have ha1 : 1 ≤ ‖z-a‖ := by linarith [le_max_right (Real.exp b) 1]
      have hab : Real.exp b ≤ ‖z-a‖ := by linarith [le_max_left (Real.exp b) 1]
      unfold L
      apply (Real.le_log_iff_exp_le (by positivity)).2
      nlinarith [mul_nonneg (norm_nonneg (z-a)) (sub_nonneg.mpr ha1)]
    simpa [cost] using integral_mono_ae (integrable_const b) (hi z) hpoint
  obtain ⟨z₀,hm⟩ := cont.exists_forall_le' 0 (coerc.eventually_ge_atTop _)
  have jeq : J μ = cost μ z₀ := IsLeast.csInf_eq
    ⟨Set.mem_range_self z₀, fun _ ⟨y,hy⟩ => hy ▸ hm y⟩
  refine ⟨cont, coerc, ⟨z₀, jeq.symm⟩, ?_⟩
  intro z hz
  have hmin : IsLocalMin (cost μ) z := Eventually.of_forall fun y => (hz.trans jeq) ▸ hm y
  have hzero := hmin.fderiv_eq_zero
  refine ⟨hzero, ?_⟩
  have hzeroD := (derivCost z).fderiv.symm.trans hzero
  let V (a : X) := (1+‖z-a‖^2)⁻¹ • (z-a)
  have hV : Continuous V := ((continuous_const.add ((continuous_const.sub continuous_id).norm.pow 2)).inv₀
    (fun a => by change (1+‖z-a‖^2:ℝ) ≠ 0; positivity)).smul (continuous_const.sub continuous_id)
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ V (integrable_of_compact_law μ hμ hV)
  intro v
  have hv := congrArg (fun h : X →L[ℝ] ℝ => h v) hzeroD
  rw [ContinuousLinearMap.integral_apply (iD z)] at hv
  have hfun : (fun a : X => D z a v) = (fun a => 2 * inner ℝ v (V a)) := by
    funext a
    change (2/(1+‖z-a‖^2)) * inner ℝ (z-a) v = 2 * inner ℝ v ((1+‖z-a‖^2)⁻¹ • (z-a))
    rw [real_inner_smul_right,real_inner_comm (z-a) v]
    ring
  rw [hfun, integral_const_mul] at hv
  change 2 * _ = 0 at hv
  linarith

/-- Both Jensen inequalities, the exact quadratic identity and the inscribed ball. -/
theorem stability_center_ball (μ : Law) (hμ : admissible μ) (z : X) (hz : cost μ z = J μ) :
    0 ≤ J μ ∧ Real.exp (-J μ) ≤ M μ z ∧
    (∀ v : X, ‖v‖ ≤ 1 →
      Real.exp (-J μ) * gMeasure μ (z+v)^2 ≤ (∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ) ∧
      (∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ) = 1 - (1-‖v‖^2) * M μ z ∧
      gMeasure μ (z+v)^2 ≤ Real.exp (J μ) - 1 + ‖v‖^2) ∧
    (J μ < Real.log 2 →
      Metric.closedBall z (Real.sqrt (2-Real.exp (J μ))) ⊆ measureSolid μ 1) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let r (a : X) := (1 + ‖z-a‖^2)⁻¹
  have hden (a : X) : (1+‖z-a‖^2:ℝ) ≠ 0 := by positivity
  have cr : Continuous r := (continuous_const.add ((continuous_const.sub continuous_id).norm.pow 2)).inv₀ hden
  have cv : Continuous (fun a : X => r a • (z-a)) := cr.smul (continuous_const.sub continuous_id)
  have hJ : 0 ≤ J μ := by
    rw [←hz]
    apply integral_nonneg
    intro a
    exact Real.log_nonneg (by linarith [sq_nonneg ‖z-a‖])
  have hM : Real.exp (-J μ) ≤ M μ z := by
    have hj := exp_mean_le μ hμ (fun a => -L (z-a)) (continuous_L.comp (continuous_const.sub continuous_id)).neg
    rw [integral_neg] at hj
    change Real.exp (-cost μ z) ≤ _ at hj
    rw [hz] at hj
    exact hj.trans_eq (integral_congr_ae (Eventually.of_forall fun a => by
      change Real.exp (-Real.log (1+‖z-a‖^2)) = (1+‖z-a‖^2)⁻¹
      rw [Real.exp_neg, Real.exp_log (by positivity)]))
  have hzv := ((stability_center μ hμ).2.2.2 z hz).2
  have hcalc (v : X) : (∫ a, ‖z-a+v‖^2 / (1+‖z-a‖^2) ∂μ) = 1-(1-‖v‖^2)*M μ z := by
    have hinner : (∫ a, inner ℝ v (r a • (z-a)) ∂μ) = 0 := by
      rw [integral_inner (integrable_of_compact_law μ hμ cv)]
      change inner ℝ v (∫ a, (1+‖z-a‖^2)⁻¹ • (z-a) ∂μ) = 0
      rw [hzv,inner_zero_right]
    have hi := integrable_of_compact_law μ hμ cr
    have hci : Continuous (fun a : X => 2 * inner ℝ v (r a • (z-a))) :=
      continuous_const.mul (continuous_const.inner cv)
    have heq (a : X) : ‖z-a+v‖^2 / (1+‖z-a‖^2) =
        (1 - (1-‖v‖^2) * r a) + 2 * inner ℝ v (r a • (z-a)) := by
      rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm (z-a) v]
      dsimp [r]
      field_simp [hden a]
      <;> ring
    simp_rw [heq]
    have i1 : Integrable (fun a => (1-‖v‖^2)*r a) μ := hi.const_mul _
    have i2 : Integrable (fun a => 1-(1-‖v‖^2)*r a) μ := (integrable_const 1).sub i1
    have i3 : Integrable (fun a => 2 * inner ℝ v (r a • (z-a))) μ := integrable_of_compact_law μ hμ hci
    rw [integral_add i2 i3, integral_sub (integrable_const (1:ℝ)) i1,
      integral_const_mul, integral_const_mul, hinner]
    simp [M,r]
  have bound (v : X) (hv : ‖v‖ ≤ 1) : gMeasure μ (z+v)^2 ≤ Real.exp (J μ) - 1 + ‖v‖^2 := by
    have h := adjusted_jensen μ hμ z v
    rw [hz,hcalc] at h
    have hv' : 0 ≤ 1-‖v‖^2 := by nlinarith [norm_nonneg v, sq_le_sq' (by linarith [norm_nonneg v]) hv]
    have hm := mul_le_mul_of_nonneg_left hM hv'
    rw [Real.exp_neg] at h hm
    have hh : (Real.exp (J μ))⁻¹ * (gMeasure μ (z+v)^2 + 1 - ‖v‖^2) ≤ 1 := by nlinarith
    have hh' : (gMeasure μ (z+v)^2 + 1 - ‖v‖^2) / Real.exp (J μ) ≤ 1 := by
      simpa [div_eq_inv_mul] using hh
    linarith [(div_le_one (Real.exp_pos _)).mp hh']
  refine ⟨hJ,hM,fun v hv => ⟨by simpa [hz] using adjusted_jensen μ hμ z v,hcalc v,bound v hv⟩,?_⟩
  intro hj x hx
  have hp : 0 ≤ 2-Real.exp (J μ) := sub_nonneg.mpr ((Real.lt_log_iff_exp_lt (by norm_num)).mp hj).le
  have hs := Real.sq_sqrt hp
  have hx' : ‖x-z‖ ≤ Real.sqrt (2-Real.exp (J μ)) := by simpa [dist_eq_norm] using hx
  have h1 : Real.sqrt (2-Real.exp (J μ)) ≤ 1 := by nlinarith [Real.add_one_le_exp (J μ),Real.sqrt_nonneg (2-Real.exp (J μ))]
  have h := bound (x-z) (hx'.trans h1)
  rw [show z + (x-z) = x by abel] at h
  change gMeasure μ x ≤ 1
  have h2 := mul_self_le_mul_self (norm_nonneg (x-z)) hx'
  nlinarith [sq_nonneg (gMeasure μ x - 1)]

/-- Scalar error estimates at zero. -/
theorem stability_scalar_limits :
    (∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t ∈ Set.Icc 0 δ,
      |(1 - Real.sqrt (2 - Real.exp t)) - t/2| ≤ C*t^2) ∧
    Tendsto (fun d : ℝ => -Real.log (1-d)/d) (𝓝[>] 0) (𝓝 1) := by
  constructor
  · let δ : ℝ := Real.log 2 / 2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let f := fun t : ℝ => 1 - Real.sqrt (2 - Real.exp t)
    have harg : ∀ t ∈ Set.Icc 0 δ, 2 - Real.exp t ≠ 0 := by
      intro t ht
      have h : t < Real.log 2 := lt_of_le_of_lt ht.2 (by dsimp [δ]; linarith)
      exact ne_of_gt (sub_pos.mpr ((Real.lt_log_iff_exp_lt (by norm_num)).mp h))
    have hs : ContDiffOn ℝ 2 (fun t : ℝ => 2-Real.exp t) (Set.Icc 0 δ) :=
      contDiffOn_const.sub Real.contDiff_exp.contDiffOn
    have hf : ContDiffOn ℝ 2 f (Set.Icc 0 δ) := contDiffOn_const.sub (hs.sqrt harg)
    obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (n := 1) hδ.le hf
    have h0 : HasDerivAt f (1/2) 0 := by
      have h := ((Real.hasDerivAt_exp 0).const_sub 2).sqrt (by norm_num)
      convert h.const_sub 1 using 1 <;> norm_num [f]
    have hder := h0.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hδ 0 (Set.left_mem_Icc.mpr hδ.le))
    refine ⟨max C 1, δ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hδ, ?_⟩
    intro t ht
    have htay : taylorWithinEval f 1 (Set.Icc 0 δ) 0 t = t/2 := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval]
      simp [iteratedDerivWithin_one, hder, f]
      <;> ring
    have h := hC t ht
    rw [htay] at h
    exact (by simpa [f, Real.norm_eq_abs] using h : |(1-Real.sqrt (2-Real.exp t))-t/2| ≤ C*t^2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg t))
  · have h := (((hasDerivAt_id (0:ℝ)).const_sub 1).log (by norm_num)).neg.tendsto_slope_zero_right
    simpa [div_eq_mul_inv,mul_comm] using h

/-- Compact exhaustion at the printed error scale. -/
theorem stability_compact_piece (μ : Law) (hμ : admissible μ)
    (hD : 0 < deficit μ 1) (hD' : deficit μ 1 < 1) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ measureSolid μ 1 ∧
      omega 3 * Real.exp (-gamma μ - (gamma μ)^2) ≤ vol K := by
  let D := deficit μ 1
  let γ := gamma μ
  have hw := omega3_pos
  have hr : 0 < 1-D := by dsimp [D]; linarith
  have hg : 0 < γ := by
    change 0 < -Real.log (1-D)
    exact neg_pos.mpr (Real.log_neg hr (by dsimp [D]; linarith))
  have he : Real.exp (-γ) = 1 - D := by
    change Real.exp (- -Real.log (1-D)) = _
    simpa using Real.exp_log hr
  have hvol : vol (measureSolid μ 1) = omega 3 * Real.exp (-γ) := by
    rw [he]
    dsimp [D,deficit]
    field_simp [hw.ne']
    <;> ring
  have hlt : omega 3 * Real.exp (-γ-γ^2) < vol (measureSolid μ 1) := by
    rw [hvol]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by nlinarith [sq_pos_of_pos hg])) hw
  obtain ⟨hm,hfin⟩ := solid3_regular μ hμ
  obtain ⟨K, hsub,hK,hgt⟩ := hm.exists_lt_isCompact_of_ne_top hfin.ne
    ((ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hw.le (Real.exp_pos _).le) hfin.ne).mpr hlt)
  exact ⟨K,hK,hsub,((ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hw.le (Real.exp_pos _).le) hK.measure_ne_top).mp hgt).le⟩

/-- The inverse-potential bound removes the pole before real integration. -/
theorem stability_log_moment (ν : Law) (hν : admissible ν) (c : ℝ) (hc : 0 < c)
    (hpot : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) (a : X) :
    ν {a} = 0 ∧ Integrable (fun x => Real.log (dist x a)) ν ∧ Real.log c ≤ g ν a := by
  letI : IsProbabilityMeasure ν := hν.1
  obtain ⟨hn,hi,hint⟩ := inv_data ν a c⁻¹ (inv_nonneg.mpr hc.le) (hpot a)
  have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using hn
  have hgi : Integrable (fun x => Real.log (dist x a)) ν := by
    have hd := integrable_of_compact_law ν hν (continuous_id.dist continuous_const : Continuous (fun x : X => dist x a))
    apply (hd.add hi).mono' (Real.measurable_log.comp (continuous_id.dist continuous_const).measurable).aestronglyMeasurable
    filter_upwards [hne] with x hx
    have hp := dist_pos.mpr hx
    rw [Real.norm_eq_abs,abs_le]
    have h1 := Real.log_le_sub_one_of_pos hp
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at h2
    change -(dist x a + (dist x a)⁻¹) ≤ Real.log (dist x a) ∧ Real.log (dist x a) ≤ dist x a + (dist x a)⁻¹
    constructor <;> linarith [inv_pos.mpr hp]
  have hform : (Real.exp ∘ (fun x => -Real.log (dist x a))) =ᵐ[ν] (fun x => (dist x a)⁻¹) := by
    filter_upwards [hne] with x hx
    simp [Function.comp_def, Real.exp_neg,Real.exp_log (dist_pos.mpr hx)]
  have hj := strictConvexOn_exp.convexOn.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hgi.neg (hi.congr hform.symm)
  have hneg : (∫ x, -Real.log (dist x a) ∂ν) = -g ν a := integral_neg _
  change Real.exp (∫ x, -Real.log (dist x a) ∂ν) ≤ _ at hj
  rw [hneg] at hj
  have he : Real.exp (-g ν a) ≤ c⁻¹ := hj.trans ((integral_congr_ae hform).le.trans hint)
  have hh := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp,Real.log_inv] at hh
  exact ⟨hn,hgi,by linarith⟩

private theorem log_product (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (c : ℝ) (hc : 0 < c) (hpot : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) :
    Integrable (fun q : X × X => Real.log (dist q.1 q.2)) (ν.prod μ) := by
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure ν := hν.1
  let f (x a : X) := Real.log (dist x a)
  have hlog (a : X) := stability_log_moment ν hν c hc hpot a
  have hm : Measurable (Function.uncurry f) :=
    Real.measurable_log.comp (continuous_fst.dist continuous_snd).measurable
  have hprod : Integrable (Function.uncurry f) (ν.prod μ) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun a => (hlog a).2.1, ?_⟩
    have hn := integrable_of_compact_law ν hν (continuous_norm : Continuous (norm : X → ℝ))
    have hcst : Continuous (fun a : X => (∫ x, ‖x‖ ∂ν) + ‖a‖ + c⁻¹) := (continuous_const.add continuous_norm).add continuous_const
    apply (integrable_of_compact_law μ hμ hcst).mono' hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    apply Eventually.of_forall
    intro a
    have hinv := inv_data ν a c⁻¹ (inv_nonneg.mpr hc.le) (hpot a)
    have hd : Integrable (fun x : X => ‖x‖+‖a‖+(dist x a)⁻¹) ν := (hn.add (integrable_const _)).add hinv.2.1
    change ‖∫ x, ‖Real.log (dist x a)‖ ∂ν‖ ≤ _
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc (∫ x, ‖Real.log (dist x a)‖ ∂ν) ≤ ∫ x, ‖x‖+‖a‖+(dist x a)⁻¹ ∂ν := by
           apply integral_mono_ae (hlog a).2.1.norm hd
           have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using hinv.1
           filter_upwards [hne] with x hx
           have hp := dist_pos.mpr hx
           have h1 := Real.log_le_sub_one_of_pos hp
           have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
           rw [Real.log_inv] at h2
           have ht : dist x a ≤ ‖x‖ + ‖a‖ := by simpa using dist_triangle x 0 a
           rw [Real.norm_eq_abs, abs_le]
           constructor <;> linarith [norm_nonneg x,norm_nonneg a,inv_pos.mpr hp]
         _ ≤ _ := by
           have hadd : Integrable (fun x : X => ‖x‖+‖a‖) ν := hn.add (integrable_const _)
           rw [integral_add hadd hinv.2.1, integral_add hn (integrable_const _)]
           simpa using add_le_add_left hinv.2.2 ((∫ x, ‖x‖ ∂ν) + ‖a‖)
  exact hprod

private theorem admissible_map (μ : Law) (hμ : admissible μ) {T : X → X}
    (hT : Continuous T) : admissible (μ.map T) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hK := hμ.2.image hT
  refine ⟨(Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hμ.1,
    hK.of_isClosed_subset Measure.isClosed_support (Measure.support_subset_of_isClosed hK.isClosed ?_)⟩
  apply (ae_map_iff hT.aemeasurable (p := fun x => x ∈ T '' μ.support) hK.measurableSet).2
  filter_upwards [Measure.support_mem_ae (μ := μ)] with x hx
  exact Set.mem_image_of_mem T hx

private theorem measurable_log_moment (ν : Law) [IsFiniteMeasure ν] : Measurable (g ν) :=
  (Real.measurable_log.comp (continuous_fst.dist continuous_snd).measurable).stronglyMeasurable.integral_prod_left'.measurable

private theorem measurable_kernel (a : X) : Measurable (fun x : X => newtonKernel x a) := by
  simp only [kernel3]
  fun_prop

private theorem sigma_sphere : ∀ᵐ x ∂sigma, x ∈ Metric.sphere (0:X) 1 := by
  unfold sigma
  apply Measure.ae_smul_measure
  exact (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).ae_map_iff.mpr
    (Eventually.of_forall fun x => x.property)

private theorem sigma_admissible : admissible sigma := by
  constructor
  · constructor
    unfold sigma
    rw [Measure.smul_apply,Measure.map_apply measurable_subtype_coe MeasurableSet.univ,Set.preimage_univ]
    apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (by simp [X,Space]) (Metric.measure_ball_pos volume (0:X) zero_lt_one).ne'
  · exact (isCompact_sphere (0:X) 1).of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed Metric.isClosed_sphere sigma_sphere)

open scoped Pointwise

private theorem sigma_map_isometry (U : X ≃ₗᵢ[ℝ] X) : Measure.map U sigma = sigma := by
  let I := Subtype.val (p := fun x : X => x ∈ Metric.sphere (0:X) 1)
  have hI : Measurable I := measurable_subtype_coe
  have hU := U.continuous.measurable
  ext A hA
  rw [Measure.map_apply hU hA]
  let sector (D : Set X) := Set.Ioo (0:ℝ) 1 • (I '' (I ⁻¹' D))
  have form (D : Set X) (hD : MeasurableSet D) : sigma D =
      ((volume : Law).toSphere Set.univ)⁻¹ * ((Module.finrank ℝ X : ℝ≥0∞) * volume (sector D)) := by
    change ((volume.toSphere Set.univ)⁻¹ • (volume.toSphere.map I)) D = _
    rw [Measure.smul_apply, Measure.map_apply hI hD, Measure.toSphere_apply' _ (hI hD)]
    rfl
  have hsec : sector (U ⁻¹' A) = U ⁻¹' sector A := by
    ext x
    constructor
    · rintro ⟨r,hr,_,⟨θ,hθ,rfl⟩,rfl⟩
      let t : Metric.sphere (0:X) 1 := ⟨U θ,by simpa [Metric.mem_sphere] using θ.property⟩
      exact ⟨r,hr,U θ,⟨t,hθ,rfl⟩,(U.map_smul r (I θ)).symm⟩
    · rintro ⟨r,hr,_,⟨θ,hθ,rfl⟩,heq⟩
      let t : Metric.sphere (0:X) 1 := ⟨U.symm θ,by simpa [Metric.mem_sphere] using θ.property⟩
      refine ⟨r,hr,U.symm θ,⟨t,?_,rfl⟩,?_⟩
      · simpa [Set.mem_preimage,I,t] using hθ
      · apply U.injective
        simpa [I] using heq
  rw [form _ (hU hA),form _ hA,hsec,U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding]


/-- Absolute integrability on the product and the logarithm identity almost everywhere. -/
theorem stability_fubini (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (K : Set X) (hK : IsCompact K) (hsub : K ⊆ measureSolid μ 1) (hνK : ν Kᶜ = 0)
    (c : ℝ) (hc : 0 < c) (hpot : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) :
    Integrable (fun p : X × X => Real.log (dist p.1 p.2)) (ν.prod μ) ∧
    (∀ᵐ x ∂ν, 0 < gMeasure μ x ∧ Real.log (gMeasure μ x) = ∫ a, Real.log (dist x a) ∂μ) ∧
    (∫ a, g ν a ∂μ) = (∫ x, Real.log (gMeasure μ x) ∂ν) ∧
    (∫ a, g ν a ∂μ) ≤ 0 ∧ c ≤ 1 := by
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure ν := hν.1
  let f (x a : X) := Real.log (dist x a)
  have hlog (a : X) := stability_log_moment ν hν c hc hpot a
  have hprod : Integrable (Function.uncurry f) (ν.prod μ) := log_product μ ν hμ hν c hc hpot
  have hne : ∀ᵐ x ∂ν, ∀ᵐ a ∂μ, x ≠ a := by
    apply (Measure.ae_ae_comm (p := fun x a : X => x ≠ a) (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall fun a => by simpa [ae_iff] using (hlog a).1
  have hbridge : ∀ᵐ x ∂ν, 0 < gMeasure μ x ∧ Real.log (gMeasure μ x) = ∫ a, f x a ∂μ := by
    filter_upwards [hne, hprod.prod_right_ae] with x hx hi
    rw [geometric_log_ae μ hμ x hx hi]
    exact ⟨Real.exp_pos _,Real.log_exp _⟩
  have hswap : (∫ a, g ν a ∂μ) = (∫ x, Real.log (gMeasure μ x) ∂ν) :=
    (integral_integral_swap (f := f) hprod).symm.trans (integral_congr_ae (hbridge.mono (fun _ hx => hx.2.symm)))
  have hKν : ∀ᵐ x ∂ν, x ∈ K := hνK
  have havg : (∫ a, g ν a ∂μ) ≤ 0 := by
    rw [hswap]
    apply integral_nonpos_of_ae
    filter_upwards [hKν,hbridge] with x hx hb
    exact Real.log_nonpos hb.1.le (hsub hx)
  refine ⟨hprod,hbridge,hswap,havg,?_⟩
  have hbound := integral_mono_ae (integrable_const (Real.log c)) hprod.integral_prod_right
    (Eventually.of_forall (fun a => (hlog a).2.2))
  apply (Real.log_le_log_iff hc zero_lt_one).mp
  simpa [g] using (show Real.log c ≤ 0 by
    have hh : Real.log c ≤ ∫ a, g ν a ∂μ := by simpa [g,f] using hbound
    linarith)

/-- An equilibrium measure on a compact subset with the required volume and beta bounds. -/
theorem stability_piece_bounds (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) (hD : 0 < deficit μ 1) (hD' : deficit μ 1 < 1) :
    ∃ (K : Set X) (ν : Law), IsCompact K ∧ K ⊆ measureSolid μ 1 ∧
      omega 3 * Real.exp (-gamma μ - (gamma μ)^2) ≤ vol K ∧ equilibrium K ν ∧
      0 < capRadius K ∧ capRadius K ≤ 1 ∧ (vol K / omega 3) ^ (1/3:ℝ) ≤ capRadius K ∧
      0 ≤ beta K ∧ beta K ≤ (gamma μ + (gamma μ)^2)/3 := by
  obtain ⟨K,hK,hsub,hvol⟩ := stability_compact_piece μ hμ hD hD'
  have hw := omega3_pos
  have hv := (mul_pos hw (Real.exp_pos _)).trans_le hvol
  have hiso := iso K hK
  have hc : 0 < capRadius K := by
    by_contra! hn
    have h0 : capRadius K = 0 := le_antisymm hn ENNReal.toReal_nonneg
    rw [h0] at hiso
    norm_num at hiso
    linarith
  obtain ⟨ν,he⟩ := existsEq K hK hc
  have hν : admissible ν := ⟨he.1,hK.of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed hK.isClosed he.2.1)⟩
  have h1 := (stability_fubini μ ν hμ hν K hK hsub he.2.1 (capRadius K) hc (frost K ν hK hc he)).2.2.2.2
  have hp : vol K / omega 3 ≤ capRadius K^3 := (div_le_iff₀ hw).mpr (by linarith)
  have hl : Real.exp (-gamma μ - gamma μ^2) ≤ capRadius K ^ 3 :=
    (le_of_mul_le_mul_left (hvol.trans hiso) hw)
  have hlog := Real.log_le_log (Real.exp_pos _) hl
  rw [Real.log_exp,Real.log_pow] at hlog
  refine ⟨K,ν,hK,hsub,hvol,he,hc,h1,?_,neg_nonneg.mpr (Real.log_nonpos hc.le h1),?_⟩
  · rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (div_nonneg hv.le hw.le) hc.le (by norm_num : (0:ℝ)<3)).mpr
    simpa using hp
  · dsimp [beta]
    push_cast at hlog
    linarith

/-- The compact-set comparison applies to every positive-volume compact subset. -/
theorem stability_compact_comparison (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) (K : Set X) (hK : IsCompact K) (hvol : 0 < vol K)
    (hsub : K ⊆ measureSolid μ 1) :
    volume K < ⊤ ∧ 0 < capRadius K ∧ capRadius K ≤ 1 ∧ vol K ≤ omega 3 * capRadius K ^ 3 := by
  have he := iso K hK
  have hc : 0 < capRadius K := by
    by_contra! hn
    have hf : capRadius K = 0 := le_antisymm hn ENNReal.toReal_nonneg
    rw [hf] at he
    norm_num at he
    linarith
  obtain ⟨ν,heq⟩ := existsEq K hK hc
  have hν : admissible ν := ⟨heq.1,hK.of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed hK.isClosed heq.2.1)⟩
  exact ⟨hK.measure_lt_top,hc,(stability_fubini μ ν hμ hν K hK hsub heq.2.1 (capRadius K) hc
    (frost K ν hK hc heq)).2.2.2.2,he⟩

/-- Volume upper bound for general compactly supported source probabilities. -/
theorem stability_measure_volume (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (μ : Law) (hμ : admissible μ) :
    volume (measureSolid μ 1) < ⊤ ∧ vol (measureSolid μ 1) ≤ omega 3 := by
  obtain ⟨hm,hfin⟩ := solid3_regular μ hμ
  refine ⟨hfin, ?_⟩
  by_contra! h
  have hw := omega3_pos
  obtain ⟨K,hsub,hK,hgt⟩ := hm.exists_lt_isCompact_of_ne_top hfin.ne
    ((ENNReal.ofReal_lt_iff_lt_toReal hw.le hfin.ne).mpr h)
  have hgt' : omega 3 < vol K := (ENNReal.ofReal_lt_iff_lt_toReal hw.le hK.measure_ne_top).mp hgt
  obtain ⟨_,hc,hc1,hle⟩ := stability_compact_comparison iso existsEq frost μ hμ K hK (hw.trans hgt') hsub
  have hp : capRadius K ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hc.le hc1 3
  linarith [mul_le_mul_of_nonneg_left hp hw.le]

/-- The inverse-distance formula includes the pole; the log formula is off the pole. -/
theorem stability_rescale_dist (c : ℝ) (hc : 0 < c) (x a : X) :
    newtonKernel (c⁻¹ • x) (c⁻¹ • a) = ENNReal.ofReal c * newtonKernel x a ∧
    (x ≠ a → Real.log (dist (c⁻¹ • x) (c⁻¹ • a)) = Real.log (dist x a) - Real.log c) := by
  have hd : dist (c⁻¹ • x) (c⁻¹ • a) = c⁻¹ * dist x a := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  constructor
  · unfold newtonKernel
    norm_num only [Nat.cast_ofNat, show (2:ℝ)-3 = -1 by norm_num, ENNReal.rpow_neg_one]
    by_cases h : x = a
    · subst a
      simp [ENNReal.ofReal_pos.mpr hc |>.ne']
    · have ht : 0 < dist x a := dist_pos.mpr h
      rw [hd, ← ENNReal.ofReal_inv_of_pos (mul_pos (inv_pos.mpr hc) ht),
        ← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_mul hc.le]
      congr 1
      simp [mul_comm]
  · intro h
    rw [hd, Real.log_mul (inv_ne_zero hc.ne') (dist_pos.mpr h).ne', Real.log_inv]
    ring

/-- Normalize the equilibrium law and center the two laws at the same point. -/
theorem stability_normalize (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hp : ∀ a, potential ν a ≤ ENNReal.ofReal c⁻¹) (havg : (∫ a, g ν a ∂μ) ≤ 0) :
    (∀ a, potential (scaled c ν) a ≤ 1 ∧ 0 ≤ g (scaled c ν) a) ∧
    (∫ a, g (scaled c ν) a ∂(scaled c μ)) ≤ -Real.log c ∧
    ∃ p : X, g (scaled c ν) p ≤ -Real.log c + ε ∧
      g (shifted p (scaled c ν)) 0 = g (scaled c ν) p ∧
      (∀ a, potential (shifted p (scaled c ν)) a ≤ 1) ∧
      (∫ a, g (shifted p (scaled c ν)) a ∂(shifted p (scaled c μ))) ≤ -Real.log c ∧
      ∀ x a : X, dist (x-p) (a-p) = dist x a := by
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure ν := hν.1
  let T (x : X) := c⁻¹ • x
  have hT : Continuous T := continuous_id.const_smul (c⁻¹)
  have undo (a : X) : T (c • a) = a := by simp [T,smul_smul,hc.ne']
  have hμs : admissible (scaled c μ) := admissible_map μ hμ hT
  have hνs : admissible (scaled c ν) := admissible_map ν hν hT
  letI : IsProbabilityMeasure (scaled c μ) := hμs.1
  letI : IsProbabilityMeasure (scaled c ν) := hνs.1
  have hlog (a : X) := stability_log_moment ν hν c hc hp a
  have hscaled (a : X) : potential (scaled c ν) (T a) ≤ 1 := by
    unfold potential scaled
    rw [lintegral_map (measurable_kernel _) hT.measurable]
    change (∫⁻ x, newtonKernel (c⁻¹ • x) (c⁻¹ • a) ∂ν) ≤ 1
    simp_rw [(stability_rescale_dist c hc _ a).1]
    rw [lintegral_const_mul _ (measurable_kernel a)]
    calc ENNReal.ofReal c * potential ν a ≤ ENNReal.ofReal c * ENNReal.ofReal c⁻¹ := mul_le_mul_right (hp a) _
      _ = 1 := by rw [← ENNReal.ofReal_mul hc.le]; simp [hc.ne']
  have changeg (a : X) : g (scaled c ν) (T a) = g ν a - Real.log c := by
    unfold g scaled
    rw [integral_map (f := fun x : X => Real.log (dist x (T a))) hT.aemeasurable (Real.measurable_log.comp (continuous_id.dist continuous_const).measurable).aestronglyMeasurable]
    have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using (hlog a).1
    calc _ = ∫ x, Real.log (dist x a) - Real.log c ∂ν :=
          integral_congr_ae (hne.mono (fun x hx => (stability_rescale_dist c hc x a).2 hx))
      _ = _ := by rw [integral_sub (hlog a).2.1 (integrable_const _)]; simp
  have hboth (a : X) : potential (scaled c ν) a ≤ 1 ∧ 0 ≤ g (scaled c ν) a := by
    rw [← undo a]
    exact ⟨hscaled _,by rw [changeg]; linarith [(hlog (c • a)).2.2]⟩
  have hgi : Integrable (g ν) μ := (log_product μ ν hμ hν c hc hp).integral_prod_right
  have hav : (∫ a, g (scaled c ν) a ∂(scaled c μ)) ≤ -Real.log c := by
    change (∫ a, g (scaled c ν) a ∂(μ.map T)) ≤ _
    rw [integral_map hT.aemeasurable (measurable_log_moment _).aestronglyMeasurable]
    simp_rw [changeg]
    rw [integral_sub hgi (integrable_const _)]
    simpa using sub_le_sub_right havg (Real.log c)
  have hgi' : Integrable (g (scaled c ν)) (scaled c μ) :=
    (log_product _ _ hμs hνs 1 zero_lt_one (fun a => by simpa using (hboth a).1)).integral_prod_right
  obtain ⟨p,hp'⟩ := exists_le_integral hgi'
  let S (x : X) := x-p
  have hS : Continuous S := continuous_id.sub continuous_const
  have hνt : admissible (shifted p (scaled c ν)) := admissible_map _ hνs hS
  letI : IsProbabilityMeasure (shifted p (scaled c ν)) := hνt.1
  have sg (a : X) : g (shifted p (scaled c ν)) (S a) = g (scaled c ν) a := by
    unfold g shifted
    rw [integral_map (f := fun x : X => Real.log (dist x (S a))) hS.aemeasurable (Real.measurable_log.comp (continuous_id.dist continuous_const).measurable).aestronglyMeasurable]
    simp [S,dist_sub_right]
  refine ⟨hboth,hav,p,by linarith [hp'.trans hav],by simpa [S] using sg p,?_,?_,fun x a => dist_sub_right _ _ _⟩
  · intro a
    have eq : a = S (a+p) := by simp [S]
    rw [eq]
    unfold potential shifted
    rw [lintegral_map (measurable_kernel _) hS.measurable]
    simpa only [potential,S,kernel3,dist_sub_right] using (show potential (scaled c ν) (a+p) ≤ 1 from (hboth _).1)
  · change (∫ a, g (shifted p (scaled c ν)) a ∂((scaled c μ).map S)) ≤ _
    rw [integral_map hS.aemeasurable (measurable_log_moment _).aestronglyMeasurable]
    simpa only [sg] using hav

/-- The two-ended coercivity and the unique zero of phi. -/
theorem stability_phi_shape :
    (∀ s : ℝ, 0 < s → 0 ≤ phi s ∧ (phi s = 0 ↔ s = 1)) ∧
    Tendsto phi (𝓝[>] 0) atTop ∧ Tendsto phi atTop atTop := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    rw [Real.log_inv] at h
    refine ⟨by unfold phi; linarith, ?_⟩
    constructor
    · intro hz
      by_contra hne
      have he : s⁻¹ ≠ 1 := fun h => hne (by simpa using congrArg Inv.inv h)
      have hlt := Real.log_lt_sub_one_of_pos (inv_pos.mpr hs) he
      rw [Real.log_inv] at hlt
      unfold phi at hz
      linarith
    · rintro rfl
      simp [phi]
  · apply tendsto_atTop.2
    intro b
    filter_upwards [self_mem_nhdsWithin, (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).eventually_ge_atTop
      (2*(b+Real.log 2))] with s hs hb
    have hs' : 0 < s := hs
    have h := Real.log_le_sub_one_of_pos (show 0 < s⁻¹ / 2 by positivity)
    rw [Real.log_div (inv_ne_zero hs'.ne') (by norm_num), Real.log_inv] at h
    unfold phi
    linarith
  · apply tendsto_atTop.2
    intro b
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (b+1), eventually_gt_atTop (0:ℝ)] with s hb hs
    unfold phi
    linarith [inv_pos.mpr hs]

/-- Nonnegative phi integral and concentration in every fixed spherical annulus. -/
theorem stability_phi_integral (ν : Law) (hν : admissible ν) (h : ∀ a, potential ν a ≤ 1) (a : X) :
    Integrable (fun x => phi (dist x a)) ν ∧ 0 ≤ (∫ x, phi (dist x a) ∂ν) ∧
      (∫ x, phi (dist x a) ∂ν) ≤ g ν a := by
  letI : IsProbabilityMeasure ν := hν.1
  obtain ⟨hn,hi,hint⟩ := inv_data ν a 1 (by norm_num) (by simpa using h a)
  obtain ⟨_,hlog,_⟩ := stability_log_moment ν hν 1 (by norm_num) (by simpa using h) a
  have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using hn
  have hadd : Integrable (fun x => Real.log (dist x a) + (dist x a)⁻¹) ν := hlog.add hi
  refine ⟨hadd.sub (integrable_const 1), integral_nonneg_of_ae (hne.mono fun x hx => (stability_phi_shape.1 _ (dist_pos.mpr hx)).1), ?_⟩
  unfold phi g
  rw [integral_sub hadd (integrable_const (1:ℝ)),integral_add hlog hi]
  simp only [integral_const,probReal_univ,one_smul]
  linarith

/-- Every fixed annulus contains asymptotically full mass. -/
theorem stability_annulus_mass (ν : ℕ → Law) (hn : Normalized ν) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun j => ν j (ann δ)) atTop (𝓝 1) := by
  intro δ hδ
  let η := min δ (1/2:ℝ)
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηδ : η ≤ δ := min_le_left _ _
  have dphi (s : ℝ) (hs : 0 < s) : HasDerivAt phi ((s-1)/s^2) s := by
    have h := ((Real.hasDerivAt_log hs.ne').add ((hasDerivAt_id s).inv hs.ne')).sub_const 1
    change HasDerivAt (fun x : ℝ => Real.log x + x⁻¹ - 1) _ s
    convert h using 1 <;> simp <;> field_simp <;> ring
  have down : AntitoneOn phi (Set.Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _) (fun s hs => (dphi s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (dphi s (interior_subset hs).1).differentiableAt.differentiableWithinAt)
    intro s hs
    have hi : s ∈ Set.Ioc (0:ℝ) 1 := interior_subset hs
    rw [(dphi s hi.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi.2) (sq_nonneg _)
  have up : MonotoneOn phi (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun s hs => (dphi s (lt_of_lt_of_le zero_lt_one hs)).continuousAt.continuousWithinAt)
      (fun s hs => (dphi s (lt_of_lt_of_le zero_lt_one (interior_subset hs))).differentiableAt.differentiableWithinAt)
    intro s hs
    have h1 : 1 ≤ s := interior_subset hs
    rw [(dphi _ (lt_of_lt_of_le zero_lt_one h1)).deriv]
    exact div_nonneg (sub_nonneg.mpr h1) (sq_nonneg _)
  let k := min (phi (1-η)) (phi (1+η))
  have pos (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : 0 < phi x :=
    lt_of_le_of_ne (stability_phi_shape.1 x hx).1 (Ne.symm (fun h => hx1 ((stability_phi_shape.1 x hx).2.mp h)))
  have hk : 0 < k := lt_min (pos _ (by linarith) (by linarith)) (pos _ (by linarith) (by linarith))
  have hm : MeasurableSet (ann δ) :=
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  have bound (j : ℕ) : (ν j).real (ann δ)ᶜ ≤ g (ν j) 0 / k := by
    have hp := (hn.1 j).2
    have ha := (stability_log_moment (ν j) (hn.1 j).1 1 (by norm_num) (by simpa using hp) 0).1
    have hne : ∀ᵐ x ∂ν j, x ≠ 0 := by simpa [ae_iff] using ha
    have h := stability_phi_integral (ν j) (hn.1 j).1 hp 0
    have hh := mul_meas_ge_le_integral_of_nonneg
      (hne.mono fun x hx => (stability_phi_shape.1 _ (dist_pos.mpr hx)).1) h.1 k
    have hsub : (ann δ)ᶜ ≤ᵐ[ν j] {x | k ≤ phi (dist x 0)} := by
      filter_upwards [hne] with x hx
      intro hbad
      have hxpos := norm_pos_iff.mpr hx
      change k ≤ phi (dist x 0)
      rw [dist_zero_right]
      change ¬(1-δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1+δ) at hbad
      by_cases hleft : ‖x‖ ≤ 1-η
      · exact (min_le_left _ _).trans (down ⟨hxpos, by linarith⟩ ⟨by linarith, by linarith⟩ hleft)
      · have hright : 1+η ≤ ‖x‖ := by
          by_contra! hn'
          exact hbad ⟨by linarith, by linarith⟩
        exact (min_le_right _ _).trans (up (by change 1 ≤ 1+η; linarith) (by change 1 ≤ ‖x‖; linarith) hright)
    have hmeasure := ENNReal.toReal_mono (measure_ne_top (ν j) _) (measure_mono_ae hsub)
    apply (le_div_iff₀ hk).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left hmeasure hk.le).trans (hh.trans h.2.2)
  have hzero : Tendsto (fun j => (ν j).real (ann δ)ᶜ) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) bound (by simpa using hn.2.div_const k)
  have hone := hzero.const_sub 1
  apply (ENNReal.tendsto_toReal_iff (fun j => measure_ne_top (ν j) _) (by norm_num)).mp
  simpa [measureReal_compl hm, measureReal_def] using hone

/-- Tightness and inequalities for each weak subsequential limit. -/
theorem stability_weak_limit (ν : ℕ → Law) (hn : Normalized ν) :
    IsTightMeasureSet (Set.range ν) ∧
    ∀ (k : ℕ → ℕ) (limLaw : Law), StrictMono k → IsProbabilityMeasure limLaw →
      weak (ν ∘ k) limLaw → limLaw (Metric.sphere 0 1)ᶜ = 0 ∧
      (∀ a, potential limLaw a ≤ 1) ∧ energy limLaw ≤ 1 := by
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  have closedAnn (δ : ℝ) : IsClosed (ann δ) :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have compAnn (δ : ℝ) (hδ : 0 < δ) : Tendsto (fun j => ν j (ann δ)ᶜ) atTop (𝓝 0) := by
    simpa only [prob_compl_eq_one_sub (closedAnn δ).measurableSet] using
      (ENNReal.tendsto_const_sub_nhds_zero_iff (by norm_num : (1:ℝ≥0∞) ≠ ⊤)
        (fun j => prob_le_one (μ := ν j) (s := ann δ))).2 (stability_annulus_mass ν hn δ hδ)
  constructor
  · apply isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (2:ℝ)] with r hr
    apply le_antisymm zero_le
    calc _ ≤ atTop.limsup (fun j => ν j (ann 1)ᶜ) := by
              apply limsup_le_limsup (Eventually.of_forall (fun j => measure_mono ?_))
              intro x hx ha
              exact (not_lt_of_ge (ha.2.trans (by linarith))) hx
         _ = 0 := (compAnn 1 zero_lt_one).limsup_eq
  · intro k ρ hk hρ hw
    let P (j : ℕ) : ProbabilityMeasure X := ⟨ν (k j),prob _⟩
    let Q : ProbabilityMeasure X := ⟨ρ,hρ⟩
    have hweak : Tendsto P atTop (𝓝 Q) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hw
    have hopens (G : Set X) (ho : IsOpen G) :
        ρ G ≤ atTop.liminf (fun j => ν (k j) G) :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak ho
    have full (δ : ℝ) (hδ : 0 < δ) : ∀ᵐ x ∂ρ, x ∈ ann δ := by
      rw [ae_iff]
      exact le_antisymm ((hopens _ (closedAnn δ).isOpen_compl).trans_eq
        ((compAnn δ hδ).comp hk.tendsto_atTop).liminf_eq) zero_le
    have sphere : ∀ᵐ x ∂ρ, x ∈ Metric.sphere 0 1 := by
      have h := ae_all_iff.2 (fun n : ℕ => full (1/((n:ℝ)+1)) (by positivity))
      filter_upwards [h] with x hx
      rw [Metric.mem_sphere, dist_zero_right]
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      apply le_antisymm
      · have t := h0.const_add (1:ℝ)
        simpa using le_of_tendsto_of_tendsto' tendsto_const_nhds t (fun n => (hx n).2)
      · have t := h0.const_sub (1:ℝ)
        simpa using le_of_tendsto_of_tendsto' t tendsto_const_nhds (fun n => (hx n).1)
    have bound (a : X) : potential ρ a ≤ 1 := by
      let K (n : ℕ) (x : X) := min (n:ℝ≥0∞) (newtonKernel x a)
      have cK (n : ℕ) : Continuous (K n) := by
        simp only [K,kernel3]
        exact continuous_const.min ((ENNReal.continuous_ofReal.comp (continuous_id.dist continuous_const)).inv)
      have finite (n : ℕ) (x : X) : K n x ≠ ⊤ :=
        ((min_le_left _ _).trans_lt (ENNReal.natCast_lt_top n)).ne
      have cf (n : ℕ) : Continuous (fun x => (K n x).toReal) :=
        continuous_iff_continuousAt.mpr fun x => (ENNReal.continuousAt_toReal (finite n x)).comp (cK n).continuousAt
      have hi (n : ℕ) : (∫⁻ x, K n x ∂ρ) ≤ 1 := by
        have hl := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
          (cf n) (fun _ => ENNReal.toReal_nonneg) hopens
        simp only [ENNReal.ofReal_toReal (finite n _)] at hl
        exact hl.trans ((liminf_le_liminf (Eventually.of_forall (fun j =>
          (lintegral_mono (μ := ν (k j)) (fun x => min_le_right (n:ℝ≥0∞) (newtonKernel x a))).trans ((hn.1 (k j)).2 a)))).trans_eq (liminf_const 1))
      have eq (x : X) : newtonKernel x a = ⨆ n, K n x := by
        change _ = ⨆ n : ℕ, (n:ℝ≥0∞) ⊓ newtonKernel x a
        rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
      unfold potential
      change (∫⁻ x, newtonKernel x a ∂ρ) ≤ 1
      conv_lhs => arg 2; intro x; rw [eq x]
      rw [lintegral_iSup (fun n => (cK n).measurable) (fun n m h x => min_le_min_right _ (Nat.cast_le.mpr h))]
      exact iSup_le hi
    refine ⟨ae_iff.mp sphere,bound,?_⟩
    calc energy ρ ≤ ∫⁻ _ : X, 1 ∂ρ := by
           apply lintegral_mono
           intro x
           convert bound x using 1
           simp only [potential,kernel3,dist_comm x]
         _ = 1 := by simp

/-- Uniqueness identifies every weak limit with the uniform sphere law. -/
theorem stability_sphere_limit (uniqueEq : EqUnique) (ballLaw : BallLaw) (ν : ℕ → Law) (hn : Normalized ν) :
    (IsProbabilityMeasure sigma ∧ energy sigma = 1) ∧
    (∀ limLaw : Law, IsProbabilityMeasure limLaw → limLaw (Metric.sphere 0 1)ᶜ = 0 →
      1 ≤ energy limLaw ∧ (energy limLaw = 1 → limLaw = sigma)) ∧ weak ν sigma := by
  let B := Metric.closedBall (0:X) 1
  have hB : IsCompact B := isCompact_closedBall _ _
  have eqσ : equilibrium B sigma := ballLaw.2.2
  have hlow (ρ : Law) (hρ : IsProbabilityMeasure ρ)
      (hs : ρ (Metric.sphere 0 1)ᶜ = 0) : 1 ≤ energy ρ ∧ (energy ρ = 1 → ρ = sigma) := by
    have hm : ρ Bᶜ = 0 := measure_mono_null (compl_subset_compl.mpr Metric.sphere_subset_closedBall) hs
    have hle : leastEnergy B ≤ energy ρ := sInf_le ⟨ρ,hρ,hm,rfl⟩
    refine ⟨ballLaw.2.1 ▸ hle,fun he => uniqueEq B ρ sigma hB (by rw [show capRadius B = 1 from ballLaw.1]; norm_num)
      ⟨hρ,hm,he.trans ballLaw.2.1.symm⟩ eqσ⟩
  refine ⟨⟨eqσ.1,eqσ.2.2.trans ballLaw.2.1⟩,hlow,?_⟩
  let P (j : ℕ) : ProbabilityMeasure X := ⟨ν j,(hn.1 j).1.1⟩
  let Q : ProbabilityMeasure X := ⟨sigma,eqσ.1⟩
  have lims := stability_weak_limit ν hn
  have cmp : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have e : {((R : ProbabilityMeasure X) : Measure X) | R ∈ Set.range P} = Set.range ν := by
      ext μ
      exact ⟨fun ⟨R,⟨j,hj⟩,he⟩ => ⟨j,by rw [←hj] at he; exact he⟩,fun ⟨j,hj⟩ => ⟨P j,Set.mem_range_self j,hj⟩⟩
    rw [e]
    exact lims.1
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := P) (μ := Q)).mp
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨u,hu,hnu⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨R,_,v,hv,hconv⟩ := cmp.tendsto_subseq (fun j => subset_closure (Set.mem_range_self (ns (u j))))
  let k := (ns ∘ u) ∘ v
  have hw : weak (ν ∘ k) (R : Measure X) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
  obtain ⟨hsp,_,hen⟩ := lims.2 k R (hnu.comp hv) R.prop hw
  have h₁ := hlow R R.prop hsp
  have heq : R = Q := Subtype.ext (h₁.2 (le_antisymm hen h₁.1))
  exact ⟨u ∘ v,heq ▸ hconv⟩

/-- Rotational invariance identifies the log moment about any center. -/
theorem stability_spherical_radial (a : X) : g sigma a = H ‖a‖ := by
  let b := ‖a‖ • e₁
  have hn : ‖a‖ = ‖b‖ := by simp [b,e₁,norm_smul,Real.norm_eq_abs]
  let U := (ℝ ∙ (a-b))ᗮ.reflection
  have hu : U a = b := Submodule.reflection_sub hn
  have hU := U.continuous.measurable
  have rot := sigma_map_isometry U
  change g sigma a = g sigma b
  calc _ = ∫ x, Real.log (dist (U x) b) ∂sigma := by simp only [g,←hu,U.isometry.dist_eq]
       _ = ∫ x, Real.log (dist x b) ∂(sigma.map U) := (integral_map (f := fun x : X => Real.log (dist x b))
            hU.aemeasurable (Real.measurable_log.comp (continuous_id.dist continuous_const).measurable).aestronglyMeasurable).symm
       _ = _ := by rw [rot]; rfl

local instance : NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

private def translateAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Law) (f : X → E) (y : X) : E := ∫ x, f (y-x) ∂μ

private theorem translated_integrable {E : Type*} [NormedAddCommGroup E] (μ : Law) [IsFiniteMeasure μ]
    (K : Set X) (hK : IsCompact K) (hm : ∀ᵐ x ∂μ, x ∈ K)
    (f : X → E) (hf : ∀ x ≠ 0, ContinuousAt f x) {y : X} (hy : y ∉ K) :
    Integrable (fun x => f (y-x)) μ := by
  have h : ContinuousOn (fun x => f (y-x)) K := by
    intro x hx
    exact ((hf _ (sub_ne_zero.mpr (fun (e : y = x) => hy (e.symm ▸ hx)))).comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hi := h.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hm] at hi

private theorem translateAverage_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Law) [IsFiniteMeasure μ] (K : Set X) (hK : IsCompact K) (hm : ∀ᵐ x ∂μ, x ∈ K)
    (f : X → E) (hf : ∀ x ≠ 0, ContDiffAt ℝ 1 f x) {y : X} (hy : y ∉ K) :
    HasFDerivAt (translateAverage μ f) (translateAverage μ (fderiv ℝ f) y) y := by
  have hyU := hK.isClosed.isOpen_compl.mem_nhds hy
  obtain ⟨r,hr,hrK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hyU
  let W := Metric.closedBall y r
  have cn (x : X) (hx : x ≠ 0) : ContinuousAt (fderiv ℝ f) x :=
    ((hf _ hx).fderiv_right (m := 0) (by norm_num)).continuousAt
  let A := (fun p : X × X => p.1-p.2) '' (W ×ˢ K)
  have cA : IsCompact A := ((isCompact_closedBall y r).prod hK).image (continuous_fst.sub continuous_snd)
  have off (x : X) (hx : x ∈ A) : x ≠ 0 := by
    obtain ⟨⟨b,z⟩,⟨hb,hz⟩,rfl⟩ := hx
    exact sub_ne_zero.mpr (fun eq => hrK hb (eq ▸ hz))
  obtain ⟨B,hB⟩ := cA.bddAbove_image (f := fun x => ‖fderiv ℝ f x‖)
    (fun x hx => (cn _ (off x hx)).norm.continuousWithinAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := W) (bound := fun _ : X => B) (Metric.closedBall_mem_nhds y hr)
  · filter_upwards [hyU] with t ht
    exact (translated_integrable μ K hK hm f (fun x hx => (hf x hx).continuousAt) ht).aestronglyMeasurable
  · exact translated_integrable μ K hK hm f (fun x hx => (hf x hx).continuousAt) hy
  · exact (translated_integrable μ K hK hm (fderiv ℝ f) cn hy).aestronglyMeasurable
  · filter_upwards [hm] with x hx
    intro t ht
    exact hB (Set.mem_image_of_mem _ (Set.mem_image_of_mem (fun q : X × X => q.1-q.2) (show (t,x) ∈ W ×ˢ K from ⟨ht,hx⟩)))
  · exact integrable_const _
  · filter_upwards [hm] with x hx
    intro t ht
    exact (hasFDerivAt_comp_sub x).mpr ((hf _ (sub_ne_zero.mpr (fun (e : t = x) => hrK ht (e.symm ▸ hx)))).differentiableAt one_ne_zero).hasFDerivAt

private theorem translateAverage_c2 (μ : Law) [IsFiniteMeasure μ] (K : Set X) (hK : IsCompact K)
    (hm : ∀ᵐ x ∂μ, x ∈ K) (f : X → ℝ) (hf : ∀ x ≠ 0, ContDiffAt ℝ 3 f x) {y : X} (hy : y ∉ K) :
    ContDiffAt ℝ 2 (translateAverage μ f) y ∧
    fderiv ℝ (fderiv ℝ (translateAverage μ f)) y = translateAverage μ (fderiv ℝ (fderiv ℝ f)) y := by
  let df := fderiv ℝ f
  let ddf := fderiv ℝ df
  have hdf (x : X) (hx : x ≠ 0) : ContDiffAt ℝ 2 df x := (hf _ hx).fderiv_right (by norm_num)
  have hddf (x : X) (hx : x ≠ 0) : ContDiffAt ℝ 1 ddf x := (hdf _ hx).fderiv_right (by norm_num)
  have hD (z : X) (hz : z ∉ K) := translateAverage_deriv μ K hK hm f (fun x hx => (hf x hx).of_le (by norm_num)) hz
  have hDD (z : X) (hz : z ∉ K) := translateAverage_deriv μ K hK hm df (fun x hx => (hdf x hx).of_le (by norm_num)) hz
  have hDDD (z : X) (hz : z ∉ K) := translateAverage_deriv μ K hK hm ddf hddf hz
  have hU := hK.isClosed.isOpen_compl.mem_nhds hy
  constructor
  · apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).2
    refine ⟨translateAverage μ df,⟨Kᶜ,hU,hD⟩,?_⟩
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).2
    exact ⟨translateAverage μ ddf,⟨Kᶜ,hU,hDD⟩,contDiffAt_zero.mpr ⟨Kᶜ,hU,fun z hz => (hDDD z hz).continuousAt.continuousWithinAt⟩⟩
  · have eq : fderiv ℝ (translateAverage μ f) =ᶠ[𝓝 y] translateAverage μ df :=
      Filter.mem_of_superset hU (fun z hz => (hD z hz).fderiv)
    exact eq.fderiv_eq.trans (hDD y hy).fderiv

private def trace3 (A : X →L[ℝ] X →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin 3, A (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)

private theorem norm_derivative (w : X) (hw : w ≠ 0) :
    HasFDerivAt (norm : X → ℝ) (‖w‖⁻¹ • innerSL ℝ w) w := by
  have hn := (norm_pos_iff.mpr hw).ne'
  have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.sqrt (by simp [hn])
  convert h using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg y)).symm
  · ext v
    simp [Real.sqrt_sq (norm_nonneg w),innerSL_apply_apply]
    field_simp

private theorem radial_trace (f : ℝ → ℝ) (w : X) (hw : w ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖w‖) :
    trace3 (fderiv ℝ (fderiv ℝ (fun z : X => f ‖z‖)) w) = radialLap f ‖w‖ := by
  let A (s : ℝ) := deriv f s / s
  let r := ‖w‖
  have hr : 0 < r := norm_pos_iff.mpr hw
  have hDf : DifferentiableAt ℝ (deriv f) r :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : DifferentiableAt ℝ A r := hDf.div differentiableAt_id hr.ne'
  have cf : fderiv ℝ (fun z : X => f ‖z‖) =ᶠ[𝓝 w] (fun z => A ‖z‖ • innerSL ℝ z) := by
    have hf' := hf.eventually (by norm_num)
    filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds hf',eventually_ne_nhds hw] with z hz hnz
    change ContDiffAt ℝ 2 f ‖z‖ at hz
    have h := (hz.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt z (norm_derivative z hnz)
    simpa [A,smul_smul,div_eq_mul_inv,Function.comp_def] using h.fderiv
  have da := hA.hasDerivAt.comp_hasFDerivAt w (norm_derivative w hw)
  let J : X →L[ℝ] X →L[ℝ] ℝ := innerSL ℝ
  have dh := (da.smul J.hasFDerivAt).fderiv
  have eq : (fun s => s^2 * deriv f s) =ᶠ[𝓝 r] fun s => s^3 * A s := by
    filter_upwards [eventually_ne_nhds hr.ne'] with s hs
    dsimp [A]; field_simp
  have der := (((hasDerivAt_id r).pow 3).mul hA.hasDerivAt).deriv
  have rhs : radialLap f r = 3*A r + deriv A r * r := by
    unfold radialLap
    rw [eq.deriv_eq]
    erw [der]
    simp only [Pi.pow_apply,id_eq]
    field_simp
    ring
  rw [rhs,cf.fderiv_eq]
  erw [dh]
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have bn (i : Fin 3) : inner ℝ (b i) (b i) = 1 := by simp [real_inner_self_eq_norm_sq,b.orthonormal.norm_eq_one]
  have sum : (∑ i : Fin 3, (inner ℝ w (b i))^2) = r^2 := by
    simpa [Real.norm_eq_abs,sq_abs,r] using b.sum_sq_norm_inner_left w
  have point (i : Fin 3) : ((A ‖w‖ • J +
      (deriv A ‖w‖ • (‖w‖⁻¹ • innerSL ℝ w)).smulRight (innerSL ℝ w)) (b i)) (b i) =
      A r + (deriv A r / r) * (inner ℝ w (b i))^2 := by
    have e : (innerSL ℝ (b i)) (b i) = 1 := bn i
    simp [J,e,bn,r,div_eq_mul_inv] <;> ring
  unfold trace3
  change (∑ i : Fin 3, ((A ‖w‖ • J + (deriv A ‖w‖ • (‖w‖⁻¹ • innerSL ℝ w)).smulRight (innerSL ℝ w)) (b i)) (b i)) = _
  simp_rw [point]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum]
  simp
  field_simp <;> ring

private def logNorm (x : X) := Real.log ‖x‖

private theorem logNorm_smooth (x : X) (hx : x ≠ 0) : ContDiffAt ℝ 3 logNorm x :=
  (contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)

private theorem logNorm_average (ν : Law) : translateAverage ν logNorm = g ν := by
  funext y
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp [logNorm,dist_comm x y,dist_eq_norm])

private theorem H_smooth {s : ℝ} (hs : |s| < 1) : ContDiffAt ℝ 2 H s := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  have hn : s • e₁ ∉ Metric.sphere (0:X) 1 := by simpa [Metric.mem_sphere,e₁,norm_smul] using hs.ne
  have h := (translateAverage_c2 sigma _ (isCompact_sphere _ _) sigma_sphere logNorm logNorm_smooth hn).1
  rw [logNorm_average] at h
  exact h.comp s (contDiffAt_id.smul contDiffAt_const)

private theorem sigma_inner_zero (a : X) : (∫ x, inner ℝ x a ∂sigma) = 0 := by
  let U : X ≃ₗᵢ[ℝ] X := LinearIsometryEquiv.neg ℝ
  have hm := integral_map (μ := sigma) (f := fun x : X => inner ℝ x a)
    U.continuous.aemeasurable (continuous_id.inner continuous_const).aestronglyMeasurable
  rw [sigma_map_isometry] at hm
  change (∫ x, inner ℝ x a ∂sigma) = (∫ x, inner ℝ (-x) a ∂sigma) at hm
  simp only [inner_neg_left,integral_neg] at hm
  linarith

private theorem trace3_average (μ : Law) {T : X → X →L[ℝ] X →L[ℝ] ℝ} (hT : Integrable T μ) :
    trace3 (∫ x, T x ∂μ) = ∫ x, trace3 (T x) ∂μ := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hi (i : Fin 3) : Integrable (fun x => T x (b i)) μ :=
    (ContinuousLinearMap.apply ℝ _ (b i)).integrable_comp hT
  have hii (i : Fin 3) : Integrable (fun x => T x (b i) (b i)) μ :=
    (ContinuousLinearMap.apply ℝ ℝ (b i)).integrable_comp (hi i)
  change (∑ i, (∫ x, T x ∂μ) (b i) (b i)) = ∫ x, ∑ i, T x (b i) (b i) ∂μ
  rw [integral_finsetSum _ (fun i _ => hii i)]
  exact Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.integral_apply hT,ContinuousLinearMap.integral_apply (hi i)]

/-- Radial Laplacian identity for the spherical logarithmic moment. -/
theorem stability_radial_lap (s : ℝ) (hs : s ∈ Set.Ioo 0 1) :
    radialLap H s = (∫ θ, (dist θ (s • e₁))⁻¹ ^ 2 ∂sigma) ∧
    (1+s^2)⁻¹ ≤ radialLap H s ∧
    radialLap comparison s = (1+s^2)⁻¹ - (2/3 : ℝ)*s^2/(1+s^2)^2 := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  let w := s • e₁
  have hw : ‖w‖ = s := by simp [w,e₁,norm_smul,abs_of_pos hs.1]
  have hout : w ∉ Metric.sphere (0:X) 1 := by simpa [Metric.mem_sphere,hw] using hs.2.ne
  have hC := translateAverage_c2 sigma _ (isCompact_sphere _ _) sigma_sphere logNorm logNorm_smooth hout
  have hF : translateAverage sigma logNorm = (fun a : X => H ‖a‖) :=
    (logNorm_average sigma).trans (funext stability_spherical_radial)
  let D : X → X →L[ℝ] X →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ logNorm)
  have hi := translated_integrable sigma _ (isCompact_sphere _ _) sigma_sphere D
    (fun x hx => (((logNorm_smooth x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuousAt) hout
  have trace (y : X) (hy : y ≠ 0) : trace3 (D y) = ‖y‖⁻¹^2 := by
    have hr := norm_pos_iff.mpr hy
    have tr := radial_trace Real.log y hy (Real.contDiffAt_log.mpr hr.ne')
    have same : (fun t => t^2 * deriv Real.log t) =ᶠ[𝓝 ‖y‖] id := by
      filter_upwards [eventually_ne_nhds hr.ne'] with t ht
      simp [Real.deriv_log,ht,field]
    rw [radialLap,same.deriv_eq,deriv_id] at tr
    change trace3 (fderiv ℝ (fderiv ℝ (fun z : X => Real.log ‖z‖)) y) = _
    simpa only [one_div,inv_pow] using tr
  have first : radialLap H s = ∫ θ, (dist θ w)⁻¹^2 ∂sigma := by
    have hsmooth : ContDiffAt ℝ 2 H ‖w‖ := by rw [hw]; exact H_smooth (by simpa only [abs_of_pos hs.1] using hs.2)
    have tr := radial_trace H w (norm_ne_zero_iff.mp (hw.trans_ne hs.1.ne')) hsmooth
    rw [hw,←hF,hC.2] at tr
    rw [←tr,translateAverage,trace3_average sigma hi]
    apply integral_congr_ae
    filter_upwards [sigma_sphere] with x hx
    have nz : w-x ≠ 0 := sub_ne_zero.mpr (fun h => hout (h.symm ▸ hx))
    simpa [dist_comm x w,dist_eq_norm] using trace (w-x) nz
  refine ⟨first,?_,?_⟩
  · rw [first]
    let m := 1+s^2
    have mp : 0 < m := by dsimp [m]; positivity
    have id2 : (∫ x, dist x w ^ 2 ∂sigma) = m := by
      have he : ∀ᵐ x ∂sigma, dist x w ^ 2 = m - 2*inner ℝ x w := by
        filter_upwards [sigma_sphere] with x hx
        have hx' : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
        simp [dist_eq_norm,norm_sub_sq_real,hx',hw,m]; ring
      rw [integral_congr_ae he]
      erw [integral_sub (integrable_const m) ((integrable_of_compact_law _ sigma_admissible (continuous_id.inner continuous_const)).const_mul 2),
        integral_const_mul,sigma_inner_zero]
      simp
    have hsq : Integrable (fun x : X => dist x w ^ 2) sigma :=
      integrable_of_compact_law _ sigma_admissible ((continuous_id.dist continuous_const).pow 2)
    have hdis : Integrable (fun x : X => (dist x w)⁻¹^2) sigma := by
      have h := translated_integrable sigma _ (isCompact_sphere _ _) sigma_sphere (fun y : X => ‖y‖⁻¹^2)
        (fun y hy => (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hy)).pow 2) hout
      simpa [dist_eq_norm,norm_sub_rev w] using h
    have h := integral_mono_ae (μ := sigma) ((integrable_const (2/m)).sub (hsq.div_const (m^2))) hdis (by
      filter_upwards [sigma_sphere] with x hx
      have hd : 0 < dist x w := dist_pos.mpr (fun h => hout (h ▸ hx))
      change 2/m - dist x w^2/m^2 ≤ (dist x w)⁻¹^2
      field_simp
      nlinarith [sq_nonneg (dist x w^2-m)])
    erw [integral_sub (integrable_const _) (hsq.div_const _),integral_div (m^2) (fun x => dist x w ^ 2),id2] at h
    simp only [integral_const,probReal_univ,one_smul] at h
    change m⁻¹ ≤ _
    convert h using 1
    field_simp
    ring
  · have df (t : ℝ) : HasDerivAt comparison ((2*t)/(6*(1+t^2))) t := by
      have h := ((((hasDerivAt_id t).pow 2).const_add 1).log (by change 1+t^2 ≠ 0; positivity)).div_const 6
      change HasDerivAt (fun x : ℝ => Real.log (1+x^2) / 6) _ t
      convert h using 1 <;> simp [comparison] <;> field_simp <;> ring
    have eq : (fun t => t^2*deriv comparison t) = (fun t : ℝ => t^3/(3*(1+t^2))) := by
      funext t; rw [(df t).deriv]; field_simp; ring
    have der := ((hasDerivAt_id s).pow 3).div ((((hasDerivAt_id s).pow 2).const_add 1).const_mul 3)
      (by change 3*(1+s^2) ≠ 0; positivity)
    rw [radialLap,eq]
    erw [der.deriv]
    simp only [id_eq,Pi.pow_apply]
    field_simp [hs.1.ne',show (1+s^2:ℝ) ≠ 0 by positivity]
    ring

private theorem comparison_smooth : ContDiff ℝ 2 comparison :=
  ((contDiff_const.add (contDiff_id.pow 2)).log (fun s => by change (1+s^2:ℝ) ≠ 0; positivity)).div_const 6

private theorem sphere_distance (θ : X) (hθ : ‖θ‖=1) (s : ℝ) :
    dist θ (s • e₁)^2 = (1-s)^2+s*dist θ e₁^2 := by
  have en : ‖e₁‖ = 1 := by simp [e₁]
  simp only [dist_eq_norm,norm_sub_sq_real,real_inner_smul_right,norm_smul,en,
    Real.norm_eq_abs,abs_one,mul_one,sq_abs,hθ,one_pow]
  ring

private theorem sigma_null_pole : sigma {e₁} = 0 := by
  have h1 : ‖e₁‖ = 1 := by simp [e₁]
  have hne : e₁ ≠ 0 := norm_ne_zero_iff.mp (h1.trans_ne one_ne_zero)
  let K := ℝ ∙ e₁
  have hk : K ≠ ⊤ := by
    intro he
    have h := congrArg (fun S : Submodule ℝ X => Module.finrank ℝ S) he
    simp [K,finrank_span_singleton hne,X,Space] at h
  unfold sigma
  rw [Measure.smul_apply,Measure.map_apply measurable_subtype_coe (measurableSet_singleton _),
    Measure.toSphere_apply' _ (measurable_subtype_coe (measurableSet_singleton _))]
  have z := Measure.addHaar_submodule (volume : Law) K hk
  have sub : Set.Ioo (0:ℝ) 1 • (Subtype.val '' (Subtype.val ⁻¹' {e₁} : Set (Metric.sphere (0:X) 1))) ⊆ (K : Set X) := by
    rintro _ ⟨r,_,_,⟨θ,hθ,rfl⟩,rfl⟩
    change (θ:X) = e₁ at hθ
    rw [hθ]
    exact K.smul_mem r (Submodule.subset_span (Set.mem_singleton _))
  rw [measure_mono_null sub z,mul_zero,smul_zero]

private theorem H_zero : H 0 = 0 := by
  change (∫ x, Real.log (dist x ((0:ℝ) • e₁)) ∂sigma) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [sigma_sphere] with x hx
  simp [Metric.mem_sphere.mp hx]

private theorem H_deriv_zero : deriv H 0 = 0 := by
  have dif := (H_smooth (s := 0) (by norm_num)).differentiableAt (by norm_num)
  have even : (fun s => H (-s)) = H := by
    funext s
    change g sigma ((-s) • e₁) = g sigma (s • e₁)
    rw [stability_spherical_radial,stability_spherical_radial]
    simp
  have der : HasDerivAt H (deriv H 0) (-(0:ℝ)) := by simpa using dif.hasDerivAt
  have d := der.comp 0 (hasDerivAt_neg (0:ℝ))
  have h := d.deriv
  change deriv (fun s => H (-s)) 0 = deriv H 0 * (-1) at h
  rw [even] at h
  linarith

private theorem interior_gap_deriv (s : ℝ) (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    0 < deriv (fun t => H t - comparison t) s := by
  let W (t : ℝ) := t^2*(deriv H t - deriv comparison t)
  have smooth (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) := H_smooth (s := t) (by simpa only [abs_of_nonneg ht.1] using ht.2)
  have reg (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) : DifferentiableAt ℝ W t :=
    (differentiableAt_id.pow 2).mul ((((smooth t ht).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).sub
      (comparison_smooth.differentiable_deriv_two t))
  have wmono : StrictMonoOn W (Set.Ico (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun t ht => (reg t ht).continuousAt.continuousWithinAt)
    intro t ht
    have mem : t ∈ Set.Ioo (0:ℝ) 1 := by simpa using ht
    obtain ⟨_,hl,hr⟩ := stability_radial_lap t mem
    have lt : radialLap comparison t < radialLap H t := by have hp := mem.1; rw [hr]; nlinarith [show 0 < (2/3:ℝ)*t^2/(1+t^2)^2 by positivity]
    have dh := (H_smooth (s := t) (by simpa only [abs_of_pos mem.1] using mem.2)).derivWithin (m := 1) (by norm_num)
    have hd1 : DifferentiableAt ℝ (fun x : ℝ => x^2*deriv H x) t :=
      (differentiableAt_id.pow 2).mul (dh.differentiableAt one_ne_zero)
    have hd2 : DifferentiableAt ℝ (fun x : ℝ => x^2*deriv comparison x) t :=
      (differentiableAt_id.pow 2).mul (comparison_smooth.differentiable_deriv_two t)
    have he : W = fun x : ℝ => x^2*deriv H x - x^2*deriv comparison x := by funext x; dsimp [W]; ring
    rw [he,deriv_fun_sub hd1 hd2]
    exact sub_pos.mpr ((div_lt_div_iff_of_pos_right (sq_pos_of_pos mem.1)).mp lt)
  have hw := wmono (show 0 ∈ Set.Ico (0:ℝ) 1 from ⟨le_rfl,zero_lt_one⟩) ⟨hs.1.le,hs.2⟩ hs.1
  rw [deriv_fun_sub ((smooth s ⟨hs.1.le,hs.2⟩).differentiableAt (by norm_num)) (comparison_smooth.differentiable (by norm_num) _)]
  have pos : 0 < s^2*(deriv H s - deriv comparison s) := by simpa [W] using hw
  exact pos_of_mul_pos_right pos (sq_nonneg _)

private theorem H_nonnegative {s : ℝ} (hs : s ∈ Set.Ico (0:ℝ) 1) : 0 ≤ H s := by
  have mono : MonotoneOn (fun t => H t - comparison t) (Set.Ico (0:ℝ) 1) := by
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun t ht => ((H_smooth (s := t) (by simpa only [abs_of_nonneg ht.1] using ht.2)).continuousAt.sub comparison_smooth.continuous.continuousAt).continuousWithinAt)
    intro t ht
    exact interior_gap_deriv t (by simpa using ht)
  have h := mono (show 0 ∈ Set.Ico (0:ℝ) 1 from ⟨le_rfl,zero_lt_one⟩) hs hs.1
  simp [H_zero,comparison] at h
  linarith [Real.log_nonneg (show 1 ≤ 1+s^2 by linarith [sq_nonneg s])]

/-- Integration from zero and continuity at the unit sphere. -/
theorem stability_radial_gap :
    H 0 = 0 ∧ deriv H 0 = 0 ∧ comparison 0 = 0 ∧ deriv comparison 0 = 0 ∧
    StrictMonoOn (fun s => H s - comparison s) (Set.Icc 0 1) ∧ ContinuousAt H 1 ∧
    Integrable (fun θ => Real.log (dist θ e₁)) sigma ∧
    ∀ θ : X, ‖θ‖ = 1 → ∀ s : ℝ, dist θ (s • e₁)^2 = (1-s)^2 + s * dist θ e₁ ^ 2 := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  let f (s : ℝ) (x : X) := Real.log (dist x (s • e₁))
  have en : ‖e₁‖ = 1 := by simp [e₁]
  have hne : ∀ᵐ x ∂sigma, x ≠ e₁ := by simpa [ae_iff] using sigma_null_pole
  have meas (s : ℝ) : Measurable (f s) := Real.measurable_log.comp (continuous_id.dist continuous_const).measurable
  have cts (x : X) (hx : x ≠ e₁) : ContinuousAt (fun s => f s x) 1 := by
    apply ((continuous_const.dist (continuous_id.smul continuous_const)).continuousAt).log
    simpa using (dist_pos.mpr hx).ne'
  have intf {s : ℝ} (hs : s ∈ Set.Ico (0:ℝ) 1) : Integrable (f s) sigma := by
    have hout : s • e₁ ∉ Metric.sphere (0:X) 1 := by simpa [Metric.mem_sphere,norm_smul,en,Real.norm_eq_abs,abs_of_nonneg hs.1] using hs.2.ne
    have hi := translated_integrable sigma _ (isCompact_sphere _ _) sigma_sphere logNorm (fun x hx => (logNorm_smooth x hx).continuousAt) hout
    simpa [f,logNorm,dist_eq_norm,norm_sub_rev (s • e₁)] using hi
  have upper (s : ℝ) (hs : |s| ≤ 2) (x : X) (hx : ‖x‖=1) (hd : 0 < dist x (s • e₁)) : f s x ≤ Real.log 3 := by
    apply Real.log_le_log hd
    calc dist x (s • e₁) ≤ ‖x‖ + ‖s • e₁‖ := by simpa using dist_triangle x 0 (s • e₁)
         _ ≤ 3 := by simp [hx,norm_smul,en,Real.norm_eq_abs]; linarith
  let r (j : ℕ) := 1 - 1/((j:ℝ)+1)
  have hr (j : ℕ) : r j ∈ Set.Ico (0:ℝ) 1 := by
    dsimp [r]; constructor
    · apply sub_nonneg.mpr; apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) j]
    · linarith [show 0 < 1/((j:ℝ)+1) by positivity]
  have hr1 : Tendsto r atTop (𝓝 1) := by simpa [r] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
  have C0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hb (j : ℕ) : (∫⁻ x, ‖f (r j) x‖ₑ ∂sigma) ≤ ENNReal.ofReal (2*Real.log 3) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (intf (hr j))]
    apply ENNReal.ofReal_le_ofReal
    have hle := integral_mono_ae (intf (hr j)).norm ((integrable_const (2*Real.log 3)).sub (intf (hr j))) (by
      filter_upwards [sigma_sphere] with x hx
      have hx' : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
      have hd : 0 < dist x (r j • e₁) := by
        apply dist_pos.mpr
        intro e
        have hn := congrArg norm e
        simp [hx',norm_smul,en,Real.norm_eq_abs,abs_of_nonneg (hr j).1] at hn
        linarith [(hr j).2]
      have u := upper _ (by rw [abs_of_nonneg (hr j).1]; linarith [(hr j).2]) x hx' hd
      change |f (r j) x| ≤ 2*Real.log 3 - f (r j) x
      exact (abs_le.mpr ⟨by linarith,by linarith⟩))
    erw [integral_sub (integrable_const _) (intf (hr j))] at hle
    have hn : 0 ≤ ∫ x, f (r j) x ∂sigma := H_nonnegative (hr j)
    simpa using hle.trans (by simpa using sub_le_self (2*Real.log 3) hn)
  have hi : Integrable (f 1) sigma := by
    refine ⟨(meas _).aestronglyMeasurable,?_⟩
    have hlim : (∫⁻ x, ‖f 1 x‖ₑ ∂sigma) = ∫⁻ x, atTop.liminf (fun j => ‖f (r j) x‖ₑ) ∂sigma :=
      lintegral_congr_ae (hne.mono (fun x hx => (((cts x hx).tendsto.comp hr1).enorm.liminf_eq).symm))
    exact (hlim.le.trans ((lintegral_liminf_le (fun j => (meas _).enorm)).trans
      ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq (liminf_const _)))).trans_lt ENNReal.ofReal_lt_top
  have continuity : ContinuousAt H 1 := by
    apply continuousAt_of_dominated (F := f) (bound := fun x => ‖f 1 x‖ + Real.log 3)
      (Eventually.of_forall fun s => (meas s).aestronglyMeasurable) _ (hi.norm.add (integrable_const _)) (hne.mono cts)
    filter_upwards [Ioo_mem_nhds (show (1/2:ℝ)<1 by norm_num) (show (1:ℝ)<2 by norm_num)] with s hs
    filter_upwards [sigma_sphere,hne] with x hx hxe
    have hx' : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
    have hd := dist_pos.mpr hxe
    have hsq := sphere_distance x hx' s
    have hle : dist x e₁ / 2 ≤ dist x (s • e₁) := by
      nlinarith [(dist_nonneg : 0 ≤ dist x (s • e₁)),sq_nonneg (1-s), mul_nonneg (by linarith [hs.1] : 0 ≤ s-1/4) (sq_nonneg (dist x e₁))]
    have hpos := (half_pos hd).trans_le hle
    have hu := upper s (by rw [abs_of_pos (by linarith [hs.1])]; exact hs.2.le) x hx' hpos
    have hl := Real.log_le_log (half_pos hd) hle
    rw [Real.log_div hd.ne' (by norm_num)] at hl
    change |f s x| ≤ |Real.log (dist x ((1:ℝ) • e₁))| + Real.log 3
    rw [one_smul]
    apply abs_le.mpr
    constructor
    · change _ ≤ Real.log (dist x (s • e₁))
      linarith [neg_abs_le (Real.log (dist x e₁)),Real.log_le_log (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≤3)]
    · linarith [abs_nonneg (Real.log (dist x e₁))]
  have mono : StrictMonoOn (fun s => H s - comparison s) (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) _ (fun s hs => interior_gap_deriv s (by simpa using hs))
    intro s hs
    obtain eq | lt := eq_or_lt_of_le hs.2
    · subst s; exact (continuity.sub comparison_smooth.continuous.continuousAt).continuousWithinAt
    · exact ((H_smooth (s := s) (by rwa [abs_of_nonneg hs.1])).continuousAt.sub comparison_smooth.continuous.continuousAt).continuousWithinAt
  have cder : HasDerivAt comparison 0 0 := by
    have h := ((((hasDerivAt_id (0:ℝ)).pow 2).const_add 1).log (by norm_num)).div_const 6
    change HasDerivAt (fun t : ℝ => Real.log (1+t^2)/6) 0 0
    simpa [Pi.pow_def,id_def,Function.comp_def] using h
  exact ⟨H_zero,H_deriv_zero,by simp [comparison],cder.deriv,mono,continuity,by simpa [f] using hi,sphere_distance⟩

/-- Spherical inversion and the strict inequality on the entire positive axis. -/
theorem stability_sphere_H :
    (∀ s : ℝ, 1 < s → H s = Real.log s + H (1/s) ∧
      H s - comparison s = H (1/s) - comparison (1/s) + (2/3 : ℝ)*Real.log s) ∧
    ∀ s : ℝ, 0 < s → comparison s < H s := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  obtain ⟨h0,_,c0,_,mon,_,_,sqdist⟩ := stability_radial_gap
  have small (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) : comparison s < H s := by
    have h := mon (show 0 ∈ Set.Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩) ⟨hs.le,hs'⟩ hs
    change H 0 - comparison 0 < H s - comparison s at h
    rw [h0,c0] at h
    linarith
  have invert (s : ℝ) (hs : 1 < s) :
      H s = Real.log s + H (1/s) ∧ H s - comparison s =
        H (1/s) - comparison (1/s) + (2/3 : ℝ)*Real.log s := by
    have sp : 0 < s := zero_lt_one.trans hs
    have ip : 0 < 1/s := one_div_pos.mpr sp
    have il : 1/s < 1 := (div_lt_one sp).mpr hs
    have out : (1/s) • e₁ ∉ Metric.sphere (0:X) 1 := by simpa [Metric.mem_sphere,norm_smul,e₁,abs_of_pos sp] using il.ne
    have hi : Integrable (fun x : X => Real.log (dist x ((1/s) • e₁))) sigma := by
      have h := translated_integrable sigma _ (isCompact_sphere _ _) sigma_sphere logNorm
        (fun x hx => (logNorm_smooth x hx).continuousAt) out
      simpa only [logNorm,dist_eq_norm,norm_sub_rev ((1/s) • e₁)] using h
    have eq : H s = Real.log s + H (1/s) := by
      change (∫ x, Real.log (dist x (s • e₁)) ∂sigma) = Real.log s + ∫ x, Real.log (dist x ((1/s) • e₁)) ∂sigma
      calc _ = ∫ x, Real.log s + Real.log (dist x ((1/s) • e₁)) ∂sigma := by
               apply integral_congr_ae
               filter_upwards [sigma_sphere] with x hx
               have hn : ‖x‖=1 := by simpa [Metric.mem_sphere] using hx
               have hd := dist_pos.mpr (fun (h : x=(1/s) • e₁) => out (h ▸ hx))
               have sq : dist x (s • e₁)^2 = (s * dist x ((1/s) • e₁))^2 := by
                 rw [mul_pow,sqdist x hn s,sqdist x hn (1/s)]
                 field_simp
                 ring
               rw [((sq_eq_sq₀ dist_nonneg (mul_nonneg sp.le hd.le)).mp sq),Real.log_mul sp.ne' hd.ne']
           _ = _ := by rw [integral_add (integrable_const _) hi]; simp
    refine ⟨eq,?_⟩
    have realEq : 1+s^2 = s^2 * (1+(1/s)^2) := by field_simp; ring
    unfold comparison
    rw [eq,realEq,Real.log_mul (pow_ne_zero 2 sp.ne') (by positivity),Real.log_pow]
    ring
  refine ⟨invert,fun s hs => ?_⟩
  by_cases h : s ≤ 1
  · exact small s hs h
  · have hs' := lt_of_not_ge h
    have hi : 0 < 1/s := one_div_pos.mpr hs
    linarith [(invert s hs').2, small (1/s) hi ((div_lt_one hs).mpr hs').le,Real.log_pos hs']

/-- Uniform errors from truncating below log eta, including moving poles. -/
theorem stability_truncation :
    (∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Ioo (0:ℝ) 1, |Real.log s| ≤ C / Real.sqrt s) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Law), admissible ν → (∀ a, potential ν a ≤ 1) →
      ∀ a : X, ∀ η ∈ Set.Ioo (0:ℝ) 1,
      0 ≤ (∫ x, Real.log (max η (dist x a)) ∂ν) - g ν a ∧
      (∫ x, Real.log (max η (dist x a)) ∂ν) - g ν a ≤ C * Real.sqrt η := by
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    intro s hs
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hs.1))
    rw [Real.log_inv, Real.log_sqrt hs.1.le] at h
    rw [abs_of_nonpos (Real.log_nonpos hs.1.le hs.2.le), div_eq_mul_inv]
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ν hν hp a η hη
    letI : IsProbabilityMeasure ν := hν.1
    have hi := stability_log_moment ν hν 1 zero_lt_one (fun a => by simpa using hp a) a
    have hinv := inv_data ν a 1 zero_le_one (by simpa using hp a)
    let d (x : X) := dist x a
    have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using hi.1
    have hlog : Integrable (fun x => Real.log (d x)) ν := hi.2.1
    have htr : Integrable (fun x => Real.log (max η (d x))) ν := integrable_of_compact_law ν hν
      ((continuous_const.max (continuous_id.dist continuous_const)).log
        (fun x : X => (hη.1.trans_le (le_max_left η (d x))).ne'))
    change 0 ≤ (∫ x, Real.log (max η (d x)) ∂ν) - (∫ x, Real.log (d x) ∂ν) ∧ _
    constructor
    · exact sub_nonneg.mpr (integral_mono_ae hi.2.1 htr
        (hne.mono (fun x hx => Real.log_le_log (dist_pos.mpr hx) (le_max_right _ _))))
    · change (∫ x, Real.log (max η (d x)) ∂ν) - (∫ x, Real.log (d x) ∂ν) ≤ _
      rw [← integral_sub htr hlog]
      calc _ ≤ ∫ x, η * (d x)⁻¹ ∂ν := by
                apply integral_mono_ae (htr.sub hi.2.1) (hinv.2.1.const_mul η)
                filter_upwards [hne] with x hx
                have hd : 0 < d x := dist_pos.mpr hx
                change Real.log (max η (d x)) - Real.log (d x) ≤ η * (d x)⁻¹
                by_cases h : η ≤ d x
                · rw [max_eq_right h,sub_self]; exact mul_nonneg hη.1.le (inv_nonneg.mpr hd.le)
                · rw [max_eq_left (le_of_not_ge h), ← Real.log_div hη.1.ne' hd.ne', ← div_eq_mul_inv]
                  linarith [Real.log_le_sub_one_of_pos (div_pos hη.1 hd)]
           _ = η * (∫ x, (d x)⁻¹ ∂ν) := integral_const_mul _ _
           _ ≤ η * 1 := mul_le_mul_of_nonneg_left hinv.2.2 hη.1.le
           _ ≤ _ := by
               simpa using (Real.le_sqrt_of_sq_le (show η^2 ≤ η by nlinarith [mul_nonneg hη.1.le (sub_nonneg.mpr hη.2.le)]))

/-- Eventual lower bounds express a liminf even if log moments grow without bound. -/
theorem stability_moving_center (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (a : X) (ha : a ≠ 0) (p : ℕ → X) (hp : Tendsto p atTop (𝓝 a)) :
    weak (fun j => shifted (p j) (ν j)) (shifted a sigma) ∧
    (∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      (∫ x, Real.log (max η (dist x a)) ∂sigma) - ε ≤
        ∫ x, Real.log (max η (dist x (p j))) ∂(ν j)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, H ‖a‖ - ε ≤ g (ν j) (p j) := by
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  let P (j : ℕ) : ProbabilityMeasure X := ⟨ν j,prob j⟩
  let Q : ProbabilityMeasure X := ⟨sigma,sigma_admissible.1⟩
  have hsub : Continuous (fun q : X × X => q.1-q.2) := continuous_fst.sub continuous_snd
  have hweak : Tendsto P atTop (𝓝 Q) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hw
  have hpair := (ProbabilityMeasure.continuous_prod (α := X) (β := X)).continuousAt.tendsto.comp
    (hweak.prodMk_nhds (continuous_diracProba.continuousAt.tendsto.comp hp))
  have hdiff := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hpair hsub
  have push (R : ProbabilityMeasure X) (z : X) :
      (((R.prod (diracProba z)).map (fun q : X × X => q.1-q.2)) : Measure X) =
        shifted z (R : Measure X) := by
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod]
    change Measure.map _ ((R : Measure X).prod (Measure.dirac z)) = _
    rw [Measure.prod_dirac,Measure.map_map (f := fun x : X => (x,z)) hsub.measurable (measurable_id.prodMk measurable_const)]
    rfl
  have ht : weak (fun j => shifted (p j) (ν j)) (shifted a sigma) := by
    intro f
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hdiff f
    change Tendsto (fun j => ∫ x, f x ∂((((P j).prod (diracProba (p j))).map (fun q : X × X => q.1-q.2)) : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(((Q.prod (diracProba a)).map (fun q : X × X => q.1-q.2)) : Measure X))) at h
    simp only [push] at h
    exact h
  have lower (η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j in atTop, (∫ x, Real.log (max η (dist x a)) ∂sigma) - ε ≤
        ∫ x, Real.log (max η (dist x (p j))) ∂(ν j) := by
    let R := max η (1+‖a‖)
    let f (x : X) := Real.log (min R (max η ‖x‖))
    have low (x : X) : η ≤ min R (max η ‖x‖) := le_min (le_max_left _ _) (le_max_left _ _)
    have cf : Continuous f := (continuous_const.min (continuous_const.max continuous_norm)).log
      (fun x => (hη.trans_le (low x)).ne')
    have bounds (x : X) : Real.log η ≤ f x ∧ f x ≤ Real.log R :=
      ⟨Real.log_le_log hη (low x),Real.log_le_log (hη.trans_le (low x)) (min_le_left _ _)⟩
    let F : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f,cf⟩ (Real.log R - Real.log η) (by
      intro x y
      rw [Real.dist_eq,abs_le]
      change _ ≤ f x - f y ∧ f x - f y ≤ _
      constructor <;> linarith [(bounds x).1,(bounds x).2,(bounds y).1,(bounds y).2])
    have form (μ : Law) (z : X) : (∫ x, F x ∂shifted z μ) = ∫ x, f (x-z) ∂μ :=
      integral_map (continuous_id.sub continuous_const).aemeasurable cf.aestronglyMeasurable
    have eq : (∫ x, f (x-a) ∂sigma) = ∫ x, Real.log (max η (dist x a)) ∂sigma := by
      apply integral_congr_ae
      filter_upwards [sigma_sphere] with x hx
      have hx' : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
      have hd := norm_sub_le x a
      have hmax : max η ‖x-a‖ ≤ R := max_le_max_left η (by linarith)
      simp [f,min_eq_right hmax,dist_eq_norm]
    have h : Tendsto (fun j => ∫ x, f (x-p j) ∂ν j) atTop (𝓝 (∫ x, Real.log (max η (dist x a)) ∂sigma)) := by
      simpa only [form,eq] using ht F
    filter_upwards [h.eventually_const_lt (show (∫ x, Real.log (max η (dist x a)) ∂sigma) - ε <
      ∫ x, Real.log (max η (dist x a)) ∂sigma by linarith)] with j hj
    apply hj.le.trans
    apply integral_mono (integrable_of_compact_law _ (hn.1 j).1 (cf.comp (continuous_id.sub continuous_const)))
      (integrable_of_compact_law _ (hn.1 j).1 ((continuous_const.max (continuous_id.dist continuous_const)).log
        (fun x : X => (hη.trans_le (le_max_left η (dist x (p j)))).ne')))
    intro x
    change Real.log (min R (max η ‖x-p j‖)) ≤ Real.log (max η (dist x (p j)))
    rw [dist_eq_norm]
    exact Real.log_le_log (hη.trans_le (low _)) (min_le_right _ _)
  refine ⟨ht,lower,?_⟩
  intro ε hε
  obtain ⟨C,hC,htr⟩ := stability_truncation.2
  let t := min (1/2:ℝ) (ε/(2*C))
  have tp : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ts : t ≤ 1/2 := min_le_left _ _
  have te : C*t ≤ ε/2 := by
    have h := (le_div_iff₀ (show 0 < 2*C by positivity)).1 (min_le_right (1/2:ℝ) (ε/(2*C)))
    dsimp [t]
    linarith
  have ht' : t^2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by positivity,by nlinarith [sq_nonneg (1/2 - t), mul_le_mul_of_nonneg_right ts tp.le]⟩
  have hsPot := (stability_weak_limit ν hn).2 id sigma strictMono_id sigma_admissible.1 hw
  have hlo := (htr sigma sigma_admissible hsPot.2.1 a (t^2) ht').1
  filter_upwards [lower (t^2) ht'.1 (ε/2) (by positivity)] with j hj
  have hhi := (htr _ (hn.1 j).1 (hn.1 j).2 (p j) (t^2) ht').2
  rw [Real.sqrt_sq tp.le] at hhi
  rw [← stability_spherical_radial a]
  linarith

/-- The strict spherical gap is uniform on every compact radial annulus. -/
theorem stability_compact_gap (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ A : ℝ) (hδ : 0 < δ) (hA : δ < A) :
    ∀ᶠ j in atTop, ∀ a : X, δ ≤ ‖a‖ → ‖a‖ ≤ A → L a / 6 ≤ g (ν j) a := by
  by_contra h
  have bad : ∃ᶠ j in atTop, ∃ a : X, δ ≤ ‖a‖ ∧ ‖a‖ ≤ A ∧ g (ν j) a < L a / 6 := by
    simpa only [Filter.Frequently,not_exists,not_and,not_lt] using h
  obtain ⟨k,hk,hbad⟩ := extraction_of_frequently_atTop bad
  choose x hδx hxA hfail using hbad
  let K := Metric.closedBall (0:X) A ∩ {y : X | δ ≤ ‖y‖}
  have hc : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  obtain ⟨a,ha,l,hl,hxa⟩ := hc.tendsto_subseq (fun j => (show x j ∈ K from ⟨by simpa [Metric.mem_closedBall] using hxA j,hδx j⟩))
  have ha' : 0 < ‖a‖ := hδ.trans_le ha.2
  let m := k ∘ l
  have hm := (hk.comp hl).tendsto_atTop
  have hnorm : Normalized (ν ∘ m) := ⟨fun j => hn.1 _,hn.2.comp hm⟩
  have weakm : weak (ν ∘ m) sigma := fun f => (hw f).comp hm
  have low := (stability_moving_center _ hnorm weakm a (norm_pos_iff.mp ha') (x ∘ l) hxa).2.2
  have gap : L a/6 < H ‖a‖ := stability_sphere_H.2 _ ha'
  let ε := (H ‖a‖ - L a/6)/3
  have ep : 0 < ε := by dsimp [ε]; linarith
  have hlc := (continuous_L.continuousAt.tendsto.comp hxa).div_const 6
  obtain ⟨j,jlow,jhigh⟩ := ((low ε ep).and (hlc.eventually_lt_const (show L a/6 < L a/6 + ε by linarith))).exists
  have hj := hfail (l j)
  change H ‖a‖ - ε ≤ g (ν (k (l j))) (x (l j)) at jlow
  change L (x (l j))/6 < L a/6 + ε at jhigh
  dsimp only [ε] at *
  linarith

/-- Tail bound, its error estimate, and the resulting uniform exterior inequality. -/
theorem stability_exterior (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    Tendsto (fun j => ν j (Metric.ball 0 2)) atTop (𝓝 1) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → (max 0 (-Real.log s))^2 ≤ C/s) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ j (a : X), 3 < ‖a‖ →
      ((ν j (Metric.ball 0 2)).toReal * Real.log (‖a‖-2)
        - C * Real.sqrt ((ν j (Metric.ball 0 2)ᶜ).toReal)) ≤ g (ν j) a) ∧
    Tendsto (fun r : ℝ => Real.log (r-2)/Real.log (1+r^2)) atTop (𝓝 (1/2)) ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, ∀ a : X, δ ≤ ‖a‖ → L a / 6 ≤ g (ν j) a := by
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  let B := Metric.ball (0:X) 2
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have mass : Tendsto (fun j => ν j B) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (stability_annulus_mass ν hn (1/2) (by norm_num)) tendsto_const_nhds
      (fun j => measure_mono ?_) (fun j => prob_le_one)
    intro x hx
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hx.2]
  obtain ⟨K,hK,logbound⟩ := stability_truncation.1
  let q (s : ℝ) := max 0 (-Real.log s)
  have bound (s : ℝ) (hs : 0 < s) : q s ^ 2 ≤ K^2/s := by
    by_cases h : s < 1
    · have hh := logbound s ⟨hs,h⟩
      have hneg := Real.log_nonpos hs.le h.le
      rw [abs_of_nonpos hneg] at hh
      change (max 0 (-Real.log s))^2 ≤ _
      rw [max_eq_right (neg_nonneg.mpr hneg)]
      calc _ ≤ (K/Real.sqrt s)^2 := by exact pow_le_pow_left₀ (neg_nonneg.mpr hneg) hh 2
           _ = _ := by rw [div_pow,Real.sq_sqrt hs.le]
    · simp [q,max_eq_left (neg_nonpos.mpr (Real.log_nonneg (le_of_not_gt h))),div_nonneg (sq_nonneg K) hs.le]
  let C := (K^2+1)/2
  have cp : 0 < C := by dsimp [C]; positivity
  have tail (j : ℕ) (a : X) (ha : 3 < ‖a‖) :
      (ν j).real B * Real.log (‖a‖-2) - C*Real.sqrt ((ν j).real Bᶜ) ≤ g (ν j) a := by
    let μ := ν j
    let f (x : X) := Real.log (dist x a)
    let Q (x : X) := q (dist x a)
    let m := μ.real Bᶜ
    let t := Real.sqrt m
    obtain ⟨ha0,hinv,hpot⟩ := inv_data μ a 1 zero_le_one (by simpa using (hn.1 j).2 a)
    have hne : ∀ᵐ x ∂μ, x ≠ a := by simpa [ae_iff] using ha0
    have hf : Integrable f μ := (stability_log_moment μ (hn.1 j).1 1 zero_lt_one (by simpa using (hn.1 j).2) a).2.1
    have mq : Measurable Q := measurable_const.max ((Real.measurable_log.comp (continuous_id.dist continuous_const).measurable).neg)
    have Qp (x : X) : 0 ≤ Q x := le_max_left _ _
    have hQ : Integrable Q μ := hf.norm.mono' mq.aestronglyMeasurable (Eventually.of_forall (fun x => by
      change |Q x| ≤ |f x|; rw [abs_of_nonneg (Qp x)]; exact max_le (abs_nonneg _) (neg_le_abs _)))
    have boundQ : ∀ᵐ x ∂μ, Q x ^ 2 ≤ K^2*(dist x a)⁻¹ :=
      hne.mono fun x hx => by simpa only [Q,div_eq_mul_inv] using bound _ (dist_pos.mpr hx)
    have hQ2 : Integrable (fun x => Q x ^2) μ :=
      (hinv.const_mul (K^2)).mono' (mq.pow_const 2).aestronglyMeasurable (boundQ.mono fun x hx => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Q x))] using hx)
    have ht2 : t^2 = m := Real.sq_sqrt ENNReal.toReal_nonneg
    have hQint : (∫ x in Bᶜ, Q x ^2 ∂μ) ≤ K^2 := by
      refine (setIntegral_le_integral hQ2 (Eventually.of_forall fun x => sq_nonneg _)).trans ?_
      have h := integral_mono_ae hQ2 (hinv.const_mul _) boundQ
      erw [integral_const_mul] at h
      simpa using h.trans (mul_le_mul_of_nonneg_left hpot (sq_nonneg K))
    have err : (∫ x in Bᶜ, Q x ∂μ) ≤ C*t := by
      by_cases hm : m=0
      · have hz : μ Bᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hm
        simp [Measure.restrict_eq_zero.mpr hz,t,hm]
      · have tp : 0 < t := Real.sqrt_pos.mpr (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm))
        have h := integral_mono (μ := μ.restrict Bᶜ) (hQ.integrableOn.const_mul (2*t))
          ((hQ2.integrableOn.const_mul m).add (integrable_const 1)) (fun x => by
            change 2*t*Q x ≤ m*Q x^2 + 1
            nlinarith [sq_nonneg (t*Q x - 1),show (t*Q x)^2=m*Q x^2 by rw [mul_pow,ht2]])
        erw [integral_const_mul,integral_add (hQ2.integrableOn.const_mul m) (integrable_const 1),integral_const_mul,setIntegral_const] at h
        change 2*t*(∫ x in Bᶜ, Q x ∂μ) ≤ m*(∫ x in Bᶜ, Q x^2 ∂μ)+ m*1 at h
        apply (mul_le_mul_iff_right₀ tp).mp
        dsimp only [C]
        nlinarith [mul_le_mul_of_nonneg_left hQint (show 0 ≤ m from ENNReal.toReal_nonneg)]
    have hin : μ.real B * Real.log (‖a‖-2) ≤ ∫ x in B, f x ∂μ := by
      rw [← smul_eq_mul,← setIntegral_const]
      apply setIntegral_mono_on (integrable_const _).integrableOn hf.integrableOn hB
      intro x hx
      have hnorm : ‖x‖ < 2 := by simpa [B,Metric.mem_ball] using hx
      apply Real.log_le_log (by linarith)
      rw [dist_comm,dist_eq_norm]
      linarith [norm_sub_norm_le a x]
    have hout : -(∫ x in Bᶜ, Q x ∂μ) ≤ ∫ x in Bᶜ, f x ∂μ := by
      rw [←integral_neg]
      exact integral_mono hQ.neg.integrableOn hf.integrableOn (fun x => neg_le.mp (le_max_right 0 (-f x)))
    change _ ≤ ∫ x, f x ∂μ
    rw [← integral_add_compl hB hf]
    linarith
  have ratio : Tendsto (fun r : ℝ => Real.log (r-2) / Real.log (1+r^2)) atTop (𝓝 (1/2)) := by
    have h1 := (Real.tendsto_log_comp_add_sub_log (-2)).div_atTop Real.tendsto_log_atTop
    have h2 := ((Real.tendsto_log_comp_add_sub_log 1).comp (tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0))).div_atTop Real.tendsto_log_atTop
    have h := (h1.const_add 1).div (h2.const_add 2) (by norm_num)
    apply Tendsto.congr' _ (by simpa using h)
    filter_upwards [eventually_gt_atTop (2:ℝ)] with r hr
    have hl : 0 < Real.log r := Real.log_pos (by linarith)
    have hp : 0 < Real.log (1+r^2) := Real.log_pos (by nlinarith)
    change (1+(Real.log (r + -2)-Real.log r)/Real.log r)/(2+(Real.log (r^2+1)-2*Real.log r)/Real.log r) = _
    rw [add_comm (r^2) 1]
    simp only [sub_eq_add_neg]
    field_simp [hl.ne',hp.ne'] <;> ring_nf <;> rw [mul_assoc, mul_inv_cancel₀ hp.ne',mul_one]
  refine ⟨mass,⟨K^2,sq_pos_of_pos hK,bound⟩,⟨C,cp,tail⟩,ratio,?_⟩
  intro δ hδ
  have hm : Tendsto (fun j => (ν j).real B) atTop (𝓝 1) := by
    simpa [Measure.real] using (ENNReal.tendsto_toReal_iff (fun j => measure_ne_top (ν j) _) ENNReal.one_ne_top).mpr mass
  have hr2 : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_mono (f := fun r : ℝ => r^2) (fun r => by change r^2 ≤ 1+r^2; linarith) (tendsto_pow_atTop (by norm_num))
  have hl := Real.tendsto_log_atTop.comp hr2
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((ratio.eventually_const_lt (by norm_num : (1/3:ℝ) < 1/2)).and
    (hl.eventually_ge_atTop (18*C)))
  let R := max (max A 4) (δ+1)
  have hR : δ < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  filter_upwards [stability_compact_gap ν hn hw δ R hδ hR, hm.eventually_const_lt (by norm_num : (2/3:ℝ)<1)] with j near hmass
  intro a ha
  by_cases h : ‖a‖ ≤ R
  · exact near a ha h
  · have hA' : A ≤ ‖a‖ := (le_max_left A 4).trans ((le_max_left _ _).trans (le_of_not_ge h))
    have h4 : 4 ≤ ‖a‖ := (le_max_right A 4).trans ((le_max_left _ _).trans (le_of_not_ge h))
    have Lp : 0 < L a := Real.log_pos (by nlinarith)
    have e := ((lt_div_iff₀ Lp).mp (hA _ hA').1)
    have hden : 18*C ≤ L a := (hA _ hA').2
    have ht := tail j a (by linarith)
    have measle : (ν j).real Bᶜ ≤ 1 := by simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν j) (s := Bᶜ))
    have sqrtle := Real.sqrt_le_sqrt measle
    rw [Real.sqrt_one] at sqrtle
    have logp := Real.log_pos (by linarith : 1 < ‖a‖-2)
    nlinarith [mul_le_mul_of_nonneg_right hmass.le logp.le,mul_le_mul_of_nonneg_left sqrtle cp.le]

/-- Uniform bilinear bound on the error of the pointwise Hessian. -/
theorem stability_hessian_kernel :
    deriv phi 1 = 0 ∧ deriv (deriv phi) 1 = 1 ∧
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioo (0:ℝ) (1/8), ∀ x ∈ ann δ, ∀ a : X, ‖a‖ ≤ δ →
      |dist x a - 1| ≤ 2*δ ∧ ContDiffAt ℝ 2 (fun y : X => phi (dist x y)) a ∧
      ∀ u v : X, |hess (fun y => phi (dist x y)) a u v -
        inner ℝ (direction x) u * inner ℝ (direction x) v| ≤ C*δ*‖u‖*‖v‖ := by
  let Φ (w : X) := phi ‖w‖
  let D := fderiv ℝ (fderiv ℝ Φ)
  have smooth {n : WithTop ℕ∞} {w : X} (hw : w ≠ 0) : ContDiffAt ℝ n Φ w := by
    have h : ContDiffAt ℝ n (norm : X → ℝ) w := contDiffAt_norm ℝ hw
    exact (h.log (norm_ne_zero_iff.mpr hw)).add (h.inv (norm_ne_zero_iff.mpr hw)) |>.sub contDiffAt_const
  have dphi {s : ℝ} (hs : s ≠ 0) : HasDerivAt phi ((s-1)/s^2) s := by
    have h := ((Real.hasDerivAt_log hs).add ((hasDerivAt_id s).inv hs)).sub_const 1
    change HasDerivAt (fun t : ℝ => Real.log t + t⁻¹ - 1) _ s
    convert h using 1 <;> simp <;> field_simp <;> ring
  have hphi : HasDerivAt (deriv phi) 1 1 := by
    have h := ((hasDerivAt_id (1:ℝ)).sub_const 1).div ((hasDerivAt_id (1:ℝ)).pow 2) (by norm_num)
    apply (show HasDerivAt (fun s : ℝ => (s-1)/s^2) 1 1 by simpa [Pi.div_def,Pi.pow_def,id_def] using h).congr_of_eventuallyEq
    exact (eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0)).mono (fun s hs => (dphi hs).deriv)
  have hzero : deriv phi 1 = 0 := by simpa using (dphi (s := 1) one_ne_zero).deriv
  have sphere (w : X) (hw : ‖w‖ = 1) (u v : X) :
      D w u v = inner ℝ w u * inner ℝ w v := by
    have hnz : w ≠ 0 := norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)
    have dn : HasFDerivAt (norm : X → ℝ) (innerSL ℝ w) w := by
      have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.sqrt (by simp [hw])
      convert h using 1
      · funext y; exact (Real.sqrt_sq (norm_nonneg y)).symm
      · ext v; simp [hw,innerSL_apply_apply] <;> ring
    let N := fderiv ℝ (norm : X → ℝ)
    have dN : DifferentiableAt ℝ N w :=
      ((contDiffAt_norm ℝ (n := 2) hnz).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have dc : HasFDerivAt (fun x : X => deriv phi ‖x‖) (innerSL ℝ w) w := by
      have hg : HasDerivAt (deriv phi) 1 ‖w‖ := hw ▸ hphi
      simpa [Function.comp_def] using hg.comp_hasFDerivAt w dn
    have form : fderiv ℝ Φ =ᶠ[𝓝 w] (fun x => deriv phi ‖x‖ • N x) := by
      filter_upwards [eventually_ne_nhds hnz] with x hx
      have h := (dphi (norm_ne_zero_iff.mpr hx)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
        ((contDiffAt_norm ℝ (n := 1) hx).differentiableAt one_ne_zero).hasFDerivAt
      exact h.fderiv
    change fderiv ℝ (fderiv ℝ Φ) w u v = _
    rw [form.fderiv_eq]
    erw [(dc.smul dN.hasFDerivAt).fderiv]
    simp [hw,hzero,N,dn.fderiv,innerSL_apply_apply]
  let K := Metric.closedBall (0:X) 2 ∩ {x : X | 1/2 ≤ ‖x‖}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have loc : LocallyLipschitzOn K D := by
    intro w hw
    have hnz : w ≠ 0 := by
      rintro rfl
      have h : 1/2 ≤ ‖(0:X)‖ := hw.2
      norm_num at h
    have h : ContDiffAt ℝ 1 D w := ((smooth (n := 3) hnz).fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
    obtain ⟨C,t,ht,hC⟩ := h.exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B,hB⟩ := loc.exists_lipschitzOnWith_of_compact hK
  refine ⟨hzero,hphi.deriv,2*(B:ℝ)+1,by positivity,?_⟩
  intro δ hδ x hx a ha
  obtain ⟨hxl,hxu⟩ := hx
  have xn : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hxl
    linarith [hδ.2]
  let w := -direction x
  have hw : ‖w‖ = 1 := by simpa [w,direction] using norm_smul_inv_norm (𝕜 := ℝ) xn
  have xp : ‖x-direction x‖ = |‖x‖-1| := by
    have eq : x - direction x = (‖x‖-1) • direction x := by
      rw [sub_smul,one_smul]
      simp [direction,smul_smul,norm_ne_zero_iff.mpr xn]
    rw [eq,norm_smul,show ‖direction x‖=1 by simpa [w] using hw,Real.norm_eq_abs,mul_one]
  have hd : dist (a-x) w ≤ 2*δ := by
    have h : |‖x‖-1| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
    have e : a-x-w = a-(x-direction x) := by dsimp [w]; abel
    rw [dist_eq_norm,e]
    linarith [norm_sub_le a (x-direction x),xp]
  have dl : |‖a-x‖ - 1| ≤ 2*δ := by
    rw [← hw]
    exact (abs_norm_sub_norm_le (a-x) w).trans (by simpa [dist_eq_norm] using hd)
  have lower := (abs_le.mp dl).1
  have upper := (abs_le.mp dl).2
  have anz : a-x ≠ 0 := norm_ne_zero_iff.mp (by linarith [hδ.2])
  have feq : (fun y : X => phi (dist x y)) = fun y => Φ (y-x) := by
    funext y
    simp [Φ,dist_comm x y,dist_eq_norm]
  refine ⟨by simpa [dist_comm x a,dist_eq_norm] using dl,?_,?_⟩
  · rw [feq]
    exact (smooth (n := 2) anz).comp a (contDiffAt_id.sub contDiffAt_const)
  · intro u v
    have hxK : a-x ∈ K := ⟨by simpa [Metric.mem_closedBall] using (show ‖a-x‖ ≤ 2 by linarith [hδ.2]),by change 1/2 ≤ ‖a-x‖; linarith [hδ.2]⟩
    have hwK : w ∈ K := ⟨by simp [Metric.mem_closedBall,hw],by change 1/2 ≤ ‖w‖; rw [hw]; norm_num⟩
    have op := hB.dist_le_mul _ hxK _ hwK
    rw [dist_eq_norm] at op
    have dif : ‖D (a-x) - D w‖ ≤ 2*(B:ℝ)*δ := by
      nlinarith [mul_le_mul_of_nonneg_left hd B.coe_nonneg]
    have ev := ((D (a-x) - D w) u).le_opNorm v
    have eu := (D (a-x) - D w).le_opNorm u
    have hessEq : hess (fun y : X => phi (dist x y)) a u v = D (a-x) u v := by
      rw [feq]
      unfold hess D
      simp_rw [show fderiv ℝ (fun y : X => Φ (y-x)) = fun y => fderiv ℝ Φ (y-x) from funext (fun _ => fderiv_comp_sub _)]
      rw [fderiv_comp_sub]
    rw [hessEq,show inner ℝ (direction x) u * inner ℝ (direction x) v = D w u v by simp [sphere w hw,w]]
    change ‖((D (a-x)-D w) u) v‖ ≤ _
    calc _ ≤ ‖(D (a-x)-D w) u‖ * ‖v‖ := ev
         _ ≤ (‖D (a-x)-D w‖ * ‖u‖) * ‖v‖ := by gcongr
         _ ≤ _ := by gcongr; linarith [hδ.1]

private theorem sigma_second (u v : X) :
    (∫ x, inner ℝ x u * inner ℝ x v ∂sigma) = inner ℝ u v / 3 := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  let q (y : X) := ∫ x, (inner ℝ x y)^2 ∂sigma
  have cts (y : X) : Continuous (fun x : X => inner ℝ x y) := continuous_id.inner continuous_const
  have hi (i j : X) := integrable_of_compact_law _ sigma_admissible ((cts i).mul (cts j))
  have radial (y z : X) (h : ‖y‖ = ‖z‖) : q y = q z := by
    let U := (ℝ ∙ (y-z))ᗮ.reflection
    have hu : U y = z := Submodule.reflection_sub h
    calc q y = ∫ x, (inner ℝ (U x) z)^2 ∂sigma := by simp only [q,←hu,U.inner_map_map]
         _ = ∫ x, (inner ℝ x z)^2 ∂(sigma.map U) := (integral_map (f := fun x : X => (inner ℝ x z)^2)
              U.continuous.aemeasurable ((cts z).pow 2).aestronglyMeasurable).symm
         _ = q z := by rw [sigma_map_isometry]
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have bn (i : Fin 3) : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have sum : (∑ i : Fin 3, q (b i)) = 1 := by
    unfold q
    erw [←integral_finsetSum Finset.univ (fun i _ => integrable_of_compact_law _ sigma_admissible ((cts (b i)).pow 2))]
    calc _ = ∫ _ : X, (1 : ℝ) ∂sigma := by
              apply integral_congr_ae
              filter_upwards [sigma_sphere] with x hx
              have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
              simpa [Real.norm_eq_abs,sq_abs,hn] using b.sum_sq_norm_inner_left x
         _ = 1 := by simp
  have bq : q (b 0) = 1/3 := by
    have e (i : Fin 3) : q (b i) = q (b 0) := radial _ _ ((bn i).trans (bn 0).symm)
    calc _ = (∑ i : Fin 3, q (b i))/3 := by simp_rw [e]; simp
         _ = _ := by rw [sum]
  have qeq (y : X) : q y = ‖y‖^2/3 := by
    have hh : ‖‖y‖ • b 0‖ = ‖y‖ := by simp [norm_smul,bn]
    rw [radial y _ hh.symm]
    change (∫ x, (inner ℝ x (‖y‖ • b 0))^2 ∂sigma) = _
    simp_rw [real_inner_smul_right,mul_pow,integral_const_mul]
    change ‖y‖^2*q (b 0) = _
    rw [bq]; ring
  have polar : q (u+v) = q u + q v + 2*(∫ x, inner ℝ x u * inner ℝ x v ∂sigma) := by
    have eq (x : X) : (inner ℝ x (u+v))^2 =
        (inner ℝ x u)^2 + (inner ℝ x v)^2 + 2*(inner ℝ x u * inner ℝ x v) := by
      rw [inner_add_right]; ring
    have hu := integrable_of_compact_law _ sigma_admissible ((cts u).pow 2)
    have hv := integrable_of_compact_law _ sigma_admissible ((cts v).pow 2)
    simp only [q,eq]
    erw [integral_add (hu.add hv) ((hi u v).const_mul 2),integral_add hu hv,integral_const_mul]
    rfl
  rw [qeq,qeq,qeq,norm_add_sq_real] at polar
  linarith

/-- The limiting annular second moment is the bilinear form I/3. -/
theorem stability_annular_second_moment (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) (1/8)) :
    sigma (frontier (ann δ)) = 0 ∧ ∀ u v : X,
      Tendsto (fun j => ∫ x in ann δ, inner ℝ (direction x) u * inner ℝ (direction x) v ∂(ν j))
        atTop (𝓝 (inner ℝ u v / 3)) := by
  letI : IsProbabilityMeasure sigma := sigma_admissible.1
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  have hA : MeasurableSet (ann δ) :=
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  have interior_mem {x : X} (hx : x ∈ Metric.sphere (0:X) 1) : x ∈ interior (ann δ) := by
    let V := {y : X | 1-δ < ‖y‖ ∧ ‖y‖ < 1+δ}
    have hV : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hh : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds (x := x)
      (show x ∈ V from ⟨by linarith [hδ.1],by linarith [hδ.1]⟩)) (fun _ h => ⟨h.1.le,h.2.le⟩))
  constructor
  · apply measure_mono_null (t := (Metric.sphere (0:X) 1)ᶜ) _ (ae_iff.mp sigma_sphere)
    intro x hx hs
    exact hx.2 (interior_mem hs)
  · intro u v
    let d (x : X) := (max (1/2:ℝ) ‖x‖)⁻¹ • x
    have dp (x : X) : 0 < max (1/2:ℝ) ‖x‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have cd : Continuous d := ((continuous_const.max continuous_norm).inv₀ (fun x => (dp x).ne')).smul continuous_id
    have bd (x : X) : ‖d x‖ ≤ 1 := by
      simp only [d,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (dp x)), inv_mul_eq_div]
      exact (div_le_one (dp x)).mpr (le_max_right _ _)
    let f (x : X) := inner ℝ (d x) u * inner ℝ (d x) v
    have cf : Continuous f := (cd.inner continuous_const).mul (cd.inner continuous_const)
    have bf (x : X) : ‖f x‖ ≤ ‖u‖*‖v‖ := by
      have h (z : X) : ‖inner ℝ (d x) z‖ ≤ ‖z‖ := (norm_inner_le_norm _ _).trans
        (by simpa using mul_le_mul_of_nonneg_right (bd x) (norm_nonneg z))
      exact (norm_mul _ _).le.trans (mul_le_mul (h u) (h v) (norm_nonneg _) (norm_nonneg _))
    let G : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f cf _ bf
    have eqσ : (∫ x, f x ∂sigma) = inner ℝ u v / 3 := by
      rw [← sigma_second]
      apply integral_congr_ae
      filter_upwards [sigma_sphere] with x hx
      have hh : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
      norm_num [f,d,hh]
    have conv : Tendsto (fun j => ∫ x, f x ∂ν j) atTop (𝓝 (inner ℝ u v / 3)) := by
      rw [←eqσ]; exact hw G
    have hmass : Tendsto (fun j => (ν j).real (ann δ)ᶜ) atTop (𝓝 0) := by
      have H := (ENNReal.tendsto_toReal_iff (fun j => measure_ne_top (ν j) _) (by norm_num : (1:ℝ≥0∞) ≠ ⊤)).mpr
        (stability_annulus_mass ν hn δ hδ.1)
      simpa [measureReal_compl hA,measureReal_def] using H.const_sub 1
    have he : Tendsto (fun j => ∫ x in (ann δ)ᶜ, f x ∂ν j) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun j => norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun x _ => bf x))
      simpa [mul_comm] using hmass.mul_const (‖u‖*‖v‖)
    apply Tendsto.congr' _ (show Tendsto (fun j => (∫ x, f x ∂ν j) - (∫ x in (ann δ)ᶜ, f x ∂ν j))
      atTop (𝓝 (inner ℝ u v / 3)) by simpa using conv.sub he)
    exact Eventually.of_forall fun j => by
      dsimp only
      rw [← integral_add_compl hA (integrable_of_compact_law _ (hn.1 j).1 cf),add_sub_cancel_right]
      apply setIntegral_congr_fun hA
      intro x hx
      have hx' : (1/2:ℝ) ≤ ‖x‖ := by linarith [hx.1,hδ.2]
      simp only [f,d,direction,max_eq_right hx']

private theorem closed_ann (δ : ℝ) : IsClosed (ann δ) :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

private theorem compact_ann (δ : ℝ) : IsCompact (ann δ) :=
  (isCompact_closedBall (0:X) (1+δ)).of_isClosed_subset (closed_ann _) (fun x hx => by simpa [Metric.mem_closedBall] using hx.2)

private theorem F_bounds (ν : Law) (hν : admissible ν) (hp : ∀ a, potential ν a ≤ 1) (δ : ℝ) (a : X) :
    0 ≤ F ν δ a ∧ F ν δ a ≤ g ν a := by
  letI : IsProbabilityMeasure ν := hν.1
  have he := stability_phi_integral ν hν hp a
  have ha := (stability_log_moment ν hν 1 zero_lt_one (fun x => by simpa using hp x) a).1
  have hn : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using ha
  have pos := hn.mono (fun x hx => (stability_phi_shape.1 _ (dist_pos.mpr hx)).1)
  exact ⟨integral_nonneg_of_ae (ae_mono Measure.restrict_le_self pos), (setIntegral_le_integral he.1 pos).trans he.2.2⟩

private def phiNorm (w : X) := phi ‖w‖

private theorem phi_smooth (w : X) (hw : w ≠ 0) : ContDiffAt ℝ 3 phiNorm w := by
  have h : ContDiffAt ℝ 3 (norm : X → ℝ) w := contDiffAt_norm ℝ hw
  exact ((h.log (norm_ne_zero_iff.mpr hw)).add (h.inv (norm_ne_zero_iff.mpr hw))).sub contDiffAt_const

private theorem F_regular (ν : Law) [IsFiniteMeasure ν] (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) (1/8))
    (a : X) (ha : a ∈ Metric.closedBall (0:X) δ) :
    ContDiffAt ℝ 2 (F ν δ) a ∧ ∀ u v : X,
    (hess (F ν δ) a u v = ∫ x in ann δ, hess (fun y : X => phi (dist x y)) a u v ∂ν) ∧
      Integrable (fun x => hess (fun y : X => phi (dist x y)) a u v) (ν.restrict (ann δ)) := by
  let ρ := ν.restrict (ann δ)
  have hρ : ∀ᵐ x ∂ρ, x ∈ ann δ := ae_restrict_mem (closed_ann _).measurableSet
  have han : a ∉ ann δ := by
    intro h
    have ha' : ‖a‖ ≤ δ := by simpa [Metric.mem_closedBall] using ha
    linarith [h.1,hδ.2]
  have eq : F ν δ = translateAverage ρ phiNorm := by
    funext y
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp [phiNorm,dist_comm x y,dist_eq_norm]
  rw [eq]
  have h := translateAverage_c2 ρ _ (compact_ann δ) hρ phiNorm phi_smooth han
  refine ⟨h.1,fun u v => ?_⟩
  let D : X → X →L[ℝ] X →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ phiNorm)
  have hi : Integrable (fun x => D (a-x)) ρ := translated_integrable ρ _ (compact_ann δ) hρ D
    (fun x hx => (((phi_smooth x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuousAt) han
  have hu : Integrable (fun x => D (a-x) u) ρ := (ContinuousLinearMap.apply ℝ _ u).integrable_comp hi
  have e (x : X) : hess (fun y : X => phi (dist x y)) a u v = D (a-x) u v := by
    have eqf : (fun y : X => phi (dist x y)) = (fun y => phiNorm (y-x)) := by
      funext y; simp [phiNorm,dist_comm x y,dist_eq_norm]
    simp only [hess,eqf,show fderiv ℝ (fun y : X => phiNorm (y-x)) = fun y => fderiv ℝ phiNorm (y-x) from funext (fun _ => fderiv_comp_sub _),fderiv_comp_sub,D]
  simp only [e]
  refine ⟨?_,(ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hu⟩
  unfold hess
  rw [h.2]
  change ((∫ x, D (a-x) ∂ρ) u) v = _
  rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply hu]

private def dyad (x : X) := (innerSL ℝ x).smulRight (innerSL ℝ x)

private theorem dyad_cont : Continuous dyad := by
  let S := ContinuousLinearMap.smulRightL ℝ X (X →L[ℝ] ℝ)
  exact (S.continuous.comp (innerSL ℝ (E := X)).continuous).clm_apply (innerSL ℝ (E := X)).continuous

private theorem form_converges {B : ℕ → X →L[ℝ] X →L[ℝ] ℝ} {A : X →L[ℝ] X →L[ℝ] ℝ}
    (h : ∀ u v, Tendsto (fun j => B j u v) atTop (𝓝 (A u v))) : Tendsto B atTop (𝓝 A) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let E : (X →L[ℝ] X →L[ℝ] ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) :=
    { toFun := fun t i k => t (b i) (b k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have inj : Function.Injective E := by
    intro t q h
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro k
    exact congrFun (congrFun h i) k
  have emb := LinearMap.isClosedEmbedding_of_injective (f := E) ((LinearMap.ker_eq_bot (f := E)).mpr inj)
  apply emb.isEmbedding.tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => h (b i) (b k)

/-- A single O(delta) constant and the fixed-delta large-index loss. -/
theorem stability_annular_curvature (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    (∀ (j : ℕ) (δ : ℝ) (a : X), 0 ≤ F (ν j) δ a ∧ F (ν j) δ a ≤ g (ν j) a) ∧
    ∃ (C δ₀ : ℝ), 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1/8 ∧
      ∀ δ ∈ Set.Ioo (0:ℝ) δ₀, ∃ b : ℕ → ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, 1/6 - C*δ - ε ≤ b j) ∧
      (∀ᶠ j in atTop, 0 < b j ∧ ∀ a ∈ Metric.closedBall (0:X) δ,
        ContDiffAt ℝ 2 (F (ν j) δ) a ∧
        ∀ v : X, 2*b j * ‖v‖^2 ≤ hess (F (ν j) δ) a v v) := by
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  refine ⟨fun j δ a => F_bounds _ (hn.1 j).1 (hn.1 j).2 δ a,?_⟩
  obtain ⟨C,hC,hpoint⟩ := stability_hessian_kernel.2.2
  let d₀ := min (1/8:ℝ) ((1/6)/C)
  have hd₀ : 0 < d₀ := lt_min (by norm_num) (div_pos (by norm_num) hC)
  refine ⟨C,d₀,hC,hd₀,min_le_left _ _,?_⟩
  intro δ hδ
  have hd : δ ∈ Set.Ioo (0:ℝ) (1/8) := ⟨hδ.1,hδ.2.trans_le (min_le_left _ _)⟩
  let B (j : ℕ) := ∫ x in ann δ, dyad (direction x) ∂ν j
  let A : X →L[ℝ] X →L[ℝ] ℝ := (1/3:ℝ) • (innerSL ℝ (E := X) : X →L[ℝ] X →L[ℝ] ℝ)
  have hi (j : ℕ) : Integrable (fun x => dyad (direction x)) ((ν j).restrict (ann δ)) := by
    apply ContinuousOn.integrableOn_compact (compact_ann δ)
    intro x hx
    have hx' : ‖x‖ ≠ 0 := by linarith [hx.1,hd.2]
    exact (dyad_cont.continuousAt.comp ((continuous_norm.continuousAt.inv₀ hx').smul continuousAt_id)).continuousWithinAt
  have form (j : ℕ) (u v : X) : B j u v = ∫ x in ann δ, inner ℝ (direction x) u * inner ℝ (direction x) v ∂ν j := by
    unfold B
    have hu : Integrable (fun x => dyad (direction x) u) ((ν j).restrict (ann δ)) :=
      (ContinuousLinearMap.apply ℝ _ u).integrable_comp (hi j)
    rw [ContinuousLinearMap.integral_apply (hi j),ContinuousLinearMap.integral_apply hu]
    rfl
  have hb : Tendsto B atTop (𝓝 A) := by
    apply form_converges
    intro u v
    simp only [form]
    have t := (stability_annular_second_moment ν hn hw δ hd).2 u v
    convert t using 2 <;> simp [A,div_eq_mul_inv,mul_comm,innerSL_apply_apply] <;> rfl
  let diff (j : ℕ) := ‖B j - A‖
  have hlim : Tendsto diff atTop (𝓝 0) := by simpa [diff] using (hb.sub_const A).norm
  let b (j : ℕ) := (1/3 - C*δ - diff j)/2
  have blim : Tendsto b atTop (𝓝 ((1/3-C*δ)/2)) := by
    simpa [b] using (hlim.const_sub (1/3-C*δ)).div_const 2
  have βpos : 0 < (1/3-C*δ)/2 := by
    have t := (lt_div_iff₀ hC).mp (hδ.2.trans_le (min_le_right _ _))
    linarith
  refine ⟨b,fun ε hε => (blim.eventually_const_lt (show 1/6-C*δ-ε < (1/3-C*δ)/2 by nlinarith [mul_pos hC hd.1])).mono fun _ h => h.le,?_⟩
  filter_upwards [blim.eventually_const_lt βpos] with j hj
  refine ⟨hj,fun a ha => ⟨(F_regular (ν j) δ hd a ha).1,fun v => ?_⟩⟩
  have ha' : ‖a‖ ≤ δ := by simpa [Metric.mem_closedBall] using ha
  obtain ⟨hform,hint⟩ := (F_regular (ν j) δ hd a ha).2 v v
  have hiR : Integrable (fun x => inner ℝ (direction x) v * inner ℝ (direction x) v) ((ν j).restrict (ann δ)) :=
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp ((ContinuousLinearMap.apply ℝ _ v).integrable_comp (hi j))
  have err := norm_setIntegral_le_of_norm_le_const (μ := ν j) (s := ann δ) (measure_lt_top _ _)
    (f := fun x => hess (fun y : X => phi (dist x y)) a v v - inner ℝ (direction x) v * inner ℝ (direction x) v)
    (fun x hx => (hpoint δ hd x hx a ha').2.2 v v)
  rw [integral_sub hint hiR,←form,←hform] at err
  have le1 : (ν j).real (ann δ) ≤ 1 := by simpa [Measure.real] using ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (prob_le_one (μ := ν j) (s := ann δ))
  have ep : 0 ≤ C * δ * ‖v‖ * ‖v‖ := by have hd' := hd.1; positivity
  have hh : - (C*δ*‖v‖*‖v‖) ≤ hess (F (ν j) δ) a v v - B j v v := (abs_le.mp (err.trans (mul_le_of_le_one_right ep le1))).1
  have op : ‖((B j - A) v) v‖ ≤ diff j * ‖v‖ * ‖v‖ :=
    (((B j - A) v).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((B j-A).le_opNorm v) (norm_nonneg v))
  change |B j v v - A v v| ≤ _ at op
  have al : A v v = (1/3)*‖v‖^2 := by change (1/3:ℝ)*inner ℝ v v = _; rw [real_inner_self_eq_norm_sq]
  rw [al] at op
  dsimp only [b]
  nlinarith [(abs_le.mp op).1]

/-- A constrained minimizer, its first variation, the Taylor bound and convergence. -/
theorem stability_trial_min (ν : ℕ → Law) (hn : Normalized ν)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) (1/8)) (b : ℕ → ℝ)
    (hb : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ b j)
    (hh : ∀ᶠ j in atTop, ∀ a ∈ Metric.closedBall (0:X) δ,
      ContDiffAt ℝ 2 (F (ν j) δ) a ∧ ∀ v : X, 2*b j * ‖v‖^2 ≤ hess (F (ν j) δ) a v v) :
    ∃ z : ℕ → X, (∀ j, z j ∈ Metric.closedBall 0 δ ∧
      ∀ a ∈ Metric.closedBall (0:X) δ, F (ν j) δ (z j) ≤ F (ν j) δ a ∧
        0 ≤ (fderiv ℝ (F (ν j) δ) (z j)) (a-z j)) ∧
    (∀ᶠ j in atTop, b j * ‖z j‖^2 ≤ g (ν j) 0 ∧
      ∀ a ∈ Metric.closedBall (0:X) δ, F (ν j) δ (z j) + b j * ‖a-z j‖^2 ≤ g (ν j) a) ∧ Tendsto z atTop (𝓝 0) := by
  let K := Metric.closedBall (0:X) δ
  have h0K : (0:X) ∈ K := Metric.mem_closedBall_self hδ.1.le
  have hcK : Convex ℝ K := convex_closedBall _ _
  haveI prob (j : ℕ) : IsProbabilityMeasure (ν j) := (hn.1 j).1.1
  have reg (j : ℕ) (x : X) (hx : x ∈ K) := (F_regular (ν j) δ hδ x hx).1
  have ex (j : ℕ) := (isCompact_closedBall (0:X) δ).exists_isMinOn ⟨0,h0K⟩
    (show ContinuousOn (F (ν j) δ) K from fun x hx => (reg j x hx).continuousAt.continuousWithinAt)
  choose z hz hmin using ex
  have first (j : ℕ) (a : X) (ha : a ∈ K) :
      0 ≤ fderiv ℝ (F (ν j) δ) (z j) (a-z j) :=
    (hmin j).isLocalMinOn.hasFDerivWithinAt_nonneg
      ((reg j _ (hz j)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hcK.segment_subset (hz j) ha))
  have bound (j : ℕ) (x : X) := F_bounds _ (hn.1 j).1 (hn.1 j).2 δ x
  have ht : ∀ᶠ j in atTop, ∀ a ∈ K, F (ν j) δ (z j) + b j * ‖a-z j‖^2 ≤ g (ν j) a := by
    filter_upwards [hh] with j hj
    intro a ha
    let f := F (ν j) δ
    let v := a-z j
    let p (t : ℝ) := z j + t • v
    have path (t : ℝ) (h : t ∈ Set.Icc (0:ℝ) 1) : p t ∈ K := hcK.add_smul_sub_mem (hz j) ha h
    have dp (t : ℝ) : HasDerivAt p v t := by
      simpa [p] using ((hasDerivAt_id t).smul_const v).const_add (z j)
    let Q := b j * ‖v‖^2
    let G (t : ℝ) := f (p t) - t^2*Q
    let G' (t : ℝ) := fderiv ℝ f (p t) v - 2*t*Q
    have dG (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : HasDerivAt G (G' t) t := by
      have h := ((reg j _ (path t ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (dp t)
      convert h.sub (((hasDerivAt_id t).pow 2).mul_const Q) using 1 <;> simp [G,G',f,Function.comp_def,Pi.sub_def]
    have dG' (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : HasDerivAt G' (hess f (p t) v v - 2*Q) t := by
      have h := ((reg j _ (path t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have e := (h.hasFDerivAt.comp_hasDerivAt t (dp t)).clm_apply (hasDerivAt_const t v)
      convert e.sub (((hasDerivAt_id t).const_mul 2).mul_const Q) using 1 <;> simp [G',hess,f,Function.comp_def,Pi.sub_def]
    have mon : MonotoneOn G' (Set.Icc 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (dG' t ht).continuousAt.continuousWithinAt)
        (fun t ht => (dG' t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [(dG' t (interior_subset ht)).deriv]
      linarith [(hj _ (path _ (interior_subset ht))).2 v]
    have monot : MonotoneOn G (Set.Icc 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (dG t ht).continuousAt.continuousWithinAt)
        (fun t ht => (dG t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [(dG t (interior_subset ht)).deriv]
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := interior_subset ht
      have hzero : 0 ≤ G' 0 := by simpa [G',p,v,f] using first j a ha
      exact hzero.trans (mon (Set.left_mem_Icc.mpr zero_le_one) ht' ht'.1)
    have m := monot (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
    have step : f (z j) ≤ f a - Q := by simpa [G,p,v] using m
    exact (le_sub_iff_add_le.mp step).trans (bound j a).2
  have hsmall : ∀ᶠ j in atTop, b j * ‖z j‖^2 ≤ g (ν j) 0 := by
    filter_upwards [ht] with j hj
    have h := hj 0 h0K
    simp only [zero_sub,norm_neg] at h
    linarith [(bound j (z j)).1]
  refine ⟨z,fun j => ⟨hz j,fun a ha => ⟨hmin j ha,first j a ha⟩⟩,hsmall.and ht,?_⟩
  obtain ⟨c,hc,hcb⟩ := hb
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero_norm' (a := fun j => Real.sqrt (g (ν j) 0/c))
  · filter_upwards [hsmall,hcb] with j hj hj'
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact Real.le_sqrt_of_sq_le ((le_div_iff₀ hc).mpr (by nlinarith [mul_le_mul_of_nonneg_right hj' (sq_nonneg ‖z j‖)]))
  · simpa using (hn.2.div_const c).sqrt

/-- The logarithmic cost and the loss for shifting the exterior bound. -/
theorem stability_shift_loss :
    (∀ a : X, L a ≤ ‖a‖^2) ∧ LipschitzWith 1 L ∧
    (∀ (δ : ℝ) (z a : X), 0 < δ → δ ≤ ‖a‖ →
      L (a-z) ≤ L a + ‖z‖ ∧ L a + ‖z‖ ≤ (1 + ‖z‖ / Real.log (1+δ^2))*L a) ∧
    ∀ (δ : ℝ) (z : ℕ → X), 0 < δ → Tendsto z atTop (𝓝 0) →
      Tendsto (fun j => ‖z j‖ / Real.log (1+δ^2)) atTop (𝓝 0) := by
  have hlow (a : X) : L a ≤ ‖a‖^2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+‖a‖^2 by positivity)
    simpa [L] using h
  let f (t : ℝ) := Real.log (1+t^2)
  have hd (t : ℝ) : HasDerivAt f (2*t/(1+t^2)) t := by
    convert ((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2)).log
      (show 1+t^2 ≠ 0 by positivity) using 1 <;> simp [f] <;> ring
  have hf : LipschitzWith 1 f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
    intro t
    rw [(hd t).deriv]
    change |2*t/(1+t^2)| ≤ 1
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (t+1)]
    · apply (div_le_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (t-1)]
  have hLip : LipschitzWith 1 L := by
    apply LipschitzWith.mk_one
    intro x y
    calc dist (L x) (L y) = dist (f ‖x‖) (f ‖y‖) := rfl
         _ ≤ dist ‖x‖ ‖y‖ := by simpa using hf.dist_le_mul ‖x‖ ‖y‖
         _ ≤ dist x y := dist_norm_norm_le x y
  refine ⟨hlow, hLip, ?_, ?_⟩
  · intro δ z a hδ ha
    have hlog : 0 < Real.log (1+δ^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hδ])
    have hcomp : Real.log (1+δ^2) ≤ L a := Real.log_le_log (by positivity) (by
      have := sq_le_sq' (show -‖a‖ ≤ δ by linarith [norm_nonneg a]) ha
      linarith)
    have hratio := mul_le_mul_of_nonneg_left hcomp (div_nonneg (norm_nonneg z) hlog.le)
    rw [div_mul_cancel₀ _ hlog.ne'] at hratio
    refine ⟨?_, by nlinarith⟩
    have h := hLip.dist_le_mul (a-z) a
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm] at h
    have he : a-z-a = -z := by abel
    rw [he, norm_neg] at h
    linarith [le_abs_self (L (a-z)-L a)]
  · intro δ z hδ hz
    simpa using hz.norm.div_const (Real.log (1+δ^2))

/-- Interior and exterior bounds about one center, followed by their minimum. -/
theorem stability_join_at_center (ν : Law) (δ b : ℝ) (z : X) (hδ : 0 < δ) (hb : 0 ≤ b)
    (hi : ∀ a : X, ‖a‖ ≤ δ → b*‖a-z‖^2 ≤ g ν a)
    (ho : ∀ a : X, δ ≤ ‖a‖ → L a/6 ≤ g ν a) :
    let q := ‖z‖ / Real.log (1+δ^2)
    (∀ a : X, ‖a‖ ≤ δ → b*L (a-z) ≤ g ν a) ∧
      (∀ a : X, δ ≤ ‖a‖ → L (a-z) / (6*(1+q)) ≤ g ν a) ∧
      ∀ a : X, min b (1/(6*(1+q))) * L (a-z) ≤ g ν a := by
  dsimp only
  have hL := stability_shift_loss
  have hden : 0 < Real.log (1+δ^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hδ])
  have hq : 0 ≤ ‖z‖ / Real.log (1+δ^2) := div_nonneg (norm_nonneg _) hden.le
  have hin (a : X) (ha : ‖a‖ ≤ δ) := (mul_le_mul_of_nonneg_left (hL.1 (a-z)) hb).trans (hi a ha)
  have hout (a : X) (ha : δ ≤ ‖a‖) : L (a-z)/(6*(1+‖z‖/Real.log (1+δ^2))) ≤ g ν a := by
    apply (div_le_iff₀ (by positivity)).2
    have h := (hL.2.2.1 δ z a hδ ha)
    have h' := mul_le_mul_of_nonneg_left (show L a ≤ 6*g ν a by linarith [ho a ha])
      (show 0 ≤ 1+‖z‖/Real.log (1+δ^2) by linarith)
    exact (h.1.trans h.2).trans (by linarith [h'])
  refine ⟨hin, hout, ?_⟩
  intro a
  have hnn : 0 ≤ L (a-z) := Real.log_nonneg (by nlinarith [sq_nonneg ‖a-z‖])
  rcases le_total ‖a‖ δ with ha | ha
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hnn).trans (hin a ha)
  · apply (mul_le_mul_of_nonneg_right (min_le_right _ _) hnn).trans
    simpa only [div_mul_eq_mul_div,one_mul] using hout a ha

/-- The exterior and interior estimates use the same point for every mark. -/
theorem stability_common_center (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma) :
    (∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ δ ∈ Set.Ioo (0:ℝ) δ₀,
      ∃ z : ℕ → X, (∀ j, ‖z j‖ ≤ δ) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a : X, (1/6-C*δ-ε)*L (a-z j) ≤ g (ν j) a) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∃ z : X, ∀ a : X, (1/6-ε)*L (a-z) ≤ g (ν j) a := by
  obtain ⟨hF,C,h₀,hC,hpos,heighth,hcurv⟩ := stability_annular_curvature ν hn hw
  let δ₀ := min h₀ ((1/12)/C)
  have hd0 : 0 < δ₀ := lt_min hpos (div_pos (by norm_num) hC)
  have fixed (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) δ₀) :
      ∃ z : ℕ → X, (∀ j, ‖z j‖ ≤ δ) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a : X, (1/6-C*δ-ε)*L (a-z j) ≤ g (ν j) a := by
    have hm : δ < h₀ := hδ.2.trans_le (min_le_left _ _)
    have hCD := (lt_div_iff₀ hC).mp (hδ.2.trans_le (min_le_right _ _))
    obtain ⟨b,hbl,hbh⟩ := hcurv δ ⟨hδ.1,hm⟩
    have low := hbl (1/24) (by norm_num)
    have hb : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ b j := ⟨1/24,by norm_num,low.mono fun j hj => by linarith⟩
    obtain ⟨z,hz,ht,hz0⟩ := stability_trial_min ν hn δ ⟨hδ.1,hm.trans_le heighth⟩ b hb
      (hbh.mono fun j hj => hj.2)
    refine ⟨z,fun j => by simpa [Metric.mem_closedBall] using (hz j).1,hz0,?_⟩
    intro ε hε
    let q (j : ℕ) := ‖z j‖ / Real.log (1+δ^2)
    have hq : Tendsto q atTop (𝓝 0) := stability_shift_loss.2.2.2 δ z hδ.1 hz0
    have hc : Tendsto (fun j => 1/(6*(1+q j))) atTop (𝓝 (1/6)) := by
      simpa [Pi.div_def] using (tendsto_const_nhds (x := (1:ℝ))).div ((hq.const_add 1).const_mul 6) (by norm_num)
    have gg : 1/6-C*δ-ε < 1/6 := by nlinarith [mul_pos hC hδ.1]
    filter_upwards [ht,hbh,hbl ε hε,hc.eventually_const_lt gg,(stability_exterior ν hn hw).2.2.2.2 δ hδ.1] with j ht' hb' hl' he' ext
    intro a
    have near (y : X) (hy : ‖y‖ ≤ δ) : b j * ‖y-z j‖^2 ≤ g (ν j) y := by
      have hh := ht'.2 y (by simpa [Metric.mem_closedBall] using hy)
      linarith [(hF j δ (z j)).1]
    have both := (stability_join_at_center (ν j) δ (b j) (z j) hδ.1 hb'.1.le near ext).2.2 a
    exact (mul_le_mul_of_nonneg_right (le_min hl' he'.le) (Real.log_nonneg (by change 1 ≤ 1+‖a-z j‖^2; linarith [sq_nonneg ‖a-z j‖]))).trans both
  refine ⟨⟨C,δ₀,hC,hd0,fixed⟩,?_⟩
  intro ε hε
  let δ := min (δ₀/2) (ε/(2*C))
  have hd : δ ∈ Set.Ioo (0:ℝ) δ₀ :=
    ⟨lt_min (half_pos hd0) (div_pos hε (by positivity)),(min_le_left _ _).trans_lt (half_lt_self hd0)⟩
  obtain ⟨z,_,_,hz⟩ := fixed δ hd
  have hcd : C*δ ≤ ε/2 := by
    have h := (le_div_iff₀ (show 0<2*C by positivity)).mp (min_le_right (δ₀/2) (ε/(2*C)))
    dsimp only [δ]; linarith
  filter_upwards [hz (ε/2) (half_pos hε)] with j hj
  refine ⟨z j,fun a => (mul_le_mul_of_nonneg_right (by linarith : 1/6-ε ≤ 1/6-C*δ-ε/2)
    (Real.log_nonneg (by change 1 ≤ 1+‖a-z j‖^2; linarith [sq_nonneg ‖a-z j‖]))).trans (hj a)⟩

/-- Average and return to the original coordinates. -/
theorem stability_unscale_cost (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (hp : ∀ a, potential ν a ≤ 1) (c b β : ℝ) (p z : X) (hc : 0 < c) (hc' : c ≤ 1)
    (hb : 0 < b) (hz : ∀ a, b*L (a-z) ≤ g ν a)
    (havg : (∫ a, g ν a ∂(shifted p (scaled c μ))) ≤ β) :
    b * cost (shifted p (scaled c μ)) z ≤ β ∧
    cost μ (c • (z+p)) ≤ cost (shifted p (scaled c μ)) z ∧ b * J μ ≤ β := by
  let T (a : X) := c⁻¹ • a
  let S (a : X) := a-p
  let ρ := shifted p (scaled c μ)
  have hT : Continuous T := continuous_id.const_smul (c⁻¹)
  have hS : Continuous S := continuous_id.sub continuous_const
  have hρ : admissible ρ := admissible_map _ (admissible_map μ hμ hT) hS
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure ρ := hρ.1
  have hg : Integrable (g ν) ρ :=
    (log_product _ _ hρ hν 1 zero_lt_one (fun a => by simpa using hp a)).integral_prod_right
  have cts (y : X) : Continuous (fun a => L (y-a)) := continuous_L.comp (continuous_const.sub continuous_id)
  have hf : b * cost ρ z ≤ β := by
    change b * (∫ a, L (z-a) ∂ρ) ≤ _
    rw [← integral_const_mul]
    refine (integral_mono ((integrable_of_compact_law _ hρ (cts z)).const_mul b) hg ?_).trans havg
    intro a
    simpa only [L, norm_sub_rev z a] using hz a
  have eq : cost ρ z = ∫ a, L (z-S (T a)) ∂μ := by
    unfold cost
    change (∫ a, L (z-a) ∂((μ.map T).map S)) = _
    rw [integral_map hS.aemeasurable (cts z).aestronglyMeasurable,
      integral_map (f := fun a => L (z-S a)) hT.aemeasurable ((cts z).comp hS).aestronglyMeasurable]
  have hcost : cost μ (c • (z+p)) ≤ cost ρ z := by
    rw [eq]
    apply integral_mono (integrable_of_compact_law μ hμ (cts _))
      (integrable_of_compact_law μ hμ (((cts z).comp hS).comp hT))
    intro a
    have v : c • (z-S (T a)) = c • (z+p) - a := by
      simp [S,T, smul_sub,smul_add,smul_smul,hc.ne']
      abel
    change L (c • (z+p) - a) ≤ L (z-S (T a))
    unfold L
    rw [←v,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    apply Real.log_le_log (by positivity)
    have hv := mul_le_mul_of_nonneg_right hc' (norm_nonneg (z-S (T a)))
    nlinarith [mul_self_le_mul_self (mul_nonneg hc.le (norm_nonneg _)) (show c*‖z-S (T a)‖ ≤ ‖z-S (T a)‖ by simpa using hv)]
  refine ⟨hf,hcost,?_⟩
  have low : BddBelow (Set.range (cost μ)) := by
    refine ⟨0,fun y ⟨a,ha⟩ => ha ▸ integral_nonneg fun x => ?_⟩
    apply Real.log_nonneg
    linarith [sq_nonneg ‖a-x‖]
  have hj : J μ ≤ cost μ (c • (z+p)) := csInf_le low (Set.mem_range_self _)
  exact (mul_le_mul_of_nonneg_left (hj.trans hcost) hb.le).trans hf

/-- Sequence form and uniform epsilon form of the limsup bound. -/
theorem stability_cost_upper (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (uniqueEq : EqUnique) (ballLaw : BallLaw) :
    (∀ μ : ℕ → Law, (∀ j, admissible (μ j) ∧ 0 < deficit (μ j) 1 ∧ deficit (μ j) 1 < 1) →
      Tendsto (fun j => gamma (μ j)) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, J (μ j) ≤ (2+ε)*gamma (μ j)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ ∀ μ : Law, admissible μ →
      0 < deficit μ 1 → deficit μ 1 ≤ h → J μ ≤ (2+ε)*gamma μ := by
  have seq (μ : ℕ → Law) (hm : ∀ j, admissible (μ j) ∧ 0 < deficit (μ j) 1 ∧ deficit (μ j) 1 < 1)
      (hg : Tendsto (fun j => gamma (μ j)) atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j in atTop, J (μ j) ≤ (2+ε)*gamma (μ j) := by
    choose K ν hK hsub hvol he hcap hle hrad hlo hβ using fun j =>
      stability_piece_bounds iso existsEq frost (μ j) (hm j).1 (hm j).2.1 (hm j).2.2
    let c (j : ℕ) := capRadius (K j)
    have hν (j : ℕ) : admissible (ν j) := ⟨(he j).1,(hK j).of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed (hK j).isClosed (he j).2.1)⟩
    have pot (j : ℕ) := frost (K j) (ν j) (hK j) (hcap j) (he j)
    have av (j : ℕ) := (stability_fubini (μ j) (ν j) (hm j).1 (hν j) (K j) (hK j) (hsub j)
      (he j).2.1 (c j) (hcap j) (pot j)).2.2.2.1
    have hpG (j : ℕ) : 0 < gamma (μ j) :=
      neg_pos.mpr (Real.log_neg (sub_pos.mpr (hm j).2.2) (by linarith [(hm j).2.1]))
    have normed (j : ℕ) := stability_normalize (μ j) (ν j) (hm j).1 (hν j) (c j) ((gamma (μ j))^2)
      (hcap j) (sq_pos_of_pos (hpG j)) (pot j) (av j)
    choose p hnear he0 hpot hav hdist using fun j => (normed j).2.2
    let ρ (j : ℕ) := shifted (p j) (scaled (c j) (ν j))
    have hadm (j : ℕ) : admissible (ρ j) :=
      admissible_map _ (admissible_map _ (hν j) (continuous_id.const_smul (c j)⁻¹)) (continuous_id.sub continuous_const)
    have hβ0 : Tendsto (fun j => beta (K j)) atTop (𝓝 0) :=
      squeeze_zero hlo hβ (by simpa using (hg.add (hg.pow 2)).div_const 3)
    have hn : Normalized ρ := by
      refine ⟨fun j => ⟨hadm j,hpot j⟩,squeeze_zero (fun j => ?_) (fun j => ?_) (by simpa using hβ0.add (hg.pow 2))⟩
      · change 0 ≤ g (shifted (p j) (scaled (c j) (ν j))) 0
        rw [he0]
        exact ((normed j).1 _).2
      · change g (shifted (p j) (scaled (c j) (ν j))) 0 ≤ _
        rw [he0]
        exact hnear j
    have hweak := (stability_sphere_limit uniqueEq ballLaw ρ hn).2.2
    let b := 1/(3*(2+ε/2))
    have bp : 0 < b := by dsimp [b]; positivity
    have blt : b < 1/6 := by dsimp [b]; apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr; linarith
    have trial := (stability_common_center ρ hn hweak).2 (1/6-b) (sub_pos.mpr blt)
    have close := hg.eventually_lt_const (show 0 < (ε/2)/(2+ε/2) by positivity)
    filter_upwards [trial,close] with j hj hj'
    obtain ⟨z,hz⟩ := hj
    have bound : b * J (μ j) ≤ beta (K j) := (stability_unscale_cost (μ j) (ρ j) (hm j).1 (hadm j) (hpot j)
      (c j) b (beta (K j)) (p j) z (hcap j) (hle j) bp (fun a => by simpa only [sub_sub_cancel] using hz a) (hav j)).2.2
    have H := bound.trans (hβ j)
    have ha : J (μ j) ≤ (2+ε/2)*(gamma (μ j)+gamma (μ j)^2) := by
      dsimp [b] at H
      have hD : 0 < 3*(2+ε/2) := by positivity
      have hh := (div_le_iff₀ hD).mp (show J (μ j)/(3*(2+ε/2)) ≤ _ by simpa [div_eq_inv_mul] using H)
      linarith
    have hj2 := (lt_div_iff₀ (by positivity : 0 < 2+ε/2)).mp hj'
    nlinarith [mul_le_mul_of_nonneg_right hj2.le (hpG j).le]
  refine ⟨seq,?_⟩
  intro ε hε
  by_contra! bad
  let d (j : ℕ) := 1/((j:ℝ)+1)/2
  have dp (j : ℕ) : 0 < d j := by dsimp [d]; positivity
  choose μ hm hpos hle failure using fun j => bad (d j) (dp j)
  have lt1 (j : ℕ) : deficit (μ j) 1 < 1 := by
    apply (hle j).trans_lt
    have h : 1/((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    dsimp [d]; linarith
  have hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0) :=
    squeeze_zero (fun j => (hpos j).le) hle (by simpa [d] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2)
  have hg : Tendsto (fun j => gamma (μ j)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => 1-deficit (μ j) 1) atTop (𝓝 1) := by simpa using hd.const_sub 1
    simpa [gamma] using (h.log one_ne_zero).neg
  obtain ⟨j,hj⟩ := (seq μ (fun j => ⟨hm j,hpos j,lt1 j⟩) hg ε hε).exists
  exact (failure j).not_ge hj

/-- Main theorem's uniform upper direction at every positive threshold. -/
theorem stability_uniform_upper (iso : CompactIso) (existsEq : EqExists) (frost : Frostman)
    (uniqueEq : EqUnique) (ballLaw : BallLaw) (R : ℝ) (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ ∀ μ : Law, admissible μ →
      0 < deficit μ R → deficit μ R ≤ h →
      1 - inradius (measureSolid μ R) / R ≤ (1+ε) * deficit μ R := by
  intro ε hε
  let t (d : ℝ) := (2+ε)*(-Real.log (1-d))
  let loss (d : ℝ) := 1 - Real.sqrt (2 - Real.exp (t d))
  have t0 : t 0 = 0 := by simp [t]
  have dlog := (((hasDerivAt_id (0:ℝ)).const_sub 1).log (by norm_num)).neg
  have dt : HasDerivAt t (2+ε) 0 := by
    simpa [t,Function.comp_def,Pi.mul_def] using dlog.const_mul (2+ε)
  have dl : HasDerivAt loss ((2+ε)/2) 0 := by
    have h := ((dt.exp.const_sub 2).sqrt (by norm_num [t0])).const_sub 1
    convert h using 1 <;> norm_num [loss,t0] <;> ring
  have hl := dl.tendsto_slope_zero_right
  have ratio : Tendsto (fun d => loss d/d) (𝓝[>] 0) (𝓝 ((2+ε)/2)) := by
    simpa only [zero_add,show loss 0=0 by norm_num [loss,t0],sub_zero,smul_eq_mul,div_eq_inv_mul] using hl
  have tsmall : ∀ᶠ d in 𝓝[>] (0:ℝ), t d < Real.log 2 :=
    ((dt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually_lt_const (by simpa [t0] using Real.log_pos (by norm_num : (1:ℝ)<2)))
  have good := (ratio.eventually_lt_const (by linarith : (2+ε)/2 < 1+ε)).and tsmall
  obtain ⟨h,hp,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp good
  obtain ⟨h',hp',hh'⟩ := (stability_cost_upper iso existsEq frost uniqueEq ballLaw).2 ε hε
  refine ⟨min h h',lt_min hp hp',?_⟩
  intro μ hμ hd hle
  let μ' := scaled R μ
  have adm : admissible μ' := admissible_map μ hμ (continuous_id.const_smul R⁻¹)
  have scale := scale_identities μ hμ R hR
  have equal : deficit μ' 1 = deficit μ R := scale.2.2
  have eqr : inradius (measureSolid μ' 1) = inradius (measureSolid μ R)/R := scale.2.1
  let d := deficit μ' 1
  have dp : 0 < d := by change 0 < deficit μ' 1; rwa [equal]
  have dsm : d ≤ min h h' := by change deficit μ' 1 ≤ _; rwa [equal]
  obtain ⟨hlo,ht⟩ := hh (show d ∈ Set.Ioc 0 h from ⟨dp,dsm.trans (min_le_left _ _)⟩)
  have hJ : J μ' ≤ t d := hh' μ' adm dp (dsm.trans (min_le_right _ _))
  obtain ⟨z,hz⟩ := (stability_center μ' adm).2.2.1
  have ball := (stability_center_ball μ' adm z hz).2.2.2 (hJ.trans_lt ht)
  let r := Real.sqrt (2-Real.exp (J μ'))
  have rp : 0 < r := Real.sqrt_pos.mpr (sub_pos.mpr ((Real.lt_log_iff_exp_lt (by norm_num)).mp (hJ.trans_lt ht)))
  have bounded := (measureSolid_regular μ' adm 1 zero_lt_one).2
  have radius : r ≤ inradius (measureSolid μ' 1) := by
    apply le_csSup (a := r) (s := insert 0 {l : ℝ | 0 < l ∧ ∃ w : X, Metric.ball w l ⊆ measureSolid μ' 1})
    · refine ⟨Metric.diam (measureSolid μ' 1),?_⟩
      rintro y (rfl | ⟨hy,w,hw⟩)
      · exact Metric.diam_nonneg
      · have dm := Metric.diam_mono hw bounded
        rw [Metric.diam_ball_eq w hy.le] at dm
        linarith
    · exact Or.inr ⟨rp,z,Metric.ball_subset_closedBall.trans ball⟩
  have comp : Real.sqrt (2-Real.exp (t d)) ≤ r :=
    Real.sqrt_le_sqrt (sub_le_sub_left (Real.exp_le_exp.mpr hJ) 2)
  rw [←eqr,←equal]
  change 1 - inradius (measureSolid μ' 1) ≤ (1+ε)*d
  have ub := (div_lt_iff₀ dp).mp hlo
  dsimp only [loss] at ub
  linarith

/-- The normalized sequence hypotheses have a concrete witness, the constant unit-sphere law. -/
theorem stability_normalized_example (frost : Frostman) (ballLaw : BallLaw) :
    Normalized (fun _ => sigma) := by
  have hball : IsCompact (Metric.closedBall (0:X) 1) := isCompact_closedBall _ _
  obtain ⟨hc, _, he⟩ := ballLaw
  have hadm : admissible sigma := ⟨he.1, hball.of_isClosed_subset
    Measure.isClosed_support (Measure.support_subset_of_isClosed Metric.isClosed_closedBall he.2.1)⟩
  have hp := frost _ sigma hball (by rw [hc]; norm_num) he
  have hs : ∀ᵐ x ∂sigma, x ∈ Metric.sphere (0:X) 1 := by
    unfold sigma
    apply Measure.ae_smul_measure
    exact (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).ae_map_iff.mpr
      (Eventually.of_forall fun x => x.property)
  have hzero : g sigma 0 = 0 := by
    unfold g
    apply integral_eq_zero_of_ae
    filter_upwards [hs] with x hx
    change Real.log (dist x 0) = 0
    rw [Metric.mem_sphere.mp hx, Real.log_one]
  refine ⟨fun _ => ⟨hadm, fun a => ?_⟩, ?_⟩
  · simpa [hc] using hp a
  · simpa [hzero] using (tendsto_const_nhds (x := (0:ℝ)) (f := (atTop : Filter ℕ)))

end ErdosVolume

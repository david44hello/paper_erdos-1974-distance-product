import ErdosVolume.Paper.Conditional

/-! Explicit representation of the logarithmic potential and two-mark reductions.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace ErdosVolume.Paper

def logPos {d : ℕ} (x a : Space d) : ℝ≥0∞ := ENNReal.ofReal (Real.log (dist x a))
def logNeg {d : ℕ} (x a : Space d) : ℝ≥0∞ :=
  if x = a then ⊤ else ENNReal.ofReal (-Real.log (dist x a))

/-- Includes every compact source, even with infinite negative log integral. -/
theorem general_log_bridge (μ : Measure (Space 3)) (hμ : admissible μ) (x : Space 3) :
    let p := ∫⁻ a, logPos x a ∂μ
    let n := ∫⁻ a, logNeg x a ∂μ
    p < ⊤ ∧ gMeasure μ x = if n = ⊤ then 0 else Real.exp (p.toReal - n.toReal) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let P := ∫⁻ a, logPos x a ∂μ
  let N := ∫⁻ a, logNeg x a ∂μ
  let cut (k : ℕ) (a : Space 3) := min (logNeg x a) (k : ℝ≥0∞)
  let T (k : ℕ) := ∫⁻ a, cut k a ∂μ
  have hPmeas : Measurable (logPos x) := by unfold logPos; fun_prop
  have hNmeas : Measurable (logNeg x) := by
    unfold logNeg
    apply Measurable.ite (by measurability) measurable_const
    fun_prop
  have hm (k : ℕ) : Measurable (cut k) := hNmeas.min measurable_const
  obtain ⟨B,hB⟩ := hμ.2.isBounded.exists_norm_le
  have hP : P < ⊤ := by
    have hb : P ≤ ∫⁻ _ : Space 3, ENNReal.ofReal (‖x‖+B+1) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [Measure.support_mem_ae (μ := μ)] with a ha
      apply ENNReal.ofReal_le_ofReal
      by_cases h : x = a
      · simp [h]; linarith [hB a ha,norm_nonneg a]
      · linarith [Real.log_le_sub_one_of_pos (dist_pos.mpr h),dist_le_norm_add_norm x a,hB a ha]
    exact hb.trans_lt (by simp)
  have hTk (k : ℕ) : T k < ⊤ := by
    refine (lintegral_mono (μ := μ) (fun a => min_le_right (logNeg x a) (k : ℝ≥0∞))).trans_lt ?_
    simp
  have fin (k : ℕ) (a : Space 3) : cut k a < ⊤ :=
    (min_le_right _ _).trans_lt (by finiteness : (k:ℝ≥0∞) < ⊤)
  have hsplit (k : ℕ) (a : Space 3) :
      Real.log (max (dist x a) (Real.exp (-(k:ℝ)))) = (logPos x a).toReal - (cut k a).toReal := by
    by_cases h : x = a
    · subst a
      simp [cut,logNeg,logPos, (Real.exp_pos _).le]
    · have hd := dist_pos.mpr h
      have hlog : Real.log (max (dist x a) (Real.exp (-(k:ℝ)))) = max (Real.log (dist x a)) (-(k:ℝ)) := by
        rcases le_total (dist x a) (Real.exp (-(k:ℝ))) with hl | hl
        · rw [max_eq_right hl, Real.log_exp, max_eq_right]
          simpa using Real.log_le_log hd hl
        · rw [max_eq_left hl, max_eq_left]
          simpa using Real.log_le_log (Real.exp_pos _) hl
      rw [hlog]
      simp only [logPos,cut,logNeg,if_neg h]
      rw [ENNReal.toReal_min (a := ENNReal.ofReal (-Real.log (dist x a))) (b := (k:ℝ≥0∞))
        ENNReal.ofReal_ne_top (by finiteness)]
      simp only [ENNReal.toReal_ofReal',ENNReal.toReal_natCast]
      grind [le_max_left,le_max_right, Nat.cast_nonneg (α := ℝ) k]
  have htr (k : ℕ) : (∫ a, Real.log (max (dist x a) (Real.exp (-(k:ℝ)))) ∂μ) = P.toReal - (T k).toReal := by
    simp_rw [hsplit k]
    rw [integral_sub (integrable_toReal_of_lintegral_ne_top hPmeas.aemeasurable hP.ne)
        (integrable_toReal_of_lintegral_ne_top (hm k).aemeasurable (hTk k).ne),
      integral_toReal hPmeas.aemeasurable (.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_toReal (hm k).aemeasurable (.of_forall (fin k))]
  have hlim : Tendsto T atTop (𝓝 N) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun k => (hm k).aemeasurable)
      (.of_forall fun a k j h => min_le_min_left _ (by exact_mod_cast h))
    exact .of_forall fun a => by simpa [cut] using
      (tendsto_const_nhds (x := logNeg x a)).min ENNReal.tendsto_nat_nhds_top
  refine ⟨hP, ?_⟩
  change gMeasure μ x = if N = ⊤ then _ else _
  unfold gMeasure
  simp_rw [htr]
  split
  · rename_i hinf
    have hat : Tendsto (fun k => (T k).toReal) atTop atTop := by
      apply ENNReal.tendsto_ofReal_nhds_top.mp
      simpa only [ENNReal.ofReal_toReal (hTk _).ne, hinf] using hlim
    exact iInf_eq_of_forall_le_of_tendsto (F := atTop) (fun _ => (Real.exp_pos _).le)
      (Real.tendsto_exp_atBot.comp (tendsto_atBot.2 (fun b =>
        (hat.eventually_ge_atTop (P.toReal - b)).mono fun k hk => by change P.toReal - (T k).toReal ≤ b; linarith)))
  · rename_i hn
    apply iInf_eq_of_forall_le_of_tendsto (F := atTop)
    · intro k
      exact Real.exp_le_exp.mpr (sub_le_sub_left (ENNReal.toReal_mono hn
        (lintegral_mono (fun a => min_le_left (logNeg x a) (k:ℝ≥0∞)))) _)
    · exact (tendsto_const_nhds.sub ((ENNReal.tendsto_toReal hn).comp hlim)).rexp

theorem pair_squared_mean (x : Space 3) (t : ℝ) :
    (dist x (t • axis)^2 + dist x ((-t) • axis)^2)/2 = ‖x‖^2+t^2 :=
  ErdosVolume.pair_squared_mean x t

theorem pair_outside_cylinder (x : Space 3) (t : ℝ) (ht : 0 < t) (ht' : t < 1/Real.sqrt 2)
    (hx : 1-t^2 < (transverse x)^2) : 1 < (dist x (t • axis)*dist x ((-t) • axis))^2 :=
  ErdosVolume.pair_outside_cylinder x t ht ht' hx

/-- The genuine set of ratios is nonempty for every h>0, witnessed in the equal-mass family. -/
theorem sup_nonempty (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    ∃ μ, admissible μ ∧ equalAtomic μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h := by
  obtain ⟨μ,hm,ha,hd,hδ,_⟩ := sharp_coefficient R hR 0 zero_lt_one h hh
  exact ⟨μ,hm,ha,hd,hδ⟩

/-- The real supremum is taken over a bounded-above set for all sufficiently small h. -/
theorem sup_bdd_given (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Stability.Frostman)
    (hU : Stability.EqUnique) (hL : Stability.BallLaw) (R : ℝ) (hR : 0 < R) :
    ∃ h > 0, BddAbove {v | ∃ μ, admissible μ ∧ 0 < deficit μ R ∧ deficit μ R ≤ h ∧ v = ratio μ R} := by
  obtain ⟨h,hh,hu⟩ := uniform_upper_given hO hN hB hE hF hU hL R hR 1 one_pos
  refine ⟨h,hh,1+1,?_⟩
  rintro v ⟨μ,hm,hd,hδ,rfl⟩
  exact (div_le_iff₀ hd).2 (hu μ hm hd hδ)

end ErdosVolume.Paper

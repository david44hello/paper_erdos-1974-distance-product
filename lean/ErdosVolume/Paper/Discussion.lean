import ErdosVolume.Paper.TrialCost

/-! The sharp infimum at a prescribed volume threshold in dimension three. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace ErdosVolume.Paper
open Stability

private theorem compact_piece_at_zero (iso : CompactIso) (ex : EqExists) (frost : Frostman)
    (μ : Law) (hm : admissible μ) (hzero : deficit μ 1 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ (K : Set X) (ν : Law), IsCompact K ∧ K ⊆ measureSolid μ 1 ∧ equilibrium K ν ∧
      0 < capRadius K ∧ capRadius K ≤ 1 ∧ 0 ≤ beta K ∧ beta K ≤ η/3 := by
  have hw := omega_positive 3
  have hvol : vol (measureSolid μ 1) = omega 3 := by
    have h : 1-vol (measureSolid μ 1)/omega 3 = 0 := by simpa [deficit] using hzero
    have := (div_eq_iff hw.ne').mp (show vol (measureSolid μ 1)/omega 3 = 1 by linarith)
    linarith
  obtain ⟨hms,hb⟩ := measureSolid_regular μ hm 1 one_pos
  have target : omega 3 * Real.exp (-η) < vol (measureSolid μ 1) := by
    rw [hvol]; simpa using mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hη)) hw
  have hpos := mul_pos hw (Real.exp_pos (-η))
  obtain ⟨K, hsub,hK,hgt⟩ := hms.exists_lt_isCompact_of_ne_top hb.measure_lt_top.ne
    ((ENNReal.ofReal_lt_iff_lt_toReal hpos.le hb.measure_lt_top.ne).mpr target)
  have hv : omega 3 * Real.exp (-η) < vol K :=
    (ENNReal.ofReal_lt_iff_lt_toReal hpos.le hK.measure_ne_top).mp hgt
  obtain ⟨_,hc,hc₁,hiso⟩ := stability_compact_comparison iso ex frost μ hm K hK (hpos.trans hv) hsub
  obtain ⟨ν, he⟩ := ex K hK hc
  refine ⟨K,ν,hK,hsub,he,hc,hc₁,neg_nonneg.mpr (Real.log_nonpos hc.le hc₁),?_⟩
  have hr := lt_of_mul_lt_mul_left (hv.trans_le hiso) hw.le
  have hh := Real.log_le_log (Real.exp_pos _) hr.le
  rw [Real.log_exp, Real.log_pow] at hh
  dsimp [beta]; norm_num at hh; linarith

private theorem admissible_pushforward (μ : Law) (hm : admissible μ) {T : X → X}
    (hT : Continuous T) : admissible (μ.map T) := by
  have hK := hm.2.image hT
  refine ⟨(Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hm.1,
    hK.of_isClosed_subset Measure.isClosed_support (Measure.support_subset_of_isClosed hK.isClosed ?_)⟩
  apply (ae_map_iff hT.aemeasurable (p := fun x => x ∈ T '' μ.support) hK.measurableSet).2
  filter_upwards [Measure.support_mem_ae (μ := μ)] with x hx
  exact Set.mem_image_of_mem T hx

private theorem zero_trial_data (iso : CompactIso) (ex : EqExists) (frost : Frostman)
    (μ : Law) (hm : admissible μ) (hz : deficit μ 1 = 0)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (ht : Tendsto η atTop (𝓝 0)) :
    ∃ (ρ : ℕ → Law) (c β : ℕ → ℝ) (p : ℕ → X), Normalized ρ ∧
      ∀ j, (0 < c j ∧ c j ≤ 1) ∧ β j ≤ η j / 3 ∧
        (∫ a, g (ρ j) a ∂(shifted (p j) (scaled (c j) μ))) ≤ β j := by
  choose K ν hK hsub he hcap hle hb0 hb using fun j => compact_piece_at_zero iso ex frost μ hm hz _ (hη j)
  let c (j : ℕ) := capRadius (K j)
  have hν (j : ℕ) : admissible (ν j) := ⟨(he j).1, (hK j).of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed (hK j).isClosed (he j).2.1)⟩
  have hpot j := frost (K j) (ν j) (hK j) (hcap j) (he j)
  have havg j := (stability_fubini μ (ν j) hm (hν j) (K j) (hK j)
    (hsub j) (he j).2.1 (c j) (hcap j) (hpot j)).2.2.2.1
  have hnorm j := stability_normalize μ (ν j) hm (hν j) (c j) (η j)
    (hcap j) (hη j) (hpot j) (havg j)
  choose p hnear hzero hpotential hmean _ using fun j => (hnorm j).2.2
  let ρ j := shifted (p j) (scaled (c j) (ν j))
  have hadm j : admissible (ρ j) := admissible_pushforward _
    (admissible_pushforward _ (hν j) (continuous_id.const_smul (c j)⁻¹)) (continuous_id.sub continuous_const)
  have hbLim : Tendsto (fun j => beta (K j)) atTop (𝓝 0) :=
    squeeze_zero hb0 hb (by simpa using ht.div_const 3)
  refine ⟨ρ, c, fun j => beta (K j), p, ⟨fun j => ⟨hadm j, hpotential j⟩, ?_⟩,
    fun j => ⟨⟨hcap j, hle j⟩, hb j, hmean j⟩⟩
  apply squeeze_zero (fun j => ?_) (fun j => ?_) (by simpa using hbLim.add ht)
  · change 0 ≤ g (shifted (p j) (scaled (c j) (ν j))) 0
    rw [hzero]
    exact ((hnorm j).1 _).2
  · change g (shifted (p j) (scaled (c j) (ν j))) 0 ≤ _
    rw [hzero]
    exact hnear j


/-- Equality of the unit-threshold volume forces even a general compactly supported law
to be concentrated at a single point. Its region is the unit ball. -/
theorem zero_deficit_rigidity (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : Law) (hm : admissible μ) (hz : deficit μ 1 = 0) :
    J μ = 0 ∧ ∃ z : X, μ = Measure.dirac z ∧ measureSolid μ 1 = closedBall z 1 := by
  let η (j : ℕ) := 1/((j : ℝ)+1)
  have hp (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have ht : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨ρ,c,β,p,hn,data⟩ := zero_trial_data (compact_iso_for_stability hO hN hB)
    (equilibrium_exists_for_stability hE) hF μ hm hz η hp ht
  have hw := (stability_sphere_limit hU hL ρ hn).2.2
  have hj : ∀ᶠ j in atTop, J μ ≤ 7*(η j/3) := by
    have trial := trial_cost_six (fun _ => μ) ρ (fun _ => hm) hn hw c β p
      (fun j => (data j).1) (fun j => (data j).2.2) 1 one_pos
    filter_upwards [trial] with j h
    obtain ⟨z,hz,hb⟩ := h
    linarith [hz.trans hb,(data j).2.1]
  have hu : J μ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds
    (show Tendsto (fun j => 7*(η j/3)) atTop (𝓝 0) by simpa using (ht.div_const 3).const_mul 7) hj
  obtain ⟨z,hzmin⟩ := (stability_center μ hm).2.2.1
  have hJ := le_antisymm hu (stability_center_ball μ hm z hzmin).1
  have hcont : Continuous (fun a : X => L (z-a)) := by
    unfold L
    exact (continuous_const.add (((continuous_const.sub continuous_id).norm).pow 2)).log
      (fun a => (by positivity : (0:ℝ)<1+‖z-a‖^2).ne')
  let : IsProbabilityMeasure μ := hm.1
  have hint := hcont.continuousOn.integrableOn_compact (μ := μ) hm.2
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem (s := μ.support) (μ := μ) Measure.support_mem_ae] at hint
  have hnn (a : X) : 0 ≤ L (z-a) := Real.log_nonneg (by linarith [sq_nonneg ‖z-a‖])
  have ha : (fun a : X => L (z-a)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hint).mp (hzmin.trans hJ)
  have hc : (id : X → X) =ᵐ[μ] (fun _ => z) := by
    filter_upwards [ha] with a h
    change Real.log (1+‖z-a‖^2)=0 at h
    have ha := congrArg Real.exp h
    rw [Real.exp_log (by positivity), Real.exp_zero] at ha
    have hn : ‖z-a‖ = 0 := by nlinarith [sq_nonneg ‖z-a‖]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  have hμ : μ = Measure.dirac z := by simpa [Measure.map_const] using Measure.map_congr hc
  refine ⟨hJ,z,hμ,?_⟩
  have hatom : atomic (fun _ : Fin 1 => z) (fun _ => (1:ℝ)) = Measure.dirac z := by simp [atomic]
  ext x
  have h := atomic_g (fun _ : Fin 1 => z) (fun _ => (1:ℝ)) (by constructor <;> simp) x
  rw [hatom] at h
  simp [measureSolid,hμ,h,G]

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

private abbrev Direction3 := sphere (0 : X) 1

private def radialVolume (t : ℝ) : ℝ :=
  ∫ θ : Direction3, (Real.sqrt (boundarySq t ((θ:X) 0)))^3 ∂sphereLaw

private theorem radialVolume_continuous : Continuous radialVolume := by
  let : IsProbabilityMeasure sphereLaw := ⟨by
    unfold sphereLaw; rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) (measure_ne_top _ _)⟩
  have hc : Continuous (fun v : ℝ × Direction3 => ((v.2 : X) 0)) :=
    ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).comp continuous_snd
  have hf : Continuous (fun v : ℝ × Direction3 => (Real.sqrt (boundarySq v.1 ((v.2:X) 0)))^3) := by
    unfold boundarySq
    fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ := sphereLaw)
    (f := fun t (θ : Direction3) => (Real.sqrt (boundarySq t ((θ:X) 0)))^3) hf isCompact_univ
  change Continuous (fun t => ∫ θ : Direction3, (Real.sqrt (boundarySq t ((θ:X) 0)))^3 ∂sphereLaw)
  simpa only [Measure.restrict_univ] using hi

/-- Every sufficiently small positive deficit occurs on the equal-pair family,
with half-separation as small as prescribed. -/
theorem pair_hits_volume_deficit (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∃ t ∈ Ioo (0:ℝ) δ, deficit (pairLaw t) 1 = ε := by
  let : IsProbabilityMeasure sphereLaw := ⟨by
    unfold sphereLaw; rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) (measure_ne_top _ _)⟩
  let f := fun t => 1-radialVolume t
  have fzero : f 0 = 0 := by simp [f,radialVolume,boundarySq]
  have small (t : ℝ) (hp : 0<t) (hs : t < 1/Real.sqrt 2) : deficit (pairLaw t) 1 = f t := by
    simpa [f,deficit,radialVolume] using congrArg (fun v : ℝ => 1-v) (pair_volume_fraction t hp hs).2
  obtain ⟨C,d,hC,hd,h⟩ := pair_asymptotics
  have shrink : ∀ᶠ t in 𝓝[>] (0:ℝ), C*t^2 < 1/4 := by
    have hl : Tendsto (fun t : ℝ => C*t^2) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (hid.pow 2).const_mul C
    exact hl.eventually_lt_const (by norm_num)
  have h₀ := (shrink.and ((Ioo_mem_nhdsGT (lt_min hδ (lt_min hd (by positivity : 0 < 1/Real.sqrt 2)))))).exists
  obtain ⟨t₀,hc,hp,ht⟩ := h₀
  obtain ⟨htδ,htd,hts⟩ := lt_min_iff.mp ht |>.imp_right lt_min_iff.mp
  have hfp : 0 < f t₀ := by
    rw [← small _ hp hts]
    have H := (abs_le.mp ((h t₀ hp htd).1)).1
    nlinarith [mul_lt_mul_of_pos_right hc (sq_pos_of_pos hp)]
  filter_upwards [Ioo_mem_nhdsGT hfp] with ε hε
  have hmem : ε ∈ Icc (f 0) (f t₀) := ⟨by rw [fzero]; exact hε.1.le,hε.2.le⟩
  have hfc : Continuous f := continuous_const.sub radialVolume_continuous
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hp.le hfc.continuousOn hmem
  have htp : 0 < t := lt_of_le_of_ne ht.1 fun he => by
    subst t; rw [fzero] at hft; exact hε.1.ne' hft.symm
  exact ⟨t,⟨htp,ht.2.trans_lt htδ⟩,(small t htp (ht.2.trans_lt hts)).trans hft⟩

/-- Inradii of all compactly supported source probabilities meeting the volume threshold. -/
def attainableRadii (ε : ℝ) : Set ℝ :=
  {r | ∃ μ : Law, admissible μ ∧ (1-ε)*omega 3 ≤ vol (measureSolid μ 1) ∧ r = inradius (measureSolid μ 1)}

private theorem volume_cut (μ : Law) (ε : ℝ) :
    (1-ε)*omega 3 ≤ vol (measureSolid μ 1) ↔ deficit μ 1 ≤ ε := by
  simp only [deficit,one_pow,mul_one]
  rw [← le_div_iff₀ (omega_positive 3)]
  constructor <;> intro h <;> linarith

private theorem radius_set_bounded (μ : Law) (hm : admissible μ) :
    BddAbove (insert 0 {r : ℝ | 0<r ∧ ∃ z, ball z r ⊆ measureSolid μ 1}) := by
  refine ⟨Metric.diam (measureSolid μ 1), ?_⟩
  rintro r (rfl | ⟨hr,z,hz⟩)
  · exact Metric.diam_nonneg
  · have hd := Metric.diam_mono hz (measureSolid_regular μ hm 1 one_pos).2
    rw [Metric.diam_ball_eq z hr.le] at hd
    linarith

/-- The infimum is over a nonempty, lower-bounded set. Its first-order loss at every
small allowed deficit is one times that deficit, including laws of exactly maximal volume. -/
theorem discussion_sharp_infimum (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) :
    (∀ ε : ℝ, 0 ≤ ε → (attainableRadii ε).Nonempty ∧ BddBelow (attainableRadii ε)) ∧
    Tendsto (fun ε => (1 - sInf (attainableRadii ε))/ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have good (ε : ℝ) (hp : 0 ≤ ε) : (attainableRadii ε).Nonempty ∧ BddBelow (attainableRadii ε) := by
    refine ⟨⟨_,pairLaw 0,pair_admissible 0,(volume_cut _ _).2 (by rw [coalescent_deficits.1]; exact hp),rfl⟩,0,?_⟩
    rintro r ⟨μ,hm,_,rfl⟩
    exact le_csSup (radius_set_bounded μ hm) (Or.inl rfl)
  refine ⟨good,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro a ha
    obtain ⟨δ,hδ,hclose⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (pair_ratio_limit.eventually_const_lt ha)
    filter_upwards [pair_hits_volume_deficit δ hδ,self_mem_nhdsWithin] with ε hex hp
    obtain ⟨t,ht,heq⟩ := hex
    have hrat := hclose ⟨ht.1,ht.2.le⟩
    change a < (1-inradius (measureSolid (pairLaw t) 1)/1)/deficit (pairLaw t) 1 at hrat
    rw [div_one,heq] at hrat
    have hmem : inradius (measureSolid (pairLaw t) 1) ∈ attainableRadii ε :=
      ⟨pairLaw t,pair_admissible t,(volume_cut _ _).2 heq.le,rfl⟩
    exact hrat.trans_le (div_le_div_of_nonneg_right (sub_le_sub_left (csInf_le (good ε (show (0:ℝ)<ε from hp).le).2 hmem) 1) (show (0:ℝ)<ε from hp).le)
  · intro b hb
    let k := (b+1)/2
    have hk : 1 < k := by dsimp [k]; linarith
    obtain ⟨e,he,hbound⟩ := uniform_upper_given hO hN hB hE hF hU hL 1 one_pos (k-1) (sub_pos.mpr hk)
    filter_upwards [Ioo_mem_nhdsGT he] with ε hε
    have hI : 1-k*ε ≤ sInf (attainableRadii ε) := by
      apply le_csInf (good ε hε.1.le).1
      rintro r ⟨μ,hm,hvol,rfl⟩
      have hd := (volume_cut μ ε).1 hvol
      have hv := (stability_measure_volume (compact_iso_for_stability hO hN hB)
        (equilibrium_exists_for_stability hE) hF μ hm).2
      have hnn : 0 ≤ deficit μ 1 := by
        simp only [deficit,one_pow,mul_one,sub_nonneg]
        exact (div_le_one (omega_positive 3)).2 hv
      by_cases hp : 0 < deficit μ 1
      · have h := hbound μ hm hp (hd.trans hε.2.le)
        simp only [div_one,add_sub_cancel] at h
        linarith [mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ k)]
      · have hzero : deficit μ 1 = 0 := by linarith
        obtain ⟨_,z,_,hball⟩ := zero_deficit_rigidity hO hN hB hE hF hU hL μ hm hzero
        have hr : (1:ℝ) ≤ inradius (measureSolid μ 1) := by
          apply le_csSup (radius_set_bounded μ hm)
          exact Or.inr ⟨one_pos,z,hball ▸ ball_subset_closedBall⟩
        linarith [mul_pos (by linarith : 0 < k) hε.1]
    apply (div_lt_iff₀ hε.1).mpr
    dsimp [k] at hI
    nlinarith [mul_pos (sub_pos.mpr hb) hε.1]

/-- The bounded cost estimate forces the minimum cost itself to tend to zero. -/
theorem minimum_cost_tends_zero (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hp : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    Tendsto (fun j => J (μ j)) atTop (𝓝 0) := by
  have hg : Tendsto (fun j => gamma (μ j)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => 1-deficit (μ j) 1) atTop (𝓝 1) := by simpa using hd.const_sub 1
    simpa [gamma] using (h.log one_ne_zero).neg
  obtain ⟨h,hh,hu⟩ := (stability_cost_upper (compact_iso_for_stability hO hN hB)
    (equilibrium_exists_for_stability hE) hF hU hL).2 1 one_pos
  have low (j : ℕ) : 0 ≤ J (μ j) := by
    obtain ⟨z,hz⟩ := (stability_center _ (hm j)).2.2.1
    exact (stability_center_ball _ (hm j) z hz).1
  exact squeeze_zero' (Eventually.of_forall low) ((hd.eventually_lt_const hh).mono fun j hj =>
    hu _ (hm j) (hp j) hj.le) (by simpa using hg.const_mul (2+1:ℝ))

/-- A positive cutoff always admits equal pairs, and the cutoff supremum of the
loss ratio is at least one. The set has witnesses and an actual finite upper bound. -/
theorem cutoff_sup_at_least_one (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (h : ℝ) (hh : 0 < h) (P : Law → Prop)
    (hP : ∀ μ : Law, equalAtomic μ → P μ) :
    let ratios := {v : ℝ | ∃ μ : Law, admissible μ ∧ P μ ∧
      0 < deficit μ 1 ∧ deficit μ 1 ≤ h ∧ v = ratio μ 1}
    ratios.Nonempty ∧ BddAbove ratios ∧ 1 ≤ worstRatio P 1 h := by
  obtain ⟨δ,hδ,hu⟩ := uniform_upper_given hO hN hB hE hF hU hL 1 one_pos 1 one_pos
  let S := {v : ℝ | ∃ μ : Law, admissible μ ∧ P μ ∧ 0 < deficit μ 1 ∧ deficit μ 1 ≤ h ∧ v = ratio μ 1}
  have bound : BddAbove S := by
    refine ⟨max 2 (1/δ), ?_⟩
    rintro v ⟨μ,hm,_,hd,_,rfl⟩
    by_cases small : deficit μ 1 ≤ δ
    · apply le_trans _ (le_max_left _ _)
      apply (div_le_iff₀ hd).2
      have h := hu μ hm hd small
      norm_num at h ⊢
      linarith
    · have hn : (0:ℝ) ≤ inradius (measureSolid μ 1) := le_csSup (radius_set_bounded μ hm) (Or.inl rfl)
      apply le_trans _ (le_max_right _ _)
      change (1-inradius (measureSolid μ 1)/1)/deficit μ 1 ≤ 1/δ
      rw [div_one,div_le_div_iff₀ hd hδ]
      nlinarith [mul_nonneg hn hδ.le]
  obtain ⟨μ,hm,he,hd,hb⟩ := sup_nonempty 1 h one_pos hh
  refine ⟨⟨_,μ,hm,hP μ he,hd,hb,rfl⟩,bound,?_⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  obtain ⟨ν,hν,he,hd,hb,hl⟩ := sharp_coefficient 1 one_pos c hc h hh
  exact ((lt_div_iff₀ hd).mpr hl).le.trans (le_csSup bound (show ratio ν 1 ∈ S from
    ⟨ν,hν,hP ν he,hd,hb,rfl⟩))

end ErdosVolume.Paper

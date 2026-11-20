import ErdosVolume.Paper.TrialCost

/-! Sequence bounds in the final part of the three-dimensional inradius argument.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace ErdosVolume.Paper
open Stability

private theorem inradius_le_one_of_deficit_pos (μ : Law) (hm : admissible μ)
    (hpos : 0 < deficit μ 1) : inradius (measureSolid μ 1) ≤ 1 := by
  have hv : vol (measureSolid μ 1) < omega 3 := by
    have h : vol (measureSolid μ 1) / omega 3 < 1 := by
      simpa [deficit] using (sub_pos.mp hpos)
    simpa using (div_lt_iff₀ (omega_positive 3)).mp h
  unfold inradius
  refine csSup_le ?_ ?_
  · exact ⟨0, Or.inl rfl⟩
  intro r hr
  rcases hr with hzero | ⟨_, z, hball⟩
  · simp [hzero]
  · by_contra! hlt
    have hsub : closedBall z 1 ⊆ measureSolid μ 1 := (closedBall_subset_ball hlt).trans hball
    have hle : vol (closedBall z 1) ≤ vol (measureSolid μ 1) :=
      ENNReal.toReal_mono (measureSolid_regular μ hm 1 one_pos).2.measure_lt_top.ne (measure_mono hsub)
    rw [closedBall_volume z zero_le_one, one_pow, mul_one] at hle
    exact hv.not_ge hle

/-- The fractional inradius loss along any sequence of positive deficits tending to zero. -/
theorem sequence_inradius_loss_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    atTop.IsBoundedUnder (· ≤ ·) (fun j => (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1) ∧
    Filter.limsup (fun j => (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1) atTop ≤ 1 := by
  have hlow : ∀ᶠ j in atTop, 0 ≤ (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1 :=
    Eventually.of_forall fun j => div_nonneg (sub_nonneg.mpr
      (inradius_le_one_of_deficit_pos _ (hm j) (hpos j))) (hpos j).le
  have upper (y : ℝ) (hy : 1 < y) :
      ∀ᶠ j in atTop, (1 - inradius (measureSolid (μ j) 1)) / deficit (μ j) 1 ≤ y := by
    obtain ⟨h, hh, hbound⟩ := uniform_upper_given hO hN hB hE hF hU hL 1 one_pos (y-1) (sub_pos.mpr hy)
    filter_upwards [hd.eventually_lt_const hh] with j hj
    apply (div_le_iff₀ (hpos j)).mpr
    simpa only [div_one, add_sub_cancel] using hbound (μ j) (hm j) (hpos j) hj.le
  refine ⟨isBoundedUnder_of_eventually_le (upper 2 (by norm_num)), ?_⟩
  exact le_of_forall_gt_imp_ge_of_dense fun y hy =>
    limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hlow) (upper y hy)

private theorem admissible_pushforward (μ : Law) (hm : admissible μ) {T : X → X}
    (hT : Continuous T) : admissible (μ.map T) := by
  have hK := hm.2.image hT
  refine ⟨(Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hm.1,
    hK.of_isClosed_subset Measure.isClosed_support (Measure.support_subset_of_isClosed hK.isClosed ?_)⟩
  apply (ae_map_iff hT.aemeasurable (p := fun x => x ∈ T '' μ.support) hK.measurableSet).2
  filter_upwards [Measure.support_mem_ae (μ := μ)] with x hx
  exact Set.mem_image_of_mem T hx

/-- Choose the compact pieces, scale their equilibrium laws and translate to the common origin. -/
private theorem normalized_trial_data (iso : CompactIso) (ex : EqExists) (frost : Frostman)
    (μ : ℕ → Law) (hm : ∀ j, admissible (μ j)) (hp : ∀ j, 0 < deficit (μ j) 1)
    (hlt : ∀ j, deficit (μ j) 1 < 1) (hg : Tendsto (fun j => gamma (μ j)) atTop (𝓝 0)) :
    ∃ (ρ : ℕ → Law) (c β : ℕ → ℝ) (p : ℕ → X), Normalized ρ ∧
      ∀ j, (0 < c j ∧ c j ≤ 1) ∧ β j ≤ (gamma (μ j) + gamma (μ j)^2)/3 ∧
        (∫ a, g (ρ j) a ∂(shifted (p j) (scaled (c j) (μ j)))) ≤ β j := by
  choose K ν hK hsub _ he hcap hle _ hb0 hb using fun j =>
    stability_piece_bounds iso ex frost (μ j) (hm j) (hp j) (hlt j)
  let c (j : ℕ) := capRadius (K j)
  have hν (j : ℕ) : admissible (ν j) := ⟨(he j).1, (hK j).of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed (hK j).isClosed (he j).2.1)⟩
  have hpot j := frost (K j) (ν j) (hK j) (hcap j) (he j)
  have havg j := (stability_fubini (μ j) (ν j) (hm j) (hν j) (K j) (hK j)
    (hsub j) (he j).2.1 (c j) (hcap j) (hpot j)).2.2.2.1
  have hgpos j : 0 < gamma (μ j) :=
    neg_pos.mpr (Real.log_neg (sub_pos.mpr (hlt j)) (by linarith [hp j]))
  have hnorm j := stability_normalize (μ j) (ν j) (hm j) (hν j) (c j) ((gamma (μ j))^2)
    (hcap j) (sq_pos_of_pos (hgpos j)) (hpot j) (havg j)
  choose p hnear hzero hpotential hmean _ using fun j => (hnorm j).2.2
  let ρ j := shifted (p j) (scaled (c j) (ν j))
  have hadm j : admissible (ρ j) := admissible_pushforward _
    (admissible_pushforward _ (hν j) (continuous_id.const_smul (c j)⁻¹)) (continuous_id.sub continuous_const)
  have hbLim : Tendsto (fun j => beta (K j)) atTop (𝓝 0) :=
    squeeze_zero hb0 hb (by simpa using (hg.add (hg.pow 2)).div_const 3)
  refine ⟨ρ, c, fun j => beta (K j), p, ⟨fun j => ⟨hadm j, hpotential j⟩, ?_⟩,
    fun j => ⟨⟨hcap j, hle j⟩, hb j, hmean j⟩⟩
  apply squeeze_zero (fun j => ?_) (fun j => ?_) (by simpa using hbLim.add (hg.pow 2))
  · change 0 ≤ g (shifted (p j) (scaled (c j) (ν j))) 0
    rw [hzero]
    exact ((hnorm j).1 _).2
  · change g (shifted (p j) (scaled (c j) (ν j))) 0 ≤ _
    rw [hzero]
    exact hnear j

/-- Fix the annulus width before taking the upper limit of the original costs. -/
theorem fixed_delta_cost_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      0 < 1/6 - C*δ ∧
      atTop.IsBoundedUnder (· ≤ ·) (fun j => J (μ j) / gamma (μ j)) ∧
      Filter.limsup (fun j => J (μ j) / gamma (μ j)) atTop ≤ (1/3) / (1/6 - C*δ) := by
  obtain ⟨N, hNsmall⟩ := eventually_atTop.1 (hd.eventually_lt_const zero_lt_one)
  let μ' j := μ (max j N)
  have heq : μ' =ᶠ[atTop] μ := (eventually_ge_atTop N).mono fun j hj => by simp [μ', max_eq_left hj]
  have hd' : Tendsto (fun j => deficit (μ' j) 1) atTop (𝓝 0) :=
    hd.congr' (heq.symm.mono fun _ h => congrArg (fun m => deficit m 1) h)
  have hlt j : deficit (μ' j) 1 < 1 := hNsmall _ (le_max_right j N)
  have hg : Tendsto (fun j => gamma (μ' j)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => 1 - deficit (μ' j) 1) atTop (𝓝 1) := by simpa using hd'.const_sub 1
    simpa [gamma] using (h.log one_ne_zero).neg
  have hgpos j : 0 < gamma (μ' j) :=
    neg_pos.mpr (Real.log_neg (sub_pos.mpr (hlt j)) (by linarith [hpos (max j N)]))
  obtain ⟨ρ, c, β, p, hn, hdata⟩ := normalized_trial_data (compact_iso_for_stability hO hN hB)
    (equilibrium_exists_for_stability hE) hF μ' (fun j => hm (max j N)) (fun j => hpos (max j N)) hlt hg
  obtain ⟨C, δ₁, hC, hδ₁, hfixed⟩ := (stability_common_center ρ hn (stability_sphere_limit hU hL ρ hn).2.2).1
  refine ⟨C, min δ₁ ((1/6)/C), hC, lt_min hδ₁ (div_pos (by norm_num) hC), ?_⟩
  intro δ hδ
  have hA : 0 < 1/6 - C*δ := by
    have h := (lt_div_iff₀ hC).mp (hδ.2.trans_le (min_le_right _ _))
    linarith
  obtain ⟨z, _, _, htrial⟩ := hfixed δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  refine ⟨hA, (sequence_cost_limsup hO hN hB hE hF hU hL μ hm hpos hd).2.1, ?_⟩
  have heqr : (fun j => J (μ' j) / gamma (μ' j)) =ᶠ[atTop] (fun j => J (μ j) / gamma (μ j)) :=
    heq.mono fun _ h => congrArg (fun m => J m / gamma m) h
  rw [← limsup_congr heqr]
  have hlow : ∀ᶠ j in atTop, 0 ≤ J (μ' j) / gamma (μ' j) := Eventually.of_forall fun j => by
    obtain ⟨z₀, hz₀⟩ := (stability_center (μ' j) (hm _)).2.2.1
    exact div_nonneg (stability_center_ball _ (hm _) z₀ hz₀).1 (hgpos j).le
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  have hypos : 0 < y := lt_trans (by positivity) hy
  have hsplit : (1/3) / y < 1/6 - C*δ := by
    apply (div_lt_iff₀ hypos).mpr
    linarith [(div_lt_iff₀ hA).mp hy]
  obtain ⟨k, hk₁, hk₂⟩ := exists_between hsplit
  have hk : 0 < k := lt_trans (by positivity) hk₁
  have hyk : (1/3) / k < y := by
    apply (div_lt_iff₀ hk).mpr
    linarith [(div_lt_iff₀ hypos).mp hk₁]
  have hlim : Tendsto (fun j => ((1 + gamma (μ' j))/3)/k) atTop (𝓝 ((1/3)/k)) := by
    simpa using ((hg.const_add 1).div_const 3).div_const k
  apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hlow)
  filter_upwards [htrial (1/6-C*δ-k) (sub_pos.mpr hk₂), hlim.eventually_lt_const hyk] with j hj hclose
  have hpoint : ∀ a, k * L (a-z j) ≤ g (ρ j) a := fun a => by
    simpa only [sub_sub_cancel] using hj a
  obtain ⟨_, hJ, hI, hav⟩ := original_trial_cost_chain (μ' j) (ρ j) (hm _) (hn.1 j).1
    (hn.1 j).2 (c j) k (β j) (p j) (z j) (hdata j).1.1 (hdata j).1.2 hk hpoint (hdata j).2.2
  have hbound := (hJ.trans (hI.trans hav)).trans (div_le_div_of_nonneg_right (hdata j).2.1 hk.le)
  apply le_trans _ hclose.le
  apply (div_le_iff₀ (hgpos j)).mpr
  calc J (μ' j) ≤ ((gamma (μ' j) + gamma (μ' j)^2)/3)/k := hbound
       _ = ((1 + gamma (μ' j))/3)/k * gamma (μ' j) := by ring

end ErdosVolume.Paper

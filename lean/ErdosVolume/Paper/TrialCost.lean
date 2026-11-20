import ErdosVolume.Paper.Illustrations

/-! Explicit intermediate estimates in the final short paper. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace ErdosVolume.Paper
open Stability

/-- The ratio formulation for every positive-deficit sequence, including arbitrary initial terms. -/
theorem sequence_cost_limsup (hO : OpenIsoFact 3) (hN : CapacityNormalization 3)
    (hB : BallCapacityFact 3) (hE : EquilibriumExistence 3) (hF : Frostman)
    (hU : EqUnique) (hL : BallLaw) (μ : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hpos : ∀ j, 0 < deficit (μ j) 1) (hd : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝 0)) :
    Tendsto (fun j => gamma (μ j) / deficit (μ j) 1) atTop (𝓝 1) ∧
    atTop.IsBoundedUnder (· ≤ ·) (fun j => J (μ j) / gamma (μ j)) ∧
    Filter.limsup (fun j => J (μ j) / gamma (μ j)) atTop ≤ 2 := by
  have hright : Tendsto (fun j => deficit (μ j) 1) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd, Eventually.of_forall hpos⟩
  refine ⟨stability_scalar_limits.2.comp hright, ?_⟩
  have hg : ∀ᶠ j in atTop, 0 < gamma (μ j) := by
    filter_upwards [hd.eventually_lt_const zero_lt_one] with j hj
    exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hj) (by linarith [hpos j]))
  have hlow : ∀ᶠ j in atTop, 0 ≤ J (μ j) / gamma (μ j) := by
    filter_upwards [hg] with j hj
    obtain ⟨z,hz⟩ := (stability_center (μ j) (hm j)).2.2.1
    exact div_nonneg (stability_center_ball (μ j) (hm j) z hz).1 hj.le
  have upper (y : ℝ) (hy : 2 < y) : ∀ᶠ j in atTop, J (μ j) / gamma (μ j) ≤ y := by
    obtain ⟨h,hh,hupper⟩ := (stability_cost_upper (compact_iso_for_stability hO hN hB)
      (equilibrium_exists_for_stability hE) hF hU hL).2 (y-2) (by linarith)
    filter_upwards [hd.eventually_lt_const hh,hg] with j hj hγ
    apply (div_le_iff₀ hγ).mpr
    simpa only [add_sub_cancel] using hupper (μ j) (hm j) (hpos j) hj.le
  refine ⟨isBoundedUnder_of_eventually_le (upper 3 (by norm_num)), ?_⟩
  exact le_of_forall_gt_imp_ge_of_dense fun y hy =>
    limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hlow) (upper y hy)

/-- The pointwise estimate for the logarithm removed by a lower cutoff. -/
theorem discarded_log_chain : ∃ C > (0:ℝ), ∀ {s η : ℝ}, 0 < s → s < η → η < 1 →
    0 ≤ Real.log η - Real.log s ∧ Real.log η - Real.log s ≤ |Real.log s| ∧
    |Real.log s| ≤ C / Real.sqrt s ∧ C / Real.sqrt s ≤ C * Real.sqrt η / s := by
  obtain ⟨C,hC,hl⟩ := stability_truncation.1
  refine ⟨C,hC,?_⟩
  intro s η hs hsη hη
  have hs1 := hsη.trans hη
  have hroot := Real.sqrt_pos.mpr hs
  refine ⟨sub_nonneg.mpr (Real.log_le_log hs hsη.le), ?_, hl s ⟨hs,hs1⟩, ?_⟩
  · rw [abs_of_nonpos (Real.log_nonpos hs.le hs1.le)]
    linarith [Real.log_nonpos (hs.trans hsη).le hη.le]
  · apply (div_le_div_iff₀ hroot hs).2
    have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsη.le) hroot.le
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr h), Real.mul_self_sqrt hs.le,
      congrArg (fun t : ℝ => C*t) (Real.mul_self_sqrt hs.le)]

/-- Both comparisons for an arbitrary positive-volume compact piece of the source solid. -/
theorem compact_piece_unit_bound (iso : CompactIso) (ex : EqExists) (frost : Frostman)
    (μ : Law) (hm : admissible μ) (K : Set X) (hK : IsCompact K) (hv : 0 < vol K)
    (hs : K ⊆ measureSolid μ 1) :
    capRadius K ≤ 1 ∧ vol K ≤ omega 3 ∧ volume (measureSolid μ 1) < ⊤ ∧
      vol (measureSolid μ 1) ≤ omega 3 := by
  obtain ⟨_,hc,hc1,hvol⟩ := stability_compact_comparison iso ex frost μ hm K hK hv hs
  have hpow : capRadius K ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hc.le hc1 3
  refine ⟨hc1,hvol.trans ?_,stability_measure_volume iso ex frost μ hm⟩
  simpa using mul_le_mul_of_nonneg_left hpow (omega_positive 3).le

/-- The same minimizing centers satisfy the complete interior quadratic-to-logarithmic chain. -/
theorem trial_inner_chain (ν : ℕ → Law) (hn : Normalized ν) (hw : weak ν sigma)
    (δ : ℝ) (hδ : δ ∈ Ioo (0:ℝ) (1/8)) (b : ℕ → ℝ)
    (hb : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ b j)
    (hh : ∀ᶠ j in atTop, ∀ a ∈ closedBall (0:X) δ, ContDiffAt ℝ 2 (F (ν j) δ) a ∧
      ∀ v : X, 2*b j*‖v‖^2 ≤ hess (F (ν j) δ) a v v) :
    ∃ z : ℕ → X, (∀ j, z j ∈ closedBall (0:X) δ ∧
      ∀ a ∈ closedBall (0:X) δ, F (ν j) δ (z j) ≤ F (ν j) δ a) ∧
      Tendsto z atTop (𝓝 0) ∧ ∀ᶠ j in atTop, ∀ a : X, ‖a‖ ≤ δ →
        b j * Real.log (1+‖a-z j‖^2) ≤ b j * ‖a-z j‖^2 ∧ b j * ‖a-z j‖^2 ≤ g (ν j) a := by
  obtain ⟨z,hmin,hquad,ht⟩ := stability_trial_min ν hn δ hδ b hb hh
  refine ⟨z,fun j => ⟨(hmin j).1, fun a ha => ((hmin j).2 a ha).1⟩,ht,?_⟩
  obtain ⟨c,hc,hb'⟩ := hb
  filter_upwards [hb',hquad] with j hj hq
  intro a ha
  have hb0 := hc.le.trans hj
  have hF := ((stability_annular_curvature ν hn hw).1 j δ (z j)).1
  exact ⟨mul_le_mul_of_nonneg_left (stability_shift_loss.1 _) hb0,by
    linarith [(hq.2 a (by simpa using ha))]⟩

/-- The three comparisons with the actual rescaled trial integral, before division by gamma. -/
theorem original_trial_cost_chain (μ ν : Law) (hμ : admissible μ) (hν : admissible ν)
    (hp : ∀ a, potential ν a ≤ 1) (c k β : ℝ) (p z : X) (hc : 0 < c) (hc1 : c ≤ 1)
    (hk : 0 < k) (hz : ∀ a : X, k*L (a-z) ≤ g ν a)
    (havg : (∫ a, g ν a ∂(shifted p (scaled c μ))) ≤ β) :
    let ρ := shifted p (scaled c μ)
    let I := ∫ a, Real.log (1+c^2*‖a-z‖^2) ∂ρ
    cost μ (c • (z+p)) = I ∧ J μ ≤ I ∧ I ≤ k⁻¹*(∫ a, g ν a ∂ρ) ∧ k⁻¹*(∫ a, g ν a ∂ρ) ≤ β/k := by
  let ρ := shifted p (scaled c μ)
  let T (a : X) := c⁻¹ • a
  let S (a : X) := a-p
  let f (a : X) := Real.log (1+c^2*‖a-z‖^2)
  have cf : Continuous f := (continuous_const.add
    (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))).log
      (fun a => (show 0 < 1+c^2*‖a-z‖^2 by positivity).ne')
  have hS : Continuous S := continuous_id.sub continuous_const
  have hT : Continuous T := continuous_id.const_smul (c⁻¹)
  have heq : (∫ a, f a ∂ρ) = cost μ (c • (z+p)) := by
    change (∫ a, f a ∂((μ.map T).map S)) = _
    rw [integral_map hS.aemeasurable cf.aestronglyMeasurable,
      integral_map (f := fun a => f (S a)) hT.aemeasurable (cf.comp hS).aestronglyMeasurable]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    have hid : c • (z - S (T a)) = c • (z+p) - a := by
      simp [S,T,smul_sub,smul_add,smul_smul,hc.ne']
      abel
    change Real.log (1+c^2*‖S (T a)-z‖^2) = L (c • (z+p) - a)
    rw [L,← hid,norm_smul,Real.norm_eq_abs,abs_of_pos hc,mul_pow,norm_sub_rev]
  have low : BddBelow (range (cost μ)) := ⟨0,by
    rintro _ ⟨a,rfl⟩
    exact integral_nonneg fun x => Real.log_nonneg (by linarith [sq_nonneg ‖a-x‖])⟩
  have ht := stability_unscale_cost μ ν hμ hν hp c k (∫ a, g ν a ∂ρ) p z hc hc1 hk hz le_rfl
  refine ⟨heq.symm,?_⟩
  change J μ ≤ (∫ a, f a ∂ρ) ∧ _ ∧ _
  rw [heq]
  exact ⟨csInf_le low (mem_range_self _),ht.2.1.trans (by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hk).2 (by simpa [mul_comm] using ht.1)),by
    rw [← div_eq_inv_mul]; exact div_le_div_of_nonneg_right havg hk.le⟩

/-- Given the normalized sequence and mean bound from the compact-piece argument,
each positive tolerance yields actual trial centers with coefficient at most six plus the tolerance. -/
theorem trial_cost_six (μ ν : ℕ → Law) (hm : ∀ j, admissible (μ j))
    (hn : Normalized ν) (hw : weak ν sigma) (c β : ℕ → ℝ) (p : ℕ → X)
    (hc : ∀ j, 0 < c j ∧ c j ≤ 1)
    (havg : ∀ j, (∫ a, g (ν j) a ∂(shifted (p j) (scaled (c j) (μ j)))) ≤ β j) :
    ∀ ε > (0:ℝ), ∀ᶠ j in atTop, ∃ z : X,
      J (μ j) ≤ cost (μ j) z ∧ cost (μ j) z ≤ (6+ε)*β j := by
  intro ε hε
  let k := 1/(6+ε)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk6 : k < 1/6 := by dsimp [k]; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  filter_upwards [(stability_common_center ν hn hw).2 (1/6-k) (sub_pos.mpr hk6)] with j hj
  obtain ⟨z,hz⟩ := hj
  obtain ⟨heq,hJ,hI,hlast⟩ := original_trial_cost_chain (μ j) (ν j) (hm j) (hn.1 j).1 (hn.1 j).2
    (c j) k (β j) (p j) z (hc j).1 (hc j).2 hk (fun a => by simpa only [sub_sub_cancel] using hz a) (havg j)
  refine ⟨c j • (z+p j),heq.symm ▸ hJ,?_⟩
  rw [heq]
  simpa [k,div_eq_mul_inv,mul_comm] using hI.trans hlast

end ErdosVolume.Paper

module

public import ErdosVolume.Defs

@[expose] public section

/-! The capacity route for the distance-product bound.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.ennrealScalarTower
attribute [local instance 2000] ErdosVolume.CoordinateFacts.twoAtLeastTwo
attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteThree
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelThree

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal BigOperators Topology ContDiff
namespace ErdosVolume

/-- The absolute variational capacity, using the Euclidean gradient norm. -/
def dirichletCap {d : ℕ} (K : Set (Space d)) : ℝ≥0∞ :=
  sInf {q | ∃ f : Space d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ x ∈ K, 1 ≤ f x) ∧
    q = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)}

/-- The absolute-capacity clause of De Philippis–Marini–Mukoseeva,
§1.1, display (1.3) in the authors' preprint. -/
def OpenIsoFact (d : ℕ) : Prop :=
  ∀ (U : Set (Space d)) (r : ℝ), IsOpen U → Bornology.IsBounded U → 0 < r →
    volume U = volume (Metric.ball (0 : Space d) r) →
    dirichletCap (Metric.ball (0 : Space d) r) ≤ dirichletCap U

/-- Variational capacity expressed through the probability-energy radius on compact sets. -/
def CapacityNormalization (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K →
    dirichletCap K = ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 2) * omega d *
      capRadius K ^ (d - 2))

/-- Classical equilibrium existence, atomlessness and logarithmic integrability.
The finiteness assumptions exclude polar sets and the zero-energy case. -/
def EquilibriumExistence (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → 0 < leastEnergy K → leastEnergy K < ⊤ →
    ∃ ν : Measure (Space d), equilibrium K ν ∧
      (∀ a, ν ({a} : Set (Space d)) = 0) ∧
      ∀ a, Integrable (fun x => Real.log (dist x a)) ν

/-- The closed ball's Newtonian capacity radius (Clark–Laugesen, Appendix A). -/
def BallCapacityFact (d : ℕ) : Prop :=
  ∀ (z : Space d) (r : ℝ), 0 < r → capRadius (Metric.closedBall z r) = r

/-- Clark–Laugesen, Theorem 1.1(ii),(iv) in arXiv:2403.12867, p. 2;
the d ≥ 3 part is used at an arbitrary translated center. -/
def EquilibriumMomentFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    Real.log (capRadius K) ≤ ∫ x, Real.log (dist x a) ∂ν

def EquilibriumSphereFact (d : ℕ) : Prop :=
  ∀ (K : Set (Space d)) (ν : Measure (Space d)) (a : Space d),
    IsCompact K → 0 < capRadius K → equilibrium K ν →
    (∫ x, Real.log (dist x a) ∂ν) = Real.log (capRadius K) →
    Metric.sphere a (capRadius K) ⊆ K

/-- The compact solid contains a positive-radius ball. -/
theorem solid_compact_interior {d n : ℕ} (hn : 0 < n) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    IsCompact (solid a w R) ∧ ∃ z r, 0 < r ∧ Metric.closedBall z r ⊆ solid a w R := by
  have hcont : Continuous (G a w) := continuous_finsetProd Finset.univ fun i _ =>
    (continuous_id.dist (continuous_const (y := a i))).rpow_const (fun _ => Or.inr (hw.1 i).le)
  have hsub : solid a w R ⊆ ⋃ i, Metric.closedBall (a i) (R+1) := by
    intro x hx
    by_contra h
    have hdist (i : Fin n) : R+1 ≤ dist x (a i) :=
      le_of_lt (lt_of_not_ge (fun hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩)))
    have hlow : R+1 ≤ G a w x := calc
      R+1 = ∏ i, (R+1)^w i := by
        rw [← Real.rpow_sum_of_pos (by linarith : 0 < R+1), hw.2, Real.rpow_one]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (by linarith) _)
        (fun i _ => Real.rpow_le_rpow (by linarith) (hdist i) (hw.1 i).le)
    change G a w x ≤ R at hx
    linarith
  refine ⟨(isCompact_iUnion (fun i => isCompact_closedBall (a i) (R+1))).of_isClosed_subset
    (isClosed_le hcont continuous_const) hsub, ?_⟩
  let i : Fin n := ⟨0, hn⟩
  have hz : G a w (a i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Real.zero_rpow (hw.1 i).ne']
  have hnb : solid a w R ∈ 𝓝 (a i) :=
    (hcont.continuousAt.eventually (Iio_mem_nhds (hz ▸ hR))).mono (fun _ h => h.le)
  obtain ⟨r, hr, hinc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnb
  exact ⟨a i, r, hr, hinc⟩

private theorem leastEnergy_antitone {d : ℕ} {K L : Set (Space d)} (h : K ⊆ L) :
    leastEnergy L ≤ leastEnergy K := by
  apply sInf_le_sInf
  rintro v ⟨ν, hν, hK, hval⟩
  exact ⟨ν, hν, measure_mono_null (compl_subset_compl.mpr h) hK, hval⟩

theorem energy_bounds_of_radius_pos {d : ℕ} (hd : 3 ≤ d) {K : Set (Space d)}
    (hc : 0 < capRadius K) : 0 < leastEnergy K ∧ leastEnergy K < ⊤ := by
  have hd' : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  have hneg : 1 / (2 - (d : ℝ)) < 0 := div_neg_of_pos_of_neg one_pos (sub_neg.mpr hd')
  constructor
  · apply pos_iff_ne_zero.mpr
    intro h
    rw [capRadius, h, ENNReal.zero_rpow_of_neg hneg, ENNReal.toReal_top] at hc
    exact lt_irrefl _ hc
  · apply lt_top_iff_ne_top.mpr
    intro h
    rw [capRadius, h, ENNReal.top_rpow_of_neg hneg, ENNReal.toReal_zero] at hc
    exact lt_irrefl _ hc

/-- Positive-volume interior implies finite positive energy for this compact solid. -/
theorem solid_energy {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n) (hball : BallCapacityFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    0 < leastEnergy (solid a w R) ∧ leastEnergy (solid a w R) < ⊤ := by
  obtain ⟨hK,z,r,hr,hinner⟩ := solid_compact_interior hn a w hw R hR
  obtain ⟨b, hb⟩ := Metric.isBounded_iff_subset_closedBall (0 : Space d) |>.mp hK.isBounded
  let B := max b 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hout : solid a w R ⊆ Metric.closedBall (0 : Space d) B :=
    hb.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  exact ⟨(energy_bounds_of_radius_pos hd (K := Metric.closedBall 0 B) (by rwa [hball 0 B hB])).1.trans_le
           (leastEnergy_antitone hout),
         (leastEnergy_antitone hinner).trans_lt
           (energy_bounds_of_radius_pos hd (K := Metric.closedBall z r) (by rwa [hball z r hr])).2⟩

private theorem dirichlet_mono {d : ℕ} {K U : Set (Space d)} (hKU : K ⊆ U) :
    dirichletCap K ≤ dirichletCap U := by
  apply sInf_le_sInf
  rintro v ⟨f,hf,hs,hU,hv⟩
  exact ⟨f,hf,hs,fun x hx => hU x (hKU hx),hv⟩

theorem dirichlet_outer {d : ℕ} (K : Set (Space d)) :
    dirichletCap K = sInf {v | ∃ U : Set (Space d), IsOpen U ∧ Bornology.IsBounded U ∧
      K ⊆ U ∧ dirichletCap U = v} := by
  let F := {v | ∃ U : Set (Space d), IsOpen U ∧ Bornology.IsBounded U ∧ K ⊆ U ∧ dirichletCap U = v}
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨U,_,_,hKU,rfl⟩
    exact dirichlet_mono hKU
  · apply le_sInf
    rintro q ⟨f,hf,hs,hK,rfl⟩
    let Q := ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)
    change sInf F ≤ Q
    by_cases hQ : Q = ⊤
    · simp [hQ]
    have hlim : Tendsto (fun c : ℝ => ENNReal.ofReal (c^2) * Q) (𝓝[>] 1) (𝓝 Q) := by
      have h : Continuous (fun c : ℝ => ENNReal.ofReal (c^2) * Q) := (ENNReal.continuous_mul_const hQ).comp
        (ENNReal.continuous_ofReal.comp (continuous_id.pow 2))
      simpa using (h.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with c hc
    change 1 < c at hc
    have hc0 : 0 < c := by linarith
    let U := {x | 1 < c * f x}
    have hopen : IsOpen U := isOpen_lt continuous_const (continuous_const.mul hf.continuous)
    have hb : Bornology.IsBounded U := hs.isBounded.subset (fun x hx =>
      subset_tsupport f (show x ∈ Function.support f from fun hz => by
        change 1 < c*f x at hx
        rw [hz,mul_zero] at hx
        linarith))
    have hKU : K ⊆ U := fun x hx =>
      lt_of_lt_of_le hc (by simpa using mul_le_mul_of_nonneg_left (hK x hx) hc0.le)
    have ht : HasCompactSupport (fun x => c*f x) := hs.mul_left (f := fun _ => c)
    refine (sInf_le (s := F) ⟨U,hopen,hb,hKU,rfl⟩).trans ?_
    apply sInf_le
    refine ⟨fun x => c*f x,contDiff_const.mul hf,ht,fun x hx => le_of_lt hx, ?_⟩
    dsimp only [Q]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [fderiv_const_mul (hf.differentiable (by norm_num) x), norm_smul, Real.norm_eq_abs,
      abs_of_pos hc0, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]

private theorem dirichlet_ball_eq {d : ℕ} (z : Space d) {r : ℝ} (hr : 0 < r) :
    dirichletCap (Metric.ball z r) = dirichletCap (Metric.closedBall z r) := by
  refine le_antisymm (dirichlet_mono Metric.ball_subset_closedBall) ?_
  apply sInf_le_sInf
  rintro q ⟨f,hf,hs,hball,hq⟩
  refine ⟨f,hf,hs,?_,hq⟩
  have hclosed : IsClosed {x | (1:ℝ) ≤ f x} := isClosed_le continuous_const hf.continuous
  have hsub : closure (Metric.ball z r) ⊆ {x | (1:ℝ) ≤ f x} :=
    hclosed.closure_subset_iff.mpr (fun x hx => hball x hx)
  rwa [closure_ball z hr.ne'] at hsub

theorem omega_positive (d : ℕ) : 0 < omega d :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem closedBall_volume {d : ℕ} (z : Space d) {r : ℝ} (hr : 0 ≤ r) :
    vol (Metric.closedBall z r) = omega d * r ^ d := by
  simpa [vol, omega, MeasureTheory.measureReal_def, finrank_euclideanSpace_fin, mul_comm]
    using volume.addHaar_real_closedBall z hr

/-- The variational definition extends the open-set inequality by taking open
neighborhoods of compact K. This is the compact approximation step. -/
theorem compact_isocapacity {d : ℕ} (hd : 3 ≤ d) (hopen : OpenIsoFact d)
    (hnorm : CapacityNormalization d) (hball : BallCapacityFact d)
    (K : Set (Space d)) (hK : IsCompact K) :
    volume K < ⊤ ∧ vol K ≤ omega d * capRadius K ^ d := by
  refine ⟨hK.measure_lt_top, ?_⟩
  have hω := omega_positive d
  have hc : 0 ≤ capRadius K := ENNReal.toReal_nonneg
  by_cases hv : 0 < vol K
  swap
  · exact (le_of_not_gt hv).trans (mul_nonneg hω.le (pow_nonneg hc _))
  have hd0 : d ≠ 0 := by omega
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let ρ (S : Set (Space d)) := (vol S / omega d) ^ ((d : ℝ)⁻¹)
  have radius_eq (S : Set (Space d)) : omega d * ρ S ^ d = vol S := by
    dsimp [ρ]
    rw [Real.rpow_inv_natCast_pow (div_nonneg (show 0 ≤ vol S from ENNReal.toReal_nonneg) hω.le) hd0]
    field_simp
  have hρ : 0 < ρ K := Real.rpow_pos_of_pos (div_pos hv hω) _
  have hlow : dirichletCap (Metric.closedBall (0 : Space d) (ρ K)) ≤ dirichletCap K := by
    rw [dirichlet_outer K]
    apply le_sInf
    rintro _ ⟨U,hU,hb,hKU,rfl⟩
    have hvU : vol K ≤ vol U := ENNReal.toReal_mono hb.measure_lt_top.ne (measure_mono hKU)
    have hrU : 0 < ρ U := Real.rpow_pos_of_pos (div_pos (hv.trans_le hvU) hω) _
    have hrad : ρ K ≤ ρ U := Real.rpow_le_rpow (div_nonneg hv.le hω.le)
      (div_le_div_of_nonneg_right hvU hω.le) (by positivity)
    have hmatch : volume U = volume (Metric.ball (0 : Space d) (ρ U)) := by
      rw [← ENNReal.ofReal_toReal hb.measure_lt_top.ne, ← ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      congr 1
      change vol U = vol (Metric.ball (0 : Space d) (ρ U))
      rw [← radius_eq U]
      change _ = (volume (Metric.ball (0 : Space d) (ρ U))).toReal
      rw [← volume.addHaar_closedBall_eq_addHaar_ball]
      exact (closedBall_volume 0 hrU.le).symm
    exact (dirichlet_mono (Metric.closedBall_subset_closedBall hrad)).trans
      ((dirichlet_ball_eq 0 hrU).ge.trans (hopen U (ρ U) hU hb hrU hmatch))
  rw [hnorm _ (isCompact_closedBall _ _), hnorm _ hK, hball _ _ hρ] at hlow
  let C := (d:ℝ) * ((d:ℝ)-2) * omega d
  have hC : 0 < C := by
    have hd' : (2:ℝ) < d := by exact_mod_cast (show 2 < d by omega)
    exact mul_pos (mul_pos (by linarith) (by linarith)) hω
  have hcmp := ENNReal.toReal_mono (by finiteness) hlow
  change (ENNReal.ofReal (C * ρ K ^ (d-2))).toReal ≤ (ENNReal.ofReal (C * capRadius K ^ (d-2))).toReal at hcmp
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (pow_nonneg hρ.le _)),
    ENNReal.toReal_ofReal (mul_nonneg hC.le (pow_nonneg hc _))] at hcmp
  have hpow := (mul_le_mul_iff_right₀ hC).mp hcmp
  have hrad := le_of_pow_le_pow_left₀ (show d - 2 ≠ 0 by omega) hc hpow
  rw [← radius_eq K]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hrad _) hω.le

private theorem ae_log_product {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (ν : Measure (Space d)) (ha : ∀ i, ν ({a i} : Set (Space d)) = 0) :
    ∀ᵐ x ∂ν, Real.log (G a w x) = ∑ i, w i * Real.log (dist x (a i)) := by
  have hn (i : Fin n) : ∀ᵐ x ∂ν, x ≠ a i := by simpa [ae_iff] using ha i
  filter_upwards [Filter.eventually_all.mpr hn] with x hx
  have hp (i : Fin n) := dist_pos.mpr (hx i)
  rw [G, Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hp i) _).ne')]
  exact Finset.sum_congr rfl (fun i _ => Real.log_rpow (hp i) _)

theorem integral_log_G {d n : ℕ} (a : Fin n → Space d) (w : Fin n → ℝ)
    (ν : Measure (Space d)) (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    ∫ x, Real.log (G a w x) ∂ν = ∑ i, w i * ∫ x, Real.log (dist x (a i)) ∂ν := by
  rw [integral_congr_ae (ae_log_product a w ν ha), integral_finsetSum]
  · simp [integral_const_mul]
  · exact fun i _ => (hi i).const_mul (w i)

/-- The integrated logarithmic moment is bounded at both ends. -/
theorem log_moment_sandwich {d n : ℕ} (hd : 3 ≤ d) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hM : EquilibriumMomentFact d) (ν : Measure (Space d))
    (heq : equilibrium (solid a w R) ν) (hc : 0 < capRadius (solid a w R))
    (ha : ∀ i, ν ({a i} : Set (Space d)) = 0)
    (hi : ∀ i, Integrable (fun x => Real.log (dist x (a i))) ν) :
    Real.log (capRadius (solid a w R)) ≤ ∫ x, Real.log (G a w x) ∂ν ∧
    (∫ x, Real.log (G a w x) ∂ν) ≤ Real.log R := by
  letI : IsProbabilityMeasure ν := heq.1
  have hn : 0 < n := by
    by_contra! h
    have : n = 0 := by omega
    subst n
    simpa using hw.2
  have hK := (solid_compact_interior hn a w hw R hR).1
  constructor
  · rw [integral_log_G a w ν ha hi]
    calc
      _ = ∑ i, w i * Real.log (capRadius (solid a w R)) := by rw [← Finset.sum_mul, hw.2, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM _ _ _ hK hc heq) (hw.1 i).le)
  · have hmem : ∀ᵐ x ∂ν, x ∈ solid a w R := ae_iff.mpr heq.2.1
    have hone (i : Fin n) : ∀ᵐ x ∂ν, x ≠ a i := by simpa [ae_iff] using ha i
    have hint : Integrable (fun x => Real.log (G a w x)) ν :=
      (integrable_finsetSum Finset.univ (fun i _ => (hi i).const_mul (w i))).congr
        ((ae_log_product a w ν ha).mono fun _ h => h.symm)
    calc
      _ ≤ ∫ _ : Space d, Real.log R ∂ν := by
        apply integral_mono_ae hint (integrable_const _)
        filter_upwards [hmem, Filter.eventually_all.mpr hone] with x hx hx'
        exact Real.log_le_log (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (dist_pos.mpr (hx' i)) _)) hx
      _ = _ := by simp

/-- If every mark's sphere belongs to the solid, all locations coincide. -/
theorem sphere_rigidity {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (a : Fin n → Space d)
    (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hs : ∀ i, Metric.sphere (a i) R ⊆ solid a w R) : ∀ i j, a i = a j := by
  intro i j
  by_contra hij
  obtain ⟨k,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun l => dist (a l) (a j))
    ⟨i, Finset.mem_univ _⟩
  let D := dist (a k) (a j)
  have hD : 0 < D := (dist_pos.mpr hij).trans_le (hmax i (Finset.mem_univ _))
  let c := R / D
  have hc : 0 < c := div_pos hR hD
  have hcD : c*D = R := div_mul_cancel₀ R hD.ne'
  let x := a k + c • (a k - a j)
  have hp : dist x (a k) = R := by
    simpa [x, dist_eq_norm, norm_smul, abs_of_pos hc, D] using hcD
  have hq : dist x (a j) = R+D := by
    have hid : x - a j = (c+1) • (a k - a j) := by dsimp [x]; rw [add_smul,one_smul]; abel
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    change (c+1)*D = R+D
    linarith
  have hall (l : Fin n) : R ≤ dist x (a l) := by
    have htriangle := dist_triangle x (a l) (a j)
    rw [hq] at htriangle
    linarith [show dist (a l) (a j) ≤ D from hmax l (Finset.mem_univ _)]
  have hupper : G a w x ≤ R := hs k (Metric.mem_sphere.2 hp)
  refine (not_lt_of_ge hupper) ?_
  calc R = ∏ l, R ^ w l := by rw [← Real.rpow_sum_of_pos hR, hw.2, Real.rpow_one]
       _ < G a w x := Finset.prod_lt_prod₀ (fun _ _ => Real.rpow_pos_of_pos hR _)
         (fun l _ => Real.rpow_le_rpow hR.le (hall l) (hw.1 l).le)
         ⟨j, Finset.mem_univ _, Real.rpow_lt_rpow hR.le (by linarith [hq]) (hw.1 j)⟩

theorem weighted_equality {n : ℕ} (w v : Fin n → ℝ) (m : ℝ) (hw : ValidWeights w)
    (hl : ∀ i, m ≤ v i) (hu : ∑ i, w i * v i ≤ m) : ∀ i, v i = m := by
  intro i
  have hsum : ∑ j, w j * (v j - m) ≤ 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw.2, one_mul]
    linarith
  have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j => w j * (v j - m))
    (fun j _ => mul_nonneg (hw.1 j).le (sub_nonneg.mpr (hl j))) (Finset.mem_univ i)
  refine le_antisymm ?_ (hl i)
  by_contra! h
  exact (not_lt_of_ge (hi.trans hsum)) (mul_pos (hw.1 i) (sub_pos.mpr h))

theorem capacity_sphere_consequence {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hO : OpenIsoFact d) (hN : CapacityNormalization d) (hB : BallCapacityFact d)
    (hE : EquilibriumExistence d) (hM : EquilibriumMomentFact d) (hS : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R)
    (hvol : vol (solid a w R) = omega d * R ^ d) :
    capRadius (solid a w R) = R ∧ ∀ i, sphere (a i) R ⊆ solid a w R := by
  have hK := (solid_compact_interior hn a w hw R hR).1
  obtain ⟨he0,hefin⟩ := solid_energy hd hn hB a w hw R hR
  have hc : 0 < capRadius (solid a w R) := ENNReal.toReal_pos
    (ENNReal.rpow_pos he0 hefin.ne).ne' (ENNReal.rpow_ne_top_of_nonneg' he0 hefin.ne)
  obtain ⟨ν,heq,ha,hi⟩ := hE _ hK he0 hefin
  have hsand := log_moment_sandwich hd a w hw R hR hM ν heq hc (fun i => ha (a i)) (fun i => hi (a i))
  have hle := (Real.log_le_log_iff hc hR).1 (hsand.1.trans hsand.2)
  have hv := (compact_isocapacity hd hO hN hB _ hK).2
  rw [hvol] at hv
  have hge := le_of_pow_le_pow_left₀ (show d ≠ 0 by omega) hc.le
    ((mul_le_mul_iff_right₀ (omega_positive d)).1 hv)
  have hequal := le_antisymm hle hge
  refine ⟨hequal, fun i => ?_⟩
  have hsum := hsand.2
  rw [integral_log_G a w ν (fun j => ha (a j)) (fun j => hi (a j))] at hsum
  have hall := weighted_equality w (fun j => ∫ x, Real.log (dist x (a j)) ∂ν)
    (Real.log (capRadius (solid a w R))) hw (fun j => hM _ _ _ hK hc heq) (hsum.trans_eq (congrArg Real.log hequal.symm))
  simpa only [hequal] using hS _ _ (a i) hK hc heq (hall i)

/-- Theorem 1, capacity route, with each external input visible. -/
theorem volume_capacity {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (hopen : OpenIsoFact d) (hnorm : CapacityNormalization d) (hball : BallCapacityFact d)
    (hex : EquilibriumExistence d) (hm : EquilibriumMomentFact d) (hs : EquilibriumSphereFact d)
    (a : Fin n → Space d) (w : Fin n → ℝ) (hw : ValidWeights w) (R : ℝ) (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∀ i j, a i = a j) := by
  have hK := (solid_compact_interior hn a w hw R hR).1
  obtain ⟨he0,hefin⟩ := solid_energy hd hn hball a w hw R hR
  have hc : 0 < capRadius (solid a w R) := ENNReal.toReal_pos
    (ENNReal.rpow_pos he0 hefin.ne).ne' (ENNReal.rpow_ne_top_of_nonneg' he0 hefin.ne)
  obtain ⟨ν,heq,ha,hi⟩ := hex _ hK he0 hefin
  have hsand := log_moment_sandwich hd a w hw R hR hm ν heq hc (fun i => ha (a i)) (fun i => hi (a i))
  have hle := (Real.log_le_log_iff hc hR).1 (hsand.1.trans hsand.2)
  have hv := compact_isocapacity hd hopen hnorm hball _ hK
  refine ⟨hv.1,hv.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hle _) (omega_positive d).le),?_,?_⟩
  · intro hvol
    exact sphere_rigidity (by omega) hn a w hw R hR
      (capacity_sphere_consequence hd hn hopen hnorm hball hex hm hs a w hw R hR hvol).2
  · intro hsame
    let j : Fin n := ⟨0,hn⟩
    have hset : solid a w R = Metric.closedBall (a j) R := by
      ext x
      change (∏ i, dist x (a i) ^ w i) ≤ R ↔ dist x (a j) ≤ R
      have hprod : (∏ i, dist x (a i) ^ w i) = ∏ i, dist x (a j) ^ w i :=
        Finset.prod_congr rfl (fun i _ => by rw [hsame i j])
      rw [hprod]
      rw [← Real.rpow_sum_of_nonneg dist_nonneg (fun i _ => (hw.1 i).le), hw.2, Real.rpow_one]
    rw [hset, closedBall_volume _ hR.le]

end ErdosVolume

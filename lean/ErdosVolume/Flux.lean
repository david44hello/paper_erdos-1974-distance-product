module

public import ErdosVolume.Defs

@[expose] public section

/-! Finite-charge superlevels and the direct volume comparison. The volume comparison uses the eight explicit analytic hypotheses below.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelCoordinates
attribute [local instance 2000] ErdosVolume.CoordinateFacts.ennrealScalarTower
attribute [local instance 2000] ErdosVolume.CoordinateFacts.twoAtLeastTwo
attribute [local instance 2000] ErdosVolume.CoordinateFacts.finiteThree
attribute [local instance 2000] ErdosVolume.CoordinateFacts.borelThree

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal BigOperators Topology ContDiff Classical

namespace ErdosVolume
namespace Flux

variable {d n : ℕ}

def potential (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (w i) * newtonKernel x (a i)

def off (a : Fin n → Space d) : Set (Space d) := (Set.range a)ᶜ

/-- Used for differentiation only off the finite set of marks. -/
def u (a : Fin n → Space d) (w : Fin n → ℝ) (x : Space d) : ℝ :=
  ∑ i, w i * dist x (a i) ^ (2 - (d : ℝ))

def super (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | ENNReal.ofReal t ≤ potential a w x}

def level (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Set (Space d) :=
  {x | x ∈ off a ∧ u a w x = t}

def W (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) := vol (super a w t)
def rad (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  (W a w t / omega d) ^ (1 / (d : ℝ))

/-- Mathlib uses the diameter-power normalization of Hausdorff measure. -/
def surface (S : Set (Space d)) : Measure (Space d) :=
  letI : SMul ENNReal (Measure (Space d)) :=
    @MeasureTheory.Measure.instSMul (Space d) ENNReal _ _ ErdosVolume.CoordinateFacts.ennrealScalarTower
  ENNReal.ofReal (omega (d-1) / (2 : ℝ) ^ (d-1)) •
    ((Measure.hausdorffMeasure ((d : ℝ) - 1)).restrict S)

def regular (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ x ∈ level a w t, gradient (u a w) x ≠ 0

def normal (v : Space d) := ‖v‖⁻¹ • v
def shellFlux (f : Space d → ℝ) (b : Space d) (e : ℝ) :=
  ∫ x, inner ℝ (gradient f x) (normal (x-b)) ∂(surface (sphere b e))
def density (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ∫ x, ‖gradient (u a w) x‖⁻¹ ∂(surface (level a w t))
def area (a : Fin n → Space d) (w : Fin n → ℝ) (t : ℝ) :=
  ((surface (level a w t)) Set.univ).toReal

def AnalyticNull (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → IsConnected O →
    AnalyticOnNhd ℝ f O → (∃ x ∈ O, f x ≠ 0) → volume {x | x ∈ O ∧ f x = 0} = 0

def SardScalar (d : ℕ) : Prop :=
  ∀ (O : Set (Space d)) (f : Space d → ℝ), IsOpen O → ContDiffOn ℝ ∞ f O →
    volume (f '' {x | x ∈ O ∧ gradient f x = 0}) = 0

def CoareaSlabs (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  volume {x | x ∈ off a ∧ gradient (u a w) x = 0} = 0 →
  (∀ t > 0, volume (level a w t) = 0) →
  ∀ s t : ℝ, 0 < s → s < t →
    IntervalIntegrable (density a w) volume s t ∧
    W a w s - W a w t = ∫ z in s..t, density a w z

/-- Smooth-domain Gauss applied before letting the small spheres shrink.
The sphere normals here point away from their centers. -/
def PuncturedGauss (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → ∀ᶠ e in 𝓝[>] (0 : ℝ),
    ∀ f : Space d → ℝ, HarmonicOnNhd f (super a w t \ ⋃ b ∈ Set.range a, ball b e) →
    (∫ x, inner ℝ (gradient f x) (-normal (gradient (u a w) x)) ∂(surface (level a w t))) =
      ∑ b ∈ Finset.univ.image a, shellFlux f b e

def BallGauss (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ) (f : Space d → ℝ), 0 < e →
    HarmonicOnNhd f (closedBall b e) → shellFlux f b e = 0

def SphereArea (d : ℕ) : Prop :=
  ∀ (b : Space d) (e : ℝ), 0 < e →
    (surface (sphere b e)) Set.univ = ENNReal.ofReal ((d : ℝ) * omega d * e ^ (d-1))

def SharpIso (d : ℕ) : Prop :=
  ∀ K : Set (Space d), IsCompact K → MeasurableSet K →
    ENNReal.ofReal ((d : ℝ) * omega d * (vol K / omega d) ^ (((d : ℝ)-1)/d)) ≤
      (surface (frontier K)) Set.univ

/-- Finite surface area and integrable continuous boundary data on compact regular levels. -/
def SurfaceFinite (a : Fin n → Space d) (w : Fin n → ℝ) : Prop :=
  ∀ t > 0, regular a w t → (surface (level a w t)) Set.univ < ⊤

variable (a : Fin n → Space d) (w : Fin n → ℝ)

private theorem off_dist_pos {x : Space d} (hx : x ∈ off a) (i : Fin n) :
    0 < dist x (a i) := by
  apply dist_pos.mpr
  intro h
  exact hx ⟨i, h.symm⟩

private theorem pow_product (x : Space d) (q : ℝ) :
    G a w x ^ q = ∏ i, (dist x (a i) ^ q) ^ w i := by
  unfold G
  rw [← Real.finsetProd_rpow Finset.univ _ (fun i _ => Real.rpow_nonneg dist_nonneg _) q]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_mul dist_nonneg, ← Real.rpow_mul dist_nonneg, mul_comm]

theorem combine_marks (x : Space d) :
    u a w x = ∑ b ∈ Finset.univ.image a,
      (∑ i ∈ Finset.univ.filter (fun i => a i = b), w i) * dist x b ^ (2 - (d : ℝ)) := by
  classical
  unfold u
  rw [← Finset.sum_fiberwise_of_maps_to (fun i => Finset.mem_image_of_mem a)
    (fun i => w i * dist x (a i) ^ (2 - (d : ℝ)))]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem at_mark (hd : 3 ≤ d) (hw : ValidWeights w) (i : Fin n) :
    potential a w (a i) = ⊤ := by
  have he : 2 - (d : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast (show 2 < d by omega))
  apply ENNReal.sum_eq_top.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp [newtonKernel, ENNReal.zero_rpow_of_neg he, (ENNReal.ofReal_pos.mpr (hw.1 i)).ne']

theorem off_formula (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a) :
    potential a w x = ENNReal.ofReal (u a w x) := by
  unfold potential u
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw.1 i).le (Real.rpow_nonneg dist_nonneg _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (hw.1 i).le, newtonKernel, ENNReal.ofReal_rpow_of_pos (off_dist_pos a hx i)]

theorem amgm (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a) :
    G a w x ^ (2 - (d : ℝ)) ≤ u a w x := by
  rw [pow_product]
  exact Real.geom_mean_le_arith_mean_weighted Finset.univ w _
    (fun i _ => (hw.1 i).le) hw.2 (fun i _ => Real.rpow_nonneg dist_nonneg _)

theorem inclusion (hd : 3 ≤ d) (hw : ValidWeights w) {R : ℝ} (hR : 0 < R) :
    solid a w R ⊆ super a w (R ^ (2 - (d : ℝ))) := by
  intro x hx
  change ENNReal.ofReal _ ≤ potential a w x
  by_cases h : x ∈ off a
  · rw [off_formula a w hd hw h]
    apply ENNReal.ofReal_le_ofReal
    have hg : 0 < G a w x := Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (off_dist_pos a h i) _
    have he : 2 - (d : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast (show 2 < d by omega))
    exact ((Real.rpow_le_rpow_iff_of_neg hR hg he).2 hx).trans (amgm a w hd hw h)
  · have hm : x ∈ Set.range a := by simpa [off] using h
    obtain ⟨i, rfl⟩ := hm
    rw [at_mark a w hd hw i]
    exact le_top

private theorem continuous_potential : Continuous (potential a w) := by
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp
      (continuous_id.dist (continuous_const (y := a i)))))

private theorem continuous_product (hw : ValidWeights w) : Continuous (G a w) := by
  apply continuous_finsetProd Finset.univ
  intro i _
  exact (continuous_id.dist (continuous_const (y := a i))).rpow_const (fun _ => Or.inr (hw.1 i).le)

private theorem product_at_mark (hw : ValidWeights w) (i : Fin n) : G a w (a i) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Real.zero_rpow (hw.1 i).ne']

private theorem off_of_product_pos (hw : ValidWeights w) {x : Space d} (h : 0 < G a w x) :
    x ∈ off a := by
  rintro ⟨i, rfl⟩
  simp [product_at_mark a w hw i] at h

private theorem omega_pos : 0 < omega d := by
  exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem geometry (hd : 3 ≤ d) (hw : ValidWeights w) {t : ℝ} (ht : 0 < t) :
    IsCompact (super a w t) ∧ (∀ i : Fin n, super a w t ∈ 𝓝 (a i)) ∧
    0 < rad a w t ∧ W a w t = omega d * rad a w t ^ d := by
  have hq : 2 - (d : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast (show 2 < d by omega))
  let r := (t/2) ^ (2 - (d : ℝ))⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hrq : r ^ (2 - (d : ℝ)) = t/2 := Real.rpow_inv_rpow (by linarith) hq.ne
  have hsub : super a w t ⊆ ⋃ i, closedBall (a i) r := by
    intro x hx
    by_contra h
    have hdist (i : Fin n) : r < dist x (a i) :=
      lt_of_not_ge (fun hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩))
    have hoff : x ∈ off a := by
      rintro ⟨i, rfl⟩
      simpa using (hr.trans (hdist i))
    have hu : u a w x ≤ t/2 := calc
      _ ≤ ∑ i, w i * (t/2) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hrq ▸ (Real.rpow_le_rpow_iff_of_neg (hr.trans (hdist i)) hr hq).2 (hdist i).le) (hw.1 i).le)
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]
    change ENNReal.ofReal t ≤ potential a w x at hx
    rw [off_formula a w hd hw hoff] at hx
    exact (not_lt_of_ge hx) ((ENNReal.ofReal_lt_ofReal_iff ht).2 (by linarith))
  have hcompact : IsCompact (super a w t) :=
    (isCompact_iUnion (fun i => isCompact_closedBall (a i) r)).of_isClosed_subset
      (isClosed_le continuous_const (continuous_potential a w)) hsub
  have hnhds (i : Fin n) : super a w t ∈ 𝓝 (a i) := by
    have hstrict : ENNReal.ofReal t < potential a w (a i) := by
      rw [at_mark a w hd hw i]
      exact ENNReal.ofReal_lt_top
    exact ((continuous_potential a w).continuousAt.eventually (Ioi_mem_nhds hstrict)).mono
      (fun _ h => h.le)
  obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := w)
    (by rw [hw.2]; norm_num)
  have hW : 0 < W a w t := ENNReal.toReal_pos (volume.measure_pos_of_mem_nhds (hnhds i)).ne'
    hcompact.measure_lt_top.ne
  have ho : 0 < omega d := omega_pos
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  refine ⟨hcompact, hnhds, Real.rpow_pos_of_pos (div_pos hW ho) _, ?_⟩
  rw [rad, one_div, ← Real.rpow_natCast, Real.rpow_inv_rpow (div_pos hW ho).le hd']
  field_simp

private theorem open_off : IsOpen (off a) := (Set.finite_range a).isClosed.isOpen_compl

theorem regular_frontier (hd : 3 ≤ d) (hw : ValidWeights w) {t : ℝ} (ht : 0 < t)
    (hr : regular a w t) : frontier (super a w t) = level a w t := by
  obtain ⟨hc,hm,_,_⟩ := geometry a w hd hw ht
  rw [hc.isClosed.frontier_eq]
  ext x
  constructor
  · rintro ⟨hmem,hnot⟩
    have hoff : x ∈ off a := by
      rintro ⟨i, rfl⟩
      exact hnot (mem_interior_iff_mem_nhds.mpr (hm i))
    have hupper : potential a w x ≤ ENNReal.ofReal t := by
      by_contra! h
      apply hnot
      apply mem_interior_iff_mem_nhds.mpr
      exact ((continuous_potential a w).continuousAt.eventually (Ioi_mem_nhds h)).mono
        (fun y hy => hy.le)
    have heq : potential a w x = ENNReal.ofReal t := le_antisymm hupper hmem
    rw [off_formula a w hd hw hoff] at heq
    exact ⟨hoff, (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg (fun i _ => mul_nonneg (hw.1 i).le (Real.rpow_nonneg dist_nonneg _))) ht.le).mp heq⟩
  · intro hlevel
    have heq : u a w x = t := hlevel.2
    refine ⟨?_, ?_⟩
    · change ENNReal.ofReal t ≤ potential a w x
      rw [off_formula a w hd hw hlevel.1, heq]
    · intro hint
      apply hr x hlevel
      have hmin : IsLocalMin (u a w) x := by
        filter_upwards [mem_interior_iff_mem_nhds.mp hint, (open_off a).mem_nhds hlevel.1] with y hy ho
        change ENNReal.ofReal t ≤ potential a w y at hy
        rw [off_formula a w hd hw ho] at hy
        rw [heq]
        exact (ENNReal.ofReal_le_ofReal_iff'.mp hy).resolve_right ht.not_ge
      simp [gradient, hmin.fderiv_eq_zero]

private theorem u_analytic : AnalyticOnNhd ℝ (u a w) (off a) := by
  intro x hx
  apply ContDiffAt.analyticAt
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.mul (((contDiffAt_id.dist ℝ contDiffAt_const
    (dist_pos.mp (off_dist_pos a hx i))).rpow_const_of_ne (off_dist_pos a hx i).ne'))

private theorem connected_off (hd : 3 ≤ d) : IsConnected (off a) := by
  apply (Set.finite_range a).countable.isConnected_compl_of_one_lt_rank
  apply Module.one_lt_rank_of_one_lt_finrank
  simpa only [Space, finrank_euclideanSpace_fin] using (show 1 < d by omega)

private theorem exists_unequal_level (hd : 3 ≤ d) (hw : ValidWeights w) (t : ℝ) :
    ∃ x ∈ off a, u a w x ≠ t := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  by_cases ht : 0 < t
  · obtain ⟨x,hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 (geometry a w hd hw ht).1.ne_univ
    have h : x ∈ off a := by
      rintro ⟨i, rfl⟩
      exact hx (mem_of_mem_nhds ((geometry a w hd hw ht).2.1 i))
    refine ⟨x,h,fun he => hx ?_⟩
    change ENNReal.ofReal t ≤ potential a w x
    rw [off_formula a w hd hw h, he]
  · obtain ⟨x,hx⟩ := (connected_off a hd).nonempty
    obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := w)
      (by rw [hw.2]; norm_num)
    have hpos : 0 < u a w x := Finset.sum_pos (fun k _ =>
      mul_pos (hw.1 k) (Real.rpow_pos_of_pos (off_dist_pos a hx k) _)) ⟨i,hi⟩
    exact ⟨x,hx,(lt_of_le_of_lt (le_of_not_gt ht) hpos).ne'⟩

private theorem kernel_deriv (b x : Space d) (q : ℝ) (hx : x ≠ b) :
    HasFDerivAt (fun y => dist y b ^ q)
      ((q * dist x b ^ (q-2)) • innerSL ℝ (x-b)) x := by
  let h := (((hasFDerivAt_id x).sub_const b).norm_sq).rpow_const
    (p := q/2) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))))
  have he (y : Space d) (r : ℝ) : (‖y-b‖^2) ^ r = ‖y-b‖ ^ (2*r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  convert h using 1
  · funext y
    simpa [he,dist_eq_norm] using congrArg (fun k : ℝ => ‖y-b‖ ^ k) (show q = 2*(q/2) by ring)
  · ext v
    simp [he,dist_eq_norm, innerSL_apply_apply, show 2*(q/2-1) = q-2 by ring]
    ring

private theorem kernel_harmonic {b x : Space d} (hx : x ≠ b) :
    HarmonicAt (fun y => dist y b ^ (2-(d:ℝ))) x := by
  let q := 2-(d:ℝ)
  refine ⟨((contDiffAt_id.dist ℝ contDiffAt_const hx).rpow_const_of_ne (dist_pos.mpr hx).ne'), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with z hz
  let v := z-b
  let r := dist z b
  have hr : 0 < r := dist_pos.mpr hz
  let B := EuclideanSpace.basisFun (Fin d) ℝ
  have hin : HasFDerivAt (fun y => innerSL ℝ (y-b))
      (innerSL ℝ : Space d →L[ℝ] _) z := by
    simpa using (innerSL ℝ (E := Space d)).hasFDerivAt.sub_const (innerSL ℝ b) |>.congr_of_eventuallyEq
      (show (fun y => innerSL ℝ (y-b)) =ᶠ[𝓝 z] _ from Filter.Eventually.of_forall (fun y => map_sub _ _ _))
  have hF := ((kernel_deriv b z (q-2) hz).const_mul q).smul hin
  have he : fderiv ℝ (fun y => dist y b ^ q) =ᶠ[𝓝 z]
      (fun y => (q * dist y b ^ (q-2)) • innerSL ℝ (y-b)) :=
    (eventually_ne_nhds hz).mono fun y hy => (kernel_deriv b y q hy).fderiv
  have hdF := hF.congr_of_eventuallyEq he
  have hterm (i : Fin d) :
      iteratedFDeriv ℝ 2 (fun y => dist y b ^ q) z ![B i,B i] =
        q*r^(q-2) + (q*(q-2)*r^((q-2)-2)) * (inner ℝ v (B i))^2 := by
    have hunit : ((innerSL ℝ : Space d →L[ℝ] (Space d →L[ℝ] ℝ)) (B i)) (B i) = 1 := by
      change inner ℝ (B i) (B i) = 1
      rw [real_inner_self_eq_norm_sq, B.norm_eq_one, one_pow]
    rw [iteratedFDeriv_two_apply,hdF.fderiv]
    simp [v,r,innerSL_apply_apply]
    simp only [hunit, inner_sub_left, mul_one]
    ring
  change (Laplacian.laplacian (fun y => dist y b ^ q)) z = 0
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ B]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, B.sum_sq_inner_left]
  change (d:ℝ)*(q*r^(q-2)) + q*(q-2)*r^(q-2-2)*r^2 = 0
  rw [← mul_assoc, mul_assoc (q*(q-2)), ← Real.rpow_natCast, ← Real.rpow_add hr]
  simp only [Nat.cast_ofNat]
  rw [show q-2-2+2 = q-2 by ring]
  dsimp [q]
  ring

theorem smooth_harmonic (hd : 3 ≤ d) (hw : ValidWeights w) :
    AnalyticOnNhd ℝ (u a w) (off a) ∧ ContDiffOn ℝ ∞ (u a w) (off a) ∧
    HarmonicOnNhd (u a w) (off a) := by
  refine ⟨u_analytic a w, fun x hx => (u_analytic a w x hx).contDiffAt.contDiffWithinAt, ?_⟩
  intro x hx
  have hsum (S : Finset (Fin n)) : HarmonicAt
      (fun y => ∑ i ∈ S, w i * dist y (a i) ^ (2-(d:ℝ))) x := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((kernel_harmonic (dist_pos.mp (off_dist_pos a hx i))).const_smul (c := w i)).add ih
  exact hsum Finset.univ

theorem critical_witness (hd : 3 ≤ d) (hw : ValidWeights w) :
    IsConnected (off a) ∧ ∃ k : Fin d, ∃ x ∈ off a,
      fderiv ℝ (u a w) x (EuclideanSpace.single k 1) ≠ 0 := by
  refine ⟨connected_off a hd, ?_⟩
  by_contra! h
  have hz : (off a).EqOn (fderiv ℝ (u a w)) 0 := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
    intro k
    simpa [EuclideanSpace.basisFun_apply] using h k x hx
  obtain ⟨c,hc⟩ := (open_off a).exists_is_const_of_fderiv_eq_zero (connected_off a hd).isPreconnected
    (fun x hx => ((u_analytic a w x hx).differentiableAt).differentiableWithinAt) hz
  obtain ⟨x,hx,hn⟩ := exists_unequal_level a w hd hw c
  exact hn (hc x hx)

theorem outer_derivative (t : ℝ) {x : Space d} (hx : x ∈ level a w t) :
    inner ℝ (gradient (u a w) x) (-normal (gradient (u a w) x)) =
      -‖gradient (u a w) x‖ := by
  let v := gradient (u a w) x
  change inner ℝ v (-normal v) = -‖v‖
  rw [inner_neg_right, normal, real_inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases h : ‖v‖ = 0
  · simp [h]
  · field_simp

theorem null_sets (hd : 3 ≤ d) (hw : ValidWeights w) (hZ : AnalyticNull d) :
    volume {x | x ∈ off a ∧ gradient (u a w) x = 0} = 0 ∧
    ∀ t : ℝ, volume (level a w t) = 0 := by
  obtain ⟨hc,k,x,hx,hwit⟩ := critical_witness a w hd hw
  let v : Space d := EuclideanSpace.single k 1
  let coordDeriv := fun y => fderiv ℝ (u a w) y v
  have hpart : AnalyticOnNhd ℝ coordDeriv (off a) := fun y hy =>
    (((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp (u_analytic a w y hy).fderiv)
  refine ⟨?_, ?_⟩
  · apply measure_mono_null _ (hZ _ coordDeriv (open_off a) hc hpart ⟨x,hx,hwit⟩)
    intro y hy
    refine ⟨hy.1, ?_⟩
    change fderiv ℝ (u a w) y v = 0
    rw [← inner_gradient_left, hy.2, inner_zero_left]
  · intro t
    obtain ⟨p,hp,hne⟩ := exists_unequal_level a w hd hw t
    apply measure_mono_null _ (hZ _ (fun y => u a w y - t) (open_off a) hc
      (fun y hy => (u_analytic a w y hy).sub analyticAt_const) ⟨p,hp,sub_ne_zero.mpr hne⟩)
    exact fun y hy => ⟨hy.1, sub_eq_zero.mpr hy.2⟩

theorem ae_regular (hd : 3 ≤ d) (hw : ValidWeights w) (hS : SardScalar d) :
    ∀ᵐ t : ℝ, 0 < t → regular a w t := by
  have hs := hS (off a) (u a w) (open_off a) (fun x hx =>
    ((u_analytic a w x hx).contDiffAt).contDiffWithinAt)
  filter_upwards [compl_mem_ae_iff.mpr hs] with t ht
  intro _ x hx hgrad
  exact ht ⟨x, ⟨hx.1, hgrad⟩, hx.2⟩

private theorem surface_ae {S : Set (Space d)} (hS : MeasurableSet S) :
    ∀ᵐ x ∂(surface S), x ∈ S :=
  Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hS)

private theorem surface_integrable {S : Set (Space d)} (hS : IsCompact S)
    (hfin : (surface S) Set.univ < ⊤) {f : Space d → ℝ} (hf : ContinuousOn f S) :
    Integrable f (surface S) := by
  letI : IsFiniteMeasure (surface S) := ⟨hfin⟩
  have h := hf.integrableOn_compact (μ := surface S) hS
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (surface_ae hS.measurableSet)] at h

theorem shell_self (hd : 3 ≤ d) (hA : SphereArea d) (b : Space d) {e : ℝ} (he : 0 < e) :
    shellFlux (fun x => dist x b ^ (2 - (d : ℝ))) b e = -((d : ℝ) * (d-2 : ℝ) * omega d) := by
  let q := 2-(d:ℝ)
  unfold shellFlux
  calc
    _ = ∫ _ : Space d, (q * e^(q-2) * e) ∂(surface (sphere b e)) := by
      apply integral_congr_ae
      filter_upwards [surface_ae (isClosed_sphere (x := b) (ε := e)).measurableSet] with x hx
      have hdxb : dist x b = e := hx
      have hnorm : ‖x-b‖ = e := by simpa only [dist_eq_norm] using hdxb
      rw [inner_gradient_left, (kernel_deriv b x q
        (dist_pos.mp (hdxb ▸ he : 0 < dist x b))).fderiv]
      simp [normal, innerSL_apply_apply, hnorm, hdxb]
      field_simp
      rw [← inner_sub_left, real_inner_self_eq_norm_sq, hnorm, mul_comm]
    _ = _ := by
      rw [integral_const, measureReal_def, hA b e he, ENNReal.toReal_ofReal (by positivity [omega_pos (d := d)])]
      simp only [smul_eq_mul]
      have hex : e^(d-1) * e^(q-2) * e = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add he, ← Real.rpow_add_one he.ne']
        have he0 : ((d-1:ℕ):ℝ) + (q-2) + 1 = 0 := by
          dsimp [q]
          rw [Nat.cast_sub (by omega : 1 ≤ d)]
          push_cast
          ring
        rw [he0, Real.rpow_zero]
      calc _ = (d:ℝ) * omega d * q * (e^(d-1) * e^(q-2) * e) := by ring
           _ = _ := by rw [hex]; dsimp [q]; ring

theorem shell_other (hd : 3 ≤ d) (hB : BallGauss d) (b c : Space d) {e : ℝ}
    (he : 0 < e) (hc : e < dist b c) :
    shellFlux (fun x => dist x c ^ (2 - (d : ℝ))) b e = 0 := by
  apply hB _ _ _ he
  intro x hx
  apply kernel_harmonic
  rintro rfl
  exact hc.not_ge (dist_comm b x ▸ hx)

private theorem shell_combination (b : Space d) {e : ℝ} (he : 0 < e)
    (hsep : ∀ i, b ≠ a i → e < dist b (a i)) (hA : SphereArea d) :
    shellFlux (u a w) b e = ∑ i, w i * shellFlux (fun x => dist x (a i) ^ (2-(d:ℝ))) b e := by
  let k := fun i (x : Space d) => dist x (a i) ^ (2-(d:ℝ))
  let N := fun x : Space d => normal (x-b)
  let h := fun i x => inner ℝ (gradient (k i) x) (N x)
  have hn (x : Space d) (hx : x ∈ sphere b e) (i : Fin n) : x ≠ a i := by
    rintro rfl
    change dist (a i) b = e at hx
    by_cases hbi : b = a i
    · rw [hbi,dist_self] at hx
      linarith
    · have := hsep i hbi
      rw [dist_comm,hx] at this
      exact this.false
  have hfin : (surface (sphere b e)) Set.univ < ⊤ := by rw [hA _ _ he]; exact ENNReal.ofReal_lt_top
  have hi (i : Fin n) : Integrable (h i) (surface (sphere b e)) := by
    apply surface_integrable (isCompact_sphere _ _) hfin
    intro x hx
    have heq : dist x b = e := hx
    have hxb : x-b ≠ 0 := sub_ne_zero.mpr (dist_pos.mp (heq ▸ he))
    have hN : ContinuousAt N x := by
      change ContinuousAt (fun y : Space d => ‖y-b‖⁻¹ • (y-b)) x
      apply ContinuousAt.fun_smul
      · exact ((continuous_id.sub continuous_const).norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hxb)
      · fun_prop
    have hk : ContDiffAt ℝ ω (k i) x := (contDiffAt_id.dist ℝ contDiffAt_const (hn x hx i)).rpow_const_of_ne
      (dist_pos.mpr (hn x hx i)).ne'
    have hgrad : ContinuousAt (gradient (k i)) x :=
      (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.continuousAt.comp hk.analyticAt.fderiv.continuousAt
    exact (hgrad.inner hN).continuousWithinAt
  unfold shellFlux
  calc
    _ = ∫ x, ∑ i, w i * h i x ∂(surface (sphere b e)) := by
      apply integral_congr_ae
      filter_upwards [surface_ae (isClosed_sphere (x := b) (ε := e)).measurableSet] with x hx
      have hD : HasFDerivAt (u a w) (∑ i, w i • fderiv ℝ (k i) x) x :=
        HasFDerivAt.fun_sum fun i _ =>
          (((kernel_deriv (a i) x _ (hn x hx i)).differentiableAt.hasFDerivAt).const_mul (w i))
      simp only [h,N, inner_gradient_left,hD.fderiv,ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply,smul_eq_mul]
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (w i))]
      simp only [integral_const_mul]
      rfl

theorem flux_identity (hd : 3 ≤ d) (hw : ValidWeights w)
    (hG : PuncturedGauss a w) (hB : BallGauss d) (hA : SphereArea d) {t : ℝ}
    (ht : 0 < t) (hr : regular a w t) :
    (∫ x, ‖gradient (u a w) x‖ ∂(surface (level a w t))) =
      (d : ℝ) * (d-2 : ℝ) * omega d := by
  classical
  let C := (d:ℝ)*(d-2:ℝ)*omega d
  have hsep (i j : Fin n) : ∀ᶠ e in 𝓝[>] (0 : ℝ), a i ≠ a j → e < dist (a i) (a j) := by
    by_cases h : a i = a j
    · filter_upwards with e using fun hn => (hn h).elim
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (dist_pos.mpr h))] with e he
      exact fun _ => he
  have hposE : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 < e := self_mem_nhdsWithin
  obtain ⟨e,he,hsep',hbal⟩ := (hposE.and
    ((Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hsep i))).and (hG t ht hr))).exists
  have hh : HarmonicOnNhd (u a w) (super a w t \ ⋃ b ∈ Set.range a, ball b e) := by
    apply (smooth_harmonic a w hd hw).2.2.mono
    intro x hx
    rintro ⟨i,rfl⟩
    exact hx.2 (Set.mem_iUnion.mpr ⟨a i,Set.mem_iUnion.mpr ⟨⟨i,rfl⟩,mem_ball_self he⟩⟩)
  have hbound := hbal (u a w) hh
  have hleft : (∫ x, inner ℝ (gradient (u a w) x) (-normal (gradient (u a w) x))
        ∂(surface (level a w t))) = -(∫ x, ‖gradient (u a w) x‖ ∂(surface (level a w t))) := by
    rw [← integral_neg]
    exact integral_congr_ae ((surface_ae (regular_frontier a w hd hw ht hr ▸ isClosed_frontier.measurableSet)).mono
      (fun x hx => outer_derivative a w t hx))
  let marks := Finset.univ.image a
  have hterm (b : Space d) (hb : b ∈ marks) :
      shellFlux (u a w) b e = ∑ i, (if b = a i then w i * (-C) else 0) := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    rw [shell_combination a w (a j) he (hsep' j) hA]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : a j = a i
    · rw [if_pos h,h,shell_self hd hA _ he]
    · rw [if_neg h,shell_other hd hB _ _ he (hsep' j i h),mul_zero]
  have hright : ∑ b ∈ marks, shellFlux (u a w) b e = -C := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_image_of_mem a (Finset.mem_univ _), marks,
      if_true, ← Finset.sum_mul, hw.2, one_mul]
  rw [hleft,hright] at hbound
  exact neg_injective hbound

theorem level_derivative (hd : 3 ≤ d) (hw : ValidWeights w)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    (∀ s t : ℝ, 0 < s → s < t → AbsolutelyContinuousOnInterval (W a w) s t) ∧
    ∀ᵐ t : ℝ, 0 < t → HasDerivAt (W a w) (-density a w t) t := by
  have hz := null_sets a w hd hw hZ
  have hslab := hC hz.1 (fun t _ => hz.2 t)
  have hprim {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
      W a w s - (∫ v in s..z, density a w v) = W a w z := by
    rcases hsz.eq_or_lt with rfl | h
    · simp
    · linarith [(hslab s z hs h).2]
  constructor
  · intro s t hs hst
    have hI := (hslab s t hs hst).1.absolutelyContinuousOnInterval_intervalIntegral
      (Set.left_mem_uIcc : s ∈ Set.uIcc s t)
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => W a w s) s t :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    apply (hconst.sub hI).congr
    intro z hz
    exact hprim hs ((Set.uIcc_of_le hst.le ▸ hz : z ∈ Set.Icc s t).1)
  · have hlocal (q r : ℚ) : ∀ᵐ z : ℝ, 0 < (q:ℝ) → z ∈ Set.Ioo (q:ℝ) (r:ℝ) →
        HasDerivAt (W a w) (-density a w z) z := by
      by_cases hh : 0 < (q:ℝ) ∧ (q:ℝ) < (r:ℝ)
      · filter_upwards [(hslab _ _ hh.1 hh.2).1.ae_hasDerivAt_integral] with z h _ hz
        rw [Set.uIcc_of_le hh.2.le] at h
        have hD := (h ⟨hz.1.le,hz.2.le⟩ q ⟨le_rfl,hh.2.le⟩).const_sub (W a w q)
        apply (hD.congr_of_eventuallyEq ?_)
        filter_upwards [Ioi_mem_nhds hz.1] with y hy
        exact (hprim hh.1 hy.le).symm
      · exact ae_of_all _ (fun z hq hz => (hh ⟨hq,hz.1.trans hz.2⟩).elim)
    filter_upwards [ae_all_iff.mpr (fun q => ae_all_iff.mpr (hlocal q))] with z h hz
    obtain ⟨q,hq,hqz⟩ := exists_rat_btwn hz
    obtain ⟨r,hzr,_⟩ := exists_rat_btwn (show z < z+1 by linarith)
    exact h q r hq ⟨hqz,hzr⟩

private theorem W_pos (hd : 3 ≤ d) (hw : ValidWeights w) {t : ℝ} (ht : 0 < t) :
    0 < W a w t := by
  have hg := geometry a w hd hw ht
  rw [hg.2.2.2]
  exact mul_pos omega_pos (pow_pos hg.2.2.1 _)

private theorem W_antitone (hd : 3 ≤ d) (hw : ValidWeights w) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) : W a w t ≤ W a w s :=
  ENNReal.toReal_mono (geometry a w hd hw hs).1.measure_lt_top.ne
    (measure_mono (fun _ h => (ENNReal.ofReal_le_ofReal hst).trans h))

-- Cauchy–Schwarz here follows by integrating the nonnegative square (A*g-C)^2/g.

theorem level_inequalities (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → ((d : ℝ) * omega d * rad a w t ^ (d-1)) ^ 2 ≤ area a w t ^ 2 ∧
      area a w t ^ 2 ≤ (d : ℝ) * (d-2 : ℝ) * omega d * (-deriv (W a w) t) := by
  filter_upwards [ae_regular a w hd hw hS,(level_derivative a w hd hw hZ hC).2] with t hreg hder
  intro ht
  have hr := hreg ht
  have hD := (hder ht).deriv
  have hg := geometry a w hd hw ht
  have hf := regular_frontier a w hd hw ht hr
  let μ := surface (level a w t)
  let g := fun x => ‖gradient (u a w) x‖
  let A := area a w t
  let C := (d:ℝ) * (d-2:ℝ) * omega d
  have hdreal : (2:ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  have hC : 0 < C := mul_pos (mul_pos (by linarith) (by linarith)) omega_pos
  have hcpt : IsCompact (level a w t) := hf ▸ hg.1.of_isClosed_subset isClosed_frontier hg.1.isClosed.frontier_subset
  have hfin := hF t ht hr
  let : IsFiniteMeasure μ := ⟨hfin⟩
  have hcont : ContinuousOn g (level a w t) := by
    intro x hx
    exact (((InnerProductSpace.toDual ℝ (Space d)).symm.continuous.continuousAt.comp
      (f := fderiv ℝ (u a w)) (u_analytic a w x hx.1).fderiv.continuousAt).norm).continuousWithinAt
  have hgp (x : Space d) (hx : x ∈ level a w t) : 0 < g x := norm_pos_iff.mpr (hr x hx)
  have hgi := surface_integrable hcpt hfin hcont
  have hiv := surface_integrable hcpt hfin (hcont.inv₀ (fun x hx => (hgp x hx).ne'))
  have hflux : ∫ x, g x ∂μ = C := flux_identity a w hd hw hG hB hA ht hr
  have hreal : μ.real Set.univ = A := rfl
  constructor
  · have hiso := hI _ hg.1 hg.1.measurableSet
    rw [hf] at hiso
    have hbase : 0 < W a w t / omega d := div_pos (W_pos a w hd hw ht) omega_pos
    have hrad : rad a w t ^ (d-1) = (W a w t / omega d) ^ (((d:ℝ)-1)/d) := by
      rw [rad, ← Real.rpow_mul_natCast hbase.le, Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      congr 1
      ring
    rw [hrad]
    apply pow_le_pow_left₀ (by positivity [omega_pos (d := d)]) _ 2
    have h := ENNReal.toReal_mono hfin.ne hiso
    change (ENNReal.ofReal ((d:ℝ)*omega d*(W a w t/omega d)^(((d:ℝ)-1)/d))).toReal ≤ area a w t at h
    rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (omega_pos (d := d)).le)
      (Real.rpow_nonneg hbase.le _))] at h
    exact h
  · have hnon : 0 ≤ ∫ x, A^2 * g x - 2*A*C + C^2 * (g x)⁻¹ ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [surface_ae hcpt.measurableSet] with x hx
      have hpos := hgp x hx
      change (0:ℝ) ≤ A^2 * g x - 2*A*C + C^2 * (g x)⁻¹
      apply (mul_le_mul_iff_left₀ hpos).mp
      field_simp
      nlinarith [sq_nonneg (A*g x-C)]
    have hi₁ : Integrable (fun x => A^2 * g x) μ := hgi.const_mul _
    have hi₂ : Integrable (fun x : Space d => 2*A*C) μ := integrable_const _
    have hi₃ : Integrable (fun x => C^2 * (g x)⁻¹) μ := hiv.const_mul _
    have hi₄ : Integrable (fun x => A^2 * g x - 2*A*C) μ := hi₁.sub hi₂
    rw [integral_add hi₄ hi₃,
      integral_sub hi₁ hi₂, integral_const_mul, integral_const_mul,
      hflux, integral_const, hreal, smul_eq_mul] at hnon
    rw [hD,neg_neg]
    change A^2 ≤ C * (∫ x, (g x)⁻¹ ∂μ)
    apply (mul_le_mul_iff_right₀ hC).mp
    rw [integral_const_mul (C^2) (fun x => (g x)⁻¹)] at hnon
    linarith only [hnon]

theorem scaled_derivative (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → 1 ≤ deriv (fun z => rad a w z ^ (2 - (d : ℝ))) t := by
  filter_upwards [(level_derivative a w hd hw hZ hC).2,
    level_inequalities a w hd hw hI hF hG hB hA hS hZ hC] with t hDt hIneq
  intro ht
  have rpos := (geometry a w hd hw ht).2.2.1
  have hbase := div_pos (W_pos a w hd hw ht) (omega_pos (d := d))
  have hDr : DifferentiableAt ℝ (rad a w) t :=
    (((hDt ht).div_const (omega d)).rpow_const (p := 1/(d:ℝ)) (Or.inl hbase.ne')).differentiableAt
  have hloc : W a w =ᶠ[𝓝 t] (fun z => omega d * rad a w z ^ d) :=
    (eventually_gt_nhds ht).mono fun z hz => (geometry a w hd hw hz).2.2.2
  have hW := ((hDr.hasDerivAt.pow d).const_mul (omega d)).congr_of_eventuallyEq hloc
  have hDpow := hDr.hasDerivAt.rpow_const (p := 2-(d:ℝ)) (Or.inl rpos.ne')
  rw [hDpow.deriv]
  have hex : (2-(d:ℝ))-1 = -((d-1 : ℕ):ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
  rw [hex, Real.rpow_neg rpos.le, Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos rpos (d-1))).2
  have h := (hIneq ht).1.trans (hIneq ht).2
  rw [hW.deriv] at h
  let A := (d:ℝ) * omega d * rad a w t ^ (d-1)
  have hdpos : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hA : 0 < A := mul_pos (mul_pos hdpos omega_pos) (pow_pos rpos _)
  have hb : A * (1 * rad a w t ^ (d-1)) ≤ A * (deriv (rad a w) t * (2-(d:ℝ))) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdpos (omega_pos (d := d)))).mp
    dsimp [A]
    linarith only [h]
  exact (mul_le_mul_iff_right₀ hA).mp hb

private theorem vol_closed_ball (p : Space d) {r : ℝ} (hr : 0 ≤ r) :
    vol (closedBall p r) = omega d * r ^ d := by
  simpa [vol, omega, MeasureTheory.measureReal_def, finrank_euclideanSpace_fin, mul_comm]
    using volume.addHaar_real_closedBall p hr

private theorem compact_in_super (hd : 3 ≤ d) (hw : ValidWeights w) {K : Set (Space d)}
    (hc : IsCompact K) (hn : K.Nonempty) : ∃ t > (0 : ℝ), K ⊆ super a w t := by
  obtain ⟨x,hx,hm⟩ := hc.exists_isMinOn hn (continuous_potential a w).continuousOn
  obtain ⟨i,hi,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := w)
    (by rw [hw.2]; norm_num)
  have hp : 0 < potential a w x := by
    by_cases hoff : x ∈ off a
    · rw [off_formula a w hd hw hoff, ENNReal.ofReal_pos]
      exact Finset.sum_pos (fun k _ => mul_pos (hw.1 k) (Real.rpow_pos_of_pos (off_dist_pos a hoff k) _)) ⟨i,hi⟩
    · obtain ⟨k,rfl⟩ : x ∈ Set.range a := by simpa [off] using hoff
      rw [at_mark a w hd hw k]
      exact ENNReal.zero_lt_top
  obtain ⟨q,hq,hq'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  refine ⟨q, by exact_mod_cast hq, fun y hy => ?_⟩
  change ENNReal.ofReal (q : ℝ) ≤ potential a w y
  rw [ENNReal.ofReal_coe_nnreal]
  exact hq'.le.trans (hm hy)

theorem exhaustion (hd : 3 ≤ d) (hw : ValidWeights w) :
    (⋃ t ∈ Set.Ioi (0 : ℝ), super a w t) = Set.univ ∧
    Tendsto (fun t => rad a w t ^ (2 - (d : ℝ))) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨t,ht,hsub⟩ := compact_in_super a w hd hw (isCompact_singleton (x := x)) (Set.singleton_nonempty x)
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hsub (Set.mem_singleton x)⟩⟩
  · have he : 0 < (d : ℝ)-2 := sub_pos.mpr (by exact_mod_cast (show 2 < d by omega))
    have hg : Tendsto (rad a w) (𝓝[>] 0) atTop := by
      apply Filter.tendsto_atTop.mpr
      intro B
      let r := max 1 B
      have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      obtain ⟨t,ht,hsub⟩ := compact_in_super a w hd hw (isCompact_closedBall (0 : Space d) r)
        ⟨0, mem_closedBall_self hr.le⟩
      filter_upwards [Ioo_mem_nhdsGT ht] with z hz
      have hgz := geometry a w hd hw hz.1
      have hinc : closedBall (0 : Space d) r ⊆ super a w z := fun x hx =>
        (ENNReal.ofReal_le_ofReal hz.2.le).trans (hsub hx)
      have hv : vol (closedBall (0 : Space d) r) ≤ W a w z :=
        ENNReal.toReal_mono hgz.1.measure_lt_top.ne (measure_mono hinc)
      rw [vol_closed_ball _ hr.le,hgz.2.2.2] at hv
      exact (le_max_right 1 B).trans ((pow_le_pow_iff_left₀ hr.le hgz.2.2.1.le (by omega : d ≠ 0)).mp
        ((mul_le_mul_iff_right₀ (omega_pos (d := d))).mp hv))
    simpa only [Function.comp_def,neg_sub] using (tendsto_rpow_neg_atTop he).comp hg

theorem integrated (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) {t : ℝ} (ht : 0 < t) :
    t ≤ rad a w t ^ (2 - (d : ℝ)) := by
  let f := fun z => rad a w z ^ (2-(d:ℝ))
  let P := fun x : ℝ => ((x / omega d) ^ (1/(d:ℝ))) ^ (2-(d:ℝ))
  have hder := scaled_derivative a w hd hw hI hF hG hB hA hS hZ hC
  -- On each compact interval of positive thresholds, W stays away from zero.
  have hline (s : ℝ) (hs : 0 < s) (hst : s < t) : t-s ≤ f t - f s := by
    have hAC := (level_derivative a w hd hw hZ hC).1 s t hs hst
    have hP : ContDiffOn ℝ 1 P (Set.Icc (W a w t) (W a w s)) := by
      intro x hx
      have hx' : 0 < x / omega d := div_pos ((W_pos a w hd hw ht).trans_le hx.1) omega_pos
      exact (((contDiffAt_id.div_const (omega d)).rpow_const_of_ne hx'.ne').rpow_const_of_ne
        (Real.rpow_pos_of_pos hx' _).ne').contDiffWithinAt
    obtain ⟨K,hLip⟩ := hP.exists_lipschitzOnWith one_ne_zero (convex_Icc ..) isCompact_Icc
    have hac : AbsolutelyContinuousOnInterval f s t := by
      apply hLip.comp_absolutelyContinuousOnInterval _ hAC
      intro z hz
      rw [Set.uIcc_of_le hst.le] at hz
      exact ⟨W_antitone a w hd hw (hs.trans_le hz.1) hz.2,W_antitone a w hd hw hs hz.1⟩
    have hm : (fun _ : ℝ => (1:ℝ)) ≤ᵐ[volume.restrict (Set.Icc s t)] deriv f := by
      filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with z h hz
      exact h (hs.trans_le hz.1)
    have h := intervalIntegral.integral_mono_ae_restrict hst.le intervalIntegrable_const
      hac.intervalIntegrable_deriv hm
    simpa [hac.integral_deriv_eq_sub] using h
  change t ≤ f t
  by_contra! h
  have hpos (s : ℝ) (hs : 0 < s) : 0 < f s := Real.rpow_pos_of_pos (geometry a w hd hw hs).2.2.1 _
  obtain ⟨s,hs,hst⟩ := exists_between (sub_pos.mpr h)
  have hs' : s < t := by linarith [hpos t ht]
  linarith [hline s hs hs',hpos s hs]

theorem radius_at_threshold (hd : 3 ≤ d) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (h : R ^ (2 - (d : ℝ)) ≤ r ^ (2 - (d : ℝ))) : r ≤ R := by
  exact (Real.rpow_le_rpow_iff_of_neg hR hr
    (sub_neg.mpr (by exact_mod_cast (show 2 < d by omega)))).mp h

def ray (a b : Space d) (s : ℝ) := a + s • (a-b)

theorem ray_dist (p q : Space d) (hpq : p ≠ q) {s : ℝ} (hs : 0 ≤ s) :
    dist (ray p q s) p < dist (ray p q s) q := by
  have hv : 0 < ‖p-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  have hq : ray p q s - q = (s+1) • (p-q) := by
    rw [add_smul, one_smul, ray]
    abel
  rw [dist_eq_norm, dist_eq_norm, hq]
  simp only [ray, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs, abs_of_nonneg (show 0 ≤ s+1 by linarith)]
  nlinarith

private theorem continuous_ray (p q : Space d) : Continuous (ray p q) := by
  unfold ray
  fun_prop

theorem last_point (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) : ∃ s ≥ (0 : ℝ), G a w (ray (a i) (a j) s) = R ∧
      ∀ v > s, R < G a w (ray (a i) (a j) v) := by
  let f := fun s => G a w (ray (a i) (a j) s)
  have hf : Continuous f := (continuous_product a w hw).comp (continuous_ray _ _)
  have h0 : f 0 = 0 := by simp [f, ray, product_at_mark a w hw]
  have hescape : Tendsto (ray (a i) (a j)) atTop (Bornology.cobounded _) := by
    apply (Metric.tendsto_dist_right_atTop_iff (a i)).mp
    apply ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_mul_const
      (norm_pos_iff.mpr (sub_ne_zero.mpr hij))).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    simp [ray, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hfar (k : Fin n) : ∀ᶠ s in atTop, R+1 ≤ dist (ray (a i) (a j) s) (a k) :=
    ((Metric.tendsto_dist_right_atTop_iff _).2 hescape).eventually_ge_atTop _
  have hout : ∀ᶠ s in atTop, R < f s := by
    filter_upwards [Filter.eventually_all.mpr hfar] with s hs
    calc R < R + 1 := by linarith
         _ = ∏ k, (R+1) ^ w k := by
               rw [← Real.rpow_sum_of_pos (by linarith : 0 < R+1), hw.2, Real.rpow_one]
         _ ≤ f s := Finset.prod_le_prod₀ (fun k _ => Real.rpow_nonneg (by linarith) _)
               (fun k _ => Real.rpow_le_rpow (by linarith) (hs k) (hw.1 k).le)
  let S : Set ℝ := Set.Ici 0 ∩ {s | f s ≤ R}
  have hS : IsClosed S := isClosed_Ici.inter (isClosed_le hf continuous_const)
  have hn : S.Nonempty := ⟨0, Set.self_mem_Ici, h0.le.trans hR.le⟩
  obtain ⟨B,hB⟩ := eventually_atTop.mp hout
  have hb : BddAbove S := ⟨B, fun s hs => le_of_not_ge (fun h => (hB _ h).not_ge hs.2)⟩
  have hm := hS.csSup_mem hn hb
  have hlast (v : ℝ) (hv : sSup S < v) : R < f v := by
    by_contra! h
    exact hv.not_ge (le_csSup hb (show v ∈ S from ⟨hm.1.trans hv.le,h⟩))
  refine ⟨sSup S, hm.1, le_antisymm hm.2 ?_, hlast⟩
  by_contra! h
  have he : ∀ᶠ v in 𝓝[>] (sSup S), f v < R :=
    nhdsWithin_le_nhds (hf.continuousAt.eventually (Iio_mem_nhds h))
  obtain ⟨v,hv,hv'⟩ := (he.and (self_mem_nhdsWithin : Set.Ioi (sSup S) ∈ 𝓝[>] (sSup S))).exists
  exact hv.not_gt (hlast v hv')

theorem strict_amgm (hd : 3 ≤ d) (hw : ValidWeights w) {x} (hx : x ∈ off a)
    {i j : Fin n} (hij : dist x (a i) ≠ dist x (a j)) :
    G a w x ^ (2 - (d : ℝ)) < u a w x := by
  rw [pow_product]
  apply (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos Finset.univ w
    (fun k => dist x (a k) ^ (2 - (d : ℝ))) (fun k _ => hw.1 k) hw.2
    (fun k _ => Real.rpow_nonneg dist_nonneg _)).2
  refine ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, ?_⟩
  intro h
  apply hij
  exact (Real.rpow_left_inj dist_nonneg dist_nonneg
    (sub_ne_zero.mpr (ne_of_lt (by exact_mod_cast (show 2 < d by omega))))).mp h

theorem beyond_last (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hy : G a w (ray (a i) (a j) s) = R)
    (hlast : ∀ v > s, R < G a w (ray (a i) (a j) v)) :
    ∀ᶠ v in 𝓝[>] s, R < G a w (ray (a i) (a j) v) ∧
      R ^ (2 - (d : ℝ)) < u a w (ray (a i) (a j) v) := by
  let y := ray (a i) (a j) s
  have hoff : y ∈ off a := off_of_product_pos a w hw (hy ▸ hR)
  have hu : ContinuousAt (u a w) y := by
    apply tendsto_finsetSum
    intro k _
    apply continuousAt_const.mul
    apply ContinuousAt.rpow_const
    · fun_prop
    · exact Or.inl (off_dist_pos a hoff k).ne'
  have hgap := strict_amgm a w hd hw hoff (ray_dist _ _ hij hs).ne
  rw [hy] at hgap
  have hneigh : ∀ᶠ v in 𝓝[>] s, R ^ (2-(d:ℝ)) < u a w (ray (a i) (a j) v) :=
    nhdsWithin_le_nhds ((hu.comp (f := ray (a i) (a j)) (x := s) (continuous_ray _ _).continuousAt).eventually (Ioi_mem_nhds hgap))
  filter_upwards [hneigh, (self_mem_nhdsWithin : Set.Ioi s ∈ 𝓝[>] s)] with v h1 h2
  exact ⟨hlast v h2,h1⟩

theorem strict_ball (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) : ∃ z : Space d, ∃ ε > (0 : ℝ),
      ball z ε ⊆ super a w (R ^ (2 - (d : ℝ))) \ solid a w R := by
  obtain ⟨s,hs,hy,hlast⟩ := last_point a w hw hij hR
  obtain ⟨v,hv,hU⟩ := (beyond_last a w hd hw hij hs hR hy hlast).exists
  let z := ray (a i) (a j) v
  have hoff : z ∈ off a := off_of_product_pos a w hw (hR.trans hv)
  have hpos := Real.rpow_pos_of_pos hR (2-(d:ℝ))
  have hpot : ENNReal.ofReal (R ^ (2-(d:ℝ))) < potential a w z := by
    rw [off_formula a w hd hw hoff]
    exact (ENNReal.ofReal_lt_ofReal_iff (hpos.trans hU)).2 hU
  have hnear := ((continuous_product a w hw).continuousAt.eventually (Ioi_mem_nhds hv)).and
    ((continuous_potential a w).continuousAt.eventually (Ioi_mem_nhds hpot))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨z,ε,hε,fun y h => ⟨(hball h).2.le,(hball h).1.not_ge⟩⟩

theorem strict_volume (hd : 3 ≤ d) (hw : ValidWeights w) {i j : Fin n} (hij : a i ≠ a j)
    {R : ℝ} (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ volume (super a w (R ^ (2 - (d : ℝ)))) < ⊤ ∧
    vol (solid a w R) < W a w (R ^ (2 - (d : ℝ))) := by
  let K := solid a w R
  let U := super a w (R ^ (2-(d:ℝ)))
  have hKU : K ⊆ U := inclusion a w hd hw hR
  have hU : volume U < ⊤ := (geometry a w hd hw (Real.rpow_pos_of_pos hR _)).1.measure_lt_top
  have hK := measure_lt_top_of_subset hKU hU.ne
  obtain ⟨z, ε, hε, hb⟩ := strict_ball a w hd hw hij hR
  have hdis : Disjoint K (ball z ε) := Set.disjoint_left.mpr fun y hy h => (hb h).2 hy
  have hsub : K ∪ ball z ε ⊆ U := Set.union_subset hKU (fun _ h => (hb h).1)
  refine ⟨hK,hU,(ENNReal.toReal_lt_toReal hK.ne hU.ne).2 ?_⟩
  calc volume K < volume K + volume (ball z ε) := ENNReal.lt_add_right hK.ne
          (measure_ball_pos volume z hε).ne'
       _ = volume (K ∪ ball z ε) := (measure_union hdis isOpen_ball.measurableSet).symm
       _ ≤ volume U := measure_mono hsub

theorem coincident {p : Space d} (hw : ValidWeights w) (hp : ∀ i, a i = p) {R : ℝ} :
    G a w = (fun x => dist x p) ∧ solid a w R = closedBall p R := by
  have hG : G a w = (fun x => dist x p) := by
    funext x
    unfold G
    simp_rw [hp]
    rw [← Real.rpow_sum_of_nonneg dist_nonneg (fun i _ => (hw.1 i).le), hw.2, Real.rpow_one]
  refine ⟨hG, ?_⟩
  ext x
  change G a w x ≤ R ↔ dist x p ≤ R
  rw [hG]

theorem direct_bound_eq (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) {R : ℝ} (hR : 0 < R) :
    volume (solid a w R) < ⊤ ∧ vol (solid a w R) ≤ omega d * R ^ d ∧
    (vol (solid a w R) = omega d * R ^ d ↔ ∃ p : Space d, ∀ i, a i = p) := by
  let t := R ^ (2-(d:ℝ))
  have ht : 0 < t := Real.rpow_pos_of_pos hR _
  have hg := geometry a w hd hw ht
  have hr := radius_at_threshold hd hR hg.2.2.1 (integrated a w hd hw hI hF hG hB hA hS hZ hC ht)
  have hupper : W a w t ≤ omega d * R^d := by
    rw [hg.2.2.2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.2.2.1.le hr _) omega_pos.le
  have hsub := inclusion a w hd hw hR
  refine ⟨measure_lt_top_of_subset hsub hg.1.measure_lt_top.ne,
    (ENNReal.toReal_mono hg.1.measure_lt_top.ne (measure_mono hsub)).trans hupper, ?_⟩
  constructor
  · intro heq
    obtain ⟨i,_,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := w)
      (by rw [hw.2]; norm_num)
    refine ⟨a i, fun j => ?_⟩
    by_contra h
    have hs := (strict_volume a w hd hw h hR).2.2
    exact (hs.trans_le hupper).ne heq
  · rintro ⟨p,hp⟩
    rw [(coincident a w hw hp).2, vol_closed_ball _ hR.le]

/-- The scaled equal-volume radius is absolutely continuous on every closed
interval of strictly positive levels. -/
theorem scaled_radius_absolute_continuity (hd : 3 ≤ d) (hw : ValidWeights w)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    AbsolutelyContinuousOnInterval (fun z => rad a w z ^ (2-(d:ℝ))) s t := by
  let P := fun x : ℝ => ((x / omega d) ^ (1/(d:ℝ))) ^ (2-(d:ℝ))
  have hP : ContDiffOn ℝ 1 P (Set.Icc (W a w t) (W a w s)) := by
    intro x hx
    have hx' : 0 < x / omega d := div_pos ((W_pos a w hd hw (hs.trans hst)).trans_le hx.1) omega_pos
    exact (((contDiffAt_id.div_const (omega d)).rpow_const_of_ne hx'.ne').rpow_const_of_ne
      (Real.rpow_pos_of_pos hx' _).ne').contDiffWithinAt
  obtain ⟨K,hLip⟩ := hP.exists_lipschitzOnWith one_ne_zero (convex_Icc ..) isCompact_Icc
  apply hLip.comp_absolutelyContinuousOnInterval _ ((level_derivative a w hd hw hZ hC).1 s t hs hst)
  intro z hz
  rw [Set.uIcc_of_le hst.le] at hz
  exact ⟨W_antitone a w hd hw (hs.trans_le hz.1) hz.2,W_antitone a w hd hw hs hz.1⟩

/-- The two surface integrals appearing in the level-set Cauchy–Schwarz inequality. -/
theorem level_surface_cauchy_schwarz (hd : 3 ≤ d) (hw : ValidWeights w)
    (hI : SharpIso d) (hF : SurfaceFinite a w) (hG : PuncturedGauss a w)
    (hB : BallGauss d) (hA : SphereArea d) (hS : SardScalar d)
    (hZ : AnalyticNull d) (hC : CoareaSlabs a w) :
    ∀ᵐ t : ℝ, 0 < t → area a w t ^ 2 ≤
      (∫ x, ‖gradient (u a w) x‖ ∂(surface (level a w t))) *
      (∫ x, ‖gradient (u a w) x‖⁻¹ ∂(surface (level a w t))) := by
  filter_upwards [ae_regular a w hd hw hS, (level_derivative a w hd hw hZ hC).2,
    level_inequalities a w hd hw hI hF hG hB hA hS hZ hC] with t hr hD hineq
  intro ht
  rw [flux_identity a w hd hw hG hB hA ht (hr ht)]
  simpa only [(hD ht).deriv, neg_neg, density] using (hineq ht).2

end Flux
end ErdosVolume

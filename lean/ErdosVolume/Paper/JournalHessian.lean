module

public import ErdosVolume.Paper.Illustrations

@[expose] public section

/-! The two Hessian eigenspaces and the direction estimate in the inradius proof.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/

noncomputable section
open Filter
open scoped Topology

namespace ErdosVolume.Paper
open Stability

private theorem hasFDerivAt_norm_off_zero (w : X) (hw : w ≠ 0) :
    HasFDerivAt (norm : X → ℝ) (‖w‖⁻¹ • innerSL ℝ w) w := by
  have hn := (norm_pos_iff.mpr hw).ne'
  have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.sqrt (by simp [hn])
  convert h using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg y)).symm
  · ext v
    simp [Real.sqrt_sq (norm_nonneg w),innerSL_apply_apply]
    field_simp

/-- The Hessian of a radial function has a scalar part and a radial rank-one part. -/
private theorem radial_hessian (f : ℝ → ℝ) (w : X) (hw : w ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖w‖) :
    let A := fun r : ℝ => deriv f r / r
    (A ‖w‖ + deriv A ‖w‖ * ‖w‖ = deriv (deriv f) ‖w‖) ∧
    ∀ v z : X, hess (fun y : X => f ‖y‖) w v z =
      A ‖w‖ * inner ℝ v z + (deriv A ‖w‖ / ‖w‖) * inner ℝ w v * inner ℝ w z := by
  let A := fun r : ℝ => deriv f r / r
  let s := ‖w‖
  have sp : 0 < s := norm_pos_iff.mpr hw
  have hdf : DifferentiableAt ℝ (deriv f) s :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : DifferentiableAt ℝ A s := hdf.div differentiableAt_id sp.ne'
  constructor
  · have eq : (fun r : ℝ => A r * r) =ᶠ[𝓝 s] deriv f := by
      filter_upwards [eventually_ne_nhds sp.ne'] with r hr
      exact div_mul_cancel₀ _ hr
    have d := hA.hasDerivAt.mul (hasDerivAt_id s)
    have hd : deriv (fun r : ℝ => A r * r) s = deriv A s * s + A s := by
      simpa [Pi.mul_def] using d.deriv
    rw [eq.deriv_eq] at hd
    change A s + deriv A s * s = deriv (deriv f) s
    linarith
  · intro v z
    let J : X →L[ℝ] X →L[ℝ] ℝ := innerSL ℝ
    have grad : fderiv ℝ (fun y : X => f ‖y‖) =ᶠ[𝓝 w] (fun y => A ‖y‖ • J y) := by
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (hf.eventually (by norm_num)),
        eventually_ne_nhds hw] with y hfy hy
      change ContDiffAt ℝ 2 f ‖y‖ at hfy
      have d := (hfy.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_norm_off_zero y hy)
      simpa [A,J,smul_smul,div_eq_mul_inv,Function.comp_def] using d.fderiv
    have da := hA.hasDerivAt.comp_hasFDerivAt w (hasFDerivAt_norm_off_zero w hw)
    unfold hess
    rw [grad.fderiv_eq]
    erw [(da.smul J.hasFDerivAt).fderiv]
    change A s * inner ℝ v z + (deriv A s * (s⁻¹ * inner ℝ w v)) * inner ℝ w z =
      A s * inner ℝ v z + (deriv A s / s) * inner ℝ w v * inner ℝ w z
    ring

/-- The radial unit vector and each vector orthogonal
to it are Hessian eigenvectors, expressed by testing the bilinear Hessian against any z. -/
theorem journal_hessian_eigendirections (x a : X) (hs : 0 < ‖x-a‖) :
    let s := ‖x-a‖
    let u := direction (x-a)
    ‖u‖ = 1 ∧
    (∀ z : X, hess (fun y : X => phi ‖x-y‖) a u z = deriv (deriv phi) s * inner ℝ u z) ∧
    (∀ v : X, inner ℝ u v = 0 → ∀ z : X,
      hess (fun y : X => phi ‖x-y‖) a v z = (deriv phi s / s) * inner ℝ v z) := by
  let w := a-x
  let s := ‖x-a‖
  let u := direction (x-a)
  have hw : ‖w‖ = s := norm_sub_rev _ _
  have ws : w = (-s) • u := by simp [w,u,s,direction,smul_smul,hs.ne',neg_sub]
  have un : ‖u‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp hs)
  have smooth : ContDiffAt ℝ 2 phi s := by
    exact ((contDiffAt_id.log hs.ne').add (contDiffAt_id.inv hs.ne')).sub contDiffAt_const
  have hh := radial_hessian phi w (norm_pos_iff.mp (show 0 < ‖w‖ by rw [hw]; exact hs)) (hw.symm ▸ smooth)
  rw [hw] at hh
  let A := fun r : ℝ => deriv phi r / r
  have form (v z : X) : hess (fun y : X => phi ‖x-y‖) a v z =
      A s * inner ℝ v z + (deriv A s / s) * inner ℝ w v * inner ℝ w z := by
    have eq : (fun y : X => phi ‖x-y‖) = (fun y => (fun t : X => phi ‖t‖) (y-x)) :=
      funext (fun y => congrArg phi (norm_sub_rev x y))
    rw [eq]
    unfold hess
    rw [show fderiv ℝ (fun y : X => phi ‖y-x‖) = (fun y => fderiv ℝ (fun t : X => phi ‖t‖) (y-x)) from
      funext (fun y => fderiv_comp_sub (f := fun t : X => phi ‖t‖) (x := y) x), fderiv_comp_sub]
    exact hh.2 v z
  refine ⟨un,fun z => ?_,fun v hv z => ?_⟩
  · rw [form,ws,real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq,un]
    change _ = deriv (deriv phi) s * inner ℝ u z
    rw [← hh.1]
    change A s * inner ℝ u z + (deriv A s / s) * (-s * 1^2) * (-s * inner ℝ u z) =
      (A s + deriv A s * s) * inner ℝ u z
    field_simp [show s ≠ 0 from hs.ne']
  · change inner ℝ u v = 0 at hv
    rw [form,ws,real_inner_smul_left,hv]
    simp [A,s]

private theorem norm_to_direction (y : X) (hy : y ≠ 0) :
    ‖y-direction y‖ = |‖y‖-1| := by
  have e : y - direction y = (‖y‖-1) • direction y := by
    rw [sub_smul,one_smul]
    simp [direction,smul_smul,norm_ne_zero_iff.mpr hy]
  rw [e,norm_smul,show ‖direction y‖ = 1 from norm_smul_inv_norm (𝕜 := ℝ) hy,
    Real.norm_eq_abs,mul_one]

/-- Both shell bounds hold with constants independent
of x, a and δ, including the degenerate shell at δ = 0. -/
theorem journal_shell_direction (δ : ℝ) (hδ : δ < 1/8) (x a : X) (hx : x ∈ ann δ)
    (ha : ‖a‖ ≤ δ) :
    |‖x-a‖-1| ≤ 2*δ ∧ ‖direction (x-a)-direction x‖ ≤ 4*δ := by
  obtain ⟨hlo,hhi⟩ := hx
  have hnorm : |‖x‖-1| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
  have hdist : |‖x-a‖-‖x‖| ≤ ‖a‖ := by
    simpa [sub_sub_cancel_left] using abs_norm_sub_norm_le (x-a) x
  have hrad : |‖x-a‖-1| ≤ 2*δ := abs_le.mpr ⟨by linarith [(abs_le.mp hdist).1],by linarith [(abs_le.mp hdist).2]⟩
  have xn : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have yn : x-a ≠ 0 := norm_pos_iff.mp (by linarith [(abs_le.mp hrad).1])
  refine ⟨hrad,?_⟩
  have split : direction (x-a)-direction x =
      (direction (x-a)-(x-a)) + ((x-a)-x) + (x-direction x) := by abel
  rw [split]
  calc _ ≤ (‖direction (x-a)-(x-a)‖ + ‖(x-a)-x‖) + ‖x-direction x‖ :=
             (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
       _ ≤ 4*δ := by
             rw [norm_sub_rev (direction (x-a)),norm_to_direction _ yn,norm_to_direction _ xn]
             simp only [sub_sub_cancel_left,norm_neg]
             linarith

end ErdosVolume.Paper

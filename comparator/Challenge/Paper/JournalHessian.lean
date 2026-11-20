import Challenge.Paper.Illustrations

noncomputable section

open Filter

open scoped Topology

namespace ErdosVolume.Paper

open Stability

theorem journal_hessian_eigendirections (x a : X) (hs : 0 < ‖x-a‖) :
    let s := ‖x-a‖
    let u := direction (x-a)
    ‖u‖ = 1 ∧
    (∀ z : X, hess (fun y : X => phi ‖x-y‖) a u z = deriv (deriv phi) s * inner ℝ u z) ∧
    (∀ v : X, inner ℝ u v = 0 → ∀ z : X,
      hess (fun y : X => phi ‖x-y‖) a v z = (deriv phi s / s) * inner ℝ v z) := by sorry

theorem journal_shell_direction (δ : ℝ) (hδ : δ < 1/8) (x a : X) (hx : x ∈ ann δ)
    (ha : ‖a‖ ≤ δ) :
    |‖x-a‖-1| ≤ 2*δ ∧ ‖direction (x-a)-direction x‖ ≤ 4*δ := by sorry

end ErdosVolume.Paper

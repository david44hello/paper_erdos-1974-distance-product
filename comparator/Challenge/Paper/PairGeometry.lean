import Challenge.Paper.Illustrations

noncomputable section
open Metric Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace ErdosVolume.Paper

def pairRegion {X : Type*} [PseudoMetricSpace X] (p q : X) : Set X :=
  {x | dist x p * dist x q ≤ 1}

theorem pair_axis_reach {d : ℕ} (m e : Space d) (he : ‖e‖ = 1)
    (t : ℝ) (hp : 0 < t) (ht : t ≤ 1) (s : ℝ) :
    let x := m + s • e
    let p := m + t • e
    let q := m + (-t) • e
    dist x p = |s-t| ∧ dist x q = |s+t| ∧ dist x p * dist x q = |s^2-t^2| ∧
    (x ∈ pairRegion p q ↔ t^2-1 ≤ s^2 ∧ s^2 ≤ t^2+1) ∧
    (x ∈ pairRegion p q ↔ |s| ≤ Real.sqrt (1+t^2)) ∧ 1 < Real.sqrt (1+t^2) := by sorry

theorem pair_transverse_reach {d : ℕ} (m e u : Space d) (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (horth : inner ℝ u e = 0) (t : ℝ) (hp : 0 < t) (ht : t ≤ 1) (b : ℝ) :
    let x := m+b • u
    let p := m+t • e
    let q := m+(-t) • e
    dist x p = Real.sqrt (b^2+t^2) ∧ dist x q = Real.sqrt (b^2+t^2) ∧
    dist x p * dist x q = b^2+t^2 ∧
    (x ∈ pairRegion p q ↔ |b| ≤ Real.sqrt (1-t^2)) ∧
    Real.sqrt (1-t^2) < 1 ∧ (t = 1 → (x ∈ pairRegion p q ↔ b = 0)) := by sorry

theorem line_pair_interval (m t : ℝ) (ht : 0 ≤ t) (h₁ : t ≤ 1) :
    let B := Real.sqrt (1+t^2)
    pairRegion (m-t) (m+t) = Icc (m-B) (m+B) ∧
    volume.real (pairRegion (m-t) (m+t)) = 2*B ∧
    StrictMonoOn (fun s : ℝ => 2*Real.sqrt (1+s^2)) (Icc 0 1) := by sorry

theorem line_pair_two_intervals (m t : ℝ) (ht : 1 < t) :
    let A := Real.sqrt (t^2-1)
    let B := Real.sqrt (t^2+1)
    Disjoint (Icc (m-B) (m-A)) (Icc (m+A) (m+B)) ∧
    pairRegion (m-t) (m+t) = Icc (m-B) (m-A) ∪ Icc (m+A) (m+B) ∧
    volume.real (pairRegion (m-t) (m+t)) = 2*(B-A) ∧ 2*(B-A) = 4/(B+A) ∧
    4/(B+A) < 2*Real.sqrt 2 := by sorry

theorem line_pair_optimum (p q : ℝ) :
    volume.real (pairRegion p q) ≤ 2*Real.sqrt 2 ∧
    (volume.real (pairRegion p q) = 2*Real.sqrt 2 ↔ dist p q = 2) := by sorry

end ErdosVolume.Paper

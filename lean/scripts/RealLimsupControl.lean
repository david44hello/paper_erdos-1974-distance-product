import Mathlib
/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
open Filter Set
-- On the real numbers an unbounded sequence can have a computed limsup of zero.
example : Filter.limsup (fun n : ℕ => (n : ℝ)) atTop = 0 := by
  change sInf {x : ℝ | ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ x} = 0
  have h : {x : ℝ | ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ x} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt x
    obtain ⟨m, hm⟩ := eventually_atTop.mp hx
    have he := hm (max n m) (le_max_right _ _)
    have hi : (n : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast le_max_left n m
    exact hn.not_ge (hi.trans he)
  rw [h, Real.sInf_empty]

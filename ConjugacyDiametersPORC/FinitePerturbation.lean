import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Small perturbations on a finite nonnegative vector

A direction vanishing at zero coordinates can be scaled in both directions
while retaining nonnegativity.
-/

namespace ConjugacyDiametersPORC

theorem exists_pos_le_finite {ι : Type*} [Finite ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ d i := by
  classical
  let _ := Fintype.ofFinite ι
  have h (s : Finset ι) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ d i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ε, hε, hs⟩ := ih
      refine ⟨min ε (d i), lt_min hε (hd i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨ε, hε, hs⟩ := h Finset.univ
  exact ⟨ε, hε, fun i => hs i (Finset.mem_univ i)⟩

theorem exists_two_sided_perturbation {ι : Type*} [Finite ι] (x v : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i, x i = 0 → v i = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε * |v i| ≤ x i := by
  have hlocal (i : ι) : ∃ d : ℝ, 0 < d ∧ d * |v i| ≤ x i := by
    by_cases hxi : x i = 0
    · exact ⟨1, by norm_num, by simp [hv i hxi, hxi]⟩
    · have hxp : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
      have hp : 0 < |v i| + 1 := by positivity
      let d := x i / (|v i| + 1)
      have hd : 0 < d := div_pos hxp hp
      have he : d * (|v i| + 1) = x i := div_mul_cancel₀ _ (ne_of_gt hp)
      exact ⟨d, hd, by nlinarith⟩
  choose d hd hmul using hlocal
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_finite d hd
  exact ⟨ε, hε, fun i =>
    (mul_le_mul_of_nonneg_right (hle i) (abs_nonneg (v i))).trans (hmul i)⟩

end ConjugacyDiametersPORC

import ConjugacyDiametersPORC.CycleCuts
import ConjugacyDiametersPORC.GeneratorExpansion
import ConjugacyDiametersPORC.GeneratedGroup
import Mathlib.Tactic.Linarith

/-!
# The transposition part of the diameter lower bound

Each generator has transposition rank `d`. A long even cycle belongs to the
generated group in every degree at least `b + 1`, and has rank at least `n - 2`.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

theorem ConstituentWord.tau_value_le_delta {lam : CycleType} {α : Type*}
    [Fintype α] [DecidableEq α] (w : ConstituentWord lam α) : τ w.value ≤ δ lam w.c := by
  have ht := tau_prod_le_length w.transpositions (fun _ ha => w.transpositions_isSwap ha)
  rw [w.transpositions_prod, w.transpositions_length] at ht
  exact ht

theorem tau_le_factorization_length_mul_d {lam : CycleType} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) : τ g ≤ w.length * lam.d := by
  have ht := (expandWord lam w hw.1).tau_value_le_delta
  rw [expandWord_value, expandWord_delta] at ht
  simpa only [hw.2] using ht

theorem tau_le_L_mul_d (lam : CycleType) {n : ℕ} (g : G lam n) :
    τ (g : SymmetricGroup n) ≤ L lam g * lam.d := by
  obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
  simpa only [hlen] using tau_le_factorization_length_mul_d hw

theorem tau_le_D_mul_d (lam : CycleType) {n : ℕ} (g : G lam n) :
    τ (g : SymmetricGroup n) ≤ D lam n * lam.d :=
  (tau_le_L_mul_d lam g).trans (Nat.mul_le_mul_right _ (L_le_D lam g))

theorem exists_even_cycle_with_tau (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (heven : Even (m - 1)) :
    ∃ g : SymmetricGroup n, sign g = 1 ∧ τ g = m - 1 := by
  have hex : ∃ g : SymmetricGroup n, g.cycleType = ({m} : Multiset ℕ) := by
    rw [exists_with_cycleType_iff]
    exact ⟨by simpa using hmn, by simpa using hm⟩
  obtain ⟨g, hg⟩ := hex
  have ht : τ g = m - 1 := by simp [τ, hg]
  refine ⟨g, ?_, ht⟩
  rw [sign_eq_neg_one_pow_tau, ht]
  exact heven.neg_one_pow

theorem exists_even_longCycle (n : ℕ) (hn : 3 ≤ n) :
    ∃ g : SymmetricGroup n, sign g = 1 ∧ n - 2 ≤ τ g := by
  rcases Nat.even_or_odd n with he | ho
  · have hn' : 2 ≤ n - 1 := by
      obtain ⟨k, hk⟩ := he
      omega
    have hp : Even ((n - 1) - 1) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - 1, by omega⟩
    obtain ⟨g, hg, ht⟩ := exists_even_cycle_with_tau n (n - 1) hn' (by omega) hp
    exact ⟨g, hg, by omega⟩
  · have hp : Even (n - 1) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k, by omega⟩
    obtain ⟨g, hg, ht⟩ := exists_even_cycle_with_tau n n (by omega) (by rfl) hp
    exact ⟨g, hg, by omega⟩

/-- The contribution of the slope `1/d` to the uniform lower bound. -/
theorem degree_le_D_mul_d_add_two (lam : CycleType) {n : ℕ} (hn : lam.b + 1 ≤ n) :
    n ≤ D lam n * lam.d + 2 := by
  have hn₃ : 3 ≤ n := by
    have := lam.two_mul_h_le_b
    have := lam.h_pos
    omega
  obtain ⟨g, hg, ht⟩ := exists_even_longCycle n hn₃
  have hgG : g ∈ G lam n := alternatingGroup_le_G lam hn (mem_alternatingGroup.mpr hg)
  have hbound := tau_le_D_mul_d lam ⟨g, hgG⟩
  change τ g ≤ D lam n * lam.d at hbound
  omega

theorem transposition_diameter_lowerBound (lam : CycleType) {n : ℕ} (hn : lam.b + 1 ≤ n) :
    (n : ℚ) / (lam.d : ℚ) - 2 / (lam.d : ℚ) ≤ (D lam n : ℚ) := by
  have hd : (0 : ℚ) < lam.d := by exact_mod_cast lam.d_pos
  have ht : (n : ℚ) ≤ (D lam n : ℚ) * (lam.d : ℚ) + 2 := by
    exact_mod_cast degree_le_D_mul_d_add_two lam hn
  rw [← sub_div, div_le_iff₀ hd]
  linarith

end ConjugacyDiametersPORC

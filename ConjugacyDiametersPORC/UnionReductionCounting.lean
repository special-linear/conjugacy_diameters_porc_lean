import ConjugacyDiametersPORC.UnionRecurrenceBudget
import ConjugacyDiametersPORC.UnionLongCycleCorrection

/-!
# The degree bound when all three reduction cases fail

Bound each long-cycle length by `(d+b-1)ν(ℓ)` and the short-cycle support by
the sum of `r c_r`. If every reduction fails, the degree is at most `Nbad`.
-/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

private theorem long_length_le_capacity (lam : CycleFamily) {ℓ : ℕ} (hℓ : lam.b ≤ ℓ) :
    ℓ ≤ (lam.d + lam.b - 1) * ν lam ℓ := by
  have he := long_length_decomposition lam hℓ
  have hr := Nat.mod_lt (ℓ - lam.b) lam.d_pos
  have hb := lam.h_add_d
  have hp := (nu_pos_iff lam ℓ).mpr hℓ
  have hmul : lam.b - 1 ≤ (lam.b - 1) * ν lam ℓ := Nat.le_mul_of_pos_right _ hp
  rw [show lam.d + lam.b - 1 = lam.d + (lam.b - 1) by
    have hbpos := lam.b_pos
    omega, Nat.add_mul]
  omega

theorem cycle_support_bound (lam : CycleFamily) (s : Multiset ℕ) (hs : ∀ ℓ ∈ s, 2 ≤ ℓ) :
    s.sum ≤ (∑ r ∈ shortLengths lam, r * s.count r) +
      (lam.d + lam.b - 1) * (s.map (ν lam)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ℓ s ih =>
    have ih := ih (fun t ht => hs t (Multiset.mem_cons_of_mem ht))
    have hℓ : 2 ≤ ℓ := hs ℓ (Multiset.mem_cons_self _ _)
    have hcounts : (∑ r ∈ shortLengths lam, r * (ℓ ::ₘ s).count r) =
        (∑ r ∈ shortLengths lam, r * s.count r) +
          (if ℓ ∈ shortLengths lam then ℓ else 0) := by
      simp [Multiset.count_cons, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq']
    rw [Multiset.sum_cons, hcounts, Multiset.map_cons, Multiset.sum_cons, Nat.mul_add]
    by_cases hshort : ℓ < lam.b
    · have hm : ℓ ∈ shortLengths lam := (mem_shortLengths lam ℓ).mpr ⟨hℓ, hshort⟩
      rw [ite_eq_left hm, nu_of_short lam hshort, Nat.mul_zero]
      omega
    · have hm : ℓ ∉ shortLengths lam := by simp [hshort]
      rw [ite_eq_right hm]
      have he := long_length_le_capacity lam (show lam.b ≤ ℓ by omega)
      omega

namespace RecurrenceBudget

variable {lam : CycleFamily}

/-- The degree bound in the last paragraph of **Lemma 8**. -/
def Nbad (B : RecurrenceBudget lam) : ℕ :=
  (B.P - 1) + (∑ r ∈ shortLengths lam, (B.P - r)) +
    (lam.d + lam.b - 1) * (B.T - 1)

theorem degree_le_Nbad (B : RecurrenceBudget lam) {n : ℕ} (g : SymmetricGroup n)
    (hfixed : n - g.support.card < B.P) (hlong : Qlong lam g < B.T)
    (hshort : ∀ r : shortLengths lam, g.cycleType.count r.val < B.P / r.val) :
    n ≤ B.Nbad := by
  have hs := cycle_support_bound lam g.cycleType (fun _ h => Equiv.Perm.two_le_of_mem_cycleType h)
  rw [Equiv.Perm.sum_cycleType] at hs
  change g.support.card ≤ (∑ r ∈ shortLengths lam, r * g.cycleType.count r) +
    (lam.d + lam.b - 1) * Qlong lam g at hs
  have hsum : (∑ r ∈ shortLengths lam, r * g.cycleType.count r) ≤
      ∑ r ∈ shortLengths lam, (B.P - r) := by
    apply Finset.sum_le_sum
    intro r hr
    have hc := hshort ⟨r, hr⟩
    change g.cycleType.count r < B.P / r at hc
    have hm := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hc)
    have he : r * (B.P / r) = B.P := Nat.mul_div_cancel' (B.r_dvd ⟨r, hr⟩)
    rw [Nat.mul_succ, he] at hm
    omega
  have hq : Qlong lam g ≤ B.T - 1 := by omega
  have hqmul := Nat.mul_le_mul_left (lam.d + lam.b - 1) hq
  have hcard : g.support.card ≤ n := by simpa using Finset.card_le_univ g.support
  unfold Nbad
  omega

theorem reduction_cases (B : RecurrenceBudget lam) {n : ℕ} (g : SymmetricGroup n)
    (hn : B.Nbad + 1 ≤ n) :
    B.T ≤ Qlong lam g ∨ B.P ≤ n - g.support.card ∨
      ∃ r : shortLengths lam, B.P / r.val ≤ g.cycleType.count r.val := by
  by_contra! h
  have he := B.degree_le_Nbad g h.2.1 h.1 h.2.2
  omega

end RecurrenceBudget

end FiniteUnion
end ConjugacyDiametersPORC

import ConjugacyDiametersPORC.ProductionRational
import ConjugacyDiametersPORC.ClearDenominators

/-!
# The optimal integral constituent word

Clear the denominators of a rational optimizer and take that many disjoint
copies of each dictionary entry. The resulting word has resource vector `Qm`,
length `Qh`, and exactly `S = Q Γ_r > 0` target cycles.
-/

namespace ConjugacyDiametersPORC

theorem exists_integer_optimizer (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ z : DictionaryEntry lam r hr → ℕ,
      (∑ A, z A • A.val.c) = Q • (fun ℓ : lam.J => lam.m ℓ) ∧
        (((∑ A, z A * A.val.s) : ℕ) : ℝ) = Q * Γ lam r hr := by
  obtain ⟨y, hy, hopt⟩ := exists_rational_optimizer lam r hr
  have hyQ : ∀ A, (0 : ℚ) ≤ y A := by
    intro A
    have he : (0 : ℝ) ≤ (y A : ℝ) := hy.1 A
    exact_mod_cast he
  obtain ⟨Q, hQ, z, hz⟩ := exists_nat_multiple y hyQ
  have hzR (A) : (z A : ℝ) = Q * (y A : ℝ) := by exact_mod_cast hz A
  refine ⟨Q, hQ, z, ?_, ?_⟩
  · funext ℓ
    rw [Finset.sum_apply]
    change (∑ A, z A * A.val.c ℓ) = Q * lam.m ℓ
    have he : (∑ A, (z A : ℝ) * (A.val.c ℓ : ℝ)) = (Q : ℝ) * lam.m ℓ := by
      simp_rw [hzR]
      calc
        _ = (Q : ℝ) * ∑ A, (A.val.c ℓ : ℝ) * (y A : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          ring
        _ = _ := by rw [hy.2 ℓ]
    exact_mod_cast he
  · calc
      _ = ∑ A, (z A : ℝ) * (A.val.s : ℝ) := by simp
      _ = (Q : ℝ) * ∑ A, (A.val.s : ℝ) * (y A : ℝ) := by
        simp_rw [hzR]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A _
        ring
      _ = _ := by rw [← production, hopt]

/-- The first construction in the finite-attainment proof of **Lemma 5**. -/
theorem exists_optimal_constituent_word (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ W : TargetWord lam r,
      W.c = Q • (fun ℓ : lam.J => lam.m ℓ) ∧
        0 < W.s ∧ (W.s : ℝ) = Q * Γ lam r hr ∧ W.word.factors.length = Q * lam.h := by
  obtain ⟨Q, hQ, z, hc, hs⟩ := exists_integer_optimizer lam r hr
  let l := wordCopies (fun A : DictionaryEntry lam r hr => A.val) z
  let W := TargetWord.unionList lam r l
  have hWc : W.c = Q • (fun ℓ : lam.J => lam.m ℓ) := by
    rw [TargetWord.unionList_c, wordCopies_c]
    exact hc
  have hWs : (W.s : ℝ) = Q * Γ lam r hr := by
    rw [TargetWord.unionList_s, wordCopies_s]
    exact hs
  have hS : 0 < W.s := by
    have he : (0 : ℝ) < W.s := by
      rw [hWs]
      exact mul_pos (by exact_mod_cast hQ) (Gamma_pos lam r hr)
    exact_mod_cast he
  have hK : W.word.factors.length = Q * lam.h := by
    rw [← W.word.sum_c]
    change (∑ ℓ : lam.J, W.c ℓ) = _
    rw [hWc]
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum]
    rw [Finset.sum_coe_sort lam.J lam.m, ← lam.h_eq_sum_m]
  exact ⟨Q, hQ, W, hWc, hS, hWs, hK⟩

end ConjugacyDiametersPORC

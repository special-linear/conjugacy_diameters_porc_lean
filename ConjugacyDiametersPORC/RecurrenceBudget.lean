import ConjugacyDiametersPORC.ProductionPacket

/-!
# The common period and generator budget

Choose `P` divisible by `d`, every `rK_r`, and a denominator of `α_λ`.
Then `q = α_λ P` is a positive integer. Both `T = P/d` long-cycle steps
and the packet cost for `P/r` short cycles are at most `q`.
-/

namespace ConjugacyDiametersPORC

noncomputable def shortPacket (lam : CycleType) (r : shortLengths lam) :=
  packet lam r.val ((mem_shortLengths lam r.val).mp r.property).1

structure RecurrenceBudget (lam : CycleType) where
  P : ℕ
  q : ℕ
  P_pos : 0 < P
  q_pos : 0 < q
  d_dvd : lam.d ∣ P
  packet_dvd : ∀ r : shortLengths lam, r.val * (shortPacket lam r).K_r ∣ P
  rate : (q : ℝ) = α lam * (P : ℝ)

theorem recurrenceBudget_nonempty (lam : CycleType) : Nonempty (RecurrenceBudget lam) := by
  classical
  obtain ⟨a, ha⟩ := alpha_rational lam
  have hapos : (0 : ℚ) ≤ a := by
    have he : (0 : ℝ) ≤ a := ha ▸ (alpha_pos lam).le
    exact_mod_cast he
  obtain ⟨Q, hQ, z, hz⟩ := exists_nat_multiple (fun _ : Unit => a) (fun _ => hapos)
  have hzR : (z () : ℝ) = (Q : ℝ) * α lam := by
    have he : (z () : ℝ) = (Q : ℝ) * (a : ℝ) := by exact_mod_cast hz ()
    rwa [ha] at he
  have hzpos : 0 < z () := by
    have he : (0 : ℝ) < z () := by
      rw [hzR]
      exact mul_pos (by exact_mod_cast hQ) (alpha_pos lam)
    exact_mod_cast he
  let f : shortLengths lam → ℕ := fun r => r.val * (shortPacket lam r).K_r
  let B := lam.d * ∏ r, f r
  have hB : 0 < B := Nat.mul_pos lam.d_pos (Finset.prod_pos (fun r _ =>
    Nat.mul_pos (by have he := ((mem_shortLengths lam r.val).mp r.property).1; omega)
      (shortPacket lam r).K_pos))
  have hdB : lam.d ∣ B := dvd_mul_right _ _
  have hfB (r : shortLengths lam) : f r ∣ B :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem f (Finset.mem_univ r)) _
  refine ⟨⟨Q * B, z () * B, Nat.mul_pos hQ hB, Nat.mul_pos hzpos hB,
    hdB.trans (dvd_mul_left B Q), fun r => (hfB r).trans (dvd_mul_left B Q), ?_⟩⟩
  simp only [Nat.cast_mul]
  rw [hzR]
  ring

noncomputable def recurrenceBudget (lam : CycleType) : RecurrenceBudget lam :=
  Classical.choice (recurrenceBudget_nonempty lam)

namespace RecurrenceBudget

variable {lam : CycleType}

def T (B : RecurrenceBudget lam) : ℕ := B.P / lam.d

theorem T_pos (B : RecurrenceBudget lam) : 0 < B.T :=
  Nat.div_pos (Nat.le_of_dvd B.P_pos B.d_dvd) lam.d_pos

theorem d_mul_T (B : RecurrenceBudget lam) : lam.d * B.T = B.P :=
  Nat.mul_div_cancel' B.d_dvd

theorem T_le_q (B : RecurrenceBudget lam) : B.T ≤ B.q := by
  have he : (B.T : ℝ) = (B.P : ℝ) / (lam.d : ℝ) := Nat.cast_div_charZero B.d_dvd
  have hl := mul_le_mul_of_nonneg_right (inv_d_le_alpha lam) (Nat.cast_nonneg B.P : (0 : ℝ) ≤ B.P)
  rw [one_div_mul_eq_div, ← B.rate, ← he] at hl
  exact_mod_cast hl

theorem packet_cost_le_q (B : RecurrenceBudget lam) (r : shortLengths lam) :
    B.P / (r.val * (shortPacket lam r).K_r) * (shortPacket lam r).t_r ≤ B.q := by
  have he := (shortPacket lam r).cost_le_alpha B.P (B.packet_dvd r)
    ((mem_shortLengths lam r.val).mp r.property).2
  rw [← B.rate] at he
  exact_mod_cast he

theorem r_dvd (B : RecurrenceBudget lam) (r : shortLengths lam) : r.val ∣ B.P :=
  (dvd_mul_right r.val (shortPacket lam r).K_r).trans (B.packet_dvd r)

end RecurrenceBudget

end ConjugacyDiametersPORC

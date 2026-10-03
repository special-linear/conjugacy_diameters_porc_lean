import ConjugacyDiametersPORC.Peeling

/-!
# The number of available long-cycle peelings

For `ℓ ≥ b`, `ν(ℓ) = 1 + ⌊(ℓ-b)/d⌋`. After exactly that many steps the
survivor has length `h + ((ℓ-b) mod d)`, which is positive and below `b`.
-/

namespace ConjugacyDiametersPORC

/-- Total peeling capacity, extended by zero on short cycles. -/
def ν (lam : CycleType) (ℓ : ℕ) : ℕ :=
  if lam.b ≤ ℓ then 1 + (ℓ - lam.b) / lam.d else 0

theorem nu_of_long (lam : CycleType) {ℓ : ℕ} (hℓ : lam.b ≤ ℓ) :
    ν lam ℓ = 1 + (ℓ - lam.b) / lam.d := ite_eq_left hℓ

theorem nu_of_short (lam : CycleType) {ℓ : ℕ} (hℓ : ℓ < lam.b) :
    ν lam ℓ = 0 := ite_eq_right (by omega)

theorem nu_pos_iff (lam : CycleType) (ℓ : ℕ) : 0 < ν lam ℓ ↔ lam.b ≤ ℓ := by
  unfold ν
  split_ifs <;> simp_all

theorem long_length_decomposition (lam : CycleType) {ℓ : ℕ} (hℓ : lam.b ≤ ℓ) :
    ℓ = lam.d * ν lam ℓ + lam.h + (ℓ - lam.b) % lam.d := by
  rw [nu_of_long lam hℓ, Nat.mul_add, Nat.mul_one]
  have he := Nat.mod_add_div (ℓ - lam.b) lam.d
  have hb := lam.h_add_d
  omega

/-- **Remark 2.** The final surviving length is positive and below `b`. -/
theorem residual_after_all_peelings (lam : CycleType) {ℓ : ℕ} (hℓ : lam.b ≤ ℓ) :
    ℓ - lam.d * ν lam ℓ = lam.h + (ℓ - lam.b) % lam.d ∧
      0 < ℓ - lam.d * ν lam ℓ ∧ ℓ - lam.d * ν lam ℓ < lam.b := by
  have he := long_length_decomposition lam hℓ
  have hr := Nat.mod_lt (ℓ - lam.b) lam.d_pos
  have hh := lam.h_pos
  have hb := lam.h_add_d
  omega

/-- Before the last available step, the surviving cycle is still long. -/
theorem residual_long_before_last (lam : CycleType) {ℓ t : ℕ}
    (hℓ : lam.b ≤ ℓ) (ht : t < ν lam ℓ) : lam.b ≤ ℓ - lam.d * t := by
  have he := long_length_decomposition lam hℓ
  have hm := Nat.mul_le_mul_left lam.d (Nat.succ_le_of_lt ht)
  rw [Nat.mul_succ] at hm
  have hb := lam.h_add_d
  omega

theorem residual_positive_within_budget (lam : CycleType) {ℓ t : ℕ}
    (hℓ : lam.b ≤ ℓ) (ht : t ≤ ν lam ℓ) : 0 < ℓ - lam.d * t := by
  have he := long_length_decomposition lam hℓ
  have hm := Nat.mul_le_mul_left lam.d ht
  have hh := lam.h_pos
  omega

theorem nu_after_one (lam : CycleType) {ℓ : ℕ} (hℓ : lam.b ≤ ℓ) :
    ν lam (ℓ - lam.d) + 1 = ν lam ℓ := by
  have hb := lam.h_add_d
  have hh := lam.h_pos
  by_cases hn : lam.b ≤ ℓ - lam.d
  · rw [nu_of_long lam hn, nu_of_long lam hℓ]
    have he : ℓ - lam.b = (ℓ - lam.d - lam.b) + lam.d := by omega
    rw [he, Nat.add_div_right _ lam.d_pos]
    omega
  · rw [nu_of_short lam (by omega), nu_of_long lam hℓ,
      Nat.div_eq_of_lt (show ℓ - lam.b < lam.d by omega)]

end ConjugacyDiametersPORC

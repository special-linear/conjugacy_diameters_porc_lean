import ConjugacyDiametersPORC.ReductionCounting
import ConjugacyDiametersPORC.PacketCorrection

/-!
# The eventual upper recurrence

In sufficiently large degree, use exactly `T` long-cycle peelings, existing
fixed labels, or finite packets to pass to degree `n-P` within the budget `q`.
-/

namespace ConjugacyDiametersPORC

namespace RecurrenceBudget

variable {lam : CycleType}

/-- The degree threshold ensuring all three reduction procedures are available. -/
noncomputable def threshold (B : RecurrenceBudget lam) : ℕ :=
  max (lam.b + 1 + B.P)
    (max (B.Nbad + 1) (Finset.univ.sup (fun r : shortLengths lam => (shortPacket lam r).N_r)))

theorem stable_degree (B : RecurrenceBudget lam) {n : ℕ} (hn : B.threshold ≤ n) :
    lam.b + 1 ≤ n - B.P := by
  have he := (le_max_left _ _).trans hn
  change lam.b + 1 + B.P ≤ n at he
  omega

theorem threshold_pos (B : RecurrenceBudget lam) : 0 < B.threshold := by
  have he : lam.b + 1 + B.P ≤ B.threshold := le_max_left _ _
  omega

end RecurrenceBudget

/-- **Lemma 8.** The common budget gives the eventual upper recurrence. -/
theorem lemma8 (lam : CycleType) (B : RecurrenceBudget lam) {n : ℕ}
    (hn : B.threshold ≤ n) : D lam n ≤ D lam (n - B.P) + B.q := by
  apply (D_le_iff lam n _).mpr
  intro g
  have hstable := B.stable_degree hn
  have hbad : B.Nbad + 1 ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  rcases B.reduction_cases (g : SymmetricGroup n) hbad with hlong | hfixed | ⟨r, hr⟩
  · obtain ⟨f, w, hw, hlen, hgain⟩ := long_cycle_correction lam
      (g : SymmetricGroup n) B.T hlong
    have hs : ((g : SymmetricGroup n) * f⁻¹).support.card ≤ n - B.P := by
      rw [B.d_mul_T] at hgain
      have hc : (g : SymmetricGroup n).support.card ≤ n := by
        simpa using Finset.card_le_univ (g : SymmetricGroup n).support
      omega
    apply length_le_of_correction lam hstable g f w hw _ hs
    rw [hlen]
    exact B.T_le_q
  · have hs : (g : SymmetricGroup n).support.card ≤ n - B.P := by
      have hc : (g : SymmetricGroup n).support.card ≤ n := by
        simpa using Finset.card_le_univ (g : SymmetricGroup n).support
      omega
    obtain ⟨w, hw, hlen⟩ := small_support_factorization lam hstable (Nat.sub_le n B.P) g hs
    exact (L_le_length hw).trans (hlen.trans (Nat.le_add_right _ _))
  · have hNr : (shortPacket lam r).N_r ≤ n := by
      have hs : (shortPacket lam r).N_r ≤ Finset.univ.sup
          (fun t : shortLengths lam => (shortPacket lam t).N_r) :=
        Finset.le_sup (f := fun t : shortLengths lam => (shortPacket lam t).N_r)
          (Finset.mem_univ r)
      exact hs.trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    obtain ⟨f, w, hw, hlen, hs⟩ := (shortPacket lam r).correction hNr B.P
      (B.packet_dvd r) (g : SymmetricGroup n) hr
    apply length_le_of_correction lam hstable g f w hw _ hs
    rw [hlen]
    exact B.packet_cost_le_q r

theorem exists_upper_recurrence (lam : CycleType) :
    ∃ P q N : ℕ, 0 < P ∧ 0 < q ∧ 0 < N ∧ (q : ℝ) = α lam * (P : ℝ) ∧
      ∀ n, N ≤ n → D lam (n + P) ≤ D lam n + q := by
  let B := recurrenceBudget lam
  refine ⟨B.P, B.q, B.threshold, B.P_pos, B.q_pos, B.threshold_pos, B.rate, ?_⟩
  intro n hn
  have he := lemma8 lam B (hn.trans (Nat.le_add_right n B.P))
  simpa only [Nat.add_sub_cancel] using he

end ConjugacyDiametersPORC

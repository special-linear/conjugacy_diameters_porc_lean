import ConjugacyDiametersPORC.ProductionRational
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option

/-!
# The common slope and the lower-bound constant

The maximum defining `α_λ` includes `1/d` even when there are no short lengths.
The parity factor `p_r` is two precisely when both `d` and `r` are even.
-/

namespace ConjugacyDiametersPORC

/-- Short nontrivial cycle lengths `2 ≤ r < b`. -/
def shortLengths (lam : CycleType) : Finset ℕ := (Finset.range lam.b).filter (2 ≤ ·)

@[simp]
theorem mem_shortLengths (lam : CycleType) (r : ℕ) :
    r ∈ shortLengths lam ↔ 2 ≤ r ∧ r < lam.b := by
  simp [shortLengths, and_comm]

/-- The divisor `p_r` which ensures that `r^s` has admissible parity. -/
def p_r (lam : CycleType) (r : ℕ) : ℕ := if Even lam.d ∧ Even r then 2 else 1

theorem p_r_pos (lam : CycleType) (r : ℕ) : 0 < p_r lam r := by
  unfold p_r
  split_ifs <;> decide

noncomputable def slopeCandidate (lam : CycleType) : Option (shortLengths lam) → ℝ
  | none => 1 / (lam.d : ℝ)
  | some r => 1 / ((r.val : ℝ) * Γ lam r.val ((mem_shortLengths lam r.val).mp r.property).1)

noncomputable def lowerConstantCandidate (lam : CycleType) : Option (shortLengths lam) → ℝ
  | none => 2 / (lam.d : ℝ)
  | some r => (p_r lam r.val : ℝ) / Γ lam r.val
      ((mem_shortLengths lam r.val).mp r.property).1

/-- `α_λ = max {1/d, max_{2 ≤ r < b} 1/(r Γ_r)}`. -/
noncomputable def α (lam : CycleType) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (slopeCandidate lam)

/-- The uniform constant `γ_λ = max {2/d, max_{2 ≤ r < b} p_r/Γ_r}`. -/
noncomputable def γ (lam : CycleType) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (lowerConstantCandidate lam)

theorem slopeCandidate_le_alpha (lam : CycleType) (i : Option (shortLengths lam)) :
    slopeCandidate lam i ≤ α lam := Finset.le_sup' _ (Finset.mem_univ i)

theorem lowerConstantCandidate_le_gamma (lam : CycleType) (i : Option (shortLengths lam)) :
    lowerConstantCandidate lam i ≤ γ lam := Finset.le_sup' _ (Finset.mem_univ i)

theorem inv_d_le_alpha (lam : CycleType) : 1 / (lam.d : ℝ) ≤ α lam :=
  slopeCandidate_le_alpha lam none

theorem inv_rGamma_le_alpha (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (hrb : r < lam.b) :
    1 / ((r : ℝ) * Γ lam r hr) ≤ α lam :=
  slopeCandidate_le_alpha lam (some ⟨r, (mem_shortLengths lam r).mpr ⟨hr, hrb⟩⟩)

theorem alpha_pos (lam : CycleType) : 0 < α lam :=
  lt_of_lt_of_le (div_pos one_pos (by exact_mod_cast lam.d_pos)) (inv_d_le_alpha lam)

theorem exists_alpha_maximizer (lam : CycleType) :
    ∃ i : Option (shortLengths lam), α lam = slopeCandidate lam i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (slopeCandidate lam)
  exact ⟨i, hi⟩

theorem alpha_rational (lam : CycleType) : ∃ a : ℚ, (a : ℝ) = α lam := by
  obtain ⟨i, hi⟩ := exists_alpha_maximizer lam
  rw [hi]
  cases i with
  | none => exact ⟨1 / (lam.d : ℚ), by simp [slopeCandidate]⟩
  | some r =>
    obtain ⟨a, ha⟩ := Gamma_rational lam r.val ((mem_shortLengths lam r.val).mp r.property).1
    refine ⟨1 / ((r.val : ℚ) * a), ?_⟩
    simp [slopeCandidate, ha]

theorem gamma_rational (lam : CycleType) : ∃ c : ℚ, (c : ℝ) = γ lam := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (lowerConstantCandidate lam)
  change γ lam = lowerConstantCandidate lam i at hi
  rw [hi]
  cases i with
  | none => exact ⟨2 / (lam.d : ℚ), by simp [lowerConstantCandidate]⟩
  | some r =>
    obtain ⟨a, ha⟩ := Gamma_rational lam r.val ((mem_shortLengths lam r.val).mp r.property).1
    refine ⟨(p_r lam r.val : ℚ) / a, ?_⟩
    simp [lowerConstantCandidate, ha]

end ConjugacyDiametersPORC

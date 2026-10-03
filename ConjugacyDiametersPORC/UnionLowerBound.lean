import ConjugacyDiametersPORC.UnionSlope
import ConjugacyDiametersPORC.UnionRayBound
import ConjugacyDiametersPORC.TranspositionBound

/-!
# The uniform linear diameter lower bound

Use a long even cycle for the candidate slope `1/d`. For each short length `r`,
use `s = p_r ⌊n/(r p_r)⌋` disjoint cycles and apply the production bound.
-/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

open Equiv Equiv.Perm

theorem tau_of_target {n r s : ℕ} {g : SymmetricGroup n}
    (ht : g.cycleType = Multiset.replicate s r) : τ g = s * (r - 1) := by
  simp [τ, ht, Nat.mul_sub_left_distrib]

/-- The parity divisor makes every realizable target type belong to `G_n`. -/
theorem target_mem_G (lam : CycleFamily) {n r s : ℕ} {g : SymmetricGroup n}
    (hn : lam.b + 1 ≤ n) (ht : g.cycleType = Multiset.replicate s r)
    (hps : p_r lam r ∣ s) : g ∈ G lam n := by
  classical
  by_cases hd : AllEven lam
  · apply alternatingGroup_le_G lam hn
    rw [mem_alternatingGroup, sign_eq_neg_one_pow_tau, tau_of_target ht]
    have he : Even (s * (r - 1)) := by
      rcases Nat.even_or_odd r with hr | hr
      · have hp : p_r lam r = 2 := by simp [p_r, hd, hr]
        rw [hp] at hps
        obtain ⟨k, hk⟩ := hps
        have hs : Even s := ⟨k, by omega⟩
        exact hs.mul_right _
      · have hr' : Even (r - 1) := by
          obtain ⟨k, hk⟩ := hr
          exact ⟨k, by omega⟩
        exact hr'.mul_left _
    exact he.neg_one_pow
  · rw [G_eq_symmetricGroup lam hn hd]
    trivial

theorem exists_target_mem_G (lam : CycleFamily) {n r s : ℕ} (hn : lam.b + 1 ≤ n)
    (hr : 2 ≤ r) (hrs : r * s ≤ n) (hps : p_r lam r ∣ s) :
    ∃ g : G lam n, (g : SymmetricGroup n).cycleType = Multiset.replicate s r := by
  have hex : ∃ g : SymmetricGroup n, g.cycleType = Multiset.replicate s r := by
    rw [exists_with_cycleType_iff]
    constructor
    · simpa [mul_comm] using hrs
    · intro t ht
      exact (Multiset.eq_of_mem_replicate ht) ▸ hr
  obtain ⟨g, hg⟩ := hex
  exact ⟨⟨g, target_mem_G lam hn hg hps⟩, hg⟩

theorem target_count_le_D_mul_Gamma (lam : CycleFamily) {n : ℕ} (g : G lam n)
    (r : ℕ) (hr : 2 ≤ r) (s : ℕ)
    (ht : (g : SymmetricGroup n).cycleType = Multiset.replicate s r) :
    (s : ℝ) ≤ D lam n * Γ lam r hr := by
  obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
  have hwt : w.prod.cycleType = Multiset.replicate s r := by rw [hw.2, ht]
  by_cases hq : 0 < w.length
  · have hs := ray_bound lam w hw.1 hq r s hr hwt
    rw [hlen] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast L_le_D lam g)
      (le_of_lt (Gamma_pos lam r hr)))
  · have hnil : w = [] := List.length_eq_zero_iff.mp (by omega)
    have hs : s = 0 := by
      have he := congrArg Multiset.card hwt
      simpa [hnil] using he.symm
    rw [hs, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Gamma_pos lam r hr))

/-- The lower bound from a large collection of admissible `r`-cycles. -/
theorem short_cycle_diameter_lowerBound (lam : CycleFamily) {n : ℕ}
    (hn : lam.b + 1 ≤ n) (r : ℕ) (hr : 2 ≤ r) :
    (n : ℝ) / ((r : ℝ) * Γ lam r hr) - (p_r lam r : ℝ) / Γ lam r hr ≤ D lam n := by
  let p := p_r lam r
  let s := p * (n / (r * p))
  have hrp : 0 < r * p := Nat.mul_pos (by omega) (p_r_pos lam r)
  have hsn : r * s ≤ n := by
    simpa only [s, ← Nat.mul_assoc] using Nat.mul_div_le n (r * p)
  have hns : n ≤ r * s + r * p := by
    have he := Nat.lt_mul_div_succ n hrp
    simpa only [s, ← Nat.mul_assoc, Nat.mul_add, Nat.mul_one] using he.le
  obtain ⟨g, hg⟩ := exists_target_mem_G lam hn hr hsn (dvd_mul_right p _)
  have hs := target_count_le_D_mul_Gamma lam g r hr s hg
  have hnsR : (n : ℝ) ≤ (r : ℝ) * s + (r : ℝ) * p := by exact_mod_cast hns
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hΓ := Gamma_pos lam r hr
  have hprod := mul_le_mul_of_nonneg_left hs hrR.le
  have he : (n : ℝ) / ((r : ℝ) * Γ lam r hr) - (p : ℝ) / Γ lam r hr =
      ((n : ℝ) - (r : ℝ) * p) / ((r : ℝ) * Γ lam r hr) := by
    field_simp
  change (n : ℝ) / ((r : ℝ) * Γ lam r hr) - (p : ℝ) / Γ lam r hr ≤ _
  rw [he, div_le_iff₀ (mul_pos hrR hΓ)]
  nlinarith [hprod]

/-- **Lemma 6.** `D_n ≥ α_λ n - γ_λ` for all `n ≥ b + 1`. -/
theorem lemma6 (lam : CycleFamily) {n : ℕ} (hn : lam.b + 1 ≤ n) :
    α lam * (n : ℝ) - γ lam ≤ (D lam n : ℝ) := by
  obtain ⟨i, hi⟩ := exists_alpha_maximizer lam
  rw [hi]
  cases i with
  | none =>
    have hl : (n : ℝ) / (lam.d : ℝ) - 2 / (lam.d : ℝ) ≤ (D lam n : ℝ) := by
      have hd : (0 : ℝ) < lam.d := by exact_mod_cast lam.d_pos
      have hb : (n : ℝ) ≤ (D lam n : ℝ) * lam.d + 2 := by
        exact_mod_cast degree_le_D_mul_d_add_two lam hn
      rw [← sub_div, div_le_iff₀ hd]
      linarith
    have hc := lowerConstantCandidate_le_gamma lam none
    simp only [slopeCandidate, lowerConstantCandidate] at *
    rw [one_div_mul_eq_div]
    linarith
  | some r =>
    have hr := ((mem_shortLengths lam r.val).mp r.property).1
    have hl := short_cycle_diameter_lowerBound lam hn r.val hr
    have hc := lowerConstantCandidate_le_gamma lam (some r)
    simp only [slopeCandidate, lowerConstantCandidate] at *
    rw [one_div_mul_eq_div]
    linarith

/-- Rational certificates in the form used by the stabilization argument. -/
theorem exists_rational_lowerBound (lam : CycleFamily) :
    ∃ a c : ℚ, (a : ℝ) = α lam ∧ (c : ℝ) = γ lam ∧ 0 < a ∧
      ∀ n, lam.b + 1 ≤ n → a * (n : ℚ) - c ≤ (D lam n : ℚ) := by
  obtain ⟨a, ha⟩ := alpha_rational lam
  obtain ⟨c, hc⟩ := gamma_rational lam
  have hapos : 0 < a := by
    have he : (0 : ℝ) < a := ha ▸ alpha_pos lam
    exact_mod_cast he
  refine ⟨a, c, ha, hc, hapos, ?_⟩
  intro n hn
  have he := lemma6 lam hn
  rw [← ha, ← hc] at he
  exact_mod_cast he

end FiniteUnion
end ConjugacyDiametersPORC

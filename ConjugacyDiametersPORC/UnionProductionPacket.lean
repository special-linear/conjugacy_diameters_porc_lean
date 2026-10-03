import ConjugacyDiametersPORC.UnionPacket
import ConjugacyDiametersPORC.UnionTransport
import ConjugacyDiametersPORC.UnionSlope
import Mathlib.Data.Nat.Cast.Field

/-!
# Fixed packets and their use in larger degrees

Choose one finite-attainment packet for each target length. It can be embedded
and conjugated to any target of the same type in every degree at least `N_r`.
Auxiliary labels are only required for each complete packet separately.
-/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

open Equiv Equiv.Perm

structure ProductionPacket (lam : CycleFamily) (r : ℕ) (hr : 2 ≤ r) where
  K_r : ℕ
  t_r : ℕ
  N_r : ℕ
  K_pos : 0 < K_r
  t_pos : 0 < t_r
  N_pos : 0 < N_r
  g : SymmetricGroup N_r
  word : List (SymmetricGroup N_r)
  factorization : IsFactorization lam g word
  length_word : word.length = t_r
  target : g.cycleType = Multiset.replicate K_r r
  rate : (t_r : ℝ) / (K_r : ℝ) = 1 / Γ lam r hr

theorem productionPacket_nonempty (lam : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    Nonempty (ProductionPacket lam r hr) := by
  obtain ⟨K, t, N, hK, ht, hN, g, l, hf, hl, hct, hrate⟩ := exists_packet lam r hr
  exact ⟨⟨K, t, N, hK, ht, hN, g, l, hf, hl, hct, hrate⟩⟩

noncomputable def packet (lam : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    ProductionPacket lam r hr := Classical.choice (productionPacket_nonempty lam r hr)

namespace ProductionPacket

variable {lam : CycleFamily} {r : ℕ} {hr : 2 ≤ r}

theorem factorization_in_degree (p : ProductionPacket lam r hr) {n : ℕ}
    (hn : p.N_r ≤ n) (g : SymmetricGroup n)
    (ht : g.cycleType = Multiset.replicate p.K_r r) :
    ∃ l : List (SymmetricGroup n), IsFactorization lam g l ∧ l.length = p.t_r := by
  let e : Fin p.N_r ↪ Fin n :=
    ⟨Fin.castLE hn, fun _ _ he => Fin.ext (congrArg (fun x : Fin n => x.val) he)⟩
  obtain ⟨l, hl, hlen⟩ := factorization_of_cycleType_eq (h := g)
    (p.factorization.viaEmbedding e) (by rw [viaEmbedding_cycleType, p.target, ht])
  exact ⟨l, hl, by simpa [p.length_word] using hlen⟩

/-- The exact cost of removing `P/r` cycles in groups of `K_r`. -/
theorem cost_eq (p : ProductionPacket lam r hr) (P : ℕ) (hP : r * p.K_r ∣ P) :
    (((P / (r * p.K_r) * p.t_r : ℕ) : ℝ)) =
      (P : ℝ) / ((r : ℝ) * Γ lam r hr) := by
  have hK : (p.K_r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt p.K_pos
  have hR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hΓ : Γ lam r hr ≠ 0 := ne_of_gt (Gamma_pos lam r hr)
  rw [Nat.cast_mul, Nat.cast_div_charZero hP, Nat.cast_mul]
  calc
    _ = ((P : ℝ) / (r : ℝ)) * ((p.t_r : ℝ) / (p.K_r : ℝ)) := by field_simp
    _ = _ := by rw [p.rate]; field_simp

theorem cost_le_alpha (p : ProductionPacket lam r hr) (P : ℕ)
    (hP : r * p.K_r ∣ P) (hrb : r < lam.b) :
    (((P / (r * p.K_r) * p.t_r : ℕ) : ℝ)) ≤ α lam * (P : ℝ) := by
  rw [p.cost_eq P hP, ← one_div_mul_eq_div]
  exact mul_le_mul_of_nonneg_right (inv_rGamma_le_alpha lam r hr hrb) (Nat.cast_nonneg P)

end ProductionPacket

end FiniteUnion
end ConjugacyDiametersPORC

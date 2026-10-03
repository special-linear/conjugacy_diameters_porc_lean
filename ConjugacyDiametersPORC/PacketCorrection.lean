import ConjugacyDiametersPORC.ProductionPacket
import ConjugacyDiametersPORC.CycleTypeFactor
import ConjugacyDiametersPORC.DegreeReduction

/-!
# Correcting groups of short cycles with finite packets

Select the required cycles as a disjoint factor, partition them into groups
of `K_r`, and transport one packet word to each group. Their endpoint removes
exactly the selected support, regardless of intermediate auxiliary labels.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

namespace ProductionPacket

variable {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}

def constituentType (p : ProductionPacket lam r hr) : CycleType where
  parts := Multiset.replicate p.K_r r
  nonempty := by
    intro he
    have hc := congrArg Multiset.card he
    simp only [Multiset.card_replicate, Multiset.card_zero] at hc
    exact (Nat.ne_of_gt p.K_pos) hc
  two_le := by
    intro t ht
    exact (Multiset.eq_of_mem_replicate ht) ▸ hr

theorem factorization_of_multiple (p : ProductionPacket lam r hr) {n : ℕ}
    (hn : p.N_r ≤ n) (q : ℕ) (g : SymmetricGroup n)
    (ht : g.cycleType = Multiset.replicate (q * p.K_r) r) :
    ∃ w, IsFactorization lam g w ∧ w.length = q * p.t_r := by
  obtain ⟨l, hprod, hc, hd⟩ := truncCycleFactors g
  have hlengths : (l.map (fun a => a.support.card) : Multiset ℕ) =
      q • p.constituentType.parts := by
    have he : g.cycleType = (l.map (fun a => a.support.card) : Multiset ℕ) :=
      cycleType_eq l hprod hc hd
    rw [← he, ht]
    simp only [constituentType, Multiset.nsmul_replicate]
  obtain ⟨a, ha, hat, hap⟩ := disjoint_cycles_partition p.constituentType q l hc hd hlengths
  obtain ⟨w, hw, hlen⟩ := factorization_prod_of_uniform_length lam a p.t_r
    (fun g hg => p.factorization_in_degree hn g (hat g hg))
  refine ⟨w, ?_, ?_⟩
  · rwa [hap, hprod] at hw
  · rwa [ha] at hlen

/-- The third reduction case of **Lemma 8**, before applying the common budget. -/
theorem correction (p : ProductionPacket lam r hr) {n : ℕ} (hn : p.N_r ≤ n)
    (P : ℕ) (hP : r * p.K_r ∣ P) (g : SymmetricGroup n)
    (hc : P / r ≤ g.cycleType.count r) :
    ∃ f : SymmetricGroup n, ∃ w : List (SymmetricGroup n), IsFactorization lam f w ∧
      w.length = P / (r * p.K_r) * p.t_r ∧ (g * f⁻¹).support.card ≤ n - P := by
  let q := P / (r * p.K_r)
  have hsupport : r * (q * p.K_r) = P := by
    rw [show r * (q * p.K_r) = (r * p.K_r) * q by ring]
    exact Nat.mul_div_cancel' hP
  have hcount : q * p.K_r = P / r :=
    Nat.eq_div_of_mul_eq_right (by omega) hsupport
  have htype : Multiset.replicate (q * p.K_r) r ≤ g.cycleType :=
    Multiset.le_count_iff_replicate_le.mp (hcount ▸ hc)
  obtain ⟨f, h, hgh, hd, hft⟩ := exists_disjoint_factor_of_cycleType_le g _ htype
  obtain ⟨w, hw, hlen⟩ := p.factorization_of_multiple hn q f hft
  have hfc : f.support.card = P := by
    rw [← sum_cycleType, hft]
    simpa [mul_comm] using hsupport
  have he : g * f⁻¹ = h := by
    rw [hgh, hd.commute.eq]
    simp [mul_assoc]
  have hsmall : (g * f⁻¹).support.card ≤ n - P := by
    have hc : g.support.card = f.support.card + h.support.card := by
      rw [hgh]
      exact hd.card_support_mul
    have hn : g.support.card ≤ n := by simpa using Finset.card_le_univ g.support
    rw [he]
    omega
  exact ⟨f, w, hw, hlen, hsmall⟩

end ProductionPacket

end ConjugacyDiametersPORC

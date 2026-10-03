import ConjugacyDiametersPORC.OptimalConstituentWord
import ConjugacyDiametersPORC.CyclicPacket
import ConjugacyDiametersPORC.DisjointCyclePartition

/-!
# Finite attainment of the production rate

Partition each column of the cyclic array into generators and concatenate the
columns. The resulting packet has `K_r = KS` target cycles and `t_r = KQ`
generators, so `t_r / K_r = 1 / Γ_r`.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

namespace CyclicPacket

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_generator_word (w : ConstituentWord lam α) (Q : ℕ)
    (hc : w.c = Q • (fun ℓ : lam.J => lam.m ℓ)) :
    ∃ l : List (Perm (Labels w)), l.length = w.factors.length * Q ∧
      (∀ g ∈ l, g.cycleType = lam.parts) ∧ l.prod = value w := by
  classical
  have hcol (j : Index w) : ∃ l : List (Perm (Labels w)), l.length = Q ∧
      (∀ g ∈ l, g.cycleType = lam.parts) ∧ l.prod = (column w j).value := by
    apply disjoint_cycles_partition lam Q (column w j).factors
    · exact (column w j).isCycle
    · exact column_pairwise w j
    · apply (column w j).lengths_eq_smul
      rw [column_c, hc]
  choose l hl ht hp using hcol
  refine ⟨(List.ofFn l).flatten, ?_, ?_, ?_⟩
  · simp only [List.length_flatten, List.map_ofFn, Function.comp_def, hl]
    simp [List.ofFn_const, List.sum_replicate, mul_comm]
  · intro g hg
    obtain ⟨a, ha, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact ht j g hg
  · rw [List.prod_flatten, List.map_ofFn]
    simp only [Function.comp_def, hp]
    rfl

end CyclicPacket

/-- **Lemma 5, part 2.** A finite packet attains the reciprocal production rate. -/
theorem lemma5_part_two (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ K_r t_r N_r : ℕ, 0 < K_r ∧ 0 < t_r ∧ 0 < N_r ∧
      ∃ g : SymmetricGroup N_r, ∃ l : List (SymmetricGroup N_r),
        IsFactorization lam g l ∧ l.length = t_r ∧
          g.cycleType = Multiset.replicate K_r r ∧
            (t_r : ℝ) / (K_r : ℝ) = 1 / Γ lam r hr := by
  classical
  obtain ⟨Q, hQ, W, hc, hS, hrate, hlen⟩ := exists_optimal_constituent_word lam r hr
  let K := W.word.factors.length
  have hK : 0 < K := by rw [show K = Q * lam.h from hlen]; exact Nat.mul_pos hQ lam.h_pos
  obtain ⟨l, hl, ht, hp⟩ := CyclicPacket.exists_generator_word W.word Q hc
  have hn : 0 < W.n := by
    have hbound : r * W.s ≤ W.n := by
      calc
        _ = (Multiset.replicate W.s r).sum := by simp [mul_comm]
        _ = W.word.value.cycleType.sum := congrArg Multiset.sum W.target.symm
        _ = W.word.value.support.card := sum_cycleType W.word.value
        _ ≤ W.n := by simpa using Finset.card_le_univ W.word.value.support
    have := Nat.mul_pos (show 0 < r by omega) hS
    omega
  let N := Fintype.card (CyclicPacket.Labels W.word)
  let e : CyclicPacket.Labels W.word ↪ Fin N :=
    (Fintype.equivFin (CyclicPacket.Labels W.word)).toEmbedding
  let g : SymmetricGroup N := (CyclicPacket.value W.word).viaEmbedding e
  let l' : List (SymmetricGroup N) := l.map (viaEmbeddingHom e)
  have hN : 0 < N := by
    change 0 < Fintype.card (Fin K × Fin W.n)
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hK hn
  have hf : IsFactorization lam g l' := by
    constructor
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      rw [mem_C, viaEmbeddingHom_apply, viaEmbedding_cycleType]
      exact ht b hb
    · change (l.map (viaEmbeddingHom e)).prod = (CyclicPacket.value W.word).viaEmbedding e
      rw [← map_list_prod (viaEmbeddingHom e), hp]
      rfl
  refine ⟨K * W.s, K * Q, N, Nat.mul_pos hK hS, Nat.mul_pos hK hQ, hN,
    g, l', hf, ?_, ?_, ?_⟩
  · simpa only [l', List.length_map] using hl
  · rw [viaEmbedding_cycleType]
    exact CyclicPacket.value_cycleType W.word W.target
  · have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
    have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
    have hΓ : Γ lam r hr ≠ 0 := ne_of_gt (Gamma_pos lam r hr)
    rw [Nat.cast_mul, Nat.cast_mul, hrate]
    field_simp

end ConjugacyDiametersPORC

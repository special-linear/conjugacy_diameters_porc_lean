import ConjugacyDiametersPORC.UnionProduction
import ConjugacyDiametersPORC.UnionTransport
import ConjugacyDiametersPORC.MixedCyclePartition
import ConjugacyDiametersPORC.CyclicPacket

/-! # Finite packets attaining the mixed production rate -/

namespace ConjugacyDiametersPORC
namespace FiniteUnion
open Equiv Equiv.Perm

theorem exists_integer_optimizer (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ z : Entry F r hr → ℕ, ∃ q : F.Index → ℕ,
      (∑ j, q j) = Q ∧ (∑ A, z A • A.val.c) = ∑ j, q j • F.m j ∧
        (((∑ A, z A * A.val.s) : ℕ) : ℝ) = Q * Γ F r hr := by
  obtain ⟨y, hy, hmax⟩ := exists_rational_optimizer F r hr
  have hn : ∀ i, (0 : ℚ) ≤ y i := by
    intro i
    have he : (0 : ℝ) ≤ (y i : ℝ) := hy.1 i
    exact_mod_cast he
  obtain ⟨Q, hQ, k, hk⟩ := exists_nat_multiple y hn
  have hkR (i) : (k i : ℝ) = Q * (y i : ℝ) := by exact_mod_cast hk i
  refine ⟨Q, hQ, fun A => k (Sum.inl A), fun j => k (Sum.inr j), ?_, ?_, ?_⟩
  · have he : (∑ j, (k (Sum.inr j) : ℝ)) = (Q : ℝ) := by
      simp_rw [hkR]
      rw [← Finset.mul_sum, hy.2.1, mul_one]
    exact_mod_cast he
  · funext ℓ
    simp only [Finset.sum_apply, nsmul_eq_mul]
    have he : (∑ A, (k (Sum.inl A) : ℝ) * (A.val.c ℓ : ℝ)) =
        ∑ j, (k (Sum.inr j) : ℝ) * (F.m j ℓ : ℝ) := by
      simp_rw [hkR]
      calc
        _ = (Q : ℝ) * ∑ A, (A.val.c ℓ : ℝ) * (y (Sum.inl A) : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro A _; ring
        _ = (Q : ℝ) * ∑ j, (F.m j ℓ : ℝ) * (y (Sum.inr j) : ℝ) := by rw [hy.2.2]
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    exact_mod_cast he
  · calc
      _ = ∑ A, (k (Sum.inl A) : ℝ) * (A.val.s : ℝ) := by simp
      _ = (Q : ℝ) * production F r hr (fun i => (y i : ℝ)) := by
        simp_rw [hkR]
        unfold production
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A _
        ring
      _ = _ := by rw [optimum_eq_Gamma _ hy hmax]

theorem mixed_lengths {F : CycleFamily} {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord F.pattern α) (q : F.Index → ℕ)
    (hc : w.c = ∑ j, q j • F.m j) :
    (w.factors.map (fun a => a.support.card) : Multiset ℕ) = ∑ j, q j • (F.type j).parts := by
  classical
  apply Multiset.ext.mpr
  intro t
  have he : Multiset.count t (∑ j, q j • (F.type j).parts) =
      ∑ j, q j * (F.type j).m t := by
    change (Multiset.countAddMonoidHom t) (∑ j, q j • (F.type j).parts) = _
    simp [map_sum, map_nsmul, CycleType.m]
  rw [he, Multiset.coe_count]
  by_cases ht : t ∈ F.pattern.J
  · have h := congrFun hc ⟨t, ht⟩
    simpa [ConstituentWord.c, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul, CycleFamily.m] using h
  · have hz : (w.factors.map (fun a => a.support.card)).count t = 0 := by
      rw [List.count_eq_zero]
      intro hm
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
      exact ht (he ▸ w.length_mem_J a ha)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : (F.type j).m t = 0 := Multiset.count_eq_zero.mpr (fun h =>
      ht ((F.pattern.mem_J t).mpr (F.mem_pattern h)))
    simp [hj]

theorem exists_packet (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    ∃ K_r t_r N_r : ℕ, 0 < K_r ∧ 0 < t_r ∧ 0 < N_r ∧
      ∃ g : SymmetricGroup N_r, ∃ l : List (SymmetricGroup N_r),
        IsFactorization F g l ∧ l.length = t_r ∧
          g.cycleType = Multiset.replicate K_r r ∧ (t_r : ℝ) / (K_r : ℝ) = 1 / Γ F r hr := by
  classical
  obtain ⟨Q, hQ, z, q, hq, hc, hs⟩ := exists_integer_optimizer F r hr
  let W := TargetWord.unionList F.pattern r (wordCopies (fun A : Entry F r hr => A.val) z)
  have hWc : W.c = ∑ j, q j • F.m j := by rw [TargetWord.unionList_c, wordCopies_c]; exact hc
  have hWs : (W.s : ℝ) = Q * Γ F r hr := by rw [TargetWord.unionList_s, wordCopies_s]; exact hs
  have hS : 0 < W.s := by
    have he : (0 : ℝ) < W.s := by rw [hWs]; exact mul_pos (by exact_mod_cast hQ) (Gamma_pos F r hr)
    exact_mod_cast he
  let K := W.word.factors.length
  have hK : 0 < K := by
    by_contra hn
    have hl : W.word.factors = [] := List.length_eq_zero_iff.mp (by omega)
    have he := congrArg Multiset.card W.target
    simp [ConstituentWord.value, hl] at he
    omega
  let types := (List.ofFn (fun j : F.Index => List.replicate (q j) (F.type j))).flatten
  have htlen : types.length = Q := by
    simp only [types, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_replicate]
    simpa only [List.sum_ofFn] using hq
  have htparts : (types.map CycleType.parts).sum = ∑ j, q j • (F.type j).parts := by
    simp [types, List.map_flatten, List.map_ofFn, List.sum_flatten, List.sum_replicate,
      Function.comp_def, List.sum_ofFn]
  have hcol (j : CyclicPacket.Index W.word) :
      ∃ l : List (Perm (CyclicPacket.Labels W.word)), l.length = Q ∧
        (∀ g ∈ l, ∃ i : F.Index, g.cycleType = (F.type i).parts) ∧
          l.prod = (CyclicPacket.column W.word j).value := by
    obtain ⟨l, hl, ht, hp⟩ := disjoint_cycles_partition_types types
      (CyclicPacket.column W.word j).factors (CyclicPacket.column W.word j).isCycle
        (CyclicPacket.column_pairwise W.word j)
          (by rw [htparts]; apply mixed_lengths; rw [CyclicPacket.column_c]; exact hWc)
    refine ⟨l, hl.trans htlen, ?_, hp⟩
    intro g hg
    obtain ⟨t, htmem, hgt⟩ := ht g hg
    obtain ⟨a, ha, hta⟩ := List.mem_flatten.mp htmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have he : t = F.type i := List.eq_of_mem_replicate hta
    exact ⟨i, he ▸ hgt⟩
  choose l hl ht hp using hcol
  let v := (List.ofFn l).flatten
  have hvl : v.length = K * Q := by
    simp [v, List.length_flatten, List.map_ofFn, Function.comp_def, hl,
      List.ofFn_const, List.sum_replicate, K]
  have hvp : v.prod = CyclicPacket.value W.word := by
    rw [List.prod_flatten, List.map_ofFn]
    simp only [Function.comp_def, hp]
    rfl
  let N := Fintype.card (CyclicPacket.Labels W.word)
  let e : CyclicPacket.Labels W.word ↪ Fin N := (Fintype.equivFin _).toEmbedding
  let g := (CyclicPacket.value W.word).viaEmbedding e
  let v' := v.map (viaEmbeddingHom e)
  have hn : 0 < W.n := by
    have hb : r * W.s ≤ W.n := by
      calc
        _ = (Multiset.replicate W.s r).sum := by simp [mul_comm]
        _ = W.word.value.support.card := by rw [← W.target, sum_cycleType]
        _ ≤ W.n := by simpa using Finset.card_le_univ W.word.value.support
    have := Nat.mul_pos (show 0 < r by omega) hS
    omega
  have hN : 0 < N := by
    change 0 < Fintype.card (Fin K × Fin W.n)
    simpa using Nat.mul_pos hK hn
  have hf : IsFactorization F g v' := by
    constructor
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      obtain ⟨li, hli, hbl⟩ := List.mem_flatten.mp hb
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hli
      obtain ⟨i, hi⟩ := ht j b hbl
      refine ⟨i, ?_⟩
      rw [ConjugacyDiametersPORC.mem_C, viaEmbeddingHom_apply, viaEmbedding_cycleType]
      exact hi
    · change (v.map (viaEmbeddingHom e)).prod = _
      rw [← map_list_prod (viaEmbeddingHom e), hvp]
      rfl
  refine ⟨K * W.s, K * Q, N, Nat.mul_pos hK hS, Nat.mul_pos hK hQ, hN, g, v', hf,
    by simpa [v'] using hvl, ?_, ?_⟩
  · rw [viaEmbedding_cycleType]
    exact CyclicPacket.value_cycleType W.word W.target
  · have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
    have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
    have hΓ : Γ F r hr ≠ 0 := ne_of_gt (Gamma_pos F r hr)
    rw [Nat.cast_mul, Nat.cast_mul, hWs]
    field_simp

end FiniteUnion
end ConjugacyDiametersPORC

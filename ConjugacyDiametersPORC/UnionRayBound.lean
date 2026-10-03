import ConjugacyDiametersPORC.UnionProduction
import ConjugacyDiametersPORC.UnionDiameter
import ConjugacyDiametersPORC.TranspositionBound

/-! # Expansion and lower certificates for mixed generator words -/

namespace ConjugacyDiametersPORC
namespace FiniteUnion
open Equiv Equiv.Perm

def expandGenerator (F : CycleFamily) {n : ℕ} (j : F.Index) (g : SymmetricGroup n)
    (hg : g ∈ ConjugacyDiametersPORC.C (F.type j) n) : ConstituentWord F.pattern (Fin n) where
  factors := g.cycleFactors.val
  isCycle := g.cycleFactors.property.2.1
  length_mem_J := by
    intro a ha
    apply (F.pattern.mem_J _).mpr
    apply F.mem_pattern (j := j)
    rw [← (ConjugacyDiametersPORC.mem_C (F.type j) g).mp hg]
    rw [cycleType_eq g.cycleFactors.val g.cycleFactors.property.1
      g.cycleFactors.property.2.1 g.cycleFactors.property.2.2]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem expandGenerator_c (F : CycleFamily) {n : ℕ} (j : F.Index) (g : SymmetricGroup n)
    (hg : g ∈ ConjugacyDiametersPORC.C (F.type j) n) : (expandGenerator F j g hg).c = F.m j := by
  funext ℓ
  have he := cycleType_eq g.cycleFactors.val g.cycleFactors.property.1
    g.cycleFactors.property.2.1 g.cycleFactors.property.2.2
  have ht := ((ConjugacyDiametersPORC.mem_C (F.type j) g).mp hg).symm.trans he
  change (g.cycleFactors.val.map (fun a => a.support.card)).count (ℓ : ℕ) =
    (F.type j).parts.count (ℓ : ℕ)
  rw [ht]
  simp [Function.comp_def]

theorem exists_expansion (F : CycleFamily) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C F n) :
    ∃ W : ConstituentWord F.pattern (Fin n), ∃ q : F.Index → ℕ,
      W.value = w.prod ∧ (∑ j, q j) = w.length ∧ W.c = ∑ j, q j • F.m j := by
  classical
  induction w with
  | nil => exact ⟨ConstituentWord.nil, fun _ => 0, rfl, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨j, hj⟩ := hw a List.mem_cons_self
    obtain ⟨W, q, hv, hq, hc⟩ := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    let q' : F.Index → ℕ := fun k => q k + if k = j then 1 else 0
    refine ⟨(expandGenerator F j a hj).append W, q', ?_, ?_, ?_⟩
    · rw [ConstituentWord.value_append, hv, List.prod_cons]
      exact congrArg (· * w.prod) a.cycleFactors.property.1
    · simp [q', Finset.sum_add_distrib, hq]
    · rw [ConstituentWord.c_append, expandGenerator_c, hc]
      funext ℓ
      simp only [Pi.add_apply, Finset.sum_apply, nsmul_eq_mul]
      change F.m j ℓ + (∑ k, q k * F.m k ℓ) =
        ∑ k, (q k + if k = j then 1 else 0) * F.m k ℓ
      simp [add_mul, Finset.sum_add_distrib, ite_mul, add_comm]

theorem ray_bound (F : CycleFamily) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C F n) (hQ : 0 < w.length) (r s : ℕ) (hr : 2 ≤ r)
    (ht : w.prod.cycleType = Multiset.replicate s r) : (s : ℝ) ≤ w.length * Γ F r hr := by
  classical
  obtain ⟨W, q, hv, hq, hc⟩ := exists_expansion F w hw
  obtain ⟨l, hl, hlc, hls⟩ := lemma4 W r hr s (by unfold ConstituentWord.HasTarget; rwa [hv])
  rw [TargetWord.unionList_c] at hlc
  rw [TargetWord.unionList_s] at hls
  let L := dictionaryList l hl
  let z : Variables F r hr → ℝ
    | Sum.inl A => collectionWeights L w.length A
    | Sum.inr j => (q j : ℝ) / w.length
  have hqr : (w.length : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
  have hz : Feasible F r hr z := by
    refine ⟨?_, ?_, fun ℓ => ?_⟩
    · intro i
      cases i with
      | inl A => exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      | inr j => exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · change (∑ j, (q j : ℝ) / w.length) = 1
      rw [← Finset.sum_div]
      have he : (∑ j, (q j : ℝ)) = (w.length : ℝ) := by exact_mod_cast hq
      rw [he, div_self hqr]
    · rw [collection_resource]
      have he : (L.map (fun A => A.val.c)).sum = ∑ j, q j • F.m j := by
        rw [dictionaryList_c, hlc, hc]
      have hn := congrArg (Pi.evalAddMonoidHom (fun _ : F.pattern.J => ℕ) ℓ) he
      have hn' : (L.map (fun A => A.val.c ℓ)).sum = ∑ j, q j * F.m j ℓ := by
        simpa [map_list_sum, List.map_map, Function.comp_def] using hn
      rw [hn']
      simp only [Nat.cast_sum, Nat.cast_mul]
      change (∑ j, (q j : ℝ) * F.m j ℓ) / w.length =
        ∑ j, (F.m j ℓ : ℝ) * ((q j : ℝ) / w.length)
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      simp [mul_comm]
  have hp := production_le_Gamma hz
  change ConjugacyDiametersPORC.production F.pattern r hr (collectionWeights L w.length) ≤ _ at hp
  rw [collectionWeights_production, dictionaryList_s] at hp
  have hs : (s : ℝ) / w.length ≤ (((l.map TargetWord.s).sum : ℕ) : ℝ) / w.length :=
    div_le_div_of_nonneg_right (by exact_mod_cast hls) (Nat.cast_nonneg _)
  simpa [mul_comm] using (div_le_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < w.length)).mp (hs.trans hp)

theorem tau_le_factorization_length_mul_d {F : CycleFamily} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)} (hw : IsFactorization F g w) :
    τ g ≤ w.length * F.d := by
  have hex : ∃ l : List (SymmetricGroup n), l.prod = w.prod ∧
      (∀ a ∈ l, a.IsSwap) ∧ l.length ≤ w.length * F.d := by
    have hm := hw.1
    clear hw
    induction w with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons a w ih =>
      obtain ⟨j, hj⟩ := hm a List.mem_cons_self
      obtain ⟨l, hl, hs, hlen⟩ := ih (fun a ha => hm a (List.mem_cons_of_mem _ ha))
      let A := ConjugacyDiametersPORC.expandGenerator (F.type j) a hj
      have ha : A.transpositions.prod = a := A.transpositions_prod.trans a.cycleFactors.property.1
      have hAl : A.transpositions.length = (F.type j).d := by
        rw [A.transpositions_length, ConjugacyDiametersPORC.expandGenerator_c, delta_inventory]
      refine ⟨A.transpositions ++ l, by simp [ha, hl], ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact A.transpositions_isSwap hb
        · exact hs b hb
      · have hd := F.d_le j
        rw [List.length_append, hAl, List.length_cons, Nat.add_mul]
        omega
  obtain ⟨l, hl, hs, hb⟩ := hex
  have htau := tau_prod_le_length l hs
  rw [hl, hw.2] at htau
  exact htau.trans hb

theorem degree_le_D_mul_d_add_two (F : CycleFamily) {n : ℕ} (hn : F.b + 1 ≤ n) :
    n ≤ D F n * F.d + 2 := by
  obtain ⟨g, hg, ht⟩ := exists_even_longCycle n (by have := F.b_two_le; omega)
  have hG : g ∈ G F n := alternatingGroup_le_G F hn (mem_alternatingGroup.mpr hg)
  obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization F ⟨g, hG⟩
  have hb := tau_le_factorization_length_mul_d hw
  rw [hlen] at hb
  change τ g ≤ L F ⟨g, hG⟩ * F.d at hb
  have hLD := Nat.mul_le_mul_right F.d (L_le_D F ⟨g, hG⟩)
  omega

end FiniteUnion
end ConjugacyDiametersPORC

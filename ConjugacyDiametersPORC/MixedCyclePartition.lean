import ConjugacyDiametersPORC.DisjointCyclePartition

/-! # Partition of disjoint cycles into a prescribed list of generator types -/

namespace ConjugacyDiametersPORC
open Equiv.Perm

theorem disjoint_cycles_partition_types {α : Type*} [Fintype α] [DecidableEq α]
    (types : List CycleType) (l : List (Equiv.Perm α))
    (hc : ∀ a ∈ l, a.IsCycle) (hd : l.Pairwise Disjoint)
    (hlen : (l.map (fun a => a.support.card) : Multiset ℕ) =
      (types.map CycleType.parts).sum) :
    ∃ w : List (Equiv.Perm α), w.length = types.length ∧
      (∀ g ∈ w, ∃ t ∈ types, g.cycleType = t.parts) ∧ w.prod = l.prod := by
  classical
  induction types generalizing l with
  | nil =>
    have he : l = [] := by
      have h := congrArg Multiset.card hlen
      simpa using h
    exact ⟨[], rfl, by simp, by simp [he]⟩
  | cons t ts ih =>
    have hm : (l : Multiset (Equiv.Perm α)).map (fun a => a.support.card) =
        t.parts + (ts.map CycleType.parts).sum := by simpa using hlen
    obtain ⟨a, b, hab, ha, hb⟩ := exists_map_split (fun a : Equiv.Perm α => a.support.card)
      t.parts ((ts.map CycleType.parts).sum) (l : Multiset _) hm
    let l₁ := a.toList
    let l₂ := b.toList
    have hp : l.Perm (l₁ ++ l₂) := by
      apply Multiset.coe_eq_coe.mp
      simpa only [l₁, l₂, ← Multiset.coe_add, Multiset.coe_toList] using hab
    have hdp : (l₁ ++ l₂).Pairwise Disjoint := (hp.pairwise_iff (fun h => h.symm)).mp hd
    have hc₁ : ∀ g ∈ l₁, g.IsCycle := fun g hg =>
      hc g (hp.mem_iff.mpr (List.mem_append_left l₂ hg))
    have hc₂ : ∀ g ∈ l₂, g.IsCycle := fun g hg =>
      hc g (hp.mem_iff.mpr (List.mem_append_right l₁ hg))
    have ht₁ : l₁.prod.cycleType = t.parts := by
      rw [cycleType_eq l₁ rfl hc₁ (List.pairwise_append.mp hdp).1]
      simpa only [l₁, Function.comp_def, ← Multiset.map_coe, Multiset.coe_toList] using ha
    have ht₂ : (l₂.map (fun a => a.support.card) : Multiset ℕ) =
        (ts.map CycleType.parts).sum := by
      simpa only [l₂, ← Multiset.map_coe, Multiset.coe_toList] using hb
    obtain ⟨w, hw, hwt, hprod⟩ := ih l₂ hc₂ (List.pairwise_append.mp hdp).2.1 ht₂
    refine ⟨l₁.prod :: w, by simp [hw], ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨t, List.mem_cons_self, ht₁⟩
      · obtain ⟨u, hu, hgu⟩ := hwt g hg
        exact ⟨u, List.mem_cons_of_mem t hu, hgu⟩
    · rw [List.prod_cons, hprod, ← List.prod_append]
      exact (hp.prod_eq' (hd.imp fun h => h.commute)).symm

end ConjugacyDiametersPORC

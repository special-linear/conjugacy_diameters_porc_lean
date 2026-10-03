import ConjugacyDiametersPORC.DisjointCyclePartition

/-!
# Selecting a submultiset of a permutation's cycles

A submultiset of the full cycle type is realized by a product of selected
disjoint cycle factors. The complementary factor acts on the remaining support.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem exists_disjoint_factor_of_cycleType_le (g : Perm β) (t : Multiset ℕ)
    (ht : t ≤ g.cycleType) :
    ∃ f h : Perm β, g = f * h ∧ f.Disjoint h ∧ f.cycleType = t := by
  classical
  obtain ⟨l, hprod, hc, hd⟩ := truncCycleFactors g
  have hct : g.cycleType = (l.map (fun a => a.support.card) : Multiset ℕ) :=
    cycleType_eq l hprod hc hd
  have hm : (l : Multiset (Perm β)).map (fun a => a.support.card) = t + (g.cycleType - t) := by
    rw [Multiset.map_coe, ← hct]
    exact (add_tsub_cancel_of_le ht).symm
  obtain ⟨a, b, hab, ha, _⟩ := exists_map_split (fun a : Perm β => a.support.card)
    t (g.cycleType - t) (l : Multiset _) hm
  let l₁ := a.toList
  let l₂ := b.toList
  have hp : l.Perm (l₁ ++ l₂) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [l₁, l₂, ← Multiset.coe_add, Multiset.coe_toList] using hab
  have hdp : (l₁ ++ l₂).Pairwise Equiv.Perm.Disjoint :=
    (hp.pairwise_iff (fun h => h.symm)).mp hd
  have hdprod : l₁.prod.Disjoint l₂.prod := by
    apply Equiv.Perm.Disjoint.symm
    apply disjoint_prod_right
    intro f hf
    apply Equiv.Perm.Disjoint.symm
    apply disjoint_prod_right
    intro h hh
    exact (List.pairwise_append.mp hdp).2.2 f hf h hh
  refine ⟨l₁.prod, l₂.prod, ?_, hdprod, ?_⟩
  · rw [← List.prod_append, ← hp.prod_eq' (hd.imp fun h => h.commute), hprod]
  · have hc₁ : ∀ f ∈ l₁, f.IsCycle := fun f hf =>
      hc f (hp.mem_iff.mpr (List.mem_append_left l₂ hf))
    rw [cycleType_eq l₁ rfl hc₁ (List.pairwise_append.mp hdp).1]
    simpa only [l₁, Function.comp_def, ← Multiset.map_coe, Multiset.coe_toList] using ha

end ConjugacyDiametersPORC

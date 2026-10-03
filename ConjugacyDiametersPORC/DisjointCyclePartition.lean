import ConjugacyDiametersPORC.ConstituentWord
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Partitioning disjoint constituent cycles into generators

A disjoint word with inventory `Qm` can be grouped into exactly `Q` permutations
of cycle type `λ`. Commutativity of its factors preserves the column product.
-/

namespace ConjugacyDiametersPORC

theorem exists_map_split {α β : Type*} (f : α → β)
    (a b : Multiset β) (s : Multiset α) (h : s.map f = a + b) :
    ∃ s₁ s₂ : Multiset α, s = s₁ + s₂ ∧ s₁.map f = a ∧ s₂.map f = b := by
  classical
  induction a using Multiset.induction_on generalizing s with
  | empty => exact ⟨0, s, by simp, by simp, by simpa using h⟩
  | cons t a ih =>
    have ht : t ∈ s.map f := by rw [h]; simp
    obtain ⟨x, hx, hfx⟩ := Multiset.mem_map.mp ht
    have he : (s.erase x).map f = a + b := by
      rw [Multiset.map_erase_of_mem f s hx, h, hfx, Multiset.cons_add,
        Multiset.erase_cons_head]
    obtain ⟨s₁, s₂, hs, h₁, h₂⟩ := ih (s.erase x) he
    refine ⟨x ::ₘ s₁, s₂, ?_, ?_, h₂⟩
    · rw [Multiset.cons_add, ← hs, Multiset.cons_erase hx]
    · rw [Multiset.map_cons, hfx, h₁]

open Equiv.Perm

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

/-- The full multiset of constituent lengths is determined by its resource vector. -/
theorem ConstituentWord.lengths_eq_smul (w : ConstituentWord lam α) (q : ℕ)
    (hc : w.c = q • (fun ℓ : lam.J => lam.m ℓ)) :
    (w.factors.map (fun a => a.support.card) : Multiset ℕ) = q • lam.parts := by
  apply Multiset.ext.mpr
  intro ℓ
  rw [Multiset.count_nsmul]
  by_cases hℓ : ℓ ∈ lam.J
  · simpa [ConstituentWord.c, CycleType.m, Pi.smul_apply, nsmul_eq_mul] using
      congrFun hc ⟨ℓ, hℓ⟩
  · have hz : (w.factors.map (fun a => a.support.card)).count ℓ = 0 := by
      rw [List.count_eq_zero]
      intro he
      obtain ⟨a, ha, hlen⟩ := List.mem_map.mp he
      exact hℓ (hlen ▸ w.length_mem_J a ha)
    have hp : lam.parts.count ℓ = 0 := Multiset.count_eq_zero.mpr (by
      simpa only [← lam.mem_J] using hℓ)
    simpa [hp] using hz

/-- Group a disjoint list of cycles into generators with the prescribed type. -/
theorem disjoint_cycles_partition (lam : CycleType) (q : ℕ) (l : List (Equiv.Perm α))
    (hcycle : ∀ a ∈ l, a.IsCycle) (hd : l.Pairwise Disjoint)
    (hlen : (l.map (fun a => a.support.card) : Multiset ℕ) = q • lam.parts) :
    ∃ w : List (Equiv.Perm α), w.length = q ∧
      (∀ g ∈ w, g.cycleType = lam.parts) ∧ w.prod = l.prod := by
  classical
  induction q generalizing l with
  | zero =>
    have hn : l = [] := by
      have he := congrArg Multiset.card hlen
      simpa using he
    exact ⟨[], rfl, by simp, by simp [hn]⟩
  | succ q ih =>
    have hm : (l : Multiset (Equiv.Perm α)).map (fun a => a.support.card) =
        lam.parts + q • lam.parts := by
      simpa only [Multiset.map_coe, succ_nsmul, add_comm] using hlen
    obtain ⟨a, b, hab, ha, hb⟩ := exists_map_split (fun a : Equiv.Perm α => a.support.card)
      lam.parts (q • lam.parts) (l : Multiset _) hm
    let l₁ := a.toList
    let l₂ := b.toList
    have hp : l.Perm (l₁ ++ l₂) := by
      apply Multiset.coe_eq_coe.mp
      simpa only [l₁, l₂, ← Multiset.coe_add, Multiset.coe_toList] using hab
    have hdp : (l₁ ++ l₂).Pairwise Equiv.Perm.Disjoint :=
      (hp.pairwise_iff (fun h => h.symm)).mp hd
    have hc₁ : ∀ g ∈ l₁, g.IsCycle := fun g hg =>
      hcycle g (hp.mem_iff.mpr (List.mem_append_left l₂ hg))
    have hc₂ : ∀ g ∈ l₂, g.IsCycle := fun g hg =>
      hcycle g (hp.mem_iff.mpr (List.mem_append_right l₁ hg))
    have ht₁ : l₁.prod.cycleType = lam.parts := by
      rw [cycleType_eq l₁ rfl hc₁ (List.pairwise_append.mp hdp).1]
      simpa only [l₁, Function.comp_def, ← Multiset.map_coe, Multiset.coe_toList] using ha
    have ht₂ : (l₂.map (fun a => a.support.card) : Multiset ℕ) = q • lam.parts := by
      simpa only [l₂, ← Multiset.map_coe, Multiset.coe_toList] using hb
    obtain ⟨w, hw, hwt, hprod⟩ := ih l₂ hc₂ (List.pairwise_append.mp hdp).2.1 ht₂
    refine ⟨l₁.prod :: w, by simp [hw], ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ht₁
      · exact hwt g hg
    · rw [List.prod_cons, hprod, ← List.prod_append]
      exact (hp.prod_eq' (hd.imp fun h => h.commute)).symm

end ConjugacyDiametersPORC

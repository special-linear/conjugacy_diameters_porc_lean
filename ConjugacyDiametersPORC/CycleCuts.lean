import ConjugacyDiametersPORC.Transpositions

/-!
# Joining and cutting permutation cycles

Full cycle label lists include singleton fixed labels. This lets transposition
arguments treat fixed labels and nontrivial cycles uniformly.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The cycle containing `x`, retaining a singleton when `x` is fixed. -/
def cycleLabels (g : Perm α) (x : α) : List α :=
  if g x = x then [x] else g.toList x

theorem cycleLabels_nodup (g : Perm α) (x : α) : (cycleLabels g x).Nodup := by
  by_cases hx : g x = x
  · simp [cycleLabels, hx]
  · simpa [cycleLabels, hx] using nodup_toList g x

theorem cycleLabels_formPerm (g : Perm α) (x : α) :
    (cycleLabels g x).formPerm = g.cycleOf x := by
  by_cases hx : g x = x
  · simp [cycleLabels, hx, (cycleOf_eq_one_iff g).mpr hx]
  · simp [cycleLabels, hx, formPerm_toList]

theorem mem_cycleLabels (g : Perm α) (x y : α) :
    y ∈ cycleLabels g x ↔ g.SameCycle x y := by
  by_cases hx : g x = x
  · simp only [cycleLabels, ite_eq_left hx, List.mem_singleton]
    exact ⟨fun hy => hy ▸ SameCycle.rfl, fun h => (h.eq_of_left hx).symm⟩
  · simp [cycleLabels, hx, mem_toList_iff, mem_support.mpr hx]

theorem cycleLabels_head (g : Perm α) (x : α) : ∃ l, cycleLabels g x = x :: l := by
  by_cases hx : g x = x
  · exact ⟨[], by simp [cycleLabels, hx]⟩
  · have hn : g.toList x ≠ [] := by simpa using mem_support.mpr hx
    cases he : g.toList x with
    | nil => exact (hn he).elim
    | cons y l =>
      have hy := toList_getElem_zero g x (mem_support.mpr hx)
      simp only [he, List.getElem_cons_zero] at hy
      exact ⟨l, by simp [cycleLabels, hx, he, hy]⟩

theorem cycleLabels_disjoint (g : Perm α) (x y : α) (hxy : ¬g.SameCycle x y) :
    (cycleLabels g x).Disjoint (cycleLabels g y) := by
  intro z hx hy
  exact hxy (((mem_cycleLabels g x z).mp hx).trans ((mem_cycleLabels g y z).mp hy).symm)

theorem cycleLabels_append_nodup (g : Perm α) (x y : α) (hxy : ¬g.SameCycle x y) :
    (cycleLabels g x ++ cycleLabels g y).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨cycleLabels_nodup g x, cycleLabels_nodup g y, ?_⟩
  intro a ha b hb he
  subst b
  exact cycleLabels_disjoint g x y hxy ha hb

/-- Remove the cycle of `x` from a permutation. -/
def cycleRemainder (g : Perm α) (x : α) : Perm α := g * (g.cycleOf x)⁻¹

theorem cycleRemainder_mul_cycle (g : Perm α) (x : α) :
    cycleRemainder g x * g.cycleOf x = g := by
  simp [cycleRemainder, mul_assoc]

theorem cycleRemainder_disjoint (g : Perm α) (x : α) :
    (cycleRemainder g x).Disjoint (g.cycleOf x) := by
  by_cases hx : g x = x
  · rw [(cycleOf_eq_one_iff g).mpr hx]
    exact disjoint_one_right _
  · exact disjoint_mul_inv_of_mem_cycleFactorsFinset
      (cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx))

theorem cycle_mul_remainder (g : Perm α) (x : α) :
    g.cycleOf x * cycleRemainder g x = g := by
  rw [← (cycleRemainder_disjoint g x).commute.eq, cycleRemainder_mul_cycle]

theorem cycleRemainder_support_subset (g : Perm α) (x : α) :
    (cycleRemainder g x).support ⊆ g.support := by
  calc
    (cycleRemainder g x).support ⊆
        (cycleRemainder g x).support ∪ (g.cycleOf x).support := Finset.subset_union_left
    _ = (cycleRemainder g x * g.cycleOf x).support :=
      (cycleRemainder_disjoint g x).support_mul.symm
    _ = g.support := congrArg support (cycleRemainder_mul_cycle g x)

theorem cycleRemainder_fix (g : Perm α) (x y : α) (hxy : g.SameCycle x y) :
    cycleRemainder g x y = y := by
  by_cases hx : g x = x
  · have he : x = y := hxy.eq_of_left hx
    subst y
    simp [cycleRemainder, (cycleOf_eq_one_iff g).mpr hx, hx]
  · exact notMem_support.mp
      ((cycleRemainder_disjoint g x).symm.mem_imp
        (mem_support_cycleOf_iff.mpr ⟨hxy, mem_support.mpr hx⟩))

theorem cycleRemainder_fix_self (g : Perm α) (x : α) : cycleRemainder g x x = x :=
  cycleRemainder_fix g x x SameCycle.rfl

theorem cycleOf_cycleRemainder (g : Perm α) (x y : α) (hxy : ¬g.SameCycle x y) :
    (cycleRemainder g x).cycleOf y = g.cycleOf y := by
  have hf : g.cycleOf x y = y := cycleOf_apply_of_not_sameCycle hxy
  have he := cycleOf_mul_of_apply_right_eq_self (cycleRemainder_disjoint g x).commute y hf
  rw [cycleRemainder_mul_cycle] at he
  exact he.symm

/-- Multiplying by a swap between different cycles increases `τ` by one. -/
theorem tau_swap_mul_of_not_sameCycle (g : Perm α) (x y : α)
    (hxy : ¬g.SameCycle x y) : τ (swap x y * g) = τ g + 1 := by
  let f := g.cycleOf x
  let h := cycleRemainder g x
  let f' := h.cycleOf y
  let h' := cycleRemainder h y
  have hfh : f.Disjoint h := (cycleRemainder_disjoint g x).symm
  have hf'h' : f'.Disjoint h' := (cycleRemainder_disjoint h y).symm
  have hf'f : f'.Disjoint f := hfh.symm.mono (support_cycleOf_le h y) (by rfl)
  have hfh' : f.Disjoint h' :=
    hfh.mono (by rfl) (cycleRemainder_support_subset h y)
  have hh'x : h' x = x := by
    apply notMem_support.mp
    intro hx
    have he := cycleRemainder_fix_self g x
    exact mem_support.mp (cycleRemainder_support_subset h y hx) he
  have hh'y : h' y = y := cycleRemainder_fix_self h y
  have hswaph' : (swap x y).Disjoint h' := by
    intro z
    by_cases hzx : z = x
    · exact Or.inr (hzx ▸ hh'x)
    by_cases hzy : z = y
    · exact Or.inr (hzy ▸ hh'y)
    exact Or.inl (swap_apply_of_ne_of_ne hzx hzy)
  have hg : (f * f') * h' = g := by
    rw [mul_assoc, cycle_mul_remainder h y, cycle_mul_remainder g x]
  have ht : τ g = τ f + τ f' + τ h' := by
    rw [← hg, tau_disjoint_mul (hfh'.mul_left hf'h'),
      tau_disjoint_mul hf'f.symm]
  have hgy : f' = g.cycleOf y := cycleOf_cycleRemainder g x y hxy
  obtain ⟨l₁, hl₁⟩ := cycleLabels_head g x
  obtain ⟨l₂, hl₂⟩ := cycleLabels_head g y
  have hnodup : ((x :: l₁) ++ y :: l₂).Nodup := by
    rw [← hl₁, ← hl₂]
    exact cycleLabels_append_nodup g x y hxy
  have hjoin : τ (swap x y * f * f') = τ f + τ f' + 1 := by
    change τ (swap x y * g.cycleOf x * f') = τ (g.cycleOf x) + τ f' + 1
    rw [hgy, ← cycleLabels_formPerm g x, ← cycleLabels_formPerm g y, hl₁, hl₂]
    exact tau_join_cycles x y l₁ l₂ hnodup
  calc
    τ (swap x y * g) = τ ((swap x y * f * f') * h') := by
      congr 1
      simpa only [mul_assoc] using congrArg (fun p => swap x y * p) hg.symm
    _ = τ (swap x y * f * f') + τ h' :=
      tau_disjoint_mul ((hswaph'.mul_left hfh').mul_left hf'h')
    _ = τ g + 1 := by rw [hjoin, ht]; omega

/-- Multiplying by a swap within one cycle decreases `τ` by one. -/
theorem tau_swap_mul_of_sameCycle (g : Perm α) (x y : α)
    (hxy : g.SameCycle x y) (hne : x ≠ y) : τ (swap x y * g) + 1 = τ g := by
  let f := g.cycleOf x
  let h := cycleRemainder g x
  have hfh : f.Disjoint h := (cycleRemainder_disjoint g x).symm
  have hhx : h x = x := cycleRemainder_fix_self g x
  have hhy : h y = y := cycleRemainder_fix g x y hxy
  have hswaph : (swap x y).Disjoint h := by
    intro z
    by_cases hzx : z = x
    · exact Or.inr (hzx ▸ hhx)
    by_cases hzy : z = y
    · exact Or.inr (hzy ▸ hhy)
    exact Or.inl (swap_apply_of_ne_of_ne hzx hzy)
  obtain ⟨l, hl⟩ := cycleLabels_head g x
  have hy : y ∈ l := by
    have hm := (mem_cycleLabels g x y).mpr hxy
    rw [hl] at hm
    exact (List.mem_cons.mp hm).resolve_left (fun he => hne he.symm)
  obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hy
  have hf : f = ((x :: l₁) ++ y :: l₂).formPerm := by
    change g.cycleOf x = _
    rw [← cycleLabels_formPerm g x, hl, he]
    rfl
  have hnodup : ((x :: l₁) ++ y :: l₂).Nodup := by
    have hn := cycleLabels_nodup g x
    rw [hl, he] at hn
    exact hn
  have h₁ := hnodup.of_append_left
  have h₂ := hnodup.of_append_right
  have hd := List.disjoint_of_nodup_append hnodup
  have hynot : y ∉ x :: l₁ := fun hy => hd hy List.mem_cons_self
  have hcut : τ (swap x y * f) + 1 = τ f := by
    rw [hf, swap_mul_formPerm_split x y l₁ l₂ hynot,
      tau_disjoint_mul (formPerm_disjoint_of_lists _ _ hd),
      tau_formPerm _ h₁, tau_formPerm _ h₂, tau_formPerm _ hnodup]
    simp
    omega
  have ht : τ g = τ f + τ h := by
    rw [← cycle_mul_remainder g x, tau_disjoint_mul hfh]
  have heval : swap x y * g = (swap x y * f) * h := by
    change swap x y * g = (swap x y * g.cycleOf x) * cycleRemainder g x
    rw [mul_assoc, cycle_mul_remainder]
  rw [heval, tau_disjoint_mul (hswaph.mul_left hfh), ht]
  omega

theorem tau_swap_mul_le (g : Perm α) (x y : α) : τ (swap x y * g) ≤ τ g + 1 := by
  by_cases hne : x = y
  · subst y
    simp only [swap_self]
    change τ g ≤ τ g + 1
    omega
  · by_cases hxy : g.SameCycle x y
    · have := tau_swap_mul_of_sameCycle g x y hxy hne
      omega
    · rw [tau_swap_mul_of_not_sameCycle g x y hxy]

theorem tau_le_swap_mul_add_one (g : Perm α) (x y : α) : τ g ≤ τ (swap x y * g) + 1 := by
  simpa only [swap_mul_self_mul] using tau_swap_mul_le (swap x y * g) x y

/-- Every transposition factorization has length at least `τ` of its value. -/
theorem tau_prod_le_length (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsSwap) :
    τ l.prod ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨x, y, _, rfl⟩ := hl a List.mem_cons_self
    have ht := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    have hs := tau_swap_mul_le l.prod x y
    rw [List.prod_cons, List.length_cons]
    omega

end ConjugacyDiametersPORC

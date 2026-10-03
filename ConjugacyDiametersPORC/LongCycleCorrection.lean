import ConjugacyDiametersPORC.PeelingBudget

/-!
# Repeated long-cycle correction

The sum `Qlong(g)` of the capacities `ν(ℓ)` decreases by exactly one at each
peeling step. Any prescribed number of steps up to that sum creates at least
`d` new fixed labels per step and uses exactly one generator per step.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

def Qlong (lam : CycleType) {β : Type*} [Fintype β] [DecidableEq β] (g : Perm β) : ℕ :=
  (g.cycleType.map (ν lam)).sum

private theorem exists_positive_capacity (lam : CycleType) (s : Multiset ℕ)
    (h : 0 < (s.map (ν lam)).sum) : ∃ ℓ ∈ s, 0 < ν lam ℓ := by
  induction s using Multiset.induction_on with
  | empty => simp at h
  | cons ℓ s ih =>
    by_cases hℓ : 0 < ν lam ℓ
    · exact ⟨ℓ, by simp, hℓ⟩
    · have hs : 0 < (s.map (ν lam)).sum := by
        simp only [Multiset.map_cons, Multiset.sum_cons] at h
        omega
      obtain ⟨t, ht, hν⟩ := ih hs
      exact ⟨t, Multiset.mem_cons_of_mem ht, hν⟩

theorem Qlong_disjoint_mul (lam : CycleType) {β : Type*} [Fintype β] [DecidableEq β]
    {f g : Perm β} (hd : f.Disjoint g) : Qlong lam (f * g) = Qlong lam f + Qlong lam g := by
  simp [Qlong, hd.cycleType_mul]

theorem Qlong_formPerm (lam : CycleType) {β : Type*} [Fintype β] [DecidableEq β]
    (l : List β) (hn : l.Nodup) (hp : 0 < l.length) : Qlong lam l.formPerm = ν lam l.length := by
  by_cases h₂ : 2 ≤ l.length
  · rw [Qlong, (List.isCycle_formPerm hn h₂).cycleType, support_card_formPerm l hn h₂]
    simp
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (show l.length = 1 by omega)
    have hb : 1 < lam.b := by
      have he := lam.two_mul_h_le_b
      have hh := lam.h_pos
      omega
    simp [Qlong, nu_of_short lam hb]

theorem exists_long_peeling (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (hq : 0 < Qlong lam g) :
    ∃ f ∈ C lam n, (g * f⁻¹).support.card + lam.d ≤ g.support.card ∧
      Qlong lam (g * f⁻¹) + 1 = Qlong lam g := by
  obtain ⟨ℓ, hℓ, hν⟩ := exists_positive_capacity lam g.cycleType hq
  have hb : lam.b ≤ ℓ := (nu_pos_iff lam ℓ).mp hν
  obtain ⟨c, h, hgh, hd, hc, hcl⟩ := mem_cycleType_iff.mp hℓ
  obtain ⟨x, hx⟩ := hc.nonempty_support
  let l := c.toList x
  have hlc : l.formPerm = c := (formPerm_toList c x).trans (hc.cycleOf_eq (mem_support.mp hx))
  have hllen : l.length = ℓ := by
    rw [length_toList, hc.cycleOf_eq (mem_support.mp hx), hcl]
  obtain ⟨f, hft, _, u, hun, husub, hup, hul, hprod, _⟩ :=
    exists_peeling_on_list lam l (nodup_toList c x) (by rwa [hllen])
  have hus : u.formPerm.support ⊆ c.support := by
    intro y hy
    have hm : y ∈ l := husub.subset (List.mem_toFinset.mp (List.support_formPerm_le _ hy))
    exact mem_support.mpr
      ((not_congr (mem_toList_iff.mp hm).1.apply_eq_self_iff).mp (mem_support.mp hx))
  have hdu : h.Disjoint u.formPerm := hd.symm.mono (by rfl) hus
  have he : g * f⁻¹ = h * u.formPerm := by
    rw [hgh, hd.commute.eq, mul_assoc, ← hlc, hprod]
  have hnew : (g * f⁻¹).support.card + lam.d ≤ g.support.card := by
    have huc : u.formPerm.support.card ≤ u.length := by
      calc
        _ ≤ u.toFinset.card := Finset.card_le_card (List.support_formPerm_le u)
        _ = _ := by simp [List.card_toFinset, List.dedup_eq_self.mpr hun]
    rw [he, hdu.card_support_mul, hgh, hd.card_support_mul, hcl]
    rw [hllen] at hul
    omega
  have hule : u.length = ℓ - lam.d := by rw [hllen] at hul; omega
  have hqnew : Qlong lam (g * f⁻¹) + 1 = Qlong lam g := by
    rw [he, Qlong_disjoint_mul lam hdu, Qlong_formPerm lam u hun hup,
      hgh, Qlong_disjoint_mul lam hd]
    have hqc : Qlong lam c = ν lam ℓ := by simp [Qlong, hc.cycleType, hcl]
    rw [hqc, hule]
    have he := nu_after_one lam hb
    omega
  exact ⟨f, hft, hnew, hqnew⟩

/-- The first reduction case of **Lemma 8**, before applying the common budget. -/
theorem long_cycle_correction (lam : CycleType) {n : ℕ} (g : SymmetricGroup n) (t : ℕ)
    (ht : t ≤ Qlong lam g) :
    ∃ f : SymmetricGroup n, ∃ w : List (SymmetricGroup n), IsFactorization lam f w ∧
      w.length = t ∧ (g * f⁻¹).support.card + lam.d * t ≤ g.support.card := by
  induction t generalizing g with
  | zero => exact ⟨1, [], isFactorization_nil lam n, rfl, by simp⟩
  | succ t ih =>
    obtain ⟨f, hf, hs, hq⟩ := exists_long_peeling lam g (by omega)
    obtain ⟨a, w, hw, hlen, hgain⟩ := ih (g * f⁻¹) (by omega)
    refine ⟨a * f, w ++ [f], hw.append (isFactorization_singleton lam hf),
      by simp [hlen], ?_⟩
    have he : g * (a * f)⁻¹ = (g * f⁻¹) * a⁻¹ := by simp [mul_assoc]
    rw [he, Nat.mul_succ]
    omega

end ConjugacyDiametersPORC

import ConjugacyDiametersPORC.PeelingBlocks
import ConjugacyDiametersPORC.CycleCuts
import ConjugacyDiametersPORC.Diameter

/-!
# Long-cycle peeling

Place the constituent cycles on consecutive blocks of a displayed long cycle.
Multiplication by their inverse retains each block's first label and fixes all
its other labels. The survivor has length `ℓ-d`, including length one.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The consecutive-block construction on an injectively labelled cycle. -/
theorem exists_peeling_on_list (lam : CycleType) (l : List β) (hn : l.Nodup)
    (hlen : lam.b ≤ l.length) :
    ∃ f : Perm β, f.cycleType = lam.parts ∧ f.support ⊆ l.toFinset ∧
      ∃ u : List β, u.Nodup ∧ u.Sublist l ∧ 0 < u.length ∧
        u.length + lam.d = l.length ∧ l.formPerm * f⁻¹ = u.formPerm ∧
          lam.d ≤ (l.formPerm.support \ u.formPerm.support).card := by
  classical
  obtain ⟨bs, t, hcat, hks, ht⟩ := Peeling.exists_blocks lam.parts.toList
    (fun k hk => lt_of_lt_of_le (by decide) (lam.two_le k (Multiset.mem_toList.mp hk)))
    l (by simpa [CycleType.b] using hlen)
  have hnfull : (Peeling.labels bs ++ t).Nodup := hcat ▸ hn
  have hnbs : (Peeling.labels bs).Nodup := (List.nodup_append.mp hnfull).1
  have hblen (b : Peeling.Block β) (hb : b ∈ bs) : 2 ≤ (Peeling.blockList b).length := by
    apply lam.two_le
    apply Multiset.mem_toList.mp
    rw [← hks]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hnblock (b : Peeling.Block β) (hb : b ∈ bs) : (Peeling.blockList b).Nodup :=
    hnbs.sublist (Peeling.block_sublist_labels hb)
  let f := (Peeling.factors bs).prod
  let u := Peeling.heads bs ++ t
  have hft : f.cycleType = lam.parts := by
    rw [cycleType_eq (Peeling.factors bs) rfl _ (Peeling.factors_pairwise bs hnbs)]
    · have he : (Peeling.factors bs).map (fun a => a.support.card) = lam.parts.toList := by
        rw [Peeling.factors, List.map_map]
        calc
          _ = bs.map (fun b => (Peeling.blockList b).length) := by
            apply List.map_congr_left
            intro b hb
            exact support_card_formPerm _ (hnblock b hb) (hblen b hb)
          _ = _ := hks
      simp only [Function.comp_def, he, Multiset.coe_toList]
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact List.isCycle_formPerm (hnblock b hb) (hblen b hb)
  have hfs : f.support ⊆ l.toFinset := by
    intro x hx
    obtain ⟨a, ha, hx⟩ := exists_mem_support_of_mem_support_prod hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hm : x ∈ Peeling.labels bs := Peeling.block_mem_labels hb
      (List.mem_toFinset.mp (List.support_formPerm_le _ hx))
    apply List.mem_toFinset.mpr
    rw [← hcat]
    exact List.mem_append_left t hm
  have husub : u.Sublist l := by
    rw [← hcat]
    exact (Peeling.heads_sublist bs).append_right t
  have hun : u.Nodup := hn.sublist husub
  have hbsc : bs.length = lam.h := by
    have he := congrArg List.length hks
    simpa [CycleType.h] using he
  have htt : t.length = l.length - lam.b := by simpa [CycleType.b] using ht
  have hul : u.length + lam.d = l.length := by
    have he := lam.h_add_d
    simp only [u, List.length_append, Peeling.heads, List.length_map, hbsc, htt]
    omega
  have hup : 0 < u.length := by
    have he := lam.h_pos
    simp only [u, List.length_append, Peeling.heads, List.length_map, hbsc]
    omega
  have hprod : l.formPerm * f⁻¹ = u.formPerm := by
    have he : l.formPerm = u.formPerm * f := by
      rw [← hcat]
      exact Peeling.formPerm_blocks bs t hnfull
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have hfixed : lam.d ≤ (l.formPerm.support \ u.formPerm.support).card := by
    have hl₂ : 2 ≤ l.length := by
      have he := lam.two_mul_h_le_b
      have hh := lam.h_pos
      omega
    have hlc := support_card_formPerm l hn hl₂
    have huc : u.formPerm.support.card ≤ u.length := by
      calc
        _ ≤ u.toFinset.card := Finset.card_le_card (List.support_formPerm_le u)
        _ = _ := by simp [List.card_toFinset, List.dedup_eq_self.mpr hun]
    have he := Finset.le_card_sdiff u.formPerm.support l.formPerm.support
    omega
  exact ⟨f, hft, hfs, u, hun, husub, hup, hul, hprod, hfixed⟩

/-- **Lemma 7.** Peel a selected long cycle, leaving all other cycles unchanged.
The survivor is represented as a list, so a singleton is retained explicitly. -/
theorem lemma7 (lam : CycleType) {n : ℕ} (g : SymmetricGroup n) (x : Fin n)
    (hlen : lam.b ≤ (cycleLabels g x).length) :
    ∃ f ∈ C lam n, f.support ⊆ (g.cycleOf x).support ∧
      ∃ u : List (Fin n), u.Nodup ∧ u.Sublist (cycleLabels g x) ∧ 0 < u.length ∧
        u.length + lam.d = (cycleLabels g x).length ∧
        g * f⁻¹ = cycleRemainder g x * u.formPerm ∧
        (cycleRemainder g x).Disjoint u.formPerm ∧
          lam.d ≤ (g.support \ (g * f⁻¹).support).card := by
  obtain ⟨f, hft, hfs, u, hun, husub, hup, hul, hprod, hfixed⟩ :=
    exists_peeling_on_list lam (cycleLabels g x) (cycleLabels_nodup g x) hlen
  have hl₂ : 2 ≤ (cycleLabels g x).length := by
    have he := lam.two_mul_h_le_b
    have hh := lam.h_pos
    omega
  have hlabels : (cycleLabels g x).toFinset = (g.cycleOf x).support := by
    rw [← cycleLabels_formPerm g x]
    apply (List.support_formPerm_of_nodup _ (cycleLabels_nodup g x) _).symm
    intro y he
    have hn := congrArg List.length he
    simp only [List.length_singleton] at hn
    omega
  have hus : u.formPerm.support ⊆ (g.cycleOf x).support := by
    intro y hy
    rw [← hlabels]
    apply List.mem_toFinset.mpr
    exact husub.subset (List.mem_toFinset.mp (List.support_formPerm_le _ hy))
  have hd : (cycleRemainder g x).Disjoint u.formPerm :=
    (cycleRemainder_disjoint g x).mono (by rfl) hus
  have he : g * f⁻¹ = cycleRemainder g x * u.formPerm := by
    calc
      _ = (cycleRemainder g x * g.cycleOf x) * f⁻¹ := by rw [cycleRemainder_mul_cycle]
      _ = cycleRemainder g x * ((cycleLabels g x).formPerm * f⁻¹) := by
        rw [cycleLabels_formPerm, mul_assoc]
      _ = _ := by rw [hprod]
  have hdiff : g.support \ (g * f⁻¹).support = (g.cycleOf x).support \ u.formPerm.support := by
    have ho : g.support = (cycleRemainder g x).support ∪ (g.cycleOf x).support := by
      rw [← (cycleRemainder_disjoint g x).support_mul, cycleRemainder_mul_cycle]
    rw [ho, he, hd.support_mul]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hy, hn⟩
      exact ⟨hy.resolve_left (fun hy => hn (Or.inl hy)), fun hy => hn (Or.inr hy)⟩
    · rintro ⟨hy, hn⟩
      refine ⟨Or.inr hy, ?_⟩
      rintro (hr | hu)
      · exact (Finset.disjoint_left.mp ((disjoint_iff_disjoint_support).mp
          (cycleRemainder_disjoint g x))) hr hy
      · exact hn hu
  refine ⟨f, hft, by rwa [hlabels] at hfs, u, hun, husub, hup, hul, he, hd, ?_⟩
  rw [hdiff]
  rwa [cycleLabels_formPerm] at hfixed

end ConjugacyDiametersPORC

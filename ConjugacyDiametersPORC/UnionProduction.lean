import ConjugacyDiametersPORC.CycleFamily
import ConjugacyDiametersPORC.ProductionRate
import ConjugacyDiametersPORC.RationalProgram
import ConjugacyDiametersPORC.ClearDenominators

/-! # Production rates with a convex mixture of generator inventories -/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

abbrev Entry (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) := DictionaryEntry F.pattern r hr
abbrev Variables (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) := Entry F r hr ⊕ F.Index

def matrix (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    Matrix (Option F.pattern.J) (Variables F r hr) ℚ
  | none, Sum.inl _ => 0
  | none, Sum.inr _ => 1
  | some ℓ, Sum.inl A => A.val.c ℓ
  | some ℓ, Sum.inr j => -(F.m j ℓ : ℚ)

def rhs (F : CycleFamily) : Option F.pattern.J → ℚ
  | none => 1
  | some _ => 0

def objectiveCoefficients (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) : Variables F r hr → ℚ
  | Sum.inl A => A.val.s
  | Sum.inr _ => 0

def Feasible (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) (z : Variables F r hr → ℝ) : Prop :=
  (∀ i, 0 ≤ z i) ∧ (∑ j, z (Sum.inr j)) = 1 ∧
    ∀ ℓ, ∑ A, (A.val.c ℓ : ℝ) * z (Sum.inl A) = ∑ j, (F.m j ℓ : ℝ) * z (Sum.inr j)

theorem feasible_iff (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) (z : Variables F r hr → ℝ) :
    RationalProgram.Feasible (matrix F r hr) (rhs F) z ↔ Feasible F r hr z := by
  constructor
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_, fun ℓ => ?_⟩
    · simpa [matrix, rhs, Fintype.sum_sum_type] using he none
    · have h := he (some ℓ)
      simp only [matrix, rhs, Fintype.sum_sum_type, Rat.cast_natCast, Rat.cast_neg,
        neg_mul, Finset.sum_neg_distrib, Rat.cast_zero] at h
      linarith
  · rintro ⟨hn, hy, hc⟩
    refine ⟨hn, fun k => ?_⟩
    cases k with
    | none => simpa [matrix, rhs, Fintype.sum_sum_type] using hy
    | some ℓ =>
      simp only [matrix, rhs, Fintype.sum_sum_type, Rat.cast_natCast, Rat.cast_neg,
        neg_mul, Finset.sum_neg_distrib, Rat.cast_zero]
      linarith [hc ℓ]

noncomputable def production (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r)
    (z : Variables F r hr → ℝ) : ℝ := ∑ A, (A.val.s : ℝ) * z (Sum.inl A)

theorem objective_eq (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) (z : Variables F r hr → ℝ) :
    RationalProgram.objective (objectiveCoefficients F r hr) z = production F r hr z := by
  simp [RationalProgram.objective, objectiveCoefficients, production, Fintype.sum_sum_type]

theorem sum_m (F : CycleFamily) (ℓ : F.pattern.J) : ∑ j, F.m j ℓ = F.pattern.m ℓ := by
  classical
  change (∑ j, (Multiset.countAddMonoidHom (ℓ : ℕ)) (F.type j).parts) =
    (Multiset.countAddMonoidHom (ℓ : ℕ)) (∑ j, (F.type j).parts)
  rw [map_sum]

theorem y_le_one {F : CycleFamily} {r : ℕ} {hr : 2 ≤ r} {z : Variables F r hr → ℝ}
    (hz : Feasible F r hr z) (j : F.Index) : z (Sum.inr j) ≤ 1 := by
  rw [← hz.2.1]
  exact Finset.single_le_sum (fun k _ => hz.1 (Sum.inr k)) (Finset.mem_univ j)

theorem resource_le {F : CycleFamily} {r : ℕ} {hr : 2 ≤ r} {z : Variables F r hr → ℝ}
    (hz : Feasible F r hr z) (ℓ : F.pattern.J) :
    ∑ A, (A.val.c ℓ : ℝ) * z (Sum.inl A) ≤ F.pattern.m ℓ := by
  rw [hz.2.2]
  calc
    _ ≤ ∑ j, (F.m j ℓ : ℝ) := Finset.sum_le_sum (fun j _ => by
      simpa using mul_le_mul_of_nonneg_left (y_le_one hz j) (Nat.cast_nonneg (F.m j ℓ)))
    _ = _ := by exact_mod_cast sum_m F ℓ

theorem x_sum_le {F : CycleFamily} {r : ℕ} {hr : 2 ≤ r} {z : Variables F r hr → ℝ}
    (hz : Feasible F r hr z) : ∑ A, z (Sum.inl A) ≤ F.pattern.h := by
  calc
    _ ≤ ∑ A : Entry F r hr, (∑ ℓ : F.pattern.J, (A.val.c ℓ : ℝ)) * z (Sum.inl A) :=
      Finset.sum_le_sum (fun A _ => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (dictionary_inventory_pos F.pattern r hr A) (hz.1 (Sum.inl A)))
    _ = ∑ ℓ : F.pattern.J, ∑ A, (A.val.c ℓ : ℝ) * z (Sum.inl A) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ ℓ : F.pattern.J, (F.pattern.m ℓ : ℝ) :=
      Finset.sum_le_sum (fun ℓ _ => resource_le hz ℓ)
    _ = _ := by
      exact_mod_cast (Finset.sum_coe_sort F.pattern.J F.pattern.m).trans
        F.pattern.h_eq_sum_m.symm

theorem feasible_isCompact (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    IsCompact {z | Feasible F r hr z} := by
  have hc : IsClosed {z | Feasible F r hr z} := by
    simp_rw [← feasible_iff]
    exact RationalProgram.feasible_isClosed _ _
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Variables F r hr → ℝ)
    (fun _ => (F.pattern.h : ℝ)))).of_isClosed_subset hc
  intro z hz
  refine ⟨hz.1, fun i => ?_⟩
  cases i with
  | inl A => exact (Finset.single_le_sum (fun B _ => hz.1 (Sum.inl B))
      (Finset.mem_univ A)).trans (x_sum_le hz)
  | inr j =>
    have hh : (1 : ℝ) ≤ F.pattern.h := by exact_mod_cast F.pattern.h_pos
    exact (y_le_one hz j).trans hh

private theorem sum_count_mul {ι : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι]
    (l : List ι) (f : ι → ℝ) : ∑ A, (l.count A : ℝ) * f A = (l.map f).sum := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, ite_mul, add_comm]

theorem collection_resource (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r)
    (l : List (Entry F r hr)) (Q : ℕ) (ℓ : F.pattern.J) :
    ∑ A, (A.val.c ℓ : ℝ) * collectionWeights l Q A =
      (((l.map (fun A => A.val.c ℓ)).sum : ℕ) : ℝ) / Q := by
  classical
  unfold collectionWeights
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  rw [show (∑ A, (A.val.c ℓ : ℝ) * (l.count A : ℝ)) =
      (l.map (fun A => (A.val.c ℓ : ℝ))).sum by
    simpa only [mul_comm] using sum_count_mul l (fun A => (A.val.c ℓ : ℝ))]
  simp [Function.comp_def]

theorem exists_positive_feasible (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    ∃ z, Feasible F r hr z ∧ 0 < production F r hr z := by
  classical
  let j := F.first
  let m : ResourceVector F.pattern := F.m j
  let l := baselineCopies F.pattern r hr m
  let L := dictionaryList l (baselineCopies_mem F.pattern r hr m)
  let z : Variables F r hr → ℝ
    | Sum.inl A => collectionWeights L (r + 1) A
    | Sum.inr k => if k = j then 1 else 0
  have hc : (L.map (fun A => A.val.c)).sum = (r + 1) • m := by
    rw [dictionaryList_c, baselineCopies_c]
  have hres (ℓ : F.pattern.J) : ∑ A, (A.val.c ℓ : ℝ) * z (Sum.inl A) = F.m j ℓ := by
    rw [collection_resource]
    have he := congrArg (Pi.evalAddMonoidHom (fun _ : F.pattern.J => ℕ) ℓ) hc
    have hn : (L.map (fun A => A.val.c ℓ)).sum = (r + 1) * F.m j ℓ := by
      simpa [map_list_sum, List.map_map, Function.comp_def, m] using he
    rw [hn]
    simp [mul_div_cancel_left₀, show (r : ℝ) + 1 ≠ 0 by positivity]
  have hp : production F r hr z = (δ F.pattern m : ℝ) / (r + 1) := by
    change ConjugacyDiametersPORC.production F.pattern r hr (collectionWeights L (r + 1)) = _
    rw [collectionWeights_production, dictionaryList_s, baselineCopies_s]
    simp
  have hd : 0 < δ F.pattern m := by
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (F.type j).nonempty
    let ℓ : F.pattern.J := ⟨t, (F.pattern.mem_J t).mpr (F.mem_pattern ht)⟩
    have hmt : 0 < m ℓ := Multiset.count_pos.mpr ht
    have ht2 := (F.type j).two_le t ht
    have hb : (t - 1) * m ℓ ≤ δ F.pattern m :=
      Finset.single_le_sum (f := fun k : F.pattern.J => ((k : ℕ) - 1) * m k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ℓ)
    have hprod := Nat.mul_pos (show 0 < t - 1 by omega) hmt
    exact hprod.trans_le hb
  refine ⟨z, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    cases i with
    | inl A => exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    | inr k => dsimp [z]; split_ifs <;> norm_num
  · simp [z]
  · intro ℓ
    rw [hres]
    simp [z]
  · rw [hp]
    exact div_pos (by exact_mod_cast hd) (by positivity)

noncomputable def Γ (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) : ℝ :=
  sSup {t | ∃ z, Feasible F r hr z ∧ t = production F r hr z}

theorem exists_rational_optimizer (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) :
    ∃ z : Variables F r hr → ℚ, Feasible F r hr (fun i => (z i : ℝ)) ∧
      ∀ w, Feasible F r hr w → production F r hr w ≤ production F r hr (fun i => (z i : ℝ)) := by
  have hc : IsCompact {z | RationalProgram.Feasible (matrix F r hr) (rhs F) z} := by
    simp_rw [feasible_iff]
    exact feasible_isCompact F r hr
  obtain ⟨z, hz, _⟩ := exists_positive_feasible F r hr
  obtain ⟨w, hw, hm⟩ := RationalProgram.exists_rational_maximum
    (matrix F r hr) (rhs F) (objectiveCoefficients F r hr) hc
      ⟨z, (feasible_iff F r hr z).mpr hz⟩
  refine ⟨w, (feasible_iff F r hr _).mp hw, fun y hy => ?_⟩
  simpa only [objective_eq] using hm y ((feasible_iff F r hr y).mpr hy)

theorem optimum_eq_Gamma {F : CycleFamily} {r : ℕ} {hr : 2 ≤ r}
    (z : Variables F r hr → ℝ) (hz : Feasible F r hr z)
    (hm : ∀ w, Feasible F r hr w → production F r hr w ≤ production F r hr z) :
    production F r hr z = Γ F r hr := by
  unfold Γ
  have hb : BddAbove {t | ∃ w, Feasible F r hr w ∧ t = production F r hr w} := by
    refine ⟨production F r hr z, ?_⟩
    rintro t ⟨w, hw, rfl⟩
    exact hm w hw
  have hn : ({t | ∃ w, Feasible F r hr w ∧ t = production F r hr w} : Set ℝ).Nonempty :=
    ⟨production F r hr z, z, hz, rfl⟩
  apply le_antisymm
  · exact le_csSup hb ⟨z, hz, rfl⟩
  · apply csSup_le hn
    rintro t ⟨w, hw, rfl⟩
    exact hm w hw

theorem production_le_Gamma {F : CycleFamily} {r : ℕ} {hr : 2 ≤ r}
    {z : Variables F r hr → ℝ} (hz : Feasible F r hr z) : production F r hr z ≤ Γ F r hr := by
  obtain ⟨w, hw, hm⟩ := exists_rational_optimizer F r hr
  rw [← optimum_eq_Gamma _ hw hm]
  exact hm _ hz

theorem Gamma_pos (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) : 0 < Γ F r hr := by
  obtain ⟨z, hz, hp⟩ := exists_positive_feasible F r hr
  exact hp.trans_le (production_le_Gamma hz)

theorem Gamma_rational (F : CycleFamily) (r : ℕ) (hr : 2 ≤ r) : ∃ a : ℚ, (a : ℝ) = Γ F r hr := by
  obtain ⟨z, hz, hm⟩ := exists_rational_optimizer F r hr
  refine ⟨∑ A, (A.val.s : ℚ) * z (Sum.inl A), ?_⟩
  rw [← optimum_eq_Gamma _ hz hm]
  simp [production]

end FiniteUnion
end ConjugacyDiametersPORC

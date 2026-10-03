import ConjugacyDiametersPORC.DictionaryUnion
import ConjugacyDiametersPORC.GeneratorExpansion
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# The production rate

The optimization uses nonnegative real weights on the finite realized dictionary.
The resource constraints prescribe the inventory of one generator.
-/

namespace ConjugacyDiametersPORC

abbrev DictionaryEntry (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) := ↥(𝒜 lam r hr)

noncomputable instance dictionaryEntryFintype (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    Fintype (DictionaryEntry lam r hr) := by
  let _ := (dictionary_finite lam r hr).to_subtype
  exact Fintype.ofFinite _

/-- Feasibility in the real linear program defining `Γ_r`. -/
def ProductionFeasible (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (x : DictionaryEntry lam r hr → ℝ) : Prop :=
  (∀ A, 0 ≤ x A) ∧ ∀ ℓ : lam.J, ∑ A, (A.val.c ℓ : ℝ) * x A = lam.m ℓ

noncomputable def production (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (x : DictionaryEntry lam r hr → ℝ) : ℝ := ∑ A, (A.val.s : ℝ) * x A

def productionValues (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) : Set ℝ :=
  {t | ∃ x, ProductionFeasible lam r hr x ∧ t = production lam r hr x}

/-- `Γ_r`, defined as the supremum of the real objective values. -/
noncomputable def Γ (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) : ℝ :=
  sSup (productionValues lam r hr)

theorem dictionary_inventory_pos (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (A : DictionaryEntry lam r hr) : (1 : ℝ) ≤ ∑ ℓ : lam.J, (A.val.c ℓ : ℝ) := by
  have hc := dictionary_c_ne_zero lam r hr A.val A.property
  have hn : 0 < A.val.word.factors.length :=
    List.length_pos_iff.mpr (A.val.word.c_ne_zero_iff.mp hc)
  have he := A.val.word.sum_c
  have h : 1 ≤ ∑ ℓ : lam.J, A.val.c ℓ := by
    change 1 ≤ ∑ ℓ : lam.J, A.val.word.c ℓ
    omega
  exact_mod_cast h

theorem feasible_weight_bound (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (x : DictionaryEntry lam r hr → ℝ) (hx : ProductionFeasible lam r hr x) :
    ∑ A, x A ≤ (lam.h : ℝ) := by
  calc
    ∑ A, x A ≤ ∑ A, (∑ ℓ : lam.J, (A.val.c ℓ : ℝ)) * x A := by
      apply Finset.sum_le_sum
      intro A _
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (dictionary_inventory_pos lam r hr A) (hx.1 A)
    _ = ∑ ℓ : lam.J, ∑ A, (A.val.c ℓ : ℝ) * x A := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ ℓ : lam.J, (lam.m ℓ : ℝ) := by simp_rw [hx.2]
    _ = (lam.h : ℝ) := by
      exact_mod_cast (Finset.sum_coe_sort lam.J lam.m).trans lam.h_eq_sum_m.symm

theorem feasible_production_bound (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (x : DictionaryEntry lam r hr → ℝ) (hx : ProductionFeasible lam r hr x) :
    production lam r hr x ≤ (∑ A : DictionaryEntry lam r hr, (A.val.s : ℝ)) * lam.h := by
  calc
    production lam r hr x ≤ ∑ A, (∑ B : DictionaryEntry lam r hr, (B.val.s : ℝ)) * x A := by
      apply Finset.sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_right _ (hx.1 A)
      exact Finset.single_le_sum (f := fun B : DictionaryEntry lam r hr => (B.val.s : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ A)
    _ = (∑ B : DictionaryEntry lam r hr, (B.val.s : ℝ)) * ∑ A, x A := by
      rw [Finset.mul_sum]
    _ ≤ (∑ B : DictionaryEntry lam r hr, (B.val.s : ℝ)) * lam.h :=
      mul_le_mul_of_nonneg_left (feasible_weight_bound lam r hr x hx)
        (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem productionValues_bddAbove (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    BddAbove (productionValues lam r hr) := by
  refine ⟨(∑ A : DictionaryEntry lam r hr, (A.val.s : ℝ)) * lam.h, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact feasible_production_bound lam r hr x hx

theorem production_le_Gamma (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (x : DictionaryEntry lam r hr → ℝ) (hx : ProductionFeasible lam r hr x) :
    production lam r hr x ≤ Γ lam r hr :=
  le_csSup (productionValues_bddAbove lam r hr) ⟨x, hx, rfl⟩

private theorem sum_count_mul {ι : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι]
    (l : List ι) (f : ι → ℝ) : ∑ A, (l.count A : ℝ) * f A = (l.map f).sum := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, ite_mul, add_comm]

open scoped Classical in
/-- Normalized dictionary multiplicities, `x_A = z_A/q`. -/
noncomputable def collectionWeights {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (l : List (DictionaryEntry lam r hr)) (q : ℕ) : DictionaryEntry lam r hr → ℝ :=
  fun A => (l.count A : ℝ) / q

theorem collectionWeights_feasible {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (l : List (DictionaryEntry lam r hr)) (q : ℕ) (hq : 0 < q)
    (hc : (l.map (fun A => A.val.c)).sum = q • (fun ℓ : lam.J => lam.m ℓ)) :
    ProductionFeasible lam r hr (collectionWeights l q) := by
  classical
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  constructor
  · intro A
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro ℓ
    have hn : (l.map (fun A => A.val.c ℓ)).sum = q * lam.m ℓ := by
      have h := congrArg (Pi.evalAddMonoidHom (fun _ : lam.J => ℕ) ℓ) hc
      simpa [map_list_sum, List.map_map, Function.comp_def] using h
    have hz : (l.map (fun A => (A.val.c ℓ : ℝ))).sum = (q : ℝ) * lam.m ℓ := by
      have h := congrArg (fun k : ℕ => (k : ℝ)) hn
      simpa [Nat.cast_list_sum, List.map_map, Function.comp_def] using h
    change (∑ A, (A.val.c ℓ : ℝ) * ((l.count A : ℝ) / q)) = _
    have hnum : (∑ A, (A.val.c ℓ : ℝ) * (l.count A : ℝ)) =
        (l.map (fun A => (A.val.c ℓ : ℝ))).sum := by
      simpa only [mul_comm] using sum_count_mul l (fun A => (A.val.c ℓ : ℝ))
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hnum, hz, mul_div_cancel_left₀ _ hqr]

theorem collectionWeights_production {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (l : List (DictionaryEntry lam r hr)) (q : ℕ) :
    production lam r hr (collectionWeights l q) =
      (((l.map (fun A => A.val.s)).sum : ℕ) : ℝ) / q := by
  classical
  unfold production collectionWeights
  have hnum : (∑ A, (A.val.s : ℝ) * (l.count A : ℝ)) =
      (l.map (fun A => (A.val.s : ℝ))).sum := by
    simpa only [mul_comm] using sum_count_mul l (fun A => (A.val.s : ℝ))
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, hnum]
  simp [Nat.cast_list_sum, List.map_map, Function.comp_def]

/-- Retain the membership witnesses when passing from a collection to its index type. -/
def dictionaryList {lam : CycleType} {r : ℕ} {hr : 2 ≤ r} (l : List (TargetWord lam r))
    (hl : ∀ A ∈ l, A ∈ 𝒜 lam r hr) : List (DictionaryEntry lam r hr) :=
  l.attach.map (fun A => ⟨A.val, hl A.val A.property⟩)

theorem dictionaryList_c {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (l : List (TargetWord lam r)) (hl : ∀ A ∈ l, A ∈ 𝒜 lam r hr) :
    ((dictionaryList l hl).map (fun A => A.val.c)).sum = (l.map TargetWord.c).sum := by
  simp [dictionaryList, List.map_map, Function.comp_def]

theorem dictionaryList_s {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (l : List (TargetWord lam r)) (hl : ∀ A ∈ l, A ∈ 𝒜 lam r hr) :
    ((dictionaryList l hl).map (fun A => A.val.s)).sum = (l.map TargetWord.s).sum := by
  simp [dictionaryList, List.map_map, Function.comp_def]

theorem production_ray_bound {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord lam α) (r : ℕ) (hr : 2 ≤ r) (s q : ℕ) (hq : 0 < q)
    (ht : w.HasTarget r s) (hc : w.c = q • (fun ℓ : lam.J => lam.m ℓ)) :
    (s : ℝ) ≤ q * Γ lam r hr := by
  obtain ⟨l, hl, hlc, hls⟩ := lemma4 w r hr s ht
  rw [TargetWord.unionList_c] at hlc
  rw [TargetWord.unionList_s] at hls
  let L := dictionaryList l hl
  have hLc : (L.map (fun A => A.val.c)).sum = q • (fun ℓ : lam.J => lam.m ℓ) := by
    rw [dictionaryList_c, hlc, hc]
  have hf := collectionWeights_feasible L q hq hLc
  have hp := production_le_Gamma lam r hr (collectionWeights L q) hf
  rw [collectionWeights_production, dictionaryList_s] at hp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : (s : ℝ) / q ≤ (((l.map TargetWord.s).sum : ℕ) : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast hls) (le_of_lt hqr)
  simpa [mul_comm] using (div_le_iff₀ hqr).mp (hs.trans hp)

/-- **Lemma 5, part 1.** A `q`-generator factorization produces at most `q Γ_r` target cycles. -/
theorem lemma5_part_one (lam : CycleType) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C lam n) (hq : 0 < w.length)
    (r : ℕ) (hr : 2 ≤ r) (s : ℕ) (ht : w.prod.cycleType = Multiset.replicate s r) :
    (s : ℝ) ≤ w.length * Γ lam r hr := by
  apply production_ray_bound (expandWord lam w hw) r hr s w.length hq
  · unfold ConstituentWord.HasTarget
    rw [expandWord_value]
    exact ht
  · exact expandWord_c lam w hw

theorem exists_baseline_feasible (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ x : DictionaryEntry lam r hr → ℝ, ProductionFeasible lam r hr x ∧
      production lam r hr x = (lam.d : ℝ) / ((r : ℝ) + 1) := by
  let m : ResourceVector lam := fun ℓ => lam.m ℓ
  let l := baselineCopies lam r hr m
  have hl : ∀ A ∈ l, A ∈ 𝒜 lam r hr := baselineCopies_mem lam r hr m
  let L := dictionaryList l hl
  have hLc : (L.map (fun A => A.val.c)).sum = (r + 1) • m := by
    rw [dictionaryList_c, baselineCopies_c]
  have hLs : (L.map (fun A => A.val.s)).sum = lam.d := by
    rw [dictionaryList_s, baselineCopies_s, delta_inventory]
  refine ⟨collectionWeights L (r + 1),
    collectionWeights_feasible L (r + 1) (Nat.succ_pos r) hLc, ?_⟩
  rw [collectionWeights_production, hLs]
  simp

theorem productionValues_nonempty (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    (productionValues lam r hr).Nonempty := by
  obtain ⟨x, hx, _⟩ := exists_baseline_feasible lam r hr
  exact ⟨production lam r hr x, x, hx, rfl⟩

theorem baseline_le_Gamma (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    (lam.d : ℝ) / ((r : ℝ) + 1) ≤ Γ lam r hr := by
  obtain ⟨x, hx, he⟩ := exists_baseline_feasible lam r hr
  rw [← he]
  exact production_le_Gamma lam r hr x hx

theorem Gamma_pos (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) : 0 < Γ lam r hr :=
  lt_of_lt_of_le (div_pos (by exact_mod_cast lam.d_pos) (by positivity))
    (baseline_le_Gamma lam r hr)

end ConjugacyDiametersPORC

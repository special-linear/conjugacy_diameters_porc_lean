import ConjugacyDiametersPORC.GeneratedGroup
import ConjugacyDiametersPORC.ConstituentWord

/-!
# Finite families of nontrivial generating types

The index set is nonempty and finite. Repeated types are harmless. The aggregate
type supplies the allowed constituent lengths for the shared dictionary.
-/

namespace ConjugacyDiametersPORC

structure CycleFamily where
  size : ℕ
  size_pos : 0 < size
  type : Fin size → CycleType

namespace CycleFamily

abbrev Index (F : CycleFamily) := Fin F.size

def first (F : CycleFamily) : F.Index := ⟨0, F.size_pos⟩

def pattern (F : CycleFamily) : CycleType where
  parts := ∑ j, (F.type j).parts
  nonempty := by
    intro he
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (F.type F.first).nonempty
    have hm : t ∈ ∑ j, (F.type j).parts := Multiset.mem_sum.mpr ⟨F.first, by simp, ht⟩
    rw [he] at hm
    simp at hm
  two_le := by
    intro t ht
    obtain ⟨j, _, hj⟩ := Multiset.mem_sum.mp ht
    exact (F.type j).two_le t hj

theorem mem_pattern (F : CycleFamily) {j : F.Index} {t : ℕ}
    (ht : t ∈ (F.type j).parts) : t ∈ F.pattern.parts := by
  change t ∈ ∑ k : F.Index, (F.type k).parts
  exact Multiset.mem_sum.mpr ⟨j, Finset.mem_univ j, ht⟩

/-- `b_*`, the largest support size of a generating type. -/
def b (F : CycleFamily) : ℕ := Finset.univ.sup (fun j => (F.type j).b)
/-- `d_*`, the largest transposition deficit of a generating type. -/
def d (F : CycleFamily) : ℕ := Finset.univ.sup (fun j => (F.type j).d)

theorem b_le (F : CycleFamily) (j : F.Index) : (F.type j).b ≤ F.b :=
  Finset.le_sup (f := fun j => (F.type j).b) (Finset.mem_univ j)

theorem d_le (F : CycleFamily) (j : F.Index) : (F.type j).d ≤ F.d :=
  Finset.le_sup (f := fun j => (F.type j).d) (Finset.mem_univ j)

theorem d_pos (F : CycleFamily) : 0 < F.d := ((F.type F.first).d_pos).trans_le (F.d_le _)

theorem b_two_le (F : CycleFamily) : 2 ≤ F.b := by
  have := (F.type F.first).two_mul_h_le_b
  have := (F.type F.first).h_pos
  have := F.b_le F.first
  omega

theorem exists_max_deficit (F : CycleFamily) : ∃ j : F.Index, (F.type j).d = F.d := by
  have hne : (Finset.univ : Finset F.Index).Nonempty := ⟨F.first, by simp⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun j => (F.type j).d)
  exact ⟨j, hj.symm⟩

theorem b_pos (F : CycleFamily) : 0 < F.b := lt_of_lt_of_le (by decide : 0 < 2) F.b_two_le

noncomputable def bestIndex (F : CycleFamily) : F.Index := F.exists_max_deficit.choose
noncomputable def best (F : CycleFamily) : CycleType := F.type F.bestIndex

theorem best_d (F : CycleFamily) : F.best.d = F.d := F.exists_max_deficit.choose_spec
theorem best_b_le (F : CycleFamily) : F.best.b ≤ F.b := F.b_le F.bestIndex

theorem d_lt_b (F : CycleFamily) : F.d < F.b := by
  have := F.best.h_add_d
  have := F.best.h_pos
  have := F.best_b_le
  rw [F.best_d] at *
  omega

/-- The positive residual offset `b_* - d_*` in the common peeling budget. -/
def h (F : CycleFamily) : ℕ := F.b - F.d

theorem h_pos (F : CycleFamily) : 0 < F.h := by
  have := F.d_lt_b
  unfold h
  omega

theorem h_add_d (F : CycleFamily) : F.h + F.d = F.b := Nat.sub_add_cancel F.d_lt_b.le

def m (F : CycleFamily) (j : F.Index) (t : F.pattern.J) : ℕ := (F.type j).m t

end CycleFamily

namespace FiniteUnion

def C (F : CycleFamily) (n : ℕ) : Set (SymmetricGroup n) :=
  {g | ∃ j : F.Index, g ∈ ConjugacyDiametersPORC.C (F.type j) n}

def G (F : CycleFamily) (n : ℕ) : Subgroup (SymmetricGroup n) := Subgroup.closure (C F n)

theorem single_C_le (F : CycleFamily) (j : F.Index) (n : ℕ) :
    ConjugacyDiametersPORC.C (F.type j) n ⊆ C F n := fun _ hg => ⟨j, hg⟩

theorem single_G_le (F : CycleFamily) (j : F.Index) (n : ℕ) :
    ConjugacyDiametersPORC.G (F.type j) n ≤ G F n :=
  Subgroup.closure_mono (single_C_le F j n)

@[simp]
theorem inv_mem_C_iff (F : CycleFamily) {n : ℕ} (g : SymmetricGroup n) :
    g⁻¹ ∈ C F n ↔ g ∈ C F n := by
  simp only [C, Set.mem_ofPred_eq, ConjugacyDiametersPORC.inv_mem_C_iff]

theorem alternatingGroup_le_G (F : CycleFamily) {n : ℕ} (hn : F.b + 1 ≤ n) :
    alternatingGroup (Fin n) ≤ G F n :=
  (ConjugacyDiametersPORC.alternatingGroup_le_G (F.type F.first)
    (by have := F.b_le F.first; omega)).trans (single_G_le F F.first n)

def AllEven (F : CycleFamily) : Prop := ∀ j : F.Index, Even (F.type j).d

theorem G_eq_alternatingGroup (F : CycleFamily) {n : ℕ} (hn : F.b + 1 ≤ n)
    (he : AllEven F) : G F n = alternatingGroup (Fin n) := by
  apply le_antisymm _ (alternatingGroup_le_G F hn)
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j, hj⟩
  change g ∈ alternatingGroup (Fin n)
  rw [Equiv.Perm.mem_alternatingGroup, sign_of_mem_C (F.type j) hj]
  exact (he j).neg_one_pow

theorem G_eq_symmetricGroup (F : CycleFamily) {n : ℕ} (hn : F.b + 1 ≤ n)
    (he : ¬ AllEven F) : G F n = ⊤ := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp he
  have ho : Odd (F.type j).d := Nat.not_even_iff_odd.mp hj
  have hs := ConjugacyDiametersPORC.G_eq_symmetricGroup (F.type j)
    (by have := F.b_le j; omega : (F.type j).b + 1 ≤ n) ho
  apply top_unique
  rw [← hs]
  exact single_G_le F j n

end FiniteUnion
end ConjugacyDiametersPORC

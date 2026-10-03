import ConjugacyDiametersPORC.CycleType
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Constituent words and their resource vectors

A constituent word is an ordered list of single cycles whose lengths lie in
`J`. Its value may have fixed labels which move in intermediate factors.
The support graph uses only labels appearing in factors.
-/

namespace ConjugacyDiametersPORC

/-- A resource vector indexed by the constituent lengths present in the type. -/
abbrev ResourceVector (lam : CycleType) := lam.J → ℕ

/-- One unit of the constituent inventory at the specified length. -/
def unitResource (lam : CycleType) (ℓ : lam.J) : ResourceVector lam :=
  fun t => if t = ℓ then 1 else 0

/-- Total transposition deficit of a resource vector. -/
def δ (lam : CycleType) (c : ResourceVector lam) : ℕ :=
  ∑ ℓ : lam.J, ((ℓ : ℕ) - 1) * c ℓ

@[simp]
theorem delta_zero (lam : CycleType) : δ lam 0 = 0 := by
  simp [δ]

@[simp]
theorem delta_unitResource (lam : CycleType) (ℓ : lam.J) :
    δ lam (unitResource lam ℓ) = (ℓ : ℕ) - 1 := by
  simp [δ, unitResource]

theorem delta_add (lam : CycleType) (c₁ c₂ : ResourceVector lam) :
    δ lam (c₁ + c₂) = δ lam c₁ + δ lam c₂ := by
  simp [δ, mul_add, Finset.sum_add_distrib]

theorem delta_smul (lam : CycleType) (q : ℕ) (c : ResourceVector lam) :
    δ lam (q • c) = q * δ lam c := by
  unfold δ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_id]
  ac_rfl

theorem delta_inventory (lam : CycleType) : δ lam (fun ℓ => lam.m ℓ) = lam.d := by
  rw [δ, Finset.sum_coe_sort lam.J (fun ℓ => (ℓ - 1) * lam.m ℓ)]
  exact lam.d_eq_sum_m.symm

/-- An ordered word whose factors are single cycles of lengths in `J`. -/
structure ConstituentWord (lam : CycleType) (α : Type*) [Fintype α] [DecidableEq α] where
  factors : List (Equiv.Perm α)
  isCycle : ∀ a ∈ factors, a.IsCycle
  length_mem_J : ∀ a ∈ factors, a.support.card ∈ lam.J

namespace ConstituentWord

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

/-- Value of the word, with its displayed factor order. -/
def value (w : ConstituentWord lam α) : Equiv.Perm α := w.factors.prod

/-- The multiplicity `c_ℓ(w)` of constituent factors of length `ℓ`. -/
def c (w : ConstituentWord lam α) : ResourceVector lam :=
  fun ℓ => (w.factors.map (fun a => a.support.card)).count (ℓ : ℕ)

/-- Union of the supports of all factors; unused labels are omitted. -/
def support (w : ConstituentWord lam α) : Finset α :=
  w.factors.foldr (fun a s => a.support ∪ s) ∅

/-- The word value has exactly `s` nontrivial cycles, all of length `r`. -/
def HasTarget (w : ConstituentWord lam α) (r s : ℕ) : Prop :=
  w.value.cycleType = Multiset.replicate s r

/-- The integer defect, before its nonnegativity has been established. -/
def E (w : ConstituentWord lam α) (r s : ℕ) : ℤ :=
  (δ lam w.c : ℤ) - ((r : ℤ) + 1) * (s : ℤ) + 2

/-- Support graph, on the labels actually used by factors. -/
def supportGraph (w : ConstituentWord lam α) : SimpleGraph w.support where
  Adj x y := x ≠ y ∧ ∃ a ∈ w.factors, x.val ∈ a.support ∧ y.val ∈ a.support
  symm := ⟨by
    rintro x y ⟨hxy, a, ha, hx, hy⟩
    exact ⟨hxy.symm, a, ha, hy, hx⟩⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

/-- Empty constituent word. -/
def nil : ConstituentWord lam α where
  factors := []
  isCycle := by simp
  length_mem_J := by simp

/-- Concatenation of constituent words on the same ambient labels. -/
def append (w₁ w₂ : ConstituentWord lam α) : ConstituentWord lam α where
  factors := w₁.factors ++ w₂.factors
  isCycle := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact w₁.isCycle a ha
    · exact w₂.isCycle a ha
  length_mem_J := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact w₁.length_mem_J a ha
    · exact w₂.length_mem_J a ha

@[simp]
theorem value_nil : (nil : ConstituentWord lam α).value = 1 := rfl

@[simp]
theorem c_nil : (nil : ConstituentWord lam α).c = 0 := by
  funext ℓ
  simp [c, nil]

@[simp]
theorem support_nil : (nil : ConstituentWord lam α).support = ∅ := rfl

theorem value_append (w₁ w₂ : ConstituentWord lam α) :
    (w₁.append w₂).value = w₁.value * w₂.value :=
  List.prod_append

theorem c_append (w₁ w₂ : ConstituentWord lam α) :
    (w₁.append w₂).c = w₁.c + w₂.c := by
  funext ℓ
  simp [c, append, List.count_append]

theorem sum_c (w : ConstituentWord lam α) : ∑ ℓ : lam.J, w.c ℓ = w.factors.length := by
  change (∑ ℓ : lam.J, (w.factors.map (fun a => a.support.card)).count (ℓ : ℕ)) = _
  rw [Finset.sum_coe_sort lam.J (fun ℓ => (w.factors.map (fun a => a.support.card)).count ℓ)]
  have hm : ∀ ℓ ∈ (w.factors.map (fun a => a.support.card) : Multiset ℕ), ℓ ∈ lam.J := by
    intro ℓ hℓ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hℓ
    exact w.length_mem_J a ha
  simpa using Multiset.sum_count_eq_card hm

theorem delta_c_eq_sum (w : ConstituentWord lam α) :
    δ lam w.c = (w.factors.map (fun a => a.support.card - 1)).sum := by
  let lengths := w.factors.map (fun a => a.support.card)
  have hmem : lengths.toFinset ⊆ lam.J := by
    intro ℓ hℓ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hℓ)
    exact w.length_mem_J a ha
  change (∑ ℓ : lam.J, ((ℓ : ℕ) - 1) * lengths.count (ℓ : ℕ)) = _
  rw [Finset.sum_coe_sort lam.J (fun ℓ => (ℓ - 1) * lengths.count ℓ)]
  calc
    ∑ ℓ ∈ lam.J, (ℓ - 1) * lengths.count ℓ =
        ∑ ℓ ∈ lengths.toFinset, (ℓ - 1) * lengths.count ℓ := by
      apply (Finset.sum_subset hmem _).symm
      intro ℓ _ hℓ
      have hz : lengths.count ℓ = 0 := by
        simp only [List.count_eq_zero, ← List.mem_toFinset]
        exact hℓ
      rw [hz, mul_zero]
    _ = (lengths.map (fun ℓ => ℓ - 1)).sum := by
      simpa [nsmul_eq_mul, mul_comm] using
        (Finset.sum_list_map_count lengths (fun ℓ => ℓ - 1)).symm
    _ = (w.factors.map (fun a => a.support.card - 1)).sum := by
      simp [lengths, List.map_map, Function.comp_def]

theorem c_ne_zero_iff (w : ConstituentWord lam α) : w.c ≠ 0 ↔ w.factors ≠ [] := by
  constructor
  · intro hc hnil
    apply hc
    funext ℓ
    simp [c, hnil]
  · intro hnil hc
    have hsum := w.sum_c
    rw [hc] at hsum
    simp only [Pi.zero_apply, Finset.sum_const_zero] at hsum
    exact hnil (List.length_eq_zero_iff.mp hsum.symm)

@[simp]
theorem mem_support (w : ConstituentWord lam α) (x : α) :
    x ∈ w.support ↔ ∃ a ∈ w.factors, x ∈ a.support := by
  have h : ∀ l : List (Equiv.Perm α),
      x ∈ l.foldr (fun a s => a.support ∪ s) ∅ ↔ ∃ a ∈ l, x ∈ a.support := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  exact h w.factors

theorem value_support_subset (w : ConstituentWord lam α) : w.value.support ⊆ w.support := by
  intro x hx
  exact (w.mem_support x).mpr (Equiv.Perm.exists_mem_support_of_mem_support_prod hx)

theorem support_append (w₁ w₂ : ConstituentWord lam α) :
    (w₁.append w₂).support = w₁.support ∪ w₂.support := by
  ext x
  simp [mem_support, append, List.mem_append, or_and_right, exists_or]

theorem support_nonempty (w : ConstituentWord lam α) (hw : w.factors ≠ []) :
    w.support.Nonempty := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hw
  have hlen := lam.two_le_of_mem_J (w.length_mem_J a ha)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < a.support.card by omega)
  exact ⟨x, (w.mem_support x).mpr ⟨a, ha, hx⟩⟩

end ConstituentWord

end ConjugacyDiametersPORC

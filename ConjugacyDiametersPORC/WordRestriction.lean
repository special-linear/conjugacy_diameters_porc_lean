import ConjugacyDiametersPORC.ConstituentWord
import ConjugacyDiametersPORC.Transpositions

/-!
# Restricting factors to their used labels

Restriction to a finite set containing every moved label preserves cycle types,
products, and constituent deficits. The support graph then uses the whole ambient
type, without adding unused labels to the connected-word argument.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem apply_mem_iff_of_support_subset (s : Finset α) (g : Perm α) (hg : g.support ⊆ s)
    (x : α) : g x ∈ s ↔ x ∈ s := by
  by_cases hx : x ∈ g.support
  · simp [hg hx, hg (apply_mem_support.mpr hx)]
  · rw [notMem_support.mp hx]

def restrictPerm (s : Finset α) (g : Perm α) (hg : g.support ⊆ s) : Perm s :=
  g.subtypePerm (apply_mem_iff_of_support_subset s g hg)

theorem restrictPerm_ofSubtype (s : Finset α) (g : Perm α) (hg : g.support ⊆ s) :
    ofSubtype (restrictPerm s g hg) = g :=
  ofSubtype_subtypePerm _ (fun _ hx => hg (mem_support.mpr hx))

theorem restrictPerm_cycleType (s : Finset α) (g : Perm α) (hg : g.support ⊆ s) :
    (restrictPerm s g hg).cycleType = g.cycleType := by
  rw [← cycleType_ofSubtype (g := restrictPerm s g hg), restrictPerm_ofSubtype]

theorem restrictPerm_support_card (s : Finset α) (g : Perm α) (hg : g.support ⊆ s) :
    (restrictPerm s g hg).support.card = g.support.card := by
  rw [← sum_cycleType, restrictPerm_cycleType, sum_cycleType]

theorem restrictPerm_mem_support (s : Finset α) (g : Perm α) (hg : g.support ⊆ s) (x : s) :
    x ∈ (restrictPerm s g hg).support ↔ x.val ∈ g.support := by
  simp only [mem_support, restrictPerm, subtypePerm_apply, ne_eq, Subtype.ext_iff]

theorem restrictPerm_isCycle (s : Finset α) (g : Perm α) (hg : g.support ⊆ s)
    (hcycle : g.IsCycle) : (restrictPerm s g hg).IsCycle := by
  rw [← card_cycleType_eq_one, restrictPerm_cycleType, card_cycleType_eq_one]
  exact hcycle

/-- Restrict a list of factors to a common finite set containing their supports. -/
def restrictFactors (s : Finset α) (l : List (Perm α)) (hl : ∀ a ∈ l, a.support ⊆ s) :
    List (Perm s) := l.attach.map (fun a => restrictPerm s a.val (hl a.val a.property))

theorem restrictFactors_ofSubtype (s : Finset α) (l : List (Perm α))
    (hl : ∀ a ∈ l, a.support ⊆ s) :
    (restrictFactors s l hl).map (ofSubtype (p := (· ∈ s))) = l := by
  simp [restrictFactors, List.map_map, Function.comp_def, restrictPerm_ofSubtype]

theorem restrictFactors_prod_ofSubtype (s : Finset α) (l : List (Perm α))
    (hl : ∀ a ∈ l, a.support ⊆ s) :
    ofSubtype (restrictFactors s l hl).prod = l.prod := by
  rw [map_list_prod, restrictFactors_ofSubtype]

theorem restrictFactors_tau_prod (s : Finset α) (l : List (Perm α))
    (hl : ∀ a ∈ l, a.support ⊆ s) : τ (restrictFactors s l hl).prod = τ l.prod := by
  unfold τ
  rw [← cycleType_ofSubtype (g := (restrictFactors s l hl).prod),
    restrictFactors_prod_ofSubtype]

theorem restrictFactors_deficit (s : Finset α) (l : List (Perm α))
    (hl : ∀ a ∈ l, a.support ⊆ s) :
    ((restrictFactors s l hl).map (fun a => a.support.card - 1)).sum =
      (l.map (fun a => a.support.card - 1)).sum := by
  simp [restrictFactors, List.map_map, Function.comp_def, restrictPerm_support_card]

theorem restrictFactors_isCycle (s : Finset α) (l : List (Perm α))
    (hl : ∀ a ∈ l, a.support ⊆ s) (hcycle : ∀ a ∈ l, a.IsCycle) :
    ∀ a ∈ restrictFactors s l hl, a.IsCycle := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact restrictPerm_isCycle s b.val (hl _ b.property) (hcycle _ b.property)

/-- Support graph of a cycle-factor list, on the whole ambient label type. -/
def factorSupportGraph (l : List (Perm α)) : SimpleGraph α where
  Adj x y := x ≠ y ∧ ∃ a ∈ l, x ∈ a.support ∧ y ∈ a.support
  symm := ⟨by
    rintro x y ⟨hne, a, ha, hx, hy⟩
    exact ⟨hne.symm, a, ha, hy, hx⟩⟩
  loopless := ⟨by intro x hx; exact hx.1 rfl⟩

namespace ConstituentWord

variable {lam : CycleType}

theorem factor_support_subset (w : ConstituentWord lam α) (a : Perm α) (ha : a ∈ w.factors) :
    a.support ⊆ w.support := fun x hx => (w.mem_support x).mpr ⟨a, ha, hx⟩

def supportFactors (w : ConstituentWord lam α) : List (Perm w.support) :=
  restrictFactors w.support w.factors w.factor_support_subset

theorem supportFactors_graph (w : ConstituentWord lam α) :
    factorSupportGraph w.supportFactors = w.supportGraph := by
  ext x y
  change (x ≠ y ∧ ∃ a ∈ w.supportFactors, x ∈ a.support ∧ y ∈ a.support) ↔
    (x ≠ y ∧ ∃ a ∈ w.factors, x.val ∈ a.support ∧ y.val ∈ a.support)
  constructor
  · rintro ⟨hne, a, ha, hx, hy⟩
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact ⟨hne, b.val, b.property,
      (restrictPerm_mem_support _ _ _ x).mp hx,
      (restrictPerm_mem_support _ _ _ y).mp hy⟩
  · rintro ⟨hne, a, ha, hx, hy⟩
    refine ⟨hne, restrictPerm w.support a (w.factor_support_subset a ha), ?_, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩
    · exact (restrictPerm_mem_support _ _ _ x).mpr hx
    · exact (restrictPerm_mem_support _ _ _ y).mpr hy

theorem supportFactors_isCycle (w : ConstituentWord lam α) :
    ∀ a ∈ w.supportFactors, a.IsCycle :=
  restrictFactors_isCycle w.support w.factors w.factor_support_subset w.isCycle

theorem supportFactors_deficit (w : ConstituentWord lam α) :
    (w.supportFactors.map (fun a => a.support.card - 1)).sum = δ lam w.c := by
  rw [supportFactors, restrictFactors_deficit, delta_c_eq_sum]

theorem supportFactors_tau_prod (w : ConstituentWord lam α) : τ w.supportFactors.prod = τ w.value :=
  restrictFactors_tau_prod w.support w.factors w.factor_support_subset

end ConstituentWord

end ConjugacyDiametersPORC

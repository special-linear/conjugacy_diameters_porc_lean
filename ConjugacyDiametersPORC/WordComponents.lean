import ConjugacyDiametersPORC.WordRestriction
import ConjugacyDiametersPORC.WordEmbedding
import ConjugacyDiametersPORC.JoiningGraph
import ConjugacyDiametersPORC.ConnectedDefect

/-!
# Connected components of a constituent word

Each cycle factor belongs to one support-graph component. Filtering the ordered
word by a component retains its factor order and omits every other component.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm SimpleGraph

namespace ConstituentWord

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

abbrev ambientGraph (w : ConstituentWord lam α) : SimpleGraph α := factorSupportGraph w.factors

open scoped Classical in
noncomputable def component (w : ConstituentWord lam α) (C : w.ambientGraph.ConnectedComponent) :
    ConstituentWord lam α where
  factors := w.factors.filter (fun a => (↑a.support : Set α) ⊆ C.supp)
  isCycle := by
    intro a ha
    exact w.isCycle a (List.mem_filter.mp ha).1
  length_mem_J := by
    intro a ha
    exact w.length_mem_J a (List.mem_filter.mp ha).1

theorem mem_component_factors (w : ConstituentWord lam α) (C : w.ambientGraph.ConnectedComponent)
    (a : Perm α) : a ∈ (w.component C).factors ↔ a ∈ w.factors ∧
      (↑a.support : Set α) ⊆ C.supp := by
  classical
  simp [component]

theorem factor_support_component (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (a : Perm α) (ha : a ∈ w.factors)
    (x : α) (hx : x ∈ a.support) (hC : x ∈ C.supp) :
    (↑a.support : Set α) ⊆ C.supp := by
  intro y hy
  by_cases hxy : x = y
  · simpa [← hxy] using hC
  · exact C.mem_supp_of_adj_mem_supp hC ⟨hxy, a, ha, hx, hy⟩

theorem component_support_subset (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) : (↑(w.component C).support : Set α) ⊆ C.supp := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := ((w.component C).mem_support x).mp hx
  exact ((w.mem_component_factors C a).mp ha).2 hx

theorem mem_component_support (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (x : α) (hx : x ∈ w.support) (hC : x ∈ C.supp) :
    x ∈ (w.component C).support := by
  obtain ⟨a, ha, hx⟩ := (w.mem_support x).mp hx
  exact ((w.component C).mem_support x).mpr ⟨a,
    (w.mem_component_factors C a).mpr
      ⟨ha, w.factor_support_component C a ha x hx hC⟩, hx⟩

theorem ambient_adj_support (w : ConstituentWord lam α) {x y : α}
    (hxy : w.ambientGraph.Adj x y) : x ∈ w.support ∧ y ∈ w.support := by
  obtain ⟨_, a, ha, hx, hy⟩ := hxy
  exact ⟨(w.mem_support x).mpr ⟨a, ha, hx⟩, (w.mem_support y).mpr ⟨a, ha, hy⟩⟩

theorem reachable_support (w : ConstituentWord lam α) {x y : α}
    (hxy : w.ambientGraph.Reachable x y) (hx : x ∈ w.support) : y ∈ w.support := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact hx
  | cons h p ih => exact ih (w.ambient_adj_support h).2

theorem component_support_eq (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (hne : (w.component C).factors ≠ []) :
    (↑(w.component C).support : Set α) = C.supp := by
  apply Set.Subset.antisymm (w.component_support_subset C)
  obtain ⟨x, hx⟩ := (w.component C).support_nonempty hne
  have hxC := w.component_support_subset C hx
  have hxw : x ∈ w.support := by
    obtain ⟨a, ha, hxa⟩ := ((w.component C).mem_support x).mp hx
    exact (w.mem_support x).mpr ⟨a, ((w.mem_component_factors C a).mp ha).1, hxa⟩
  intro y hy
  exact w.mem_component_support C y
    (w.reachable_support (C.reachable_of_mem_supp hxC hy) hxw) hy

theorem component_connected (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (hne : (w.component C).factors ≠ []) :
    (w.component C).supportGraph.Connected := by
  have heq := w.component_support_eq C hne
  let f : C.toSimpleGraph →g (w.component C).supportGraph :=
    { toFun := fun x => ⟨x.val, by rw [Set.ext_iff] at heq; exact (heq x.val).mpr x.property⟩
      map_rel' := by
        intro x y hxy
        obtain ⟨hne, a, ha, hx, hy⟩ := hxy
        refine ⟨?_, a, (w.mem_component_factors C a).mpr
          ⟨ha, w.factor_support_component C a ha x.val hx x.property⟩, hx, hy⟩
        intro h
        exact hne (congrArg (fun z : (w.component C).support => z.val) h) }
  apply C.connected_toSimpleGraph.map f
  intro y
  exact ⟨⟨y.val, w.component_support_subset C y.property⟩, rfl⟩

theorem factor_preserves_components (w : ConstituentWord lam α) (a : Perm α)
    (ha : a ∈ w.factors) : PreservesComponents w.ambientGraph a := by
  intro x
  by_cases hx : x ∈ a.support
  · exact (show w.ambientGraph.Adj x (a x) from
      ⟨(Equiv.Perm.mem_support.mp hx).symm, a, ha, hx, apply_mem_support.mpr hx⟩).reachable
  · rw [notMem_support.mp hx]

theorem prod_preserves_components (w : ConstituentWord lam α) (l : List (Perm α))
    (hl : l ⊆ w.factors) : PreservesComponents w.ambientGraph l.prod :=
  PreservesComponents.list_prod l (fun a ha => w.factor_preserves_components a (hl ha))

open scoped Classical in
theorem component_prod_apply (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (l : List (Perm α)) (hl : l ⊆ w.factors)
    (x : α) (hx : x ∈ C.supp) :
    (l.filter (fun a => decide ((↑a.support : Set α) ⊆ C.supp))).prod x = l.prod x := by
  classical
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ht : l ⊆ w.factors := fun b hb => hl (List.mem_cons_of_mem a hb)
    have ha := hl List.mem_cons_self
    by_cases hC : (↑a.support : Set α) ⊆ C.supp
    · simp only [List.filter_cons, hC, decide_true, ↓reduceIte,
        List.prod_cons, mul_apply]
      rw [ih ht]
    · have htail : l.prod x ∈ C.supp := by
        rw [ConnectedComponent.mem_supp_iff] at hx ⊢
        rw [← ConnectedComponent.sound (w.prod_preserves_components l ht x)]
        exact hx
      have hfix : a (l.prod x) = l.prod x := by
        apply notMem_support.mp
        intro hm
        exact hC (w.factor_support_component C a ha _ hm htail)
      simp only [List.filter_cons, hC, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.prod_cons, mul_apply]
      rw [ih ht, hfix]

theorem component_value_apply (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (x : α) (hx : x ∈ C.supp) :
    (w.component C).value x = w.value x :=
  w.component_prod_apply C w.factors (fun _ h => h) x hx

theorem component_value_fixed (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (x : α) (hx : x ∉ C.supp) :
    (w.component C).value x = x := by
  apply notMem_support.mp
  intro hm
  exact hx (w.component_support_subset C ((w.component C).value_support_subset hm))

theorem component_values_disjoint (w : ConstituentWord lam α)
    (C D : w.ambientGraph.ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (w.component C).value (w.component D).value := by
  rw [disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  apply hCD
  exact ConnectedComponent.eq_of_common_vertex
    (w.component_support_subset C ((w.component C).value_support_subset hx))
    (w.component_support_subset D ((w.component D).value_support_subset hy))

noncomputable instance componentFintype (w : ConstituentWord lam α) :
    Fintype w.ambientGraph.ConnectedComponent := Fintype.ofFinite _

theorem component_values_pairwise (w : ConstituentWord lam α) :
    (↑(Finset.univ : Finset w.ambientGraph.ConnectedComponent) : Set _).Pairwise
      (fun C D => Disjoint (w.component C).value (w.component D).value) :=
  fun C _ D _ hCD => w.component_values_disjoint C D hCD

theorem component_values_prod (w : ConstituentWord lam α) :
    Finset.univ.noncommProd (fun C => (w.component C).value)
      ((w.component_values_pairwise).imp (fun _ _ h => h.commute)) = w.value := by
  classical
  ext x
  let C := w.ambientGraph.connectedComponentMk x
  let f := fun D => (w.component D).value
  let comm := (w.component_values_pairwise).imp (fun _ _ h => h.commute)
  let comm' : (↑(Finset.univ.erase C) : Set _).Pairwise (fun D E => Commute (f D) (f E)) :=
    fun D _ E _ hDE => (w.component_values_disjoint D E hDE).commute
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ C) f comm
    (comm' := comm'), mul_apply]
  have hfix : (Finset.univ.erase C).noncommProd f comm' x = x := by
    apply Finset.noncommProd_induction (Finset.univ.erase C) f comm' (fun g => g x = x)
    · intro a b ha hb
      rw [mul_apply, hb, ha]
    · rfl
    · intro D hD
      apply w.component_value_fixed D
      intro hx
      exact (Finset.mem_erase.mp hD).1
        ((ConnectedComponent.mem_supp_iff D x).mp hx).symm
  rw [hfix]
  exact w.component_value_apply C x rfl

theorem component_cycleTypes_sum (w : ConstituentWord lam α) :
    ∑ C : w.ambientGraph.ConnectedComponent, (w.component C).value.cycleType =
      w.value.cycleType := by
  rw [← Disjoint.cycleType_noncommProd w.component_values_pairwise, w.component_values_prod]

theorem component_hasTarget (w : ConstituentWord lam α) (C : w.ambientGraph.ConnectedComponent)
    {r s : ℕ} (ht : w.HasTarget r s) :
    (w.component C).HasTarget r (w.component C).value.cycleType.card := by
  apply Multiset.eq_replicate_card.mpr
  intro ℓ hℓ
  have hle : (w.component C).value.cycleType ≤ w.value.cycleType := by
    rw [← w.component_cycleTypes_sum]
    exact Finset.single_le_sum (f := fun D => (w.component D).value.cycleType)
      (fun _ _ => zero_le) (Finset.mem_univ C)
  exact Multiset.eq_of_mem_replicate (ht ▸ Multiset.subset_of_le hle hℓ)

theorem component_target_count_sum (w : ConstituentWord lam α) {r s : ℕ}
    (ht : w.HasTarget r s) :
    ∑ C : w.ambientGraph.ConnectedComponent, (w.component C).value.cycleType.card = s := by
  have h := congrArg Multiset.card w.component_cycleTypes_sum
  change w.value.cycleType = Multiset.replicate s r at ht
  rw [ht] at h
  simpa using h

theorem factor_component_unique (w : ConstituentWord lam α) (a : Perm α) (ha : a ∈ w.factors) :
    ∃ C₀ : w.ambientGraph.ConnectedComponent,
      ∀ C, (↑a.support : Set α) ⊆ C.supp ↔ C = C₀ := by
  have hp := lam.two_le_of_mem_J (w.length_mem_J a ha)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < a.support.card by omega)
  refine ⟨w.ambientGraph.connectedComponentMk x, fun C => ?_⟩
  constructor
  · intro h
    exact ((ConnectedComponent.mem_supp_iff C x).mp (h hx)).symm
  · rintro rfl
    exact w.factor_support_component _ a ha x hx rfl

open scoped Classical in
private theorem component_counts_sum (w : ConstituentWord lam α)
    (l : List (Perm α)) (hl : l ⊆ w.factors) (ℓ : ℕ) :
    ∑ C : w.ambientGraph.ConnectedComponent,
      ((l.filter (fun a => decide ((↑a.support : Set α) ⊆ C.supp))).map
        (fun a => a.support.card)).count ℓ = (l.map (fun a => a.support.card)).count ℓ := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht : l ⊆ w.factors := fun b hb => hl (List.mem_cons_of_mem a hb)
    obtain ⟨C₀, hC₀⟩ := w.factor_component_unique a (hl List.mem_cons_self)
    have hstep (C : w.ambientGraph.ConnectedComponent) :
        (((a :: l).filter (fun b => decide ((↑b.support : Set α) ⊆ C.supp))).map
          (fun b => b.support.card)).count ℓ =
        (if C = C₀ then (if a.support.card = ℓ then 1 else 0) else 0) +
          ((l.filter (fun b => decide ((↑b.support : Set α) ⊆ C.supp))).map
            (fun b => b.support.card)).count ℓ := by
      by_cases hC : C = C₀ <;> simp [hC₀, hC, List.count_cons, add_comm]
    simp_rw [hstep, Finset.sum_add_distrib]
    rw [ih ht]
    simp [List.count_cons, add_comm]

theorem component_inventory_sum (w : ConstituentWord lam α) :
    ∑ C : w.ambientGraph.ConnectedComponent, (w.component C).c = w.c := by
  classical
  funext ℓ
  rw [Finset.sum_apply]
  exact w.component_counts_sum w.factors (fun _ h => h) ℓ

end ConstituentWord

end ConjugacyDiametersPORC

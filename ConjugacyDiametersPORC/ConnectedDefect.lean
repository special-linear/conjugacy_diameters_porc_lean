import ConjugacyDiametersPORC.JoiningGraph
import ConjugacyDiametersPORC.WordRestriction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Connected-word defects

Expand the inverse endpoint followed by the constituent factors into an identity
word in transpositions. Restrict to the used labels, whose graph is connected.
The connected identity-word bound gives `E(c,s) ≥ 2f ≥ 0`.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

noncomputable def swapEndpoints (g : Perm α) (hg : g.IsSwap) : α × α :=
  ⟨Classical.choose hg, Classical.choose (Classical.choose_spec hg)⟩

theorem swapEndpoints_ne (g : Perm α) (hg : g.IsSwap) :
    (swapEndpoints g hg).1 ≠ (swapEndpoints g hg).2 :=
  (Classical.choose_spec (Classical.choose_spec hg)).1

theorem swapEndpoints_eq (g : Perm α) (hg : g.IsSwap) :
    swap (swapEndpoints g hg).1 (swapEndpoints g hg).2 = g :=
  (Classical.choose_spec (Classical.choose_spec hg)).2.symm

namespace TranspositionWord

/-- Display the endpoints of each transposition without changing word order. -/
noncomputable def ofSwaps (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsSwap) : List (α × α) :=
  l.attach.map (fun a => swapEndpoints a.val (hl a.val a.property))

theorem ofSwaps_length (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsSwap) :
    (ofSwaps l hl).length = l.length := by simp [ofSwaps]

theorem ofSwaps_value (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsSwap) :
    value (ofSwaps l hl) = l.prod := by
  simp [value, ofSwaps, List.map_map, Function.comp_def, swapEndpoints_eq]

theorem graph_adj_mem (ps : List (α × α)) (p : α × α) (hp : p ∈ ps) (hne : p.1 ≠ p.2) :
    (graph ps).Adj p.1 p.2 := by
  rw [graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩), hne⟩

theorem preservesComponents_ofSwaps_factor (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsSwap)
    {g : Perm α} (hg : g ∈ l) : PreservesComponents (graph (ofSwaps l hl)) g := by
  have hp : swapEndpoints g (hl g hg) ∈ ofSwaps l hl :=
    List.mem_map.mpr ⟨⟨g, hg⟩, List.mem_attach _ _, rfl⟩
  have hr := (graph_adj_mem (ofSwaps l hl) _ hp (swapEndpoints_ne _ _)).reachable
  simpa only [swapEndpoints_eq] using preservesComponents_swap hr

end TranspositionWord

omit [DecidableEq α] in
theorem PreservesComponents.list_prod {G : SimpleGraph α} (l : List (Perm α))
    (hl : ∀ a ∈ l, PreservesComponents G a) : PreservesComponents G l.prod := by
  induction l with
  | nil => intro x; exact SimpleGraph.Reachable.rfl
  | cons a l ih =>
    exact (hl a List.mem_cons_self).mul
      (ih (fun b hb => hl b (List.mem_cons_of_mem a hb)))

variable [Fintype α]

theorem cycleTranspositions_mem_expandCycles (l : List (Perm α))
    (hl : ∀ a ∈ l, a.IsCycle) {a : Perm α} (ha : a ∈ l) {t : Perm α}
    (ht : t ∈ cycleTranspositions a (hl a ha)) : t ∈ expandCycles l hl := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.mem_append_left _ ht
    · exact List.mem_append_right _ (ih _ ha ht)

/-- The transposition identity-word bound for a connected list of single cycles. -/
theorem connected_cycleFactors_length_bound (l : List (Perm α))
    (hl : ∀ a ∈ l, a.IsCycle) (hgraph : (factorSupportGraph l).Connected) :
    2 * (Fintype.card α - 1) ≤
      (l.map (fun a => a.support.card - 1)).sum + τ l.prod := by
  classical
  let ts := transpositionFactors l.prod⁻¹ ++ expandCycles l hl
  have hts : ∀ a ∈ ts, a.IsSwap := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact transpositionFactors_isSwap _ ha
    · exact expandCycles_isSwap _ _ ha
  let ps := TranspositionWord.ofSwaps ts hts
  let H := TranspositionWord.graph ps
  have hvalue : TranspositionWord.value ps = 1 := by
    rw [TranspositionWord.ofSwaps_value]
    simp [ts, List.prod_append, transpositionFactors_prod, expandCycles_prod]
  have hcycle : ∀ a ∈ l, PreservesComponents H a := by
    intro a ha
    have hp : PreservesComponents H (cycleTranspositions a (hl a ha)).prod := by
      apply PreservesComponents.list_prod
      intro t ht
      apply TranspositionWord.preservesComponents_ofSwaps_factor ts hts
      exact List.mem_append_right _ (cycleTranspositions_mem_expandCycles l hl ha ht)
    rwa [cycleTranspositions_prod] at hp
  have hconnected : H.Connected := by
    let _ : Nonempty α := hgraph.nonempty
    constructor
    intro x y
    apply reachable_of_adj_reachable (G := factorSupportGraph l) _ (hgraph.preconnected x y)
    rintro x y ⟨_, a, ha, hx, hy⟩
    exact (hcycle a ha).sameCycle ((hl a ha).sameCycle (mem_support.mp hx) (mem_support.mp hy))
  have hb := TranspositionWord.connected_identity_length_bound ps hconnected hvalue
  simpa [ps, TranspositionWord.ofSwaps_length, ts, List.length_append,
    transpositionFactors_length, expandCycles_length, add_comm] using hb

namespace ConstituentWord

variable {lam : CycleType}

theorem connected_transposition_bound (w : ConstituentWord lam α)
    (hgraph : w.supportGraph.Connected) :
    2 * (w.support.card - 1) ≤ δ lam w.c + τ w.value := by
  have hg : (factorSupportGraph w.supportFactors).Connected := by
    rw [w.supportFactors_graph]
    exact hgraph
  have ht := connected_cycleFactors_length_bound w.supportFactors w.supportFactors_isCycle hg
  rw [w.supportFactors_deficit, w.supportFactors_tau_prod] at ht
  simpa only [Fintype.card_coe] using ht

theorem HasTarget.value_support_card (w : ConstituentWord lam α) {r s : ℕ}
    (ht : w.HasTarget r s) : w.value.support.card = r * s := by
  rw [← sum_cycleType, ht, Multiset.sum_replicate]
  simp [mul_comm]

theorem HasTarget.support_card_eq (w : ConstituentWord lam α) {r s : ℕ}
    (ht : w.HasTarget r s) :
    w.support.card = r * s + (w.support.card - r * s) := by
  have hle := Finset.card_mono w.value_support_subset
  rw [ht.value_support_card] at hle
  omega

end ConstituentWord

/-- **Lemma 2.** For a nonempty connected constituent word with target type
`r^s` and `v = rs + f` used labels, its defect satisfies `E(c,s) ≥ 2f ≥ 0`. -/
theorem lemma2 {lam : CycleType} (w : ConstituentWord lam α) (r s f : ℕ)
    (hr : 2 ≤ r) (hgraph : w.supportGraph.Connected) (hc : w.c ≠ 0)
    (htarget : w.HasTarget r s) (hv : w.support.card = r * s + f) :
    2 * (f : ℤ) ≤ w.E r s ∧ 0 ≤ 2 * (f : ℤ) := by
  have hp : 0 < w.support.card :=
    Finset.card_pos.mpr (w.support_nonempty (w.c_ne_zero_iff.mp hc))
  have hb := w.connected_transposition_bound hgraph
  rw [tau_of_cycleType_replicate w.value htarget] at hb
  have hnat : 2 * w.support.card ≤ δ lam w.c + (r - 1) * s + 2 := by omega
  have hrank : (r - 1) * s + s = r * s := by
    calc
      _ = ((r - 1) + 1) * s := by simp [Nat.add_mul]
      _ = r * s := by congr 1; omega
  have hnat' : 2 * (w.support.card : ℤ) ≤ (δ lam w.c : ℤ) + (((r - 1) * s : ℕ) : ℤ) + 2 := by
    exact_mod_cast hnat
  have hrank' : (((r - 1) * s : ℕ) : ℤ) + (s : ℤ) = (r : ℤ) * (s : ℤ) := by
    exact_mod_cast hrank
  have hv' : (w.support.card : ℤ) = (r : ℤ) * (s : ℤ) + (f : ℤ) := by
    exact_mod_cast hv
  constructor
  · unfold ConstituentWord.E
    nlinarith
  · positivity

theorem connected_defect_nonneg {lam : CycleType} (w : ConstituentWord lam α) (r s : ℕ)
    (hr : 2 ≤ r) (hgraph : w.supportGraph.Connected) (hc : w.c ≠ 0)
    (htarget : w.HasTarget r s) : 0 ≤ w.E r s := by
  have h := lemma2 w r s (w.support.card - r * s) hr hgraph hc htarget htarget.support_card_eq
  exact h.2.trans h.1

end ConjugacyDiametersPORC

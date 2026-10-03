import ConjugacyDiametersPORC.CycleCuts
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The graph of cycle joins in a transposition word

Process the factors from right to left, consistently with permutation
multiplication. Retain the swaps that join different permutation cycles.
The retained edges connect every pair joined by an original word edge.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {α : Type*}

/-- A permutation preserves each graph component. -/
def PreservesComponents (G : SimpleGraph α) (g : Perm α) : Prop :=
  ∀ x, G.Reachable x (g x)

theorem PreservesComponents.mul {G : SimpleGraph α} {g h : Perm α}
    (hg : PreservesComponents G g) (hh : PreservesComponents G h) :
    PreservesComponents G (g * h) := by
  intro x
  exact (hh x).trans (hg (h x))

theorem PreservesComponents.sameCycle [Finite α]
    {G : SimpleGraph α} {g : Perm α}
    (hg : PreservesComponents G g) {x y : α} (hxy : g.SameCycle x y) :
    G.Reachable x y := by
  classical
  let _ := Fintype.ofFinite α
  obtain ⟨n, _, _, hn⟩ := SameCycle.exists_pow_eq g hxy
  rw [← hn]
  have hp : ∀ k : ℕ, G.Reachable x ((g ^ k) x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply]
      exact ih.trans (hg ((g ^ k) x))
  exact hp n

theorem preservesComponents_swap [DecidableEq α] {G : SimpleGraph α} {x y : α}
    (hxy : G.Reachable x y) : PreservesComponents G (swap x y) := by
  intro z
  by_cases hz : z = x
  · subst z
    simpa using hxy
  by_cases hz' : z = y
  · subst z
    simpa using hxy.symm
  rw [swap_apply_of_ne_of_ne hz hz']

theorem reachable_of_adj_reachable {G H : SimpleGraph α}
    (h : ∀ ⦃x y⦄, G.Adj x y → H.Reachable x y) {x y : α}
    (hxy : G.Reachable x y) : H.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons ha _ ih => exact (h ha).trans ih

namespace TranspositionWord

variable [DecidableEq α]

/-- Value of the displayed word in swaps. Equal endpoints are allowed here. -/
def value (ps : List (α × α)) : Perm α :=
  (ps.map (fun p => swap p.1 p.2)).prod

@[simp]
theorem value_nil : value ([] : List (α × α)) = 1 := rfl

@[simp]
theorem value_cons (p : α × α) (ps : List (α × α)) :
    value (p :: ps) = swap p.1 p.2 * value ps := rfl

/-- The graph of all endpoint pairs, with loops omitted. -/
def graph (ps : List (α × α)) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet ((ps.map (fun p => s(p.1, p.2))).toFinset : Set (Sym2 α))

@[simp]
theorem graph_nil : graph ([] : List (α × α)) = ⊥ := by
  simp [graph, SimpleGraph.fromEdgeSet_empty]

theorem graph_tail_le (p : α × α) (ps : List (α × α)) : graph ps ≤ graph (p :: ps) := by
  apply SimpleGraph.fromEdgeSet_mono
  intro e he
  change e ∈ (s(p.1, p.2) :: ps.map (fun p => s(p.1, p.2))).toFinset
  rw [List.toFinset_cons]
  exact Finset.mem_insert_of_mem he

theorem graph_adj_head (p : α × α) (ps : List (α × α)) (hne : p.1 ≠ p.2) :
    (graph (p :: ps)).Adj p.1 p.2 := by
  rw [graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨by simp, hne⟩

theorem graph_adj_reachable {G : SimpleGraph α} (ps : List (α × α))
    (hps : ∀ p ∈ ps, G.Reachable p.1 p.2) {x y : α}
    (hxy : (graph ps).Adj x y) : G.Reachable x y := by
  rw [graph, SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hxy.1)
  rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simpa only [hx, hy] using hps p hp
  · simpa only [hx, hy] using (hps p hp).symm

theorem preservesComponents_value {G : SimpleGraph α} (ps : List (α × α))
    (hps : ∀ p ∈ ps, G.Reachable p.1 p.2) : PreservesComponents G (value ps) := by
  induction ps with
  | nil => intro x; exact SimpleGraph.Reachable.rfl
  | cons p ps ih =>
    exact (preservesComponents_swap (hps p List.mem_cons_self)).mul
      (ih (fun q hq => hps q (List.mem_cons_of_mem p hq)))

variable [Fintype α]

/-- Retain exactly the steps that join different permutation cycles. -/
noncomputable def joiningPairs : List (α × α) → List (α × α)
  | [] => []
  | p :: ps => if (value ps).SameCycle p.1 p.2 then joiningPairs ps else p :: joiningPairs ps

noncomputable def joiningGraph (ps : List (α × α)) : SimpleGraph α := graph (joiningPairs ps)

theorem joiningGraph_tail_le (p : α × α) (ps : List (α × α)) :
    joiningGraph ps ≤ joiningGraph (p :: ps) := by
  classical
  by_cases h : (value ps).SameCycle p.1 p.2
  · simp [joiningGraph, joiningPairs, h]
  · simpa only [joiningGraph, joiningPairs, ite_eq_right h] using graph_tail_le p (joiningPairs ps)

/-- Every original swap joins labels reachable in the retained graph. -/
theorem joiningGraph_reachable_pairs (ps : List (α × α)) :
    ∀ p ∈ ps, (joiningGraph ps).Reachable p.1 p.2 := by
  classical
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hle := joiningGraph_tail_le p ps
    have hhead : (joiningGraph (p :: ps)).Reachable p.1 p.2 := by
      by_cases hs : (value ps).SameCycle p.1 p.2
      · exact ((preservesComponents_value ps ih).sameCycle hs).mono hle
      · have hne : p.1 ≠ p.2 := by
          intro he
          apply hs
          rw [he]
        simpa only [joiningGraph, joiningPairs, ite_eq_right hs] using
          (graph_adj_head p (joiningPairs ps) hne).reachable
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hhead
    · exact (ih q hq).mono hle

/-- Twice the join count is bounded by word length plus endpoint rank.
For words of genuine transpositions this is an equality. -/
theorem joiningPairs_length_bound (ps : List (α × α)) :
    2 * (joiningPairs ps).length ≤ ps.length + τ (value ps) := by
  classical
  induction ps with
  | nil => simp [joiningPairs]
  | cons p ps ih =>
    by_cases hs : (value ps).SameCycle p.1 p.2
    · simp only [joiningPairs, ite_eq_left hs, List.length_cons, value_cons]
      by_cases he : p.1 = p.2
      · rw [he, swap_self]
        change 2 * (joiningPairs ps).length ≤ ps.length + 1 + τ (1 * value ps)
        rw [one_mul]
        omega
      · have ht := tau_swap_mul_of_sameCycle (value ps) p.1 p.2 hs he
        omega
    · simp only [joiningPairs, ite_eq_right hs, List.length_cons, value_cons]
      rw [tau_swap_mul_of_not_sameCycle (value ps) p.1 p.2 hs]
      omega

noncomputable instance graphEdgeFintype (ps : List (α × α)) : Fintype (graph ps).edgeSet :=
  Fintype.ofFinite _

noncomputable instance joiningGraphEdgeFintype (ps : List (α × α)) :
    Fintype (joiningGraph ps).edgeSet := Fintype.ofFinite _

theorem graph_card_edges_le_length (ps : List (α × α)) :
    (graph ps).edgeFinset.card ≤ ps.length := by
  classical
  have hsub : (graph ps).edgeFinset ⊆ (ps.map (fun p => s(p.1, p.2))).toFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset, graph, SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  exact (Finset.card_mono hsub).trans
    (by simpa using (ps.map (fun p => s(p.1, p.2))).toFinset_card_le)

theorem joiningGraph_connected (ps : List (α × α)) (hps : (graph ps).Connected) :
    (joiningGraph ps).Connected := by
  let _ : Nonempty α := hps.nonempty
  constructor
  intro x y
  exact reachable_of_adj_reachable
    (fun {_ _} ha => graph_adj_reachable ps (joiningGraph_reachable_pairs ps) ha)
    (hps.preconnected x y)

/-- A connected transposition word equal to the identity has at least
`2(v-1)` factors on its `v` labels. -/
theorem connected_identity_length_bound (ps : List (α × α))
    (hps : (graph ps).Connected) (hvalue : value ps = 1) :
    2 * (Fintype.card α - 1) ≤ ps.length := by
  classical
  have hc := (joiningGraph_connected ps hps).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hc
  have he := graph_card_edges_le_length (joiningPairs ps)
  have hj := joiningPairs_length_bound ps
  rw [hvalue, tau_one, add_zero] at hj
  change (joiningGraph ps).edgeFinset.card ≤ (joiningPairs ps).length at he
  omega

end TranspositionWord

end ConjugacyDiametersPORC

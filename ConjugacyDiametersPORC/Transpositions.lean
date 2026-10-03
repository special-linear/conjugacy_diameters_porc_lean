import ConjugacyDiametersPORC.ConstituentWord
import ConjugacyDiametersPORC.Diameter
import ConjugacyDiametersPORC.CycleProducts
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Transposition expansions

The quantity `τ(g)` is the sum of the deficits of its nontrivial cycles.
Expanding a cycle along its ordered labels uses exactly one fewer transposition
than labels. Expanding a constituent word therefore uses exactly `δ(c)` swaps.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

/-- Transposition rank: the number of labels minus the number of all cycles,
including fixed labels. Fixed labels cancel in this cycle-type formula. -/
def τ {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) : ℕ :=
  g.cycleType.sum - g.cycleType.card

theorem cycleType_card_le_sum {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) :
    g.cycleType.card ≤ g.cycleType.sum := by
  simpa using (Multiset.card_nsmul_le_sum
    (fun ℓ hℓ => (show 1 ≤ ℓ from (by
      have := two_le_of_mem_cycleType hℓ
      omega))))

theorem tau_add_card {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) :
    τ g + g.cycleType.card = g.cycleType.sum :=
  Nat.sub_add_cancel (cycleType_card_le_sum g)

@[simp]
theorem tau_one {α : Type*} [Fintype α] [DecidableEq α] : τ (1 : Perm α) = 0 := by
  simp [τ]

@[simp]
theorem tau_inv {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) : τ g⁻¹ = τ g := by
  simp [τ]

theorem tau_of_mem_C (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ C lam n) : τ g = lam.d := by
  rw [τ, (mem_C lam g).mp hg]
  rfl

theorem tau_of_cycleType_replicate {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) {r s : ℕ}
    (hg : g.cycleType = Multiset.replicate s r) : τ g = (r - 1) * s := by
  rw [τ, hg]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul, Nat.cast_id]
  rw [Nat.sub_mul]
  simp [mul_comm]

theorem tau_isCycle {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} (hg : g.IsCycle) : τ g = g.support.card - 1 := by
  simp [τ, hg.cycleType]

theorem tau_disjoint_mul {α : Type*} [Fintype α] [DecidableEq α]
    {g₁ g₂ : Perm α} (h : g₁.Disjoint g₂) : τ (g₁ * g₂) = τ g₁ + τ g₂ := by
  have h₁ := cycleType_card_le_sum g₁
  have h₂ := cycleType_card_le_sum g₂
  simp only [τ, h.cycleType_mul, Multiset.sum_add, Multiset.card_add]
  omega

theorem sign_eq_neg_one_pow_tau {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) : sign g = (-1 : ℤˣ) ^ τ g := by
  have he : g.cycleType.sum + g.cycleType.card = τ g + 2 * g.cycleType.card := by
    have := tau_add_card g
    omega
  rw [sign_of_cycleType, he, pow_add, pow_mul]
  simp

theorem tau_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (hl : l.Nodup) : τ l.formPerm = l.length - 1 := by
  by_cases hlen : 2 ≤ l.length
  · rw [tau_isCycle (List.isCycle_formPerm hl hlen), support_card_formPerm l hl hlen]
  · cases l with
    | nil => simp
    | cons x l =>
      cases l with
      | nil => simp
      | cons y l => simp at hlen

theorem tau_join_cycles {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (l₁ l₂ : List α) (hl : ((x :: l₁) ++ y :: l₂).Nodup) :
    τ (swap x y * (x :: l₁).formPerm * (y :: l₂).formPerm) =
      τ (x :: l₁).formPerm + τ (y :: l₂).formPerm + 1 := by
  have h₁ := hl.of_append_left
  have h₂ := hl.of_append_right
  have hy : y ∉ x :: l₁ := fun hy =>
    (List.disjoint_of_nodup_append hl) hy List.mem_cons_self
  rw [swap_mul_formPerm_mul_formPerm x y l₁ l₂ hy,
    tau_formPerm _ hl, tau_formPerm _ h₁, tau_formPerm _ h₂]
  simp
  omega

/-- Adjacent transpositions of an ordered label list. -/
def listTranspositions {α : Type*} [DecidableEq α] (l : List α) : List (Perm α) :=
  List.zipWith swap l l.tail

theorem listTranspositions_prod {α : Type*} [DecidableEq α] (l : List α) :
    (listTranspositions l).prod = l.formPerm := rfl

theorem listTranspositions_length {α : Type*} [DecidableEq α] (l : List α) :
    (listTranspositions l).length = l.length - 1 := by
  simp [listTranspositions, List.length_zipWith]

theorem listTranspositions_isSwap {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) {a : Perm α} (ha : a ∈ listTranspositions l) : a.IsSwap := by
  induction l with
  | nil => simp [listTranspositions] at ha
  | cons x l ih =>
    cases l with
    | nil => simp [listTranspositions] at ha
    | cons y l =>
      change a ∈ swap x y :: listTranspositions (y :: l) at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨x, y, fun he => hl.notMem (he ▸ List.mem_cons_self), rfl⟩
      · exact ih hl.of_cons ha

/-- Choose the ordered labels of a nontrivial single cycle. -/
noncomputable def cycleList {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : List α := g.toList (Classical.choose hg)

theorem cycleList_nodup {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : (cycleList g hg).Nodup := nodup_toList _ _

theorem cycleList_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : (cycleList g hg).formPerm = g := by
  rw [cycleList, formPerm_toList, hg.cycleOf_eq (Classical.choose_spec hg).1]

theorem cycleList_length {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : (cycleList g hg).length = g.support.card := by
  rw [cycleList, length_toList, hg.cycleOf_eq (Classical.choose_spec hg).1]

noncomputable def cycleTranspositions {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : List (Perm α) := listTranspositions (cycleList g hg)

theorem cycleTranspositions_prod {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : (cycleTranspositions g hg).prod = g :=
  (listTranspositions_prod _).trans (cycleList_formPerm g hg)

theorem cycleTranspositions_length {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) : (cycleTranspositions g hg).length = g.support.card - 1 := by
  rw [cycleTranspositions, listTranspositions_length, cycleList_length]

theorem cycleTranspositions_isSwap {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) (hg : g.IsCycle) {a : Perm α} (ha : a ∈ cycleTranspositions g hg) : a.IsSwap :=
  listTranspositions_isSwap _ (cycleList_nodup g hg) ha

/-- Expand an ordered list of single cycles into adjacent transpositions. -/
noncomputable def expandCycles {α : Type*} [Fintype α] [DecidableEq α] :
    (l : List (Perm α)) → (∀ a ∈ l, a.IsCycle) → List (Perm α)
  | [], _ => []
  | a :: l, hl => cycleTranspositions a (hl a List.mem_cons_self) ++
      expandCycles l (fun b hb => hl b (List.mem_cons_of_mem a hb))

theorem expandCycles_prod {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsCycle) : (expandCycles l hl).prod = l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [expandCycles, List.prod_append, cycleTranspositions_prod, ih,
      List.prod_cons]

theorem expandCycles_length {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsCycle) :
    (expandCycles l hl).length = (l.map (fun a => a.support.card - 1)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [expandCycles, List.length_append, cycleTranspositions_length, ih,
      List.map_cons, List.sum_cons]

theorem expandCycles_isSwap {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsCycle) {a : Perm α}
    (ha : a ∈ expandCycles l hl) : a.IsSwap := by
  induction l with
  | nil => simp [expandCycles] at ha
  | cons b l ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact cycleTranspositions_isSwap b _ ha
    · exact ih _ ha

theorem expandCycles_length_add_card {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Perm α)) (hl : ∀ a ∈ l, a.IsCycle) :
    (expandCycles l hl).length + l.length = (l.map (fun a => a.support.card)).sum := by
  rw [expandCycles_length]
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := (hl a List.mem_cons_self).two_le_card_support
    have ht := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A transposition word with the exact total cycle deficit. -/
noncomputable def transpositionFactors {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) : List (Perm α) :=
  expandCycles g.truncCycleFactors.out.val g.truncCycleFactors.out.property.2.1

theorem transpositionFactors_prod {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) : (transpositionFactors g).prod = g :=
  (expandCycles_prod _ _).trans g.truncCycleFactors.out.property.1

theorem transpositionFactors_isSwap {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) {a : Perm α} (ha : a ∈ transpositionFactors g) : a.IsSwap :=
  expandCycles_isSwap _ _ ha

theorem transpositionFactors_length {α : Type*} [Fintype α] [DecidableEq α]
    (g : Perm α) : (transpositionFactors g).length = τ g := by
  have ht := cycleType_eq g.truncCycleFactors.out.val
    g.truncCycleFactors.out.property.1 g.truncCycleFactors.out.property.2.1
    g.truncCycleFactors.out.property.2.2
  have he := expandCycles_length_add_card g.truncCycleFactors.out.val
    g.truncCycleFactors.out.property.2.1
  simp only [τ, ht, Multiset.sum_coe, Multiset.coe_card, List.length_map,
    Function.comp_def]
  change (expandCycles _ _).length = _
  omega

namespace ConstituentWord

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def transpositions (w : ConstituentWord lam α) : List (Perm α) :=
  expandCycles w.factors w.isCycle

theorem transpositions_prod (w : ConstituentWord lam α) : w.transpositions.prod = w.value :=
  expandCycles_prod _ _

theorem transpositions_length (w : ConstituentWord lam α) :
    w.transpositions.length = δ lam w.c := by
  rw [transpositions, expandCycles_length, delta_c_eq_sum]

theorem transpositions_isSwap (w : ConstituentWord lam α) {a : Perm α}
    (ha : a ∈ w.transpositions) : a.IsSwap := expandCycles_isSwap _ _ ha

/-- Prepend an expansion of the inverse endpoint to obtain an identity word. -/
noncomputable def closedTranspositions (w : ConstituentWord lam α) : List (Perm α) :=
  transpositionFactors w.value⁻¹ ++ w.transpositions

theorem closedTranspositions_prod (w : ConstituentWord lam α) :
    w.closedTranspositions.prod = 1 := by
  rw [closedTranspositions, List.prod_append, transpositionFactors_prod,
    transpositions_prod, inv_mul_cancel]

theorem closedTranspositions_isSwap (w : ConstituentWord lam α) {a : Perm α}
    (ha : a ∈ w.closedTranspositions) : a.IsSwap := by
  rcases List.mem_append.mp ha with ha | ha
  · exact transpositionFactors_isSwap _ ha
  · exact w.transpositions_isSwap ha

theorem closedTranspositions_length (w : ConstituentWord lam α) :
    w.closedTranspositions.length = δ lam w.c + τ w.value := by
  simp [closedTranspositions, transpositionFactors_length, transpositions_length,
    add_comm]

theorem closedTranspositions_length_of_hasTarget (w : ConstituentWord lam α)
    {r s : ℕ} (hw : w.HasTarget r s) :
    w.closedTranspositions.length = δ lam w.c + (r - 1) * s := by
  rw [closedTranspositions_length, tau_of_cycleType_replicate w.value hw]

end ConstituentWord

end ConjugacyDiametersPORC

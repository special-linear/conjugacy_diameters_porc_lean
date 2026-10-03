import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.List.OfFn

/-!
# Products of cycles sharing an endpoint

The adjacent-transposition description of a list cycle gives the elementary
concatenation identity used in baseline and peeling constructions.
-/

namespace ConjugacyDiametersPORC

open Equiv

theorem support_card_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (h₂ : 2 ≤ l.length) :
    l.formPerm.support.card = l.length := by
  rw [List.support_formPerm_of_nodup l hl]
  · simp [List.card_toFinset, List.dedup_eq_self.mpr hl]
  · intro x he
    have := congrArg List.length he
    simp only [List.length_singleton] at this
    omega

/-- Two list cycles sharing the displayed boundary label concatenate into one.
The identity holds even without distinctness assumptions on the lists. -/
theorem formPerm_append_overlap {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α) (x : α) :
    (l₁ ++ [x]).formPerm * (x :: l₂).formPerm = (l₁ ++ x :: l₂).formPerm := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₁ with
    | nil => simp [List.formPerm_cons_cons]
    | cons b l₁ =>
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using
        congrArg (fun p => swap a b * p) ih

theorem formPerm_ofFn_overlap {α : Type*} [DecidableEq α]
    (φ : ℕ → α) (m n : ℕ) :
    (List.ofFn (fun i : Fin (m + 1) => φ i.val)).formPerm *
      (List.ofFn (fun i : Fin (n + 1) => φ (m + i.val))).formPerm =
        (List.ofFn (fun i : Fin (m + n + 1) => φ i.val)).formPerm := by
  have h₁ : List.ofFn (fun i : Fin (m + 1) => φ i.val) =
      List.ofFn (fun i : Fin m => φ i.val) ++ [φ m] := by
    simpa using List.ofFn_succ_last (f := fun i : Fin (m + 1) => φ i.val)
  have h₂ : List.ofFn (fun i : Fin (n + 1) => φ (m + i.val)) =
      φ m :: List.ofFn (fun i : Fin n => φ (m + (i.val + 1))) := by
    simp [List.ofFn_succ]
  have h₃ : List.ofFn (fun i : Fin (m + n + 1) => φ i.val) =
      List.ofFn (fun i : Fin m => φ i.val) ++
        List.ofFn (fun i : Fin (n + 1) => φ (m + i.val)) := by
    simpa [Nat.add_assoc] using
      (List.ofFn_add (n := m) (m := n + 1)
        (f := fun i : Fin (m + (n + 1)) => φ i.val))
  rw [h₁, h₂, h₃, h₂]
  exact formPerm_append_overlap _ _ _

theorem formPerm_blocks_prod {α : Type*} [DecidableEq α]
    (φ : ℕ → α) (r u : ℕ) :
    (List.ofFn (fun j : Fin r =>
      (List.ofFn (fun i : Fin (u + 1) => φ (j.val * u + i.val))).formPerm)).prod =
        (List.ofFn (fun i : Fin (r * u + 1) => φ i.val)).formPerm := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    simpa only [Nat.succ_mul, Fin.val_cast] using formPerm_ofFn_overlap φ (r * u) u

/-- Evaluation of an injectively labelled cycle at one of its listed labels. -/
theorem formPerm_ofFn_apply {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (hf : Function.Injective f) (i : Fin n) :
    (List.ofFn f).formPerm (f i) =
      f ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ := by
  simpa using List.formPerm_apply_getElem (List.ofFn f)
    (List.nodup_ofFn.mpr hf) i.val (by simp)

theorem formPerm_append_singleton {α : Type*} [DecidableEq α]
    (x : α) (l : List α) (y : α) :
    ((x :: l) ++ [y]).formPerm =
      (x :: l).formPerm * swap ((x :: l).getLast (List.cons_ne_nil _ _)) y := by
  have he := List.dropLast_concat_getLast (List.cons_ne_nil x l)
  calc
    ((x :: l) ++ [y]).formPerm =
        ((x :: l).dropLast ++ [(x :: l).getLast (List.cons_ne_nil _ _), y]).formPerm := by
      apply congrArg List.formPerm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        congrArg (fun t : List α => t ++ [y]) he.symm
    _ = (x :: l).formPerm * swap ((x :: l).getLast (List.cons_ne_nil _ _)) y := by
      rw [List.formPerm_append_pair, he]

/-- A swap before a displayed cycle appends a new label to that cycle. -/
theorem swap_mul_formPerm {α : Type*} [DecidableEq α]
    (x y : α) (l : List α) (hy : y ∉ x :: l) :
    swap x y * (x :: l).formPerm = ((x :: l) ++ [y]).formPerm := by
  rw [formPerm_append_singleton, Equiv.mul_swap_eq_swap_mul,
    List.formPerm_apply_getLast, List.formPerm_apply_of_notMem hy]

/-- A swap between the heads of two disjoint cycles joins their displayed lists. -/
theorem swap_mul_formPerm_mul_formPerm {α : Type*} [DecidableEq α]
    (x y : α) (l₁ l₂ : List α) (hy : y ∉ x :: l₁) :
    swap x y * (x :: l₁).formPerm * (y :: l₂).formPerm =
      ((x :: l₁) ++ y :: l₂).formPerm := by
  rw [swap_mul_formPerm x y l₁ hy]
  exact formPerm_append_overlap _ _ _

/-- A swap between two displayed cycle boundaries cuts the cycle there. -/
theorem swap_mul_formPerm_split {α : Type*} [DecidableEq α]
    (x y : α) (l₁ l₂ : List α) (hy : y ∉ x :: l₁) :
    swap x y * ((x :: l₁) ++ y :: l₂).formPerm =
      (x :: l₁).formPerm * (y :: l₂).formPerm := by
  rw [← swap_mul_formPerm_mul_formPerm x y l₁ l₂ hy]
  simp [← mul_assoc]

theorem formPerm_disjoint_of_lists {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α) (h : l₁.Disjoint l₂) : l₁.formPerm.Disjoint l₂.formPerm := by
  intro x
  by_cases hx : x ∈ l₁
  · exact Or.inr (List.formPerm_apply_of_notMem (h hx))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

end ConjugacyDiametersPORC

import ConjugacyDiametersPORC.ConstituentWord
import Mathlib.Data.List.Rotate

/-!
# Cyclic shifts of constituent words

A cyclic shift conjugates the word value and preserves its resource vector.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

theorem cycleType_prod_rotate {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Perm α)) (p : ℕ) : (l.rotate p).prod.cycleType = l.prod.cycleType := by
  let k := p % l.length
  let a := (l.take k).prod
  let b := (l.drop k).prod
  have hl : l.prod = a * b := by
    rw [← List.prod_append, List.take_append_drop]
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append]
  change (b * a).cycleType = l.prod.cycleType
  calc
    (b * a).cycleType = (a⁻¹ * (a * b) * a).cycleType := by rw [inv_mul_cancel_left]
    _ = (a * b).cycleType := by
      simpa only [inv_inv] using (cycleType_conj (σ := a * b) (τ := a⁻¹))
    _ = l.prod.cycleType := by rw [← hl]

namespace ConstituentWord

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

def rotate (w : ConstituentWord lam α) (p : ℕ) : ConstituentWord lam α where
  factors := w.factors.rotate p
  isCycle := by
    intro a ha
    exact w.isCycle a (List.mem_rotate.mp ha)
  length_mem_J := by
    intro a ha
    exact w.length_mem_J a (List.mem_rotate.mp ha)

theorem rotate_c (w : ConstituentWord lam α) (p : ℕ) : (w.rotate p).c = w.c := by
  funext ℓ
  exact ((List.rotate_perm w.factors p).map (fun a => a.support.card)).count_eq (ℓ : ℕ)

theorem rotate_cycleType (w : ConstituentWord lam α) (p : ℕ) :
    (w.rotate p).value.cycleType = w.value.cycleType := cycleType_prod_rotate w.factors p

theorem rotate_hasTarget (w : ConstituentWord lam α) (p : ℕ) {r s : ℕ}
    (ht : w.HasTarget r s) : (w.rotate p).HasTarget r s := by
  unfold HasTarget
  rw [rotate_cycleType]
  exact ht

theorem rotate_length (w : ConstituentWord lam α) (p : ℕ) :
    (w.rotate p).factors.length = w.factors.length := List.length_rotate _ _

end ConstituentWord

end ConjugacyDiametersPORC

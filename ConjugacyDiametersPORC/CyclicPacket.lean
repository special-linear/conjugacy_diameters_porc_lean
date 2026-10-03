import ConjugacyDiametersPORC.WordRotation
import ConjugacyDiametersPORC.WordEmbedding
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.NoncommProd

/-!
# The cyclic array for a finite packet

Use one disjoint row of labels for each cyclic shift of a constituent word.
Each column contains one copy of every original constituent length.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

theorem noncommProd_fin_eq_ofFn {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M)
    (h : (↑(Finset.univ : Finset (Fin k)) : Set _).Pairwise (fun i j => Commute (f i) (f j))) :
    Finset.univ.noncommProd f h = (List.ofFn f).prod := by
  have hu : (List.finRange k).toFinset = Finset.univ := by ext i; simp
  have h' : (↑(List.finRange k).toFinset : Set _).Pairwise
      (fun i j => Commute (f i) (f j)) := by rwa [hu]
  calc
    _ = (List.finRange k).toFinset.noncommProd f h' :=
      Finset.noncommProd_congr hu.symm (fun _ _ => rfl) h
    _ = ((List.finRange k).map f).prod :=
      Finset.noncommProd_toFinset _ _ h' (List.nodup_finRange k)
    _ = _ := by rw [List.ofFn_eq_map]

namespace CyclicPacket

variable {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]

abbrev Index (w : ConstituentWord lam α) := Fin w.factors.length
abbrev Labels (w : ConstituentWord lam α) := Index w × α

def rowEmbedding (w : ConstituentWord lam α) (p : Index w) : α ↪ Labels w where
  toFun x := (p, x)
  inj' := by intro x y h; exact congrArg Prod.snd h

def factor (w : ConstituentWord lam α) (p j : Index w) : Perm α :=
  (w.rotate p.val).factors[j.val]'(by rw [w.rotate_length]; exact j.isLt)

noncomputable def entry (w : ConstituentWord lam α) (p j : Index w) : Perm (Labels w) :=
  (factor w p j).viaEmbedding (rowEmbedding w p)

theorem factor_mem (w : ConstituentWord lam α) (p j : Index w) :
    factor w p j ∈ (w.rotate p.val).factors := List.getElem_mem _

theorem entry_disjoint (w : ConstituentWord lam α) (p q j : Index w) (hpq : p ≠ q) :
    Disjoint (entry w p j) (entry w q j) := by
  rw [disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro y hy hz
  obtain ⟨x, hx⟩ := viaEmbedding_support_subset (factor w p j) (rowEmbedding w p) hy
  obtain ⟨z, hz⟩ := viaEmbedding_support_subset (factor w q j) (rowEmbedding w q) hz
  exact hpq (congrArg Prod.fst (hx.trans hz.symm))

noncomputable def column (w : ConstituentWord lam α) (j : Index w) :
    ConstituentWord lam (Labels w) where
  factors := List.ofFn (fun p => entry w p j)
  isCycle := by
    intro a ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
    exact viaEmbedding_isCycle _ _ ((w.rotate p.val).isCycle _ (factor_mem w p j))
  length_mem_J := by
    intro a ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
    rw [entry, viaEmbedding_support_card]
    exact (w.rotate p.val).length_mem_J _ (factor_mem w p j)

theorem column_pairwise (w : ConstituentWord lam α) (j : Index w) :
    (column w j).factors.Pairwise Disjoint :=
  List.pairwise_ofFn.mpr (fun _ _ hpq => entry_disjoint w _ _ j (ne_of_lt hpq))

theorem column_lengths (w : ConstituentWord lam α) (j : Index w) :
    ((column w j).factors.map (fun a => a.support.card)) =
      ((w.rotate j.val).factors.map (fun a => a.support.card)) := by
  apply List.ext_getElem
  · simp [column, ConstituentWord.rotate]
  · intro p hp hp'
    simp only [column, List.getElem_map, List.getElem_ofFn, entry,
      viaEmbedding_support_card, factor, ConstituentWord.rotate]
    simp only [List.getElem_rotate, Nat.add_comm]

theorem column_c (w : ConstituentWord lam α) (j : Index w) : (column w j).c = w.c := by
  funext ℓ
  change (((column w j).factors.map (fun a => a.support.card)).count (ℓ : ℕ)) = w.c ℓ
  rw [column_lengths]
  exact congrFun (w.rotate_c j.val) ℓ

theorem entry_apply (w : ConstituentWord lam α) (p j : Index w) (x : α) :
    entry w p j (p, x) = (p, factor w p j x) := viaEmbedding_apply _ _ x

theorem entry_fixed (w : ConstituentWord lam α) (p q j : Index w) (hpq : p ≠ q) (x : α) :
    entry w q j (p, x) = (p, x) := by
  apply viaEmbedding_apply_of_notMem
  rintro ⟨y, hy⟩
  exact hpq (congrArg Prod.fst hy).symm

theorem column_apply (w : ConstituentWord lam α) (p j : Index w) (x : α) :
    (column w j).value (p, x) = (p, factor w p j x) := by
  classical
  let f := fun q => entry w q j
  let comm : (↑(Finset.univ : Finset (Index w)) : Set _).Pairwise
      (fun q t => Commute (f q) (f t)) :=
    fun q _ t _ hqt => (entry_disjoint w q t j hqt).commute
  let comm' : (↑(Finset.univ.erase p) : Set _).Pairwise (fun q t => Commute (f q) (f t)) :=
    fun q _ t _ hqt => (entry_disjoint w q t j hqt).commute
  change (List.ofFn f).prod (p, x) = _
  rw [← noncommProd_fin_eq_ofFn f comm,
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ p) f comm (comm' := comm'),
    mul_apply]
  have hfix : (Finset.univ.erase p).noncommProd f comm' (p, x) = (p, x) := by
    apply Finset.noncommProd_induction (Finset.univ.erase p) f comm' (fun g => g (p, x) = (p, x))
    · intro a b ha hb
      rw [mul_apply, hb, ha]
    · rfl
    · intro q hq
      exact entry_fixed w p q j (Finset.mem_erase.mp hq).1.symm x
  rw [hfix]
  exact entry_apply w p j x

noncomputable def value (w : ConstituentWord lam α) : Perm (Labels w) :=
  (List.ofFn (fun j => (column w j).value)).prod

private theorem columns_prod_apply (w : ConstituentWord lam α) (p : Index w)
    (l : List (Index w)) (x : α) :
    (l.map (fun j => (column w j).value)).prod (p, x) =
      (p, (l.map (factor w p)).prod x) := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply]
    rw [ih, column_apply]

theorem row_factors (w : ConstituentWord lam α) (p : Index w) :
    List.ofFn (factor w p) = (w.rotate p.val).factors := by
  apply List.ext_getElem
  · simp [ConstituentWord.rotate]
  · intro j hj hj'
    simp [factor]

theorem value_apply (w : ConstituentWord lam α) (p : Index w) (x : α) :
    value w (p, x) = (p, (w.rotate p.val).value x) := by
  unfold value
  rw [List.ofFn_eq_map, columns_prod_apply, ← List.ofFn_eq_map, row_factors]
  rfl

noncomputable def rowValue (w : ConstituentWord lam α) (p : Index w) : Perm (Labels w) :=
  (w.rotate p.val).value.viaEmbedding (rowEmbedding w p)

theorem rowValue_disjoint (w : ConstituentWord lam α) (p q : Index w) (hpq : p ≠ q) :
    Disjoint (rowValue w p) (rowValue w q) := by
  rw [disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro y hy hz
  obtain ⟨x, hx⟩ := viaEmbedding_support_subset (w.rotate p.val).value (rowEmbedding w p) hy
  obtain ⟨z, hz⟩ := viaEmbedding_support_subset (w.rotate q.val).value (rowEmbedding w q) hz
  exact hpq (congrArg Prod.fst (hx.trans hz.symm))

theorem rowValues_pairwise (w : ConstituentWord lam α) :
    (↑(Finset.univ : Finset (Index w)) : Set _).Pairwise
      (fun p q => Disjoint (rowValue w p) (rowValue w q)) :=
  fun p _ q _ hpq => rowValue_disjoint w p q hpq

theorem rowValue_fixed (w : ConstituentWord lam α) (p q : Index w) (hpq : p ≠ q) (x : α) :
    rowValue w q (p, x) = (p, x) := by
  apply viaEmbedding_apply_of_notMem
  rintro ⟨y, hy⟩
  exact hpq (congrArg Prod.fst hy).symm

theorem value_eq_rows (w : ConstituentWord lam α) :
    value w = Finset.univ.noncommProd (rowValue w)
      ((rowValues_pairwise w).imp (fun _ _ h => h.commute)) := by
  classical
  apply Equiv.ext
  rintro ⟨p, x⟩
  let f := rowValue w
  let comm := (rowValues_pairwise w).imp (fun _ _ h => h.commute)
  let comm' : (↑(Finset.univ.erase p) : Set _).Pairwise (fun q t => Commute (f q) (f t)) :=
    fun q _ t _ hqt => (rowValue_disjoint w q t hqt).commute
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ p) f comm (comm' := comm'),
    mul_apply]
  have hfix : (Finset.univ.erase p).noncommProd f comm' (p, x) = (p, x) := by
    apply Finset.noncommProd_induction (Finset.univ.erase p) f comm' (fun g => g (p, x) = (p, x))
    · intro a b ha hb
      rw [mul_apply, hb, ha]
    · rfl
    · intro q hq
      exact rowValue_fixed w p q (Finset.mem_erase.mp hq).1.symm x
  rw [hfix, value_apply]
  exact (viaEmbedding_apply (w.rotate p.val).value (rowEmbedding w p) x).symm

theorem value_cycleType (w : ConstituentWord lam α) {r s : ℕ} (ht : w.HasTarget r s) :
    (value w).cycleType = Multiset.replicate (w.factors.length * s) r := by
  rw [value_eq_rows, Disjoint.cycleType_noncommProd (rowValues_pairwise w)]
  simp only [rowValue, viaEmbedding_cycleType, ConstituentWord.rotate_cycleType]
  change w.value.cycleType = Multiset.replicate s r at ht
  simp [ht, Multiset.nsmul_replicate]

end CyclicPacket

end ConjugacyDiametersPORC

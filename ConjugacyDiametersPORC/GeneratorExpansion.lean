import ConjugacyDiametersPORC.Diameter
import ConjugacyDiametersPORC.ConstituentWord

/-!
# Expansion of generators into constituent cycles

Expanding a word of `q` generators gives the same value and resource vector
`q m`. The constituent factors of each generator are its disjoint cycle factors.
-/

namespace ConjugacyDiametersPORC

open Equiv.Perm

/-- Expand one generator into its nontrivial constituent cycles. -/
def expandGenerator (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (hg : g ∈ C lam n) : ConstituentWord lam (Fin n) where
  factors := g.cycleFactors.val
  isCycle := g.cycleFactors.property.2.1
  length_mem_J := by
    intro a ha
    rw [lam.mem_J, ← (mem_C lam g).mp hg]
    rw [cycleType_eq g.cycleFactors.val g.cycleFactors.property.1
      g.cycleFactors.property.2.1 g.cycleFactors.property.2.2]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem expandGenerator_value (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (hg : g ∈ C lam n) : (expandGenerator lam g hg).value = g :=
  g.cycleFactors.property.1

theorem expandGenerator_c (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (hg : g ∈ C lam n) :
    (expandGenerator lam g hg).c = fun (ℓ : lam.J) => lam.m ℓ := by
  funext ℓ
  have htype := cycleType_eq g.cycleFactors.val g.cycleFactors.property.1
    g.cycleFactors.property.2.1 g.cycleFactors.property.2.2
  have hparts := ((mem_C lam g).mp hg).symm.trans htype
  change (g.cycleFactors.val.map (fun a => a.support.card)).count (ℓ : ℕ) =
    lam.parts.count (ℓ : ℕ)
  rw [hparts]
  simp [Function.comp_def]

theorem expandGenerator_length (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (hg : g ∈ C lam n) : (expandGenerator lam g hg).factors.length = lam.h := by
  rw [← ConstituentWord.sum_c, expandGenerator_c, Finset.sum_coe_sort lam.J lam.m]
  exact lam.h_eq_sum_m.symm

/-- Expand each generator in a word, preserving the order between generators. -/
def expandWord (lam : CycleType) {n : ℕ} :
    (w : List (SymmetricGroup n)) → (∀ a ∈ w, a ∈ C lam n) →
      ConstituentWord lam (Fin n)
  | [], _ => ConstituentWord.nil
  | a :: w, hw => (expandGenerator lam a (hw a (List.mem_cons_self))).append
      (expandWord lam w (fun b hb => hw b (List.mem_cons_of_mem a hb)))

theorem expandWord_value (lam : CycleType) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C lam n) : (expandWord lam w hw).value = w.prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [expandWord, ConstituentWord.value_append, expandGenerator_value, ih, List.prod_cons]

theorem expandWord_c (lam : CycleType) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C lam n) :
    (expandWord lam w hw).c = w.length • (fun (ℓ : lam.J) => lam.m ℓ) := by
  induction w with
  | nil => simp [expandWord]
  | cons a w ih =>
    rw [expandWord, ConstituentWord.c_append, expandGenerator_c, ih]
    funext ℓ
    simp [Pi.smul_apply, nsmul_eq_mul, add_mul, add_comm]

theorem expandWord_delta (lam : CycleType) {n : ℕ} (w : List (SymmetricGroup n))
    (hw : ∀ a ∈ w, a ∈ C lam n) : δ lam (expandWord lam w hw).c = w.length * lam.d := by
  rw [expandWord_c, delta_smul, delta_inventory]

end ConjugacyDiametersPORC

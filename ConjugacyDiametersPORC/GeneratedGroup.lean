import ConjugacyDiametersPORC.Diameter
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The generated symmetric or alternating group

For `n ≥ b + 1`, the generating class has a fixed label available. A commutator
with a transposition produces a three-cycle. Conjugation then gives every
three-cycle, and generator parity determines the generated group.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

theorem conj_mem_C (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ C lam n) (τ : SymmetricGroup n) : τ * g * τ⁻¹ ∈ C lam n := by
  rw [mem_C, cycleType_conj]
  exact hg

theorem conj_mem_G (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ G lam n) (τ : SymmetricGroup n) : τ * g * τ⁻¹ ∈ G lam n := by
  change g ∈ Subgroup.closure (C lam n) at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_mem_C lam hx τ)
  | one => simp
  | mul x y _ _ hx hy =>
    simpa [mul_assoc] using (G lam n).mul_mem hx hy
  | inv x _ hx =>
    simpa [mul_assoc] using (G lam n).inv_mem hx

instance G_normal (lam : CycleType) (n : ℕ) : (G lam n).Normal where
  conj_mem := fun _ hg τ => conj_mem_G lam hg τ

theorem sign_of_mem_C (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ C lam n) : sign g = (-1 : ℤˣ) ^ lam.d := by
  rw [sign_of_cycleType, (mem_C lam g).mp hg]
  change (-1 : ℤˣ) ^ (lam.b + lam.h) = (-1 : ℤˣ) ^ lam.d
  have he : lam.b + lam.h = lam.d + 2 * lam.h := by
    have := lam.h_add_d
    omega
  rw [he, pow_add, pow_mul]
  simp

theorem exists_threeCycle_mem_G (lam : CycleType) {n : ℕ} (hn : lam.b + 1 ≤ n) :
    ∃ κ : SymmetricGroup n, κ ∈ G lam n ∧ κ.IsThreeCycle := by
  obtain ⟨g, hg⟩ := (C_nonempty_iff lam n).mpr (by omega)
  have hgG : g ∈ G lam n := Subgroup.subset_closure hg
  have hcard : g.support.card = lam.b := by
    rw [← sum_cycleType, (mem_C lam g).mp hg]
    rfl
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hcard ▸ lam.b_pos)
  have hsmall : g.support.card < (Finset.univ : Finset (Fin n)).card := by
    simpa [hcard] using (show lam.b < n by omega)
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hfix : g z = z := by simpa only [mem_support, not_not] using hz
  have hxz : x ≠ z := ne_of_mem_of_not_mem hx hz
  have hgxz : g x ≠ z := ne_of_mem_of_not_mem (apply_mem_support.mpr hx) hz
  let κ := g * swap x z * g⁻¹ * swap x z
  have hκ : κ ∈ G lam n := by
    have hconj := conj_mem_G lam ((G lam n).inv_mem hgG) (swap x z)
    simpa [κ, mul_assoc] using (G lam n).mul_mem hgG hconj
  have heq : κ = swap (g x) z * swap x z := by
    dsimp [κ]
    rw [mul_swap_eq_swap_mul g x z, hfix]
    simp [mul_assoc]
  refine ⟨κ, hκ, ?_⟩
  rw [heq, swap_comm (g x) z, swap_comm x z]
  exact isThreeCycle_swap_mul_swap_same hgxz.symm hxz.symm (mem_support.mp hx)

theorem alternatingGroup_le_G (lam : CycleType) {n : ℕ} (hn : lam.b + 1 ≤ n) :
    alternatingGroup (Fin n) ≤ G lam n := by
  obtain ⟨κ, hκ, hκ3⟩ := exists_threeCycle_mem_G lam hn
  rw [← closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le _).mpr
  intro σ hσ
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_of_cycleType_eq (hκ3.cycleType.trans hσ.cycleType.symm))
  exact hτ ▸ conj_mem_G lam hκ τ

theorem G_eq_alternatingGroup (lam : CycleType) {n : ℕ}
    (hn : lam.b + 1 ≤ n) (hd : Even lam.d) : G lam n = alternatingGroup (Fin n) := by
  apply le_antisymm _ (alternatingGroup_le_G lam hn)
  apply (Subgroup.closure_le _).mpr
  intro g hg
  change g ∈ alternatingGroup (Fin n)
  rw [mem_alternatingGroup, sign_of_mem_C lam hg]
  exact hd.neg_one_pow

theorem G_eq_symmetricGroup (lam : CycleType) {n : ℕ}
    (hn : lam.b + 1 ≤ n) (hd : Odd lam.d) : G lam n = ⊤ := by
  obtain ⟨g, hg⟩ := (C_nonempty_iff lam n).mpr (by omega)
  have hgG : g ∈ G lam n := Subgroup.subset_closure hg
  have hsign : sign g = -1 := (sign_of_mem_C lam hg).trans hd.neg_one_pow
  have hA := alternatingGroup_le_G lam hn
  rw [Subgroup.eq_top_iff']
  intro σ
  rcases Int.isUnit_eq_one_or (sign σ).isUnit with hσ | hσ
  · exact hA (mem_alternatingGroup.mpr (Units.ext hσ))
  · have hσ' : sign σ = -1 := Units.ext hσ
    have hrest : g⁻¹ * σ ∈ alternatingGroup (Fin n) := by
      simp [mem_alternatingGroup, map_mul, map_inv, hsign, hσ']
    simpa using (G lam n).mul_mem hgG (hA hrest)

end ConjugacyDiametersPORC

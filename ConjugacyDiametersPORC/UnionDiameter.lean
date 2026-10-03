import ConjugacyDiametersPORC.CycleFamily
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Word lengths and diameters for finite unions -/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

def IsFactorization (lam : CycleFamily) {n : ℕ} (g : SymmetricGroup n)
    (w : List (SymmetricGroup n)) : Prop := (∀ a ∈ w, a ∈ C lam n) ∧ w.prod = g

def factorizationLengths (lam : CycleFamily) {n : ℕ} (g : SymmetricGroup n) : Set ℕ :=
  {k | ∃ w, IsFactorization lam g w ∧ w.length = k}

noncomputable def L (lam : CycleFamily) {n : ℕ} (g : G lam n) : ℕ :=
  sInf (factorizationLengths lam (g : SymmetricGroup n))

noncomputable def D (lam : CycleFamily) (n : ℕ) : ℕ := sSup (Set.range (L lam (n := n)))

@[simp]
theorem isFactorization_nil (lam : CycleFamily) (n : ℕ) :
    IsFactorization lam (1 : SymmetricGroup n) [] := by
  simp [IsFactorization]

theorem isFactorization_singleton (lam : CycleFamily) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ C lam n) : IsFactorization lam g [g] := by
  simpa [IsFactorization] using hg

theorem IsFactorization.append {lam : CycleFamily} {n : ℕ}
    {g₁ g₂ : SymmetricGroup n} {w₁ w₂ : List (SymmetricGroup n)}
    (h₁ : IsFactorization lam g₁ w₁) (h₂ : IsFactorization lam g₂ w₂) :
    IsFactorization lam (g₁ * g₂) (w₁ ++ w₂) := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h₁.1 a ha
    · exact h₂.1 a ha
  · rw [List.prod_append, h₁.2, h₂.2]

theorem IsFactorization.inverse {lam : CycleFamily} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) :
    IsFactorization lam g⁻¹ ((w.map (fun a => a⁻¹)).reverse) := by
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    exact (inv_mem_C_iff lam b).mpr (hw.1 b hb)
  · rw [← List.prod_inv_reverse, hw.2]

theorem exists_factorization_of_mem (lam : CycleFamily) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ G lam n) : ∃ w, IsFactorization lam g w := by
  change g ∈ Subgroup.closure (C lam n) at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact ⟨[x], isFactorization_singleton lam hx⟩
  | inv_mem x hx =>
    exact ⟨[x⁻¹], isFactorization_singleton lam ((inv_mem_C_iff lam x).mpr hx)⟩
  | one => exact ⟨[], isFactorization_nil lam n⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w₁, hw₁⟩ := hx
    obtain ⟨w₂, hw₂⟩ := hy
    exact ⟨w₁ ++ w₂, hw₁.append hw₂⟩

theorem exists_factorization (lam : CycleFamily) {n : ℕ} (g : G lam n) :
    ∃ w, IsFactorization lam (g : SymmetricGroup n) w :=
  exists_factorization_of_mem lam g.property

theorem factorizationLengths_nonempty (lam : CycleFamily) {n : ℕ} (g : G lam n) :
    (factorizationLengths lam (g : SymmetricGroup n)).Nonempty := by
  obtain ⟨w, hw⟩ := exists_factorization lam g
  exact ⟨w.length, w, hw, rfl⟩

theorem exists_shortest_factorization (lam : CycleFamily) {n : ℕ} (g : G lam n) :
    ∃ w, IsFactorization lam (g : SymmetricGroup n) w ∧ w.length = L lam g :=
  Nat.sInf_mem (factorizationLengths_nonempty lam g)

theorem L_le_length {lam : CycleFamily} {n : ℕ} {g : G lam n}
    {w : List (SymmetricGroup n)} (hw : IsFactorization lam (g : SymmetricGroup n) w) :
    L lam g ≤ w.length :=
  Nat.sInf_le ⟨w, hw, rfl⟩

theorem L_le_iff (lam : CycleFamily) {n : ℕ} (g : G lam n) (k : ℕ) :
    L lam g ≤ k ↔ ∃ w, IsFactorization lam (g : SymmetricGroup n) w ∧ w.length ≤ k := by
  constructor
  · intro hk
    obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
    exact ⟨w, hw, hlen ▸ hk⟩
  · rintro ⟨w, hw, hlen⟩
    exact (L_le_length hw).trans hlen

@[simp]
theorem L_eq_zero_iff (lam : CycleFamily) {n : ℕ} (g : G lam n) :
    L lam g = 0 ↔ g = 1 := by
  constructor
  · intro hg
    obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
    have hw0 : w = [] := List.length_eq_zero_iff.mp (hlen.trans hg)
    apply Subtype.ext
    simpa [hw0] using hw.2.symm
  · rintro rfl
    exact Nat.eq_zero_of_le_zero
      (L_le_length (g := (1 : G lam n)) (w := []) (isFactorization_nil lam n))

@[simp]
theorem L_one (lam : CycleFamily) (n : ℕ) : L lam (1 : G lam n) = 0 :=
  (L_eq_zero_iff lam 1).mpr rfl

theorem L_mul_le (lam : CycleFamily) {n : ℕ} (g₁ g₂ : G lam n) :
    L lam (g₁ * g₂) ≤ L lam g₁ + L lam g₂ := by
  obtain ⟨w₁, hw₁, hlen₁⟩ := exists_shortest_factorization lam g₁
  obtain ⟨w₂, hw₂, hlen₂⟩ := exists_shortest_factorization lam g₂
  simpa [List.length_append, hlen₁, hlen₂] using
    L_le_length (g := g₁ * g₂) (hw₁.append hw₂)

theorem L_inv_le (lam : CycleFamily) {n : ℕ} (g : G lam n) : L lam g⁻¹ ≤ L lam g := by
  obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
  simpa [hlen] using L_le_length (g := g⁻¹) hw.inverse

@[simp]
theorem L_inv (lam : CycleFamily) {n : ℕ} (g : G lam n) : L lam g⁻¹ = L lam g := by
  apply le_antisymm (L_inv_le lam g)
  simpa using L_inv_le lam g⁻¹

theorem L_le_D (lam : CycleFamily) {n : ℕ} (g : G lam n) : L lam g ≤ D lam n := by
  apply le_csSup (Set.finite_range (L lam (n := n))).bddAbove
  exact Set.mem_range_self g

theorem exists_length_eq_D (lam : CycleFamily) (n : ℕ) :
    ∃ g : G lam n, L lam g = D lam n :=
  (Set.range_nonempty (L lam (n := n))).csSup_mem (Set.finite_range _)

theorem D_le_iff (lam : CycleFamily) (n k : ℕ) :
    D lam n ≤ k ↔ ∀ g : G lam n, L lam g ≤ k := by
  constructor
  · intro hk g
    exact (L_le_D lam g).trans hk
  · intro hk
    obtain ⟨g, hg⟩ := exists_length_eq_D lam n
    exact hg ▸ hk g

end FiniteUnion
end ConjugacyDiametersPORC
